/-
Copyright 2026 Alliana
SPDX-License-Identifier: Apache-2.0

Portions of this file are adapted from leanfran (https://github.com/conao3/lean-leanfran, commit
07d4f2a), `langs/Clojure/LeanClj/EmitClj.lean`, licensed under the Apache License, Version 2.0.

- Taken with few changes: `skipRc`, `tailCallOf?`, `bodyCallees` and `collect` (`collect` also
  skips the externs that the runtime implements).
- Rewritten for Emela from the original's design: `mangle`, `snake` (from `kebab`), `jumpCounts`
  (from `joinPoints`), `emitExpr`, `emitPap` and `emitBody`. They write Emela text instead of
  Clojure forms, make a join point a local fn instead of `letfn`, and drop the original's
  trampolines and `loop`/`recur`.
- The rest of the file is new.
-/

import Lean
import LeanEmela.Types

/-! # Lean IR → Emela

The IR declarations reachable from a set of root functions are read from the environment with
`Lean.IR.findEnvDecl` and written as one Emela module that calls the runtime `LeanRt`
(`emela/src/lean_rt.emel`).

- Every value is a `LeanRt.Obj`, and every generated function takes and returns `Obj`.
- Reference counting (`inc`, `dec`, `del`) is dropped. `isShared` always answers "shared", so the
  branches that update an object in place (`set`, `setTag`, ...) are never taken and are emitted
  as `LeanRt.unreachable()`.
- A join point is a local fn. A join point that is jumped to once is expanded at the jump, so that
  a self tail call inside it stays a tail call of the enclosing function (`[fn.loop]`: a call
  inside a local fn is not one). A self tail call inside a join point jumped to more than once
  uses the stack.
- Calls to `Nat` externs go to `LeanRt.nat_*`. Any other extern stops the emission with an error
  that names it. -/

open Lean Lean.IR Elab Command

namespace LeanEmela

/-! ## Names -/

/-- An Emela lowercase name for a Lean name. `_` is written `_u`, `.` is written `_d`, and any
    other character that is not an ASCII letter or digit is written `_x<hex>z`, so the encoding
    is injective. -/
def mangle (n : Name) : String := Id.run do
  let mut acc := "lean_"
  for c in (n.toString (escape := false)).toList do
    if c == '_' then acc := acc ++ "_u"
    else if c == '.' then acc := acc ++ "_d"
    else if c.toNat < 128 && c.isAlphanum then acc := acc.push c
    else acc := acc ++ "_x" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "z"
  return acc

/-- `toBase64` → `to_base64`, `find?` → `find`: the public name of a root function. -/
def snake (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut acc := ""
  for h : i in [0:cs.size] do
    let c := cs[i]
    if c.isUpper then
      if i > 0 && (cs[i-1]!.isLower || cs[i-1]!.isDigit) then acc := acc.push '_'
      acc := acc.push c.toLower
    else if c.isAlphanum || c == '_' then acc := acc.push c
    -- `find?` and `get!` are named by what they compute: the mark has no Emela spelling.
    else if c == '?' || c == '!' then pure ()
    else acc := acc.push '_'
  return acc

def varName (x : VarId) : String := s!"x_{x.idx}"

def jpName (j : JoinPointId) : String := s!"block_{j.idx}"

/-! ## Runtime externs -/

/-- The externs that the runtime implements, by the Lean declaration they implement. -/
def runtimeExterns : List (Name × String) := [
  (``Nat.add, "nat_add"), (``Nat.sub, "nat_sub"), (``Nat.mul, "nat_mul"),
  (``Nat.div, "nat_div"), (``Nat.mod, "nat_mod"),
  (``Nat.decEq, "nat_dec_eq"), (``Nat.decLt, "nat_dec_lt"), (``Nat.decLe, "nat_dec_le"),
  (``Nat.beq, "nat_dec_eq"), (``Nat.blt, "nat_dec_lt"), (``Nat.ble, "nat_dec_le"),
  (``Nat.shiftRight, "nat_shift_right"), (``Nat.shiftLeft, "nat_shift_left"),
  (``Nat.land, "nat_land"), (``Nat.lor, "nat_lor"), (``Nat.xor, "nat_xor"),
  (``Array.mkEmpty, "array_mk_empty"), (``Array.push, "array_push"),
  (``Array.toList, "array_to_list")]

def runtimeExtern? (c : Name) : Option String :=
  (runtimeExterns.find? (·.1 == c)).map fun (_, f) => s!"LeanRt.{f}"

/-! ## Emission -/

structure Ctx where
  decls : Std.HashMap Name Decl
  self : Name
  /-- Join points jumped to once, expanded at the jump: parameters and body. -/
  inlineJps : Std.HashMap Nat (Array Param × FnBody) := {}
  inlineSet : Std.HashSet Nat := {}

abbrev EmitM := ReaderT Ctx (Except String)

def argStr : Arg → String
  | .var x => varName x
  | .erased => "LeanRt.erased()"

def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

/-- The function a call of `c` goes to, with the arguments it keeps. -/
def callee (c : Name) (ps? : Option (Array Param)) (ys : List String) : EmitM String := do
  if let some f := runtimeExtern? c then
    -- The runtime functions take every argument of the IR call, erased ones included.
    return callStr f ys
  let ctx ← read
  match ctx.decls[c]? with
  | some (.extern ..) => throw s!"extern not supported by the runtime: {c}"
  | some _ => return callStr (mangle c) ys
  | none => throw s!"function was not collected: {c} ({ps?.isSome})"

def emitLit (v : LitVal) : Except String String :=
  match v with
  | .num n => if n < 2 ^ 63 then .ok s!"LeanRt.nat({n})" else .error s!"literal does not fit in Int64: {n}"
  | .str _ => .error "String literals are not supported yet"

def ctorStr (i : CtorInfo) (ys : Array Arg) : Except String String :=
  if i.usize != 0 || i.ssize != 0 then .error s!"constructors with scalar fields are not supported yet: {i.name}"
  else if i.size == 0 then .ok s!"LeanRt.nat({i.cidx})"
  else .ok (callStr "LeanRt.ctor" [toString i.cidx, list (ys.toList.map argStr)])

def arity (decls : Std.HashMap Name Decl) (c : Name) : Except String Nat :=
  match decls[c]? with
  | some d => .ok d.params.size
  | none => .error s!"function was not collected: {c}"

def emitPap (c : Name) (ys : Array Arg) : EmitM String := do
  let ctx ← read
  let n ← arity ctx.decls c
  let args := (List.range n).map fun i => s!"LeanRt.arg(a, {i})"
  let body ← callee c none args
  return callStr "LeanRt.pap" [toString n, s!"|a| {body}", list (ys.toList.map argStr)]

def emitExpr : IR.Expr → EmitM String
  | .ctor i ys => liftExcept (ctorStr i ys)
  | .reset _ _ => return "LeanRt.erased()"
  | .reuse _ i _ ys => liftExcept (ctorStr i ys)
  | .proj i x => return callStr "LeanRt.proj" [varName x, toString i]
  | .uproj .. | .sproj .. => throw "scalar fields are not supported yet"
  | .fap c ys => do
    let ctx ← read
    match ctx.decls[c]? with
    | some (.fdecl _ ps ..) =>
      if ps.isEmpty then return callStr (mangle c) [] else callee c (some ps) (ys.toList.map argStr)
    | _ => callee c none (ys.toList.map argStr)
  | .pap c ys => emitPap c ys
  | .ap x ys => return callStr "LeanRt.apply" [varName x, list (ys.toList.map argStr)]
  | .box _ x | .unbox x => return varName x
  | .lit v => liftExcept (emitLit v)
  | .isShared x => return callStr "LeanRt.is_shared" [varName x]
where
  liftExcept {α} : Except String α → EmitM α
    | .ok a => pure a
    | .error e => throw e

partial def skipRc : FnBody → FnBody
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => skipRc b
  | b => b

/-- `let x := c ys; (rc ops)*; ret x` -/
def tailCallOf? : FnBody → Option (Name × Array Arg)
  | .vdecl x _ (.fap c ys) b =>
    match skipRc b with
    | .ret (.var r) => if r == x then some (c, ys) else none
    | _ => none
  | _ => none

/-- The number of `jmp`s to each join point of a body. -/
partial def jumpCounts (b : FnBody) (acc : Std.HashMap Nat Nat) : Std.HashMap Nat Nat :=
  match b with
  | .jdecl _ _ v k => jumpCounts k (jumpCounts v acc)
  | .case _ _ _ alts => alts.foldl (fun acc a => jumpCounts a.body acc) acc
  | .jmp j _ => acc.alter j.idx fun n => some (n.getD 0 + 1)
  | .ret _ | .unreachable => acc
  | b => jumpCounts b.body acc

def pad (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

/-- The lines of a block: statements, then the value of the block. -/
partial def emitBody (b : FnBody) (ind : Nat) : EmitM (Array String) := do
  if let some (c, ys) := tailCallOf? b then
    let e ← emitExpr (.fap c ys)
    return #[pad ind ++ e]
  match b with
  | .vdecl x _ e k =>
    let line := pad ind ++ s!"{varName x} = {← emitExpr e}"
    return #[line] ++ (← emitBody k ind)
  | .inc _ _ _ _ k | .dec _ _ _ _ k | .del _ k => emitBody k ind
  | .jdecl j xs v k =>
    let ctx ← read
    if ctx.inlineSet.contains j.idx then
      withReader (fun c => { c with inlineJps := c.inlineJps.insert j.idx (xs, v) }) (emitBody k ind)
    else
      let ps := ", ".intercalate (xs.toList.map fun p => s!"{varName p.x}: Obj")
      let head := pad ind ++ s!"fn {jpName j}({ps}) -> Obj \{"
      let body ← emitBody v (ind + 1)
      return #[head] ++ body ++ #[pad ind ++ "}"] ++ (← emitBody k ind)
  | .set .. | .uset .. | .sset .. | .setTag .. => return #[pad ind ++ "LeanRt.unreachable()"]
  | .case _ x _ alts =>
    let mut arms : Array (Option Nat × FnBody) := #[]
    for alt in alts do
      match alt with
      | .ctor info body => arms := arms.push (some info.cidx, body)
      | .default body => arms := arms.push (none, body)
    if h : arms.size = 1 then
      return ← emitBody arms[0].2 ind
    let mut lines := #[pad ind ++ s!"LeanRt.tag({varName x}) match \{"]
    for (pat, body) in arms do
      let p := match pat with | some i => toString i | none => "_"
      lines := lines.push (pad (ind + 1) ++ s!"{p} -> \{")
      lines := lines ++ (← emitBody body (ind + 2))
      lines := lines.push (pad (ind + 1) ++ "}")
    unless arms.any (·.1.isNone) do
      lines := lines.push (pad (ind + 1) ++ "_ -> LeanRt.unreachable()")
    return lines.push (pad ind ++ "}")
  | .ret y => return #[pad ind ++ argStr y]
  | .jmp j ys =>
    let ctx ← read
    match ctx.inlineJps[j.idx]? with
    | some (xs, v) =>
      let binds := (xs.zip ys).toList.map fun (p, y) => pad ind ++ s!"{varName p.x} = {argStr y}"
      return binds.toArray ++ (← emitBody v ind)
    | none => return #[pad ind ++ callStr (jpName j) (ys.toList.map argStr)]
  | .unreachable => return #[pad ind ++ "LeanRt.unreachable()"]

def emitDecl (decls : Std.HashMap Name Decl) : Decl → Except String (Array String)
  | .extern .. => .ok #[]
  | .fdecl f ps _ body _ => do
    let counts := jumpCounts body {}
    let inlineSet := counts.fold (fun s i n => if n == 1 then s.insert i else s) {}
    let lines ← (emitBody body 1).run { decls, self := f, inlineSet }
    let params := ", ".intercalate (ps.toList.map fun p => s!"{varName p.x}: Obj")
    return #[s!"# {f}", s!"fn {mangle f}({params}) -> Obj \{"] ++ lines ++ #["}", ""]

/-! ## Collection -/

partial def bodyCallees (b : FnBody) (acc : Array Name) : Array Name :=
  match b with
  | .vdecl _ _ e k =>
    let acc := match e with
      | .fap c _ | .pap c _ => acc.push c
      | _ => acc
    bodyCallees k acc
  | .jdecl _ _ v k => bodyCallees k (bodyCallees v acc)
  | .case _ _ _ alts => alts.foldl (fun acc a => bodyCallees a.body acc) acc
  | .ret _ | .jmp .. | .unreachable => acc
  | b => bodyCallees b.body acc

/-- The declarations reachable from `roots`, in the order they are first reached. Calls to the
    runtime's externs are not followed. -/
def collect (env : Environment) (roots : Array Name) : Except String (Array Decl) := do
  let mut seen : Std.HashSet Name := {}
  let mut out : Array Decl := #[]
  let mut stack := roots.reverse
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n || (runtimeExtern? n).isSome then continue
    seen := seen.insert n
    let some d := findEnvDecl env n | throw s!"no IR for {n} (is it noncomputable?)"
    out := out.push d
    if let .fdecl _ _ _ b _ := d then
      for c in (bodyCallees b #[]).reverse do
        unless seen.contains c do stack := stack.push c
  return out

/-- A public function of a root: it takes and returns Emela values, and converts them to and from
    `Obj` with the descriptions of their Lean types. -/
def emitPublic (r : Name) (d : Decl) (sig : Array (Option TyOut) × TyOut) : Array String := Id.run do
  let (params, result) := sig
  let mut decl : Array String := #[]
  let mut args : Array String := #[]
  for h : i in [0:params.size] do
    match params[i] with
    | some o =>
      decl := decl.push s!"a_{i}: {o.ty}"
      args := args.push (callStr "LeanRt.input" [s!"a_{i}", o.desc])
    | none => args := args.push "LeanRt.erased()"
  let call := callStr (mangle d.name) args.toList
  return #[
    s!"pub fn {snake r.getString!}({", ".intercalate decl.toList}) -> {result.ty} \{",
    "  " ++ callStr "LeanRt.output" [call, result.desc],
    "}",
    ""]

/-- The whole module: the Emela types of the Lean types met at the boundary, one public function
    per root, named by the last component of its Lean name, and the generated functions. -/
def emitModule (env : Environment) (roots : Array Name)
    (sigs : Std.HashMap Name (Array (Option TyOut) × TyOut)) (types : Array String) :
    Except String String := do
  let ds ← collect env roots
  let missing := ds.filterMap fun d => match d with
    | .extern n .. => some (toString n)
    | _ => none
  unless missing.isEmpty do
    throw s!"externs not supported by the runtime: {", ".intercalate missing.toList}"
  let decls : Std.HashMap Name Decl := ds.foldl (fun m d => m.insert d.name d) {}
  let mut lines : Array String := #[
    "# Generated by leanfran-emela from the Lean IR of",
    s!"# {", ".intercalate (roots.toList.map toString)}. Do not edit.",
    "",
    "import LeanRt",
    "import LeanRt.{Obj, Desc}",
    "import Std.Dynamic.{Encode, Decode}",
    ""] ++ types
  for r in roots do
    let some d := decls[r]? | throw s!"no IR for {r}"
    let some sig := sigs[r]? | throw s!"no signature for {r}"
    lines := lines ++ emitPublic r d sig
  for d in ds do
    lines := lines ++ (← emitDecl decls d)
  return "\n".intercalate lines.toList

/-- `#emit_emela "path" f g ...` writes the Emela module for the roots `f g ...` to `path`,
    relative to the directory Lean runs in. -/
syntax (name := emitEmela) "#emit_emela " str (ppSpace ident)+ : command

@[command_elab emitEmela] def elabEmitEmela : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  let roots ← stx[2].getArgs.mapM fun id => liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let env ← getEnv
  let (sigs, st) ← liftTermElabM do
    let act : TypesM (Std.HashMap Name (Array (Option TyOut) × TyOut)) := do
      let mut sigs := {}
      for r in roots do
        let some d := findEnvDecl env r | throwError "no IR for {r} (is it noncomputable?)"
        sigs := sigs.insert r (← publicSig r (d.params.map (·.ty.isErased)))
      return sigs
    act.run {}
  match emitModule env roots sigs st.decls with
  | .ok text =>
    let old ← (IO.FS.readFile path).toBaseIO
    let same := match old with
      | .ok t => t == text
      | .error _ => false
    unless same do IO.FS.writeFile path text
    logInfo m!"wrote {path}"
  | .error e => throwError e

end LeanEmela
