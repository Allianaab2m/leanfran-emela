/-
Copyright 2026 Alliana
SPDX-License-Identifier: Apache-2.0

Portions of this file are adapted from leanfran (https://github.com/conao3/lean-leanfran, commit
07d4f2a), `langs/Clojure/LeanClj/EmitClj.lean`, licensed under the Apache License, Version 2.0.

- `tyOf` and `registerType` follow the original's `descOf`: the fields of a constructor are read
  with `Lean.Compiler.LCNF.getCtorLayout` and `forallTelescopeReducing`. They are rewritten to
  produce Emela types, `LeanRt.Desc` expressions and derived enums instead of Clojure
  marshalling descriptors.
- `publicSig` follows the original's function of the same name, without the support for `IO`.
- The rest of the file is new.
-/

import Lean

/-! # Lean types at the boundary

A generated public function takes and returns values of Emela types. For each Lean type it meets,
this module gives the Emela type and a `LeanRt.Desc` expression that converts between the Emela
value (through `Std.Dynamic`) and the Lean object.

- `Nat` is `Int`, `Bool` is `Bool`, `List α` is `List[A]` and `Option α` is `Option[A]`.
- An inductive type becomes a `pub enum` with `derive Eq, Show, Encode, Decode`, one variant per
  constructor with positional fields, and a function `desc_<name>` that takes the descriptions of
  its type parameters. The fields are those the constructor keeps at run time
  (`Lean.Compiler.LCNF.getCtorLayout`), in the order of the object.
- Constructors with scalar fields, indexed families, parameters that are not types, and type
  class arguments of public functions are not supported yet. -/

open Lean Meta

namespace LeanEmela

/-- The Emela type of a Lean type, and the `Desc` expression that describes it. -/
structure TyOut where
  ty : String
  desc : String
  deriving Inhabited

structure TypesState where
  /-- The Emela declarations of the inductive types met so far, in the order they were met. -/
  decls : Array String := #[]
  /-- Lean inductive type → Emela type name. -/
  names : Std.HashMap Name String := {}

abbrev TypesM := StateRefT TypesState MetaM

/-- `leaf` → `Leaf`, `red_black` → `RedBlack`. -/
def pascal (s : String) : String := Id.run do
  let mut acc := ""
  let mut up := true
  for c in s.toList do
    if c == '_' then up := true
    else if c.isAlphanum && c.toNat < 128 then
      acc := acc.push (if up then c.toUpper else c)
      up := false
  return acc

/-- `RedBlack` → `red_black`. -/
def lowerSnake (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut acc := ""
  for h : i in [0:cs.size] do
    let c := cs[i]
    if c.isUpper then
      if i > 0 then acc := acc.push '_'
      acc := acc.push c.toLower
    else acc := acc.push c
  return acc

def typeParamName (i : Nat) : String :=
  String.singleton (Char.ofNat ('A'.toNat + i))

def descParamName (i : Nat) : String :=
  "d_" ++ String.singleton (Char.ofNat ('a'.toNat + i))

def applied (head : String) (args : Array String) : String :=
  if args.isEmpty then head else head ++ "[" ++ ", ".intercalate args.toList ++ "]"

def callStr (f : String) (args : List String) : String := f ++ "(" ++ ", ".intercalate args ++ ")"

mutual

partial def tyOf (params : Array (FVarId × TyOut)) (t : Expr) : TypesM TyOut := do
  let t ← whnfR (← instantiateMVars t)
  let t := t.consumeMData
  if let .fvar f := t then
    match params.find? (·.1 == f) with
    | some (_, o) => return o
    | none => throwError "a type variable that is not a parameter of an inductive type: {t}"
  let .const c _ := t.getAppFn | throwError "type not supported at the boundary: {t}"
  let args := t.getAppArgs
  match c, args with
  | ``Nat, #[] => return { ty := "Int", desc := "LeanRt.d_nat()" }
  | ``Bool, #[] => return { ty := "Bool", desc := "LeanRt.d_bool()" }
  | ``List, #[a] =>
    let o ← tyOf params a
    return { ty := s!"List[{o.ty}]", desc := s!"LeanRt.d_list({o.desc})" }
  | ``Option, #[a] =>
    let o ← tyOf params a
    return { ty := s!"Option[{o.ty}]", desc := s!"LeanRt.d_option({o.desc})" }
  | _, _ =>
    let name ← registerType c
    let os ← args.mapM (tyOf params)
    return {
      ty := applied name (os.map (·.ty))
      desc := callStr s!"desc_{lowerSnake name}" (os.toList.map (·.desc)) }

/-- The Emela name of the inductive type `c`, declaring it on first use. -/
partial def registerType (c : Name) : TypesM String := do
  if let some n := (← get).names[c]? then return n
  let some (.inductInfo ind) := (← getEnv).find? c
    | throwError "type not supported at the boundary: {c}"
  if ind.numIndices != 0 then throwError "indexed families are not supported: {c}"
  let name := pascal c.getString!
  if (← get).names.toList.any (·.2 == name) then
    throwError "two Lean types would have the same Emela name {name}: {c}"
  modify fun s => { s with names := s.names.insert c name }
  forallBoundedTelescope ind.type ind.numParams fun ps _ => do
    let mut params : Array (FVarId × TyOut) := #[]
    for h : i in [0:ps.size] do
      unless (← whnf (← inferType ps[i])).isSort do
        throwError "{c}: parameters that are not types are not supported"
      params := params.push (ps[i].fvarId!, { ty := typeParamName i, desc := descParamName i })
    let mut variants : Array String := #[]
    let mut ctorDescs : Array String := #[]
    for ctor in ind.ctors do
      let some (.ctorInfo ci) := (← getEnv).find? ctor | throwError "no constructor {ctor}"
      let layout ← Compiler.LCNF.getCtorLayout ctor
      let ctorTy ← instantiateForall ci.type ps
      let fields ← forallTelescopeReducing ctorTy fun fs _ => do
        let mut out : Array (Nat × TyOut) := #[]
        for h : i in [0:fs.size] do
          match layout.fieldInfo[i]? with
          | some (.object j _) => out := out.push (j, ← tyOf params (← inferType fs[i]))
          | some .erased | some .void => pure ()
          | _ => throwError "{ctor}: scalar fields are not supported yet"
        return out
      let fields := fields.qsort (·.1 < ·.1) |>.map (·.2)
      let tag := pascal ctor.getString!
      variants := variants.push
        (if fields.isEmpty then tag else callStr tag (fields.toList.map (·.ty)))
      let fs := "[" ++ ", ".intercalate (fields.toList.map (·.desc)) ++ "]"
      ctorDescs := ctorDescs.push s!"LeanRt.d_ctor(\"{tag}\", {layout.ctorInfo.cidx}, {fs})"
    let tps := params.map (·.2.ty)
    let dps := params.toList.map fun (_, o) => s!"{o.desc}: Desc"
    let decl := "\n".intercalate ([
      s!"# {c}",
      s!"pub enum {applied name tps} \{"] ++ variants.toList.map ("  " ++ ·) ++ [
      "}",
      "  derive Eq, Show, Encode, Decode",
      "",
      s!"pub fn desc_{lowerSnake name}({", ".intercalate dps}) -> Desc \{",
      s!"  LeanRt.d_type(|| [{", ".intercalate ctorDescs.toList}])",
      "}",
      ""])
    modify fun s => { s with decls := s.decls.push decl }
  return name

end

/-- The types of the arguments a public function keeps (`none` for an erased one), and of its
    result. `irParams` says which IR parameters are erased. -/
def publicSig (root : Name) (erased : Array Bool) : TypesM (Array (Option TyOut) × TyOut) := do
  let ci ← getConstInfo root
  forallBoundedTelescope ci.type erased.size fun xs body => do
    if xs.size != erased.size then
      throwError "{root}: the IR has {erased.size} parameters but the type has {xs.size} binders"
    let mut params := #[]
    for h : i in [0:xs.size] do
      if erased[i]! then params := params.push none
      else
        let ldecl ← xs[i].fvarId!.getDecl
        if ldecl.binderInfo.isInstImplicit then
          throwError "{root}: type class arguments are not supported in public functions"
        params := params.push (some (← tyOf #[] ldecl.type))
    return (params, ← tyOf #[] body)

end LeanEmela
