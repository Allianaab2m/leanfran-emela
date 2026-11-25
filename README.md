# leanfran-emela

[![CI](https://github.com/Allianaab2m/leanfran-emela/actions/workflows/ci.yml/badge.svg)](https://github.com/Allianaab2m/leanfran-emela/actions/workflows/ci.yml)

Write a function and its proofs in Lean 4, and generate it as an [Emela](https://github.com/emela-lang/emela)
module.

This is an Emela backend in the manner of [leanfran](https://github.com/conao3/lean-leanfran), which
brings Lean 4 to Rust, Python, TypeScript, Clojure, PHP and Go. It is a separate project, not part
of leanfran. The emitter follows the structure of leanfran's Clojure backend
(`langs/Clojure/LeanClj/EmitClj.lean`): the collection of IR declarations, the detection of tail
calls, and the expansion of join points that are jumped to once are adapted from it. leanfran is
licensed under Apache-2.0.

The emitter reads Lean's IR (`Lean.IR.Decl`) and writes Emela that calls a small runtime written in
Emela. The first use is as a test oracle: a model proved in Lean is generated into Emela, and
property-based tests check that the standard library gives the same answers.

## Layout

- `LeanEmela/Emit.lean`: the emitter and the `#emit_emela "path" f g ...` command.
- `Examples/Base64.lean`: Base64 (RFC 4648) with `decode (encode bs) = some bs` and
  `decode cs = some bs → encode bs = cs`.
- `Examples/Base64Emit.lean`: generates `emela/src/base64_model.emel`.
- `Examples/List.lean`: Lean's own `List` at `Nat` (`reverse`, `append`, `take`, `drop`, `length`,
  `sort`), with the laws of Emela's list property tests as theorems. `Examples/ListEmit.lean`
  generates `emela/src/list_model.emel`.
- `Examples/Tree.lean`: a search tree, with "an inserted key is found" and "the keys of
  `fromList xs` are the elements of `xs`". `Examples/TreeEmit.lean` generates
  `emela/src/tree_model.emel`, where the Lean type becomes `enum Tree[A]`.
- `emela/src/lean_rt.emel`: the runtime (`LeanRt`).
- `emela/test/base64_oracle_test.emel`: `Std.Bytes.to_base64` and `from_base64` against the model.
- `emela/test/tree_oracle_test.emel`: the tree against `Std.Set`.
- `emela/test/list_oracle_test.emel`: Emela's `List` against Lean's.

Generated public functions take and return Emela values. They cross into the runtime's `Obj`
through `Std.Dynamic`: the Emela side with derived `Encode` and `Decode`, the Lean side with a
`Desc` that the emitter writes from the Lean type.

## Use

Requires Lean 4.35.0 (through elan) and emela 0.28.2. Run `emela pome install` in `emela/` once.

```sh
make gen    # regenerate the Emela modules
make test   # regenerate, then run the Emela tests
make check  # also fail if the generated modules differ from the committed ones (as CI does)
```

## Supported so far

- `Nat` as an Int64. A result that does not fit is a defect.
- Constructors without scalar fields, `case`, projections, join points, closures (`pap`, `ap`).
- `Array.mkEmpty`, `push` and `toList`, which Lean's tail-recursive list functions use. An array
  is kept as its elements in reverse, so other array operations would be slow.
- At the boundary: `Nat` (as `Int`), `Bool`, `List`, `Option`, and inductive types with type
  parameters (as a derived `enum`).

Not yet: `String`, the rest of `Array`, `UInt*`, `Float`, `IO`, constructors with scalar fields, arbitrary
precision `Nat`.
