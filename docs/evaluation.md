# Evaluation

The goal of these experiments is to run translated Rust code on concrete inputs
and compare the results with the original Rust code. There are several possible
evaluation layers.

## Generated code

The generated code has type `M` and is the closest representation to the Rust
source. Evaluating it directly would test the translation before linking. Type
resolution can be avoided, but the evaluator would still need executable
resolution for functions, associated functions, and trait methods.

The experimental evaluator in
[`translated.v`](../RocqOfRust/evaluate/translated.v) can be extracted to OCaml.
The command `make evaluate-translated-add-one`, run from the `RocqOfRust`
directory, checks that the generated translation of `add_one` evaluates to `42`
on input `41`. This first experiment handles immediate allocation and reading,
closure calls, lets, tuple matching, and conditionals. Mutation and name or
trait resolution are not handled yet.

## Linked code without mutable stack access

The evaluator in [`M.v`](../RocqOfRust/evaluate/M.v) runs the typed `LinkM`
representation produced by `links.M.evaluate`. It uses fuel for recursive calls
and currently handles the cases needed by the
[`add_one` test](../RocqOfRust/examples/default/examples/custom/evaluate/add_one.v).

This evaluator returns `Unsupported` for operations that require mutable stack
access. `Stack.t` is heterogeneous, so reading or writing a mutable reference
requires evidence that the referenced value has the expected type.

## Linked code through simulation proofs

For programs that use the stack, another direction is to derive an output
together with a proof that `SimulateM.eval_f` produces it. The Rocq `Derive`
command can introduce the output as an existential value, while repeated use of
the simulation tactic `s` can construct the execution proof and the required
stack-access evidence.

## Simulate definitions

Pure simulate definitions can already be evaluated efficiently with
`vm_compute`. This is useful for testing the functional model, while the
corresponding `_eq` lemma connects that model to the linked translation.

## Extraction

An executable Rocq evaluator or simulate definition can be extracted to OCaml.
This may provide faster execution and easier integration with an external test
runner. OCaml is also more expressive and supports side effects, which could be
used to implement name and trait resolution outside Rocq. This can be an
advantage for evaluation methods that require these resolutions, but extraction
still depends on first choosing and completing the Rocq evaluation layer.
