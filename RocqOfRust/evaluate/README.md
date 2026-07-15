# Evaluation

The goal of these experiments is to run translated Rust code on concrete inputs
and compare the results with the original Rust code. There are several possible
evaluation layers.

## Generated code

The generated code has type `M` and is the closest representation to the Rust
source. Evaluating it directly would test the translation before linking, but
the evaluator would need executable resolution for types, functions, associated
functions, and trait methods.

## Linked code without mutable stack access

The evaluator in [`M.v`](M.v) runs the typed `LinkM` representation produced by
`links.M.evaluate`. It uses fuel for recursive calls and currently handles the
cases needed by the [`add_one` test](../examples/default/examples/custom/evaluate/add_one.v).

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
runner, but it still depends on first choosing and completing the Rocq
evaluation layer.
