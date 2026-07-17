Require Import links.RocqOfRust.
Require Import examples.default.examples.custom.tuple_assignment.

Instance run_tuple_assignment :
  Run.Trait tuple_assignment [] [] [] (u64 * u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_tuple_assignment.
