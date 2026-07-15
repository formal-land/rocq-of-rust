Require Import evaluate.RocqOfRust.
Require Import examples.default.examples.custom.links.add_one.

Goal
  Evaluate.eval_f
    20
    (run_add_one {| Integer.value := 41 |})
    []%stack =
  Execution.Done (
    Output.Success {| Integer.value := 42 |},
    []%stack
  ).
Proof.
  vm_compute.
  reflexivity.
Qed.
