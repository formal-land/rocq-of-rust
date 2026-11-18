Require Import RocqOfRust.evaluate.RocqOfRust ReleaseTests.add_one.

Instance run_add_one (n : u32) : Run.Trait add_one [] [] [φ n] u32.
Proof. constructor. run_symbolic. Defined.

Example add_one_control :
  Evaluate.eval_f 20 (run_add_one {| Integer.value := 41 |}) []%stack =
  Execution.Done (Output.Success {| Integer.value := 42 |}, []%stack).
Proof. vm_compute. reflexivity. Qed.
