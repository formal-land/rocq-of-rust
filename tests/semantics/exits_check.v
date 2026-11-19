Require Import RocqOfRust.evaluate.RocqOfRust ReleaseTests.exits.
Instance run_labeled (take : bool) : Run.Trait labeled [] [] [φ take] u8.
Proof. constructor. run_symbolic. Defined.
Example unsupported_taken :
  Evaluate.eval_f 40 (run_labeled true) []%stack = Execution.Unsupported.
Proof. vm_compute. reflexivity. Qed.
Example supported_untaken :
  Evaluate.eval_f 40 (run_labeled false) []%stack =
  Execution.Done (Output.Success {|Integer.value := 4|}, []%stack).
Proof. vm_compute. reflexivity. Qed.
