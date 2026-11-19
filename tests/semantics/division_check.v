Require Import RocqOfRust.evaluate.RocqOfRust.
Require Import ReleaseTests.division.

Instance run_quotient (x y : i8) : Run.Trait quotient [] [] [φ x; φ y] i8.
Proof. constructor. run_symbolic. Defined.

Instance run_remainder (x y : i8) : Run.Trait remainder [] [] [φ x; φ y] i8.
Proof. constructor. run_symbolic. Defined.

Definition signed8 (z : Z) : i8 := {| Integer.value := z |}.

Example quotient_on_negative :
  Evaluate.eval_f 80 (run_quotient (signed8 (-7)) (signed8 3)) []%stack =
  Execution.Done (Output.Success (signed8 (-2)), []%stack).
Proof. vm_compute. reflexivity. Qed.

Example remainder_on_negative :
  Evaluate.eval_f 80 (run_remainder (signed8 (-7)) (signed8 3)) []%stack =
  Execution.Done (Output.Success (signed8 (-1)), []%stack).
Proof. vm_compute. reflexivity. Qed.

Example quotient_zero_divisor :
  Evaluate.eval_f 80 (run_quotient (signed8 7) (signed8 0)) []%stack =
  Execution.Unsupported.
Proof. vm_compute. reflexivity. Qed.

Example quotient_signed_overflow :
  Evaluate.eval_f 80 (run_quotient (signed8 (-128)) (signed8 (-1))) []%stack =
  Execution.Unsupported.
Proof. vm_compute. reflexivity. Qed.
Example remainder_zero_divisor :
  Evaluate.eval_f 80 (run_remainder (signed8 7) (signed8 0)) []%stack =
  Execution.Unsupported.
Proof. vm_compute. reflexivity. Qed.

Example remainder_signed_overflow :
  Evaluate.eval_f 80 (run_remainder (signed8 (-128)) (signed8 (-1))) []%stack =
  Execution.Unsupported.
Proof. vm_compute. reflexivity. Qed.
