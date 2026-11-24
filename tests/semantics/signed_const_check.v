Require Import RocqOfRust.evaluate.RocqOfRust ReleaseTests.signed_const.

Instance run_signed (n : i8) : Run.Trait signed [φ n] [] [] i8.
Proof. constructor. run_symbolic. Defined.
Instance run_unsigned (n : u8) : Run.Trait unsigned [φ n] [] [] u8.
Proof. constructor. run_symbolic. Defined.

Instance run_negative : Run.Trait negative [] [] [] i8.
Proof. constructor. run_symbolic. Defined.
Instance run_minimum : Run.Trait minimum [] [] [] i8.
Proof. constructor. run_symbolic. Defined.
Instance run_maximum : Run.Trait maximum_byte [] [] [] u8.
Proof. constructor. run_symbolic. Defined.

Example signed_negative : Evaluate.eval_f 40 run_negative []%stack =
  Execution.Done (Output.Success {|Integer.value := -1|}, []%stack).
Proof. vm_compute. reflexivity. Qed.
Example signed_minimum : Evaluate.eval_f 40 run_minimum []%stack =
  Execution.Done (Output.Success {|Integer.value := -128|}, []%stack).
Proof. vm_compute. reflexivity. Qed.
Example unsigned_maximum : Evaluate.eval_f 40 run_maximum []%stack =
  Execution.Done (Output.Success {|Integer.value := 255|}, []%stack).
Proof. vm_compute. reflexivity. Qed.
