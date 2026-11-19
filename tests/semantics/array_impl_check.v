Require Import RocqOfRust.evaluate.RocqOfRust ReleaseTests.array_impl.
Module One := Impl_array_impl_Capacity_for_array_Usize_1_T.
Module Two := Impl_array_impl_Capacity_for_array_Usize_2_T.
Instance run_one : Run.Trait (One.marker (Φ u8)) [] [] [] u8.
Proof. constructor. run_symbolic. Defined.
Instance run_two : Run.Trait (Two.marker (Φ u8)) [] [] [] u8.
Proof. constructor. run_symbolic. Defined.
Example distinct_lengths :
  (Evaluate.eval_f 20 run_one []%stack, Evaluate.eval_f 20 run_two []%stack) =
  (Execution.Done (Output.Success {| Integer.value := 11 |}, []%stack),
   Execution.Done (Output.Success {| Integer.value := 22 |}, []%stack)).
Proof. vm_compute. reflexivity. Qed.
