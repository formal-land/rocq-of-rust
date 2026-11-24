Require Import RocqOfRust.evaluate.RocqOfRust RocqOfRust.lib.simulate.lib ReleaseTests.shifts.

Definition byte (z : Z) : u8 := {| Integer.value := z |}.
Definition count (z : Z) : u32 := {| Integer.value := z |}.

Example checked_left_discards_bits :
  BinOp.Checked.shl (byte 128) (count 1) = Some (byte 0).
Proof. reflexivity. Qed.

Example checked_right_outside_width :
  BinOp.Checked.shr (byte 1) (count 8) = None.
Proof. reflexivity. Qed.

Instance run_mixed (x : u8) (n : u32) : Run.Trait mixed_left [] [] [φ x; φ n] u8.
Proof. constructor. run_symbolic. Defined.

Instance run_signed (x : i8) (n : u16) : Run.Trait signed_right [] [] [φ x; φ n] i8.
Proof. constructor. run_symbolic. Defined.

Example left_boundary :
  List.map (fun n => Evaluate.eval_f 80 (run_mixed (byte 1) (count n)) []%stack) [7;8;9] =
  List.map (fun v => Execution.Done (Output.Success (byte v), []%stack)) [128;1;2].
Proof. vm_compute. reflexivity. Qed.

Example signed_boundary :
  List.map (fun n => Evaluate.eval_f 80
    (run_signed {|Integer.value := -128|} {|Integer.value := n|}) []%stack) [7;8;9] =
  List.map (fun v => Execution.Done (Output.Success ({|Integer.value := v|} : i8), []%stack)) [-1;-128;-64].
Proof. vm_compute. reflexivity. Qed.
