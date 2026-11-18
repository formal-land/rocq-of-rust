Require Import RocqOfRust.evaluate.RocqOfRust.
Require Import ReleaseTests.rest.
Module Shape.
  RocqOfRustLinkEnum "rest::Shape" :=
  | Pair (first : u8, last : u8)
  | Empty.
End Shape.
Export (hints) Shape.

Definition bytev (n : Z) : u8 := {| Integer.value := n |}.
Instance run_last (x : Shape.t) : Run.Trait enum_last [] [] [φ x] u8.
Proof. constructor. run_symbolic. Defined.
Example last_field :
  Evaluate.eval_f 100 (run_last (Shape.Pair (bytev 3) (bytev 9))) []%stack =
  Execution.Done (Output.Success (bytev 9), []%stack).
Proof. vm_compute. reflexivity. Qed.

Module Point.
  RocqOfRustLinkTupleStruct "rest::Point" := { first : u8; last : u8 }.
End Point.
Export (hints) Point.
Instance run_point (x : Point.t) : Run.Trait point_last [] [] [φ x] u8.
Proof. constructor. run_symbolic. Defined.
Example parameter_last :
  Evaluate.eval_f 100 (run_point {|Point.first := bytev 3; Point.last := bytev 9|}) []%stack =
  Execution.Done (Output.Success (bytev 9), []%stack).
Proof. vm_compute. reflexivity. Qed.

Instance run_first (x : u8 * u8) : Run.Trait tuple_first [] [] [φ x] u8.
Proof. constructor. run_symbolic. Defined.
Example first_parameter :
  Evaluate.eval_f 100 (run_first (bytev 4, bytev 8)) []%stack =
  Execution.Done (Output.Success (bytev 4), []%stack).
Proof. vm_compute. reflexivity. Qed.
