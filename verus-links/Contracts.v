(* Generated from the ensures clauses in the Verus VIR. *)
Inductive field := Left | Right.
Definition copy_right_post {W : Type} (old final : field -> W) : Prop :=
  final Left = old Right /\ final Right = old Right.
Definition left_mut_post {W : Type} (old final : field -> W) (returned later : W) : Prop :=
  returned = old Left /\ final Left = later /\ final Right = old Right.
Definition write_through_post {W : Type} (old final : field -> W) (v : W) : Prop :=
  final Left = v /\ final Right = old Right.
