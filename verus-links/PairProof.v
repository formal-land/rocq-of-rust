Require Import RocqOfRust.simulate.RocqOfRust.
Require Import pair Contracts.

Module Pair.
  RocqOfRustLinkRecord "pair::Pair" := {
    left : u32;
    right : u32
  }.
End Pair.
Import (hints) Pair.

Definition root : '&mut Pair.t := make_ref 0.
Definition left_ref : '&mut u32 :=
  {| Ref.core := SubPointer.Runner.apply root.(Ref.core) Pair.SubPointer.get_left |}.

#[local] Instance run_copy (p : '&mut Pair.t) :
  Run.Trait copy_right [] [] [φ p] unit.
Proof. constructor; run_symbolic. Defined.

#[local] Instance run_left (p : '&mut Pair.t) :
  Run.Trait left_mut [] [] [φ p] ('&mut u32).
Proof. constructor; run_symbolic. Defined.

#[local] Instance run_write (p : '&mut Pair.t) (v : u32) :
  Run.Trait write_through [] [] [φ p; φ v] unit.
Proof. constructor; run_symbolic. Defined.

Definition observe (p : Pair.t) (f : field) : u32 :=
  match f with Left => Pair.left p | Right => Pair.right p end.

Theorem copy_contract (initial : Pair.t) :
  exists final,
    {{ SimulateM.eval_f (run_copy root) [initial]%stack 🌲
       (Output.Success tt, [final]%stack) }} /\
    copy_right_post (observe initial) (observe final).
Proof.
  exists (initial <| Pair.left := Pair.right initial |>).
  split; [| split; reflexivity].
  repeat (cbn || get_can_access || eapply Run.Call || apply Run.LetUnfold || apply Run.Pure).
Qed.

(* The callee returns the actual field pointer. Its stack at return still
   contains the original record. The runner supplies the later observations. *)
Theorem borrow_contract (initial : Pair.t) :
  {{ SimulateM.eval_f (run_left root) [initial]%stack 🌲
     (Output.Success left_ref, [initial]%stack) }} /\
  forall later : u32, exists returned final,
    Pair.SubPointer.get_left.(SubPointer.Runner.projection) initial = Some returned /\
    Pair.SubPointer.get_left.(SubPointer.Runner.injection) initial later = Some final /\
    left_mut_post (observe initial) (observe final) returned later.
Proof.
  split.
  - repeat (cbn || get_can_access || eapply Run.Call || apply Run.LetUnfold || apply Run.Pure).
  - intro later. exists (Pair.left initial), (initial <| Pair.left := later |>).
    repeat split; reflexivity.
Qed.

Theorem caller_contract (initial : Pair.t) (v : u32) :
  exists final,
    {{ SimulateM.eval_f (run_write root v) [initial]%stack 🌲
       (Output.Success tt, [final]%stack) }} /\
    write_through_post (observe initial) (observe final) v.
Proof.
  exists (initial <| Pair.left := v |>).
  split; [| split; reflexivity].
  repeat (cbn || get_can_access || eapply Run.Call || apply Run.LetUnfold || apply Run.Pure).
Qed.

Example return_snapshot_counterexample :
  let p := {| Pair.left := {| Integer.value := 10 |};
              Pair.right := {| Integer.value := 20 |} |} in
  ~ left_mut_post (observe p) (observe p) (Pair.left p) {| Integer.value := 100 |}.
Proof. cbn. intros [_ [H _]]. discriminate. Qed.

Print Assumptions copy_contract.
Print Assumptions borrow_contract.
Print Assumptions caller_contract.
