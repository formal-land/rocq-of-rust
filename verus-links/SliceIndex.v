Require Import RocqOfRust.links.RocqOfRust.

Definition update {A : Set} (xs : list A) (i : nat) (v : A) : option (list A) :=
  match List.nth_error xs i with
  | Some _ => Some (List.replace_at xs i v)
  | None => None
  end.

Definition runner {A : Set} `{Link A} (index : Z) :
  SubPointer.Runner.t (list A) (Pointer.Index.Array index) :=
  {| SubPointer.Runner.projection xs := List.nth_error xs (Z.to_nat index);
     SubPointer.Runner.injection xs v := update xs (Z.to_nat index) v |}.

Lemma valid {A : Set} `{Link A} (index : Z) :
  SubPointer.Runner.Valid.t (runner (A := A) index).
Proof.
  constructor.
  - intros xs. change (Option.map (List.nth_error xs (Z.to_nat index)) φ =
      List.nth_error (List.map φ xs) (Z.to_nat index)).
    rewrite List.nth_error_map. now destruct (List.nth_error xs (Z.to_nat index)).
  - intros xs v. change (Option.map (update xs (Z.to_nat index) v)
      (fun ys => Value.Array (List.map φ ys)) =
      match List.nth_error (List.map φ xs) (Z.to_nat index) with
      | Some _ => Some (Value.Array (List.replace_at (List.map φ xs) (Z.to_nat index) (φ v)))
      | None => None
      end).
    unfold update. rewrite List.nth_error_map.
    destruct (List.nth_error xs (Z.to_nat index)); cbn; [|reflexivity].
    now rewrite List.replace_at_map_eq.
Qed.

Smpl Add eapply valid : run_sub_pointer.
