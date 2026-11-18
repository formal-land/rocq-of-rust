Require Import Contracts.

(* The displayed record observations can be represented by any faithful word
   model. Reflection is needed when bringing a Rocq proof back to Verus. *)
Theorem borrow_view_iff {A B : Type} (encode : A -> B)
    (reflects : forall x y, encode x = encode y -> x = y)
    (old final : field -> A) (returned later : A) :
  left_mut_post (fun f => encode (old f)) (fun f => encode (final f))
                (encode returned) (encode later) <->
  left_mut_post old final returned later.
Proof.
  unfold left_mut_post. split; intros [H1 [H2 H3]].
  - repeat split; apply reflects; assumption.
  - repeat split; congruence.
Qed.

Example lossy_view :
  let old := fun _ : field => false in
  left_mut_post (fun _ => tt) (fun _ => tt) tt tt /\
  ~ left_mut_post old old false true.
Proof. cbn. split; [repeat split | intros [_ [H _]]; discriminate]. Qed.

Print Assumptions borrow_view_iff.
