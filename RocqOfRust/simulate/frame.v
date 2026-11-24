Require Import simulate.RocqOfRust.

(** Evidence for accessing a caller-independent local slot after another
    allocation. Computations on this evidence retain the prefix verbatim. *)
Module Frame.
  Fixpoint keep {A : Set} {stack i} (slot : Stack.Nth.t A stack i)
      {B : Set} (last : B) : Stack.Nth.t A (Stack.alloc stack last) i.
  Proof.
    destruct slot.
    - constructor.
    - constructor. exact (@keep _ _ _ slot _ last).
  Defined.

  Definition at_index {A : Set} {stack i j} (slot : Stack.Nth.t A stack i) (E : i = j) :
    Stack.Nth.t A stack j :=
    match E with eq_refl => slot end.

  Lemma read_at_index {A : Set} {stack i j} (slot : Stack.Nth.t A stack i) (E : i = j) :
    Stack.read (at_index slot E) = Stack.read slot.
  Proof. now destruct E. Qed.

  Lemma write_at_index {A : Set} {stack i j} (slot : Stack.Nth.t A stack i) (E : i = j) x :
    Stack.write (at_index slot E) x = Stack.write slot x.
  Proof. now destruct E. Qed.

  Lemma read_keep {A B : Set} {stack i} (slot : Stack.Nth.t A stack i) (last : B) :
    Stack.read (keep slot last) = Stack.read slot.
  Proof. induction slot; cbn; auto. Qed.

  Lemma write_keep {A B : Set} {stack i} (slot : Stack.Nth.t A stack i) (last : B) x :
    Stack.write (keep slot last) x = Stack.alloc (Stack.write slot x) last.
  Proof. induction slot; cbn; [reflexivity | now f_equal]. Qed.

  Lemma write_last {A : Set} stack (old new : A) :
    Stack.write (Stack.nth_alloc stack old) new = Stack.alloc stack new.
  Proof. induction stack; cbn; [reflexivity | now f_equal]. Qed.
Ltac local_slot :=
  lazymatch goal with |- Stack.Nth.t ?A (Stack.alloc ?s ?last) ?i =>
    first [refine (Frame.at_index (Stack.nth_alloc s last) _);
           solve [repeat rewrite Stack.length_alloc_eq; reflexivity] |
           refine (Frame.keep _ last); local_slot]
  end.
Ltac frame_access :=
  unshelve eapply Run.GetCanAccess;
  [eapply Stack.CanAccess.Mutable; local_slot |].
Ltac advance :=
  repeat first [apply Run.Pure | frame_access | apply Run.LetUnfold | eapply Run.Call |
    progress cbn | rewrite Frame.read_at_index | rewrite Frame.write_at_index |
    rewrite Frame.read_keep | rewrite Frame.write_keep | rewrite Stack.read_nth_alloc_eq |
    rewrite Frame.write_last | rewrite Stack.dealloc_alloc_eq].
End Frame.
