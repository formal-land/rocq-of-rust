Require Import simulate.RocqOfRust alloc.vec.links.mod core.intrinsics.simulate.mod.

Module Impl_Vec_T_A.
  (** The translated let-bindings allocate the saved length and then a unit. *)
  Local Fixpoint saved_length (stack : Stack.t) (n : usize) :
    Stack.Nth.t usize (Stack.alloc (Stack.alloc stack n) tt) (Stack.length stack).
  Proof. destruct stack; constructor. apply saved_length. Defined.

  Local Lemma read_saved_length stack n : Stack.read (saved_length stack n) = n.
  Proof. induction stack; cbn; auto. Qed.

  Lemma len_eq {T A : Set} `{Link T} `{Link A} (stack : Stack.t)
      (r : '& (Vec.t T A)) (v : Vec.t T A) :
    CanRead.t stack v r -> Vec.valid_length v ->
    {{ SimulateM.eval_f (Impl_Vec_T_A.run_len r) stack 🌲
       (Output.Success v.(Vec.len), stack) }}.
  Proof.
    intros readable [_ valid].
    with_strategy transparent [Impl_Vec_T_A.run_len] (unfold Impl_Vec_T_A.run_len; cbn).
    destruct readable as [|ref_core access read_eq].
    - s.
      + apply Stack.nth_alloc.
      + rewrite Stack.read_nth_alloc_eq. eapply assume_true. now apply Z.leb_le.
      + s.
        * apply saved_length.
        * rewrite read_saved_length. reflexivity.
        * repeat rewrite Stack.dealloc_alloc_eq. reflexivity.
    - destruct access. cbn in read_eq |- *.
      eapply Run.LetUnfold. cbn.
      unshelve eapply Run.GetCanAccess; [econstructor; eassumption |].
      cbn. rewrite read_eq. cbn.
      s.
      + apply Stack.nth_alloc.
      + rewrite Stack.read_nth_alloc_eq. eapply assume_true. now apply Z.leb_le.
      + s.
        * apply saved_length.
        * rewrite read_saved_length. reflexivity.
        * repeat rewrite Stack.dealloc_alloc_eq. reflexivity.
  Qed.

  Lemma is_empty_eq {T A : Set} `{Link T} `{Link A} (stack : Stack.t)
      (r : '& (Vec.t T A)) (v : Vec.t T A) :
    CanRead.t stack v r -> Vec.valid_length v ->
    {{ SimulateM.eval_f (Impl_Vec_T_A.run_is_empty r) stack 🌲
       (Output.Success (v.(Vec.len).(Integer.value) =? 0), stack) }}.
  Proof.
    intros readable valid.
    with_strategy transparent [Impl_Vec_T_A.run_is_empty] cbn.
    eapply Run.Call; [eapply len_eq; eassumption | s].
  Qed.
End Impl_Vec_T_A.
