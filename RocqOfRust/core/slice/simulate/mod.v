Require Import simulate.RocqOfRust.
Require Import core.slice.links.mod.
Require Import core.intrinsics.links.mod.

Module Impl_Slice.
  Definition Self (T : Set) : Set :=
    list T.

  Definition len {T : Set}  (self : Self T) : usize :=
    Z.of_nat (List.length self).

  Lemma len_eq
      {T : Set} `{Link T}
      (stack : Stack.t)
      (ref_self : '& (Self T))
      (self : Self T) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (Impl_Slice.run_len ref_self)
        stack 🌲
      (
        Output.Success (len self),
        stack
      )
    }}.
  Proof.
    intro readable.
    with_strategy transparent [Impl_Slice.run_len] cbn.
    eapply Run.Call.
    - with_strategy transparent [run_metadata_for_slice] cbn.
      eapply Run.Call.
      + unfold SliceMetadata.run_intrinsic. cbn.
        destruct readable as [|ref_core access read_eq].
        * p.
        * destruct access. cbn in read_eq |- *.
          unshelve eapply Run.GetCanAccess; [econstructor; eassumption |].
          cbn. rewrite read_eq. p.
      + p.
    - cbn. unfold len. rewrite List.length_map. p.
  Qed.

  Definition is_empty {T : Set} `{Link T} (self : Self T) : bool :=
    match self with
    | [] => true
    | _ => false
    end.

  Lemma is_empty_eq
      {T : Set} `{Link T}
      (stack : Stack.t)
      (ref_self : '& (Self T))
      (self : Self T) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (@core.slice.links.mod.Impl_Slice.run_is_empty T _ ref_self)
        stack 🌲
      (
        Output.Success (is_empty self),
        stack
      )
    }}.
  Proof.
    intro readable.
    with_strategy transparent [Impl_Slice.run_is_empty] cbn.
    eapply Run.Call.
    - eapply len_eq. exact readable.
    - destruct self; s.
  Qed.
End Impl_Slice.
