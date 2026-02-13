Require Import simulate.RocqOfRust.
Require Import core.slice.links.mod.

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
  Admitted.

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
  Admitted.
End Impl_Slice.
