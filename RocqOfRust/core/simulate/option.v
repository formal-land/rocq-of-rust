Require Import simulate.RocqOfRust.
Require Import core.links.option.
Require Import core.simulate.default.

Module Impl_Option.
  Definition Self (T : Set) : Set := option T.

  Lemma unwrap_eq {T : Set} `{Link T} (stack : Stack.t) (self : Self T) (value : T) :
    self = Some value ->
    {{
      SimulateM.eval_f (Impl_Option.run_unwrap self) stack 🌲
      (Output.Success value, stack)
    }}.
  Proof.
    intros.
    subst.
    s.
  Qed.

  Definition unwrap_or_default
      {T : Set} `{Default.C T}
      (self : Self T) : T :=
    match self with
    | Some value => value
    | None => Default.default
    end.

  Lemma unwrap_or_default_eq
      {T : Set} `{Link T}
      `{!default.Default.Run T}
      `{Default_for_T : Default.C T}
      `{!Default.Eq.C (Self := T) Default_for_T}
      (stack : Stack.t) (self : Self T) :
    {{
      SimulateM.eval_f (Impl_Option.run_unwrap_or_default self) stack 🌲
      (Output.Success (unwrap_or_default self), stack)
    }}.
  Proof.
    destruct self; cbn.
    { s. }
    { s. {
        apply Default.Eq.default.
      }
      s.
    }
  Qed.

  (* pub fn unwrap_or(self, default: T) -> T *)
  Definition unwrap_or {T : Set} (self : Self T) (default : T) : T :=
    match self with
    | Some v => v
    | None => default
    end.

  Lemma unwrap_or_eq (stack : Stack.t)
      {T : Set} `{Link T} (self : Self T) (default : T) :
    {{
      SimulateM.eval_f
        (Impl_Option.run_unwrap_or self default)
        stack 🌲
      (
        Output.Success (unwrap_or self default),
        stack
      )
    }}.
  Proof.
    destruct self; s.
  Qed.
End Impl_Option.
