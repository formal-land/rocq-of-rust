Require Import simulate.RocqOfRust.
Require Import core.links.default.

Module Default.
  Class C (Self : Set) : Set := {
    default : Self;
  }.

  Module Eq.
    Class C
        {Self : Set} `{Link Self}
        `{!default.Default.Run Self}
        `(!C Self) :
        Prop := {
      default (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (default.Default.run_default (Self := Self))
            stack 🌲
          (
            Output.Success default,
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Default.
Export (hints) Default.

Module Impl_Default_for_unit.
  Definition Self : Set := unit.

  Instance I : Default.C Self := {|
    Default.default := tt;
  |}.

  Module Eq.
    Instance I : Default.Eq.C (Self := Self) Impl_Default_for_unit.I.
    Proof.
      constructor; intros.
      (* default *)
      { s. }
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_Default_for_unit.
Export (hints) Impl_Default_for_unit.

Module Impl_Default_for_bool.
  Definition Self : Set := bool.

  Instance I : Default.C Self := {|
    Default.default := false;
  |}.

  Module Eq.
    Instance I : Default.Eq.C (Self := Self) Impl_Default_for_bool.I.
    Proof.
      constructor; intros.
      (* default *)
      { s. }
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_Default_for_bool.
Export (hints) Impl_Default_for_bool.

Module Impl_Default_for_integer.
  Definition Self (kind : IntegerKind.t) : Set :=
    Integer.t kind.

  Definition default (kind : IntegerKind.t) : Self kind :=
    {| Integer.value := 0 |}.

  Instance I (kind : IntegerKind.t) : Default.C (Self kind) := {|
    Default.default := default kind;
  |}.

  Module Eq.
    Instance I (kind : IntegerKind.t) :
      Default.Eq.C (Self := Self kind) (Impl_Default_for_integer.I kind).
    Proof.
      constructor; intros.
      (* default *)
      { destruct kind; s. }
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_Default_for_integer.
Export (hints) Impl_Default_for_integer.
