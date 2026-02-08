Require Import simulate.RocqOfRust.
Require Import core.links.clone.

Module Clone.
  Class C (Self : Set) : Set := {
    clone (self : Self) : Self;
  }.

  Module Eq.
    Class C
        {Self : Set} `{Link Self}
        `{!clone.Clone.Run Self}
        (I : Clone.C Self) :
        Prop := {
      clone (ref_self : '& Self) (stack : Stack.t) (self : Self) :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (clone.Clone.run_clone ref_self)
            stack 🌲
          (
            Output.Success (I.(Clone.clone) self),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Clone.
Export (hints) Clone.

Module Impl_Clone_for_bool.
  Definition Self : Set := bool.

  Definition clone (self : Self) : Self := self.

  Instance I : Clone.C Self := {|
    Clone.clone := clone;
  |}.

  Module Eq.
    Instance I : Clone.Eq.C (Self := Self) Impl_Clone_for_bool.I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Clone_for_bool.
Export (hints) Impl_Clone_for_bool.
