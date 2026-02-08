Require Import simulate.RocqOfRust.
Require Import core.convert.links.mod.
Require Import core.links.result.

(*
pub trait From<T>: Sized {
    fn from(value: T) -> Self;
}
*)
Module From.
  Class C (Self T : Set) : Set := {
    from (value : T) : Self;
  }.

  Module Eq.
    Class C
        {Self T : Set} `{Link Self} `{Link T}
        `{!From.Run Self T}
        `(!C Self T) :
        Prop := {
      from (value : T) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (From.run_from value)
            stack 🌲
          (
            Output.Success (from value),
            stack
          )
        }};
    }.
  End Eq.
End From.
Export (hints) From.

Module Into.
  Class C (Self T : Set) : Set := {
    into (self : Self) : T;
  }.

  Module Eq.
    Class C
        {Self T : Set} `{Link Self} `{Link T}
        `{!Into.Run Self T}
        `(!C Self T) :
        Prop := {
      into (self : Self) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (Into.run_into self)
            stack 🌲
          (
            Output.Success (into self),
            stack
          )
        }};
    }.
  End Eq.
End Into.
Export (hints) Into.

Module Impl_Into_for_From_T.
  Instance I
      (T U : Set)
      `{From.C U T} :
      Into.C T U := {|
    Into.into := From.from;
  |}.

  Module Eq.
    Instance I
        {T U : Set} `{Link T} `{Link U}
        `{!From.Run U T}
        `{HFrom : From.C U T}
        `{!From.Eq.C (Self := U) (T := T) HFrom} :
        Into.Eq.C (Self := T) (T := U) (Impl_Into_for_From_T.I T U).
    Proof.
      constructor; intros.
      (* into *)
      { s. {
          apply From.Eq.from.
        }
        s.
      }
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_Into_for_From_T.
Export (hints) Impl_Into_for_From_T.

(*
pub trait TryFrom<T>: Sized {
    type Error;
    fn try_from(value: T) -> Result<Self, Self::Error>;
}
*)
Module TryFrom.
  Class C (Self T Error : Set) : Set := {
    try_from (value : T) : Result.t Self Error;
  }.

  Module Eq.
    Class C
        {Self T Error : Set} `{Link Self} `{Link T} `{Link Error}
        `{!TryFrom.Run Self T Error}
        `(!C Self T Error) :
        Prop := {
      try_from (value : T) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (TryFrom.run_try_from value)
            stack 🌲
          (
            Output.Success (try_from value),
            stack
          )
        }};
    }.
  End Eq.
End TryFrom.
Export (hints) TryFrom.
