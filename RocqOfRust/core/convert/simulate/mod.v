Require Import simulate.RocqOfRust.
Require Import core.convert.links.mod.
Require Import core.links.result.

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
