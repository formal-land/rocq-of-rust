Require Import simulate.RocqOfRust.
Require Import core.ops.links.arith.

(*
pub trait Add<Rhs = Self> {
    type Output;
    fn add(self, rhs: Rhs) -> Self::Output;
}
*)
Module Add.
  Class C (Self Rhs Output : Set) : Set := {
    add (self : Self) (rhs : Rhs) : Output;
  }.

  Module Eq.
    Class C
        (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output}
        `{!Add.Run Self Rhs Output}
        (I : C Self Rhs Output) :
        Prop := {
      add (self : Self) (rhs : Rhs) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (Add.run_add self rhs)
            stack 🌲
          (
            Output.Success (I.(add) self rhs),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Add.
Export (hints) Add.

(*
pub trait Sub<Rhs = Self> {
    type Output;
    fn sub(self, rhs: Rhs) -> Self::Output;
}
*)
Module Sub.
  Class C (Self Rhs Output : Set) : Set := {
    sub (self : Self) (rhs : Rhs) : Output;
  }.

  Module Eq.
    Class C
        (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output}
        `{!Sub.Run Self Rhs Output}
        (I : C Self Rhs Output) :
        Prop := {
      sub (self : Self) (rhs : Rhs) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (Sub.run_sub self rhs)
            stack 🌲
          (
            Output.Success (I.(sub) self rhs),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Sub.
Export (hints) Sub.

(*
pub trait Mul<Rhs = Self> {
    type Output;
    fn mul(self, rhs: Rhs) -> Self::Output;
}
*)
Module Mul.
  Class C (Self Rhs Output : Set) : Set := {
    mul (self : Self) (rhs : Rhs) : Output;
  }.

  Module Eq.
    Class C
        (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output}
        `{!Mul.Run Self Rhs Output}
        (I : C Self Rhs Output) :
        Prop := {
      mul (self : Self) (rhs : Rhs) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (Mul.run_mul self rhs)
            stack 🌲
          (
            Output.Success (I.(mul) self rhs),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Mul.
Export (hints) Mul.

(*
pub trait Div<Rhs = Self> {
    type Output;
    fn div(self, rhs: Rhs) -> Self::Output;
}
*)
Module Div.
  Class C (Self Rhs Output : Set) : Set := {
    div (self : Self) (rhs : Rhs) : Output;
  }.

  Module Eq.
    Class C
        (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output}
        `{!Div.Run Self Rhs Output}
        (I : C Self Rhs Output) :
        Prop := {
      div (self : Self) (rhs : Rhs) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (Div.run_div self rhs)
            stack 🌲
          (
            Output.Success (I.(div) self rhs),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Div.
Export (hints) Div.

(*
pub trait Rem<Rhs = Self> {
    type Output;
    fn rem(self, rhs: Rhs) -> Self::Output;
}
*)
Module Rem.
  Class C (Self Rhs Output : Set) : Set := {
    rem (self : Self) (rhs : Rhs) : Output;
  }.

  Module Eq.
    Class C
        (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output}
        `{!Rem.Run Self Rhs Output}
        (I : C Self Rhs Output) :
        Prop := {
      rem (self : Self) (rhs : Rhs) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (Rem.run_rem self rhs)
            stack 🌲
          (
            Output.Success (I.(rem) self rhs),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Rem.
Export (hints) Rem.
