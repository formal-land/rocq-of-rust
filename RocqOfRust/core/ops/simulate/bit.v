Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import core.ops.links.bit.

(*
pub trait BitAnd<Rhs = Self> {
    type Output;
    fn bitand(self, rhs: Rhs) -> Self::Output;
}
*)
Module BitAnd.
  Class C (Self Rhs Output : Set) : Set := {
    bitand (self : Self) (rhs : Rhs) : Output;
  }.

  Module Eq.
    Class C
        (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output}
        `{!BitAnd.Run Self Rhs Output}
        (I : C Self Rhs Output) :
        Prop := {
      bitand (self : Self) (rhs : Rhs) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (BitAnd.run_bitand self rhs)
            stack 🌲
          (
            Output.Success (I.(bitand) self rhs),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End BitAnd.
Export (hints) BitAnd.

(*
pub trait BitOr<Rhs = Self> {
    type Output;
    fn bitor(self, rhs: Rhs) -> Self::Output;
}
*)
Module BitOr.
  Class C (Self Rhs Output : Set) : Set := {
    bitor (self : Self) (rhs : Rhs) : Output;
  }.

  Module Eq.
    Class C
        (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output}
        `{!BitOr.Run Self Rhs Output}
        (I : C Self Rhs Output) :
        Prop := {
      bitor (self : Self) (rhs : Rhs) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (BitOr.run_bitor self rhs)
            stack 🌲
          (
            Output.Success (I.(bitor) self rhs),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End BitOr.
Export (hints) BitOr.

(*
pub trait BitXor<Rhs = Self> {
    type Output;
    fn bitxor(self, rhs: Rhs) -> Self::Output;
}
*)
Module BitXor.
  Class C (Self Rhs Output : Set) : Set := {
    bitxor (self : Self) (rhs : Rhs) : Output;
  }.

  Module Eq.
    Class C
        (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output}
        `{!BitXor.Run Self Rhs Output}
        (I : C Self Rhs Output) :
        Prop := {
      bitxor (self : Self) (rhs : Rhs) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (BitXor.run_bitxor self rhs)
            stack 🌲
          (
            Output.Success (I.(bitxor) self rhs),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End BitXor.
Export (hints) BitXor.

(*
pub trait Shl<Rhs = Self> {
    type Output;
    fn shl(self, rhs: Rhs) -> Self::Output;
}
*)
Module Shl.
  Class C (Self Rhs Output : Set) : Set := {
    shl (self : Self) (rhs : Rhs) : Output;
  }.

  Module Eq.
    Class C
        (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output}
        `{!Shl.Run Self Rhs Output}
        (I : C Self Rhs Output) :
        Prop := {
      shl (self : Self) (rhs : Rhs) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (Shl.run_shl self rhs)
            stack 🌲
          (
            Output.Success (I.(shl) self rhs),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Shl.
Export (hints) Shl.

(*
pub trait Shr<Rhs = Self> {
    type Output;
    fn shr(self, rhs: Rhs) -> Self::Output;
}
*)
Module Shr.
  Class C (Self Rhs Output : Set) : Set := {
    shr (self : Self) (rhs : Rhs) : Output;
  }.

  Module Eq.
    Class C
        (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output}
        `{!Shr.Run Self Rhs Output}
        (I : C Self Rhs Output) :
        Prop := {
      shr (self : Self) (rhs : Rhs) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (Shr.run_shr self rhs)
            stack 🌲
          (
            Output.Success (I.(shr) self rhs),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Shr.
Export (hints) Shr.

(*
pub trait Not {
    type Output;
    fn not(self) -> Self::Output;
}
*)
Module Not.
  Class C (Self Output : Set) : Set := {
    not (self : Self) : Output;
  }.

  Module Eq.
    Class C
        (Self Output : Set) `{Link Self} `{Link Output}
        `{!Not.Run Self Output}
        (I : C Self Output) :
        Prop := {
      not (self : Self) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (Not.run_not self)
            stack 🌲
          (
            Output.Success (I.(not) self),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Not.
Export (hints) Not.
