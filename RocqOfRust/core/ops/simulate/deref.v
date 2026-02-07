Require Import simulate.RocqOfRust.
Require Import core.ops.links.deref.

(*
pub trait Deref {
    type Target: ?Sized;
    fn deref(&self) -> &Self::Target;
}
*)
Module Deref.
  Class C (Self Target : Set) `{Link Self} `{Link Target} : Set := {
    deref : RefStub.t Self Target;
  }.

  Module Eq.
    Class t
        {Self Target : Set} `{Link Self} `{Link Target}
        `{!Deref.Run Self Target}
        (I : C Self Target) :
        Prop := {
      deref (ref_self : '& Self) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (Deref.run_deref ref_self)
            stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(deref)),
            stack
          )
        }};
    }.
  End Eq.
End Deref.

(*
pub trait DerefMut: Deref {
    fn deref_mut(&mut self) -> &mut Self::Target;
}
*)
Module DerefMut.
  Class C (Self Target : Set) `{Link Self} `{Link Target} : Set := {
    deref_mut : RefStub.t Self Target;
  }.

  Module Eq.
    Class t
        {Self Target : Set} `{Link Self} `{Link Target}
        `{!DerefMut.Run Self Target}
        (I : C Self Target) :
        Prop := {
      deref_mut (ref_self : '&mut Self) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (DerefMut.run_deref_mut ref_self)
            stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(deref_mut)),
            stack
          )
        }};
    }.
  End Eq.
End DerefMut.
