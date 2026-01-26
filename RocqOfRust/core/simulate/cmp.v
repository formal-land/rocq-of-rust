Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import core.links.cmp.
Require Export core.links.cmpOrdering.

(*
pub trait PartialEq<Rhs: ?Sized = Self> {
    fn eq(&self, other: &Rhs) -> bool;
    fn ne(&self, other: &Rhs) -> bool;
}
*)
Module PartialEq.
  Class C (Self Rhs : Set) : Set := {
    eq (self : Self) (other : Rhs) : bool;
    ne (self : Self) (other : Rhs) : bool;
  }.

  Module Eq.
    Class C
        (Self Rhs : Set) `{Link Self} `{Link Rhs}
        `{!PartialEq.Run Self Rhs}
        (I : C Self Rhs) :
        Prop := {
      eq (ref_self : '& Self) (ref_other : '& Rhs) (stack : Stack.t)
          (self : Self) (other : Rhs) :
        CanRead.t stack self ref_self ->
        CanRead.t stack other ref_other ->
        {{
          SimulateM.eval_f
            (PartialEq.run_eq ref_self ref_other)
            stack 🌲
          (
            Output.Success (I.(eq) self other),
            stack
          )
        }};
      ne (ref_self : '& Self) (ref_other : '& Rhs) (stack : Stack.t)
          (self : Self) (other : Rhs) :
        CanRead.t stack self ref_self ->
        CanRead.t stack other ref_other ->
        {{
          SimulateM.eval_f
            (PartialEq.run_ne ref_self ref_other)
            stack 🌲
          (
            Output.Success (I.(ne) self other),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End PartialEq.
Export (hints) PartialEq.

(*
pub trait Eq: PartialEq { }
*)
Module Eq.
  Class C (Self : Set) : Set := {
    PartialEq_for_Self :: PartialEq.C Self Self;
  }.

  Module Eq.
    Class C
        (Self : Set) `{Link Self}
        `{!links.cmp.Eq.Run Self}
        (I : C Self) :
        Prop := {
      PartialEq_for_Self :: PartialEq.Eq.C Self Self I.(PartialEq_for_Self);
    }.
  End Eq.
  Export (hints) Eq.
End Eq.
Export (hints) Eq.

(*
pub trait Ord: Eq + PartialOrd<Self> {
    fn cmp(&self, other: &Self) -> Ordering;
    fn max(self, other: Self) -> Self;
    fn min(self, other: Self) -> Self;
    fn clamp(self, min: Self, max: Self) -> Self;
}
*)
Module Ord.
  Class C (Self : Set) : Set := {
    cmp (self other : Self) : Ordering.t;
    max (self other : Self) : Self;
    min (self other : Self) : Self;
    clamp (self min max : Self) : Self;
  }.

  Module Eq.
    Class C
        (Self : Set) `{Link Self}
        `{!links.cmp.Ord.Run Self}
        (I : C Self) :
        Prop := {
      cmp (ref_self ref_other : '& Self) (stack : Stack.t)
          (self other : Self) :
        CanRead.t stack self ref_self ->
        CanRead.t stack other ref_other ->
        {{
          SimulateM.eval_f
            (links.cmp.Ord.run_cmp ref_self ref_other)
            stack 🌲
          (
            Output.Success (I.(cmp) self other),
            stack
          )
        }};
      max (self other : Self) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (links.cmp.Ord.run_max self other)
            stack 🌲
          (
            Output.Success (I.(max) self other),
            stack
          )
        }};
      min (self other : Self) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (links.cmp.Ord.run_min self other)
            stack 🌲
          (
            Output.Success (I.(min) self other),
            stack
          )
        }};
      clamp (self min max : Self) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (links.cmp.Ord.run_clamp self min max)
            stack 🌲
          (
            Output.Success (I.(clamp) self min max),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Ord.
Export (hints) Ord.

(*
pub trait PartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    fn partial_cmp(&self, other: &Rhs) -> Option<Ordering>;
    fn lt(&self, other: &Rhs) -> bool;
    fn le(&self, other: &Rhs) -> bool;
    fn gt(&self, other: &Rhs) -> bool;
    fn ge(&self, other: &Rhs) -> bool;
}
*)
Module PartialOrd.
  Class C (Self Rhs : Set) : Set := {
    partial_cmp (self : Self) (other : Rhs) : option Ordering.t;
    lt (self : Self) (other : Rhs) : bool;
    le (self : Self) (other : Rhs) : bool;
    gt (self : Self) (other : Rhs) : bool;
    ge (self : Self) (other : Rhs) : bool;
  }.

  Module Eq.
    Class C
        (Self Rhs : Set) `{Link Self} `{Link Rhs}
        `{!links.cmp.PartialOrd.Run Self Rhs}
        (I : C Self Rhs) :
        Prop := {
      partial_cmp (ref_self : '& Self) (ref_other : '& Rhs) (stack : Stack.t)
          (self : Self) (other : Rhs) :
        CanRead.t stack self ref_self ->
        CanRead.t stack other ref_other ->
        {{
          SimulateM.eval_f
            (links.cmp.PartialOrd.run_partial_cmp ref_self ref_other)
            stack 🌲
          (
            Output.Success (I.(partial_cmp) self other),
            stack
          )
        }};
      lt (ref_self : '& Self) (ref_other : '& Rhs) (stack : Stack.t)
          (self : Self) (other : Rhs) :
        CanRead.t stack self ref_self ->
        CanRead.t stack other ref_other ->
        {{
          SimulateM.eval_f
            (links.cmp.PartialOrd.run_lt ref_self ref_other)
            stack 🌲
          (
            Output.Success (I.(lt) self other),
            stack
          )
        }};
      le (ref_self : '& Self) (ref_other : '& Rhs) (stack : Stack.t)
          (self : Self) (other : Rhs) :
        CanRead.t stack self ref_self ->
        CanRead.t stack other ref_other ->
        {{
          SimulateM.eval_f
            (links.cmp.PartialOrd.run_le ref_self ref_other)
            stack 🌲
          (
            Output.Success (le self other),
            stack
          )
        }};
      gt (ref_self : '& Self) (ref_other : '& Rhs) (stack : Stack.t)
          (self : Self) (other : Rhs) :
        CanRead.t stack self ref_self ->
        CanRead.t stack other ref_other ->
        {{
          SimulateM.eval_f
            (links.cmp.PartialOrd.run_gt ref_self ref_other)
            stack 🌲
          (
            Output.Success (gt self other),
            stack
          )
        }};
      ge (ref_self : '& Self) (ref_other : '& Rhs) (stack : Stack.t)
          (self : Self) (other : Rhs) :
        CanRead.t stack self ref_self ->
        CanRead.t stack other ref_other ->
        {{
          SimulateM.eval_f
            (links.cmp.PartialOrd.run_ge ref_self ref_other)
            stack 🌲
          (
            Output.Success (ge self other),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End PartialOrd.
Export (hints) PartialOrd.

(* impl PartialEq for Ordering *)
Module Impl_PartialEq_for_Ordering.
  Definition Self : Set := Ordering.t.

  Definition eq (self other : Self) : bool :=
    match self, other with
    | Ordering.Less, Ordering.Less => true
    | Ordering.Equal, Ordering.Equal => true
    | Ordering.Greater, Ordering.Greater => true
    | _, _ => false
    end.

  Definition ne (self other : Self) : bool :=
    negb (eq self other).

  Global Instance I : PartialEq.C Self Self := {|
    PartialEq.eq := eq;
    PartialEq.ne := ne;
  |}.

  Module Eq.
    Instance I : PartialEq.Eq.C Self Self I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_PartialEq_for_Ordering.
Export (hints) Impl_PartialEq_for_Ordering.
