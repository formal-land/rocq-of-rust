Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import core.links.cmp.
Require Import core.simulate.cmp.
Require Import ruint.links.cmp.
Require Import ruint.links.lib.

Module Impl_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* pub fn is_zero(&self) -> bool *)
  Definition is_zero {BITS LIMBS : usize} (self : Self BITS LIMBS) : bool :=
    self.(Uint.value) =? 0.

  Lemma is_zero_like {BITS LIMBS : usize}
      (stack : Stack.t)
      (ref_self : '& (Self BITS LIMBS)) :
    SimulateM.eval_f
      (Impl_Uint.run_is_zero BITS LIMBS ref_self)
      stack =
    let*s self := SimulateM.read stack ref_self.(Ref.core) in
    match self with
    | Output.Success value =>
      SimulateM.Pure (Output.Success (is_zero value), stack)
    | Output.Exception exception =>
      SimulateM.Pure (Output.Exception exception, stack)
    end.
  Admitted.

  Lemma is_zero_eq {BITS LIMBS : usize}
      (stack : Stack.t)
      (ref_self : '& (Self BITS LIMBS))
      (self : Self BITS LIMBS) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (Impl_Uint.run_is_zero BITS LIMBS ref_self)
        stack 🌲
      (
        Output.Success (is_zero self),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.

(* impl<const BITS: usize, const LIMBS: usize> PartialEq for Uint<BITS, LIMBS> *)
Module Impl_PartialEq_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Section WithParams.
    Context {BITS LIMBS : usize}.

    Definition eq (self other : Self BITS LIMBS) : bool :=
      self.(Uint.value) =? other.(Uint.value).

    Definition ne (self other : Self BITS LIMBS) : bool :=
      negb (eq self other).

    Global Instance I : PartialEq.C (Self BITS LIMBS) (Self BITS LIMBS) := {|
      PartialEq.eq := eq;
      PartialEq.ne := ne;
    |}.
  End WithParams.

  Module Eq.
    Instance I {BITS LIMBS : usize} : PartialEq.Eq.C (Self BITS LIMBS) (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_PartialEq_for_Uint.
Export (hints) Impl_PartialEq_for_Uint.

(* impl<const BITS: usize, const LIMBS: usize> PartialOrd for Uint<BITS, LIMBS> *)
Module Impl_PartialOrd_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Section WithParams.
    Context {BITS LIMBS : usize}.

    Definition partial_cmp (self other : Self BITS LIMBS) : option Ordering.t :=
      Some (
        match Z.compare self.(Uint.value) other.(Uint.value) with
        | Lt => Ordering.Less
        | Eq => Ordering.Equal
        | Gt => Ordering.Greater
        end
      ).

    Definition lt (self other : Self BITS LIMBS) : bool :=
      self.(Uint.value) <? other.(Uint.value).

    Definition le (self other : Self BITS LIMBS) : bool :=
      self.(Uint.value) <=? other.(Uint.value).

    Definition gt (self other : Self BITS LIMBS) : bool :=
      self.(Uint.value) >? other.(Uint.value).

    Definition ge (self other : Self BITS LIMBS) : bool :=
      self.(Uint.value) >=? other.(Uint.value).

    Global Instance I : PartialOrd.C (Self BITS LIMBS) (Self BITS LIMBS) := {|
      PartialOrd.partial_cmp := partial_cmp;
      PartialOrd.lt := lt;
      PartialOrd.le := le;
      PartialOrd.gt := gt;
      PartialOrd.ge := ge;
    |}.
  End WithParams.

  Module Eq.
    Instance I {BITS LIMBS : usize} : PartialOrd.Eq.C (Self BITS LIMBS) (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_PartialOrd_for_Uint.
Export (hints) Impl_PartialOrd_for_Uint.

(* impl<const BITS: usize, const LIMBS: usize> Ord for Uint<BITS, LIMBS> *)
Module Impl_Ord_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Section WithParams.
    Context {BITS LIMBS : usize}.

    Definition cmp (self other : Self BITS LIMBS) : Ordering.t :=
      match Z.compare self.(Uint.value) other.(Uint.value) with
      | Lt => Ordering.Less
      | Eq => Ordering.Equal
      | Gt => Ordering.Greater
      end.

    Global Instance I : Ord.C (Self BITS LIMBS) := {|
      Ord.cmp := cmp;
      Ord.max self other := if Impl_PartialOrd_for_Uint.ge self other then self else other;
      Ord.min self other := if Impl_PartialOrd_for_Uint.le self other then self else other;
      Ord.clamp self min max :=
        if Impl_PartialOrd_for_Uint.lt self min then min
        else if Impl_PartialOrd_for_Uint.gt self max then max
        else self;
    |}.
  End WithParams.

  Module Eq.
    Instance I {BITS LIMBS : usize} : Ord.Eq.C (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Ord_for_Uint.
Export (hints) Impl_Ord_for_Uint.
