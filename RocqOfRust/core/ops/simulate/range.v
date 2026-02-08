Require Import simulate.RocqOfRust.
Require Import core.links.clone.
Require Import core.links.cmp.
Require Import core.ops.links.range.
Require Import core.simulate.clone.

Module Impl_Range.
  Definition Self (Idx : Set) : Set :=
    Range.t Idx.

  Definition is_empty (r : Range.t usize) : bool :=
    r.(Range.start).(Integer.value) >=? r.(Range.end_).(Integer.value).

  Lemma is_empty_eq (ref_self : '& (Range.t usize)) (stack : Stack.t) (self : Range.t usize) :
      CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (Impl_Range.run_is_empty ref_self)
        stack 🌲
      (
        Output.Success (is_empty self),
        stack
      )
    }}.
  Admitted.
End Impl_Range.

Module Impl_Clone_for_Range.
  Definition Self (Idx : Set) : Set :=
    Range.t Idx.

  Definition clone {Idx : Set} (self : Self Idx) : Self Idx := {|
    Range.start := self.(Range.start);
    Range.end_ := self.(Range.end_);
  |}.

  Lemma clone_eq {Idx : Set} `{Link Idx}
      (ref_self : '& (Self Idx))
      (self : Self Idx)
      (stack : Stack.t) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (clone.Clone.run_clone (Self := Self Idx) ref_self)
        stack 🌲
      (
        Output.Success (clone self),
        stack
      )
    }}.
  Admitted.

  Instance I {Idx : Set} : core.simulate.clone.Clone.C (Self Idx) := {|
    core.simulate.clone.Clone.clone := clone;
  |}.

  Module Eq.
    Instance I {Idx : Set} `{Link Idx} :
      core.simulate.clone.Clone.Eq.C (Self := Self Idx) Impl_Clone_for_Range.I.
    Proof.
      constructor; intros.
      (* clone *)
      { now apply clone_eq. }
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_Clone_for_Range.
Export (hints) Impl_Clone_for_Range.
