Require Import simulate.RocqOfRust.
Require Import core.ops.links.range.

Module Impl_Range.
  Definition Self (Idx : Set) : Set :=
    Range.t Idx.

  Definition is_empty (r : Range.t usize) : bool :=
    r.(Range.start).(Integer.value) >=? r.(Range.end_).(Integer.value).

  Lemma is_empty_eq (ref_self : '& (Range.t usize)) (stack : Stack.t) (self : Range.t usize) :
      CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (links.range.Impl_Range.run_is_empty ref_self)
        stack 🌲
      (
        Output.Success (is_empty self),
        stack
      )
    }}.
  Admitted.
End Impl_Range.
