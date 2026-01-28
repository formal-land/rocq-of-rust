Require Import links.RocqOfRust.
Require Import core.iter.traits.links.collect.
Require Import core.iter.traits.links.iterator.
Require Import core.links.array.

Require Export core.array.links.iter_IntoIter.

(*
impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;
*)
Module Impl_Iterator_for_IntoIter.
  Definition Self (T : Set) (N : usize) : Set :=
    IntoIter.t T N.

  Instance run (T : Set) (N : usize) `{Link T} :
    Iterator.Run (Self T N) T.
  Admitted.
End Impl_Iterator_for_IntoIter.
Export (hints) Impl_Iterator_for_IntoIter.

(*
impl<T, const N: usize> IntoIterator for [T; N] {
    type Item = T;
    type IntoIter = IntoIter<T, N>;
*)
Module Impl_IntoIterator_for_Array.
  Definition Self (T : Set) (N : usize) : Set :=
    array.t T N.

  Definition types (T : Set) (N : usize) : IntoIterator.Types.t :=
    {|
      IntoIterator.Types.Item := T;
      IntoIterator.Types.IntoIter := IntoIter.t T N;
    |}.

  Instance types_AreLinks (T : Set) (N : usize) `{Link T} :
    IntoIterator.Types.AreLinks (types T N).
  Proof.
    constructor; typeclasses eauto.
  Defined.

  Instance run (T : Set) (N : usize) `{Link T} :
    IntoIterator.Run (Self T N) (types T N).
  Admitted.
End Impl_IntoIterator_for_Array.
Export (hints) Impl_IntoIterator_for_Array.
