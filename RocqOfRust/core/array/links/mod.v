Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.array.mod.
Require Import core.convert.links.mod.
Require Import core.links.array.
Require Import core.ops.links.function.
Require Import core.ops.links.index.

(* pub struct TryFromSliceError(/* private fields */); *)
Module TryFromSliceError.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Instance IsLink : Link t := {
    Φ := Ty.path "core::convert::TryFromSliceError";
    φ := to_value;
  }.
End TryFromSliceError.
Export (hints) TryFromSliceError.

(*
impl<T, I, const N: usize> IndexMut<I> for [T; N]
where
    [T]: IndexMut<I>,
*)
Module Impl_IndexMut_for_Array.
  Definition Self (T I : Set) (N : usize) : Set :=
    array.t T N.

  Instance run (T I : Set) `{Link T} `{Link I} (N : usize)
    (IndexMut_Output : Set) `{Link IndexMut_Output}
    (run_IndexMut_for_slice_T : IndexMut.Run (list T) I IndexMut_Output) :
    IndexMut.Run (Self T I N) I IndexMut_Output.
  Admitted.
End Impl_IndexMut_for_Array.
Export (hints) Impl_IndexMut_for_Array.

(*
pub fn from_fn<T, const N: usize, F>(cb: F) -> [T; N]
where
    F: FnMut(usize) -> T,
{
    try_from_fn(NeverShortCircuit::wrap_mut_1(cb)).0
}
*)
Instance run_from_fn (T : Set) `{Link T} (N : usize) (F : Set) `{Link F}
    {run_FnMut_for_F : FnMut.Run F usize T}
    (cb : F) :
  Run.Trait array.from_fn
    [φ N] [Φ T; Φ F] [φ cb]
    (array.t T N).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_from_fn.

(*
impl<'a, T, const N: usize> TryFrom<&'a [T]> for &'a [T; N] {
    type Error = TryFromSliceError;
}
*)
Module Impl_TryFrom_Ref_for_Ref_Array.
  Definition Self (T : Set) (N : usize) `{Link T} : Set :=
    '& (array.t T N).

  Definition Error : Set :=
    TryFromSliceError.t.

  Instance run (T : Set) `{Link T} (N : usize) :
    TryFrom.Run (Self T N) ('& (list T)) Error.
  Admitted.
End Impl_TryFrom_Ref_for_Ref_Array.
Export (hints) Impl_TryFrom_Ref_for_Ref_Array.

(*
impl<T, const N: usize> TryFrom<&[T]> for [T; N]
where
    T: Copy,
{
    type Error = TryFromSliceError;
*)
Module Impl_TryFrom_Ref_for_Array.
  Definition Self (T : Set) (N : usize) `{Link T} : Set :=
    array.t T N.

  Definition Error : Set :=
    TryFromSliceError.t.

  Instance run (T : Set) `{Link T} (N : usize) :
    TryFrom.Run (Self T N) ('& (list T)) Error.
  Admitted.
End Impl_TryFrom_Ref_for_Array.
Export (hints) Impl_TryFrom_Ref_for_Array.
