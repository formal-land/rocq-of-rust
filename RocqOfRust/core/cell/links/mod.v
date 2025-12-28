Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.cell.
Require Import core.ops.links.deref.

Module Ref.
  Parameter t : forall (T : Set) `{Link T}, Set.

  Parameter to_value : forall {T : Set} `{Link T}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "core::cell::Ref") [] [Φ T];
    φ := to_value;
  }.

  Definition of_ty T_ty :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "core::cell::Ref") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End Ref.

(* impl<T: ?Sized> Deref for Ref<'_, T> *)
Module Impl_Deref_for_Ref.
  Instance run (T : Set) `{Link T} : Deref.Run (Ref.t T) T.
  Admitted.
End Impl_Deref_for_Ref.
Export Impl_Deref_for_Ref.

(* Approximation for core::cell::RefMut<T> *)
Module RefMut.
  Parameter t : forall (T : Set) `{Link T}, Set.

  Parameter to_value : forall {T : Set} `{Link T}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "core::cell::RefMut") [] [Φ T];
    φ := to_value;
  }.

  Definition of_ty T_ty :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "core::cell::RefMut") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End RefMut.

(* impl<T> Deref for RefMut<'_, T> *)
Module Impl_Deref_for_RefMut.
  Instance run (T : Set) `{Link T} : Deref.Run (RefMut.t T) T.
  Admitted.
End Impl_Deref_for_RefMut.
Export Impl_Deref_for_RefMut.

(* impl<T> DerefMut for RefMut<'_, T> *)
Module Impl_DerefMut_for_RefMut.
  Instance run (T : Set) `{Link T} : DerefMut.Run (RefMut.t T) T.
  Admitted.
End Impl_DerefMut_for_RefMut.
Export Impl_DerefMut_for_RefMut.
