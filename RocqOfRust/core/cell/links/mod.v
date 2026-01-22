Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.cell.
Require Import core.ops.links.deref.

Module Ref.
  Parameter t : forall (T : Set) `{Link T}, Set.

  Parameter to_value : forall {T : Set} `{Link T}, t T -> Value.t.

  Instance IsLink (T : Set) `{Link T} : Link (t T) := {
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
Export (hints) Ref.

(* impl<T: ?Sized> Deref for Ref<'_, T> *)
Module Impl_Deref_for_Ref.
  Instance run (T : Set) `{Link T} : Deref.Run (Ref.t T) T.
  Admitted.
End Impl_Deref_for_Ref.
Export (hints) Impl_Deref_for_Ref.

(* Approximation for core::cell::RefMut<T> *)
Module RefMut.
  Parameter t : forall (T : Set) `{Link T}, Set.

  Parameter to_value : forall {T : Set} `{Link T}, t T -> Value.t.

  Instance IsLink (T : Set) `{Link T} : Link (t T) := {
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
Export (hints) RefMut.

(* impl<T> Deref for RefMut<'_, T> *)
Module Impl_Deref_for_RefMut.
  Instance run (T : Set) `{Link T} : Deref.Run (RefMut.t T) T.
  Admitted.
End Impl_Deref_for_RefMut.
Export (hints) Impl_Deref_for_RefMut.

(* impl<T> DerefMut for RefMut<'_, T> *)
Module Impl_DerefMut_for_RefMut.
  Instance run (T : Set) `{Link T} : DerefMut.Run (RefMut.t T) T.
  Admitted.
End Impl_DerefMut_for_RefMut.
Export (hints) Impl_DerefMut_for_RefMut.

(* Approximation for core::cell::RefCell<T> *)
Module RefCell.
  Parameter t : forall (T : Set), Set.

  Parameter to_value : forall {T : Set} `{Link T}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "core::cell::RefCell") [] [Φ T];
    φ := to_value;
  }.

  Definition of_ty T_ty :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "core::cell::RefCell") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End RefCell.
Export (hints) RefCell.

Module Impl_RefCell.
  Definition Self (T : Set) : Set := RefCell.t T.

  (* pub const fn new(value: T) -> RefCell<T> *)
  Instance run_new {T : Set} `{Link T} (value : T) :
    Run.Trait (cell.Impl_core_cell_RefCell_T.new (Φ T)) [] [] [φ value] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_new.

  (* pub fn borrow(&self) -> Ref<'_, T> *)
  Instance run_borrow {T : Set} `{Link T} (self : '& (RefCell.t T)) :
    Run.Trait (cell.Impl_core_cell_RefCell_T.borrow (Φ T)) [] [] [φ self] (Ref.t T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_borrow.

  (* pub fn borrow_mut(&self) -> RefMut<'_, T> *)
  Instance run_borrow_mut {T : Set} `{Link T} (self : '& (RefCell.t T)) :
    Run.Trait (cell.Impl_core_cell_RefCell_T.borrow_mut (Φ T)) [] [] [φ self] (RefMut.t T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_borrow_mut.
End Impl_RefCell.
Export (hints) Impl_RefCell.
