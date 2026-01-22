Require Import RocqOfRust.RocqOfRust.
Require Import alloc.vec.mod.
Require Import links.M.
Require Import alloc.links.alloc.
Require Import alloc.links.raw_vec.
Require Import core.links.clone.
Require Import core.links.default.
Require Import core.links.option.
Require Import core.ops.links.deref.
Require Import core.ops.links.index.

(*
pub struct Vec<T, A: Allocator = Global> {
    buf: RawVec<T, A>,
    len: usize,
}
*)
Module Vec.
  Record t {T A : Set} : Set := {
    buf : RawVec.t T A;
    len : usize;
  }.
  Arguments t : clear implicits.

  Instance IsLink (T A : Set) `(Link T) `(Link A) : Link (t T A) := {
    Φ := Ty.apply (Ty.path "alloc::vec::Vec") [] [Φ T; Φ A];
    φ x := Value.StructRecord "alloc::vec::Vec" [
      ("buf", φ x.(buf));
      ("len", φ x.(len))
    ];
  }.

  Definition of_ty (T' A' : Ty.t) : 
    OfTy.t T' ->
    OfTy.t A' ->
    OfTy.t (Ty.apply (Ty.path "alloc::vec::Vec") [] [T'; A']).
  Proof. 
    intros [T] [A].
    eapply OfTy.Make with (A := t T A). 
    subst.
    reflexivity. 
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with {T A : Set} `{Link T} `{Link A}
    (buf' : Value.t) (buf : RawVec.t T A)
    (len' : Value.t) (len : usize) :
    buf' = φ buf ->
    len' = φ len ->
    Value.StructRecord "alloc::vec::Vec" [("buf", buf'); ("len", len')] =
      φ ({| buf := buf; len := len |} : t T A).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add unshelve eapply of_value_with : of_value.

  Definition of_value
    (T' A' : Ty.t)
    (H_T : OfTy.t T')
    (H_A : OfTy.t A')
    (buf' : Value.t) (buf : RawVec.t (OfTy.get_Set H_T) (OfTy.get_Set H_A))
    (len' : Value.t) (len : usize) :
    buf' = φ buf ->
    len' = φ len ->
    OfValue.t (Value.StructRecord "alloc::vec::Vec" [
      ("buf", buf');
      ("len", len')
    ]).
  Proof.
    intros.
    destruct H_T as [T].
    destruct H_A as [A].
    eapply OfValue.Make with (value := Build_t T A buf len).
    subst.
    reflexivity.
  Defined.
  Smpl Add unshelve eapply of_value : of_value.
End Vec.
Export (hints) Vec.

Module Impl_Clone_for_Vec.
  Instance method_clone {T A : Set} `{Link T} `{Link A} : Clone.Method_clone (Vec.t T A).
  Admitted.

  Instance run {T A : Set} `{Link T} `{Link A} : Clone.Run (Vec.t T A) := {}.
End Impl_Clone_for_Vec.
Export (hints) Impl_Clone_for_Vec.

Module Impl_Default_for_Vec.
  Instance method_default {T A : Set} `{Link T} `{Link A} : Default.Method_default (Vec.t T A).
  Admitted.

  Instance run {T A : Set} `{Link T} `{Link A} : Default.Run (Vec.t T A) := {}.
End Impl_Default_for_Vec.
Export (hints) Impl_Default_for_Vec.

Module Impl_Deref_for_Vec.
  Instance method_deref {T A : Set} `{Link T} `{Link A} : Deref.Method_deref (Vec.t T A) (list T).
  Admitted.

  Instance run {T A : Set} `{Link T} `{Link A} : Deref.Run (Vec.t T A) (list T) := {}.
End Impl_Deref_for_Vec.
Export (hints) Impl_Deref_for_Vec.

Module Impl_DerefMut_for_Vec.
  Instance run_deref_mut {T A : Set} `{Link T} `{Link A} (self : '&mut (Vec.t T A)) :
    Run.Trait (vec.Impl_core_ops_deref_DerefMut_where_core_alloc_Allocator_A_for_alloc_vec_Vec_T_A.deref_mut (Φ T) (Φ A)) [] [] [φ self] ('&mut (list T)).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_deref_mut.

  Instance method_deref_mut (T A : Set) `{Link T} `{Link A} :
    DerefMut.Method_deref_mut (Vec.t T A) (list T).
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { with_strategy transparent [Φ] apply vec.Impl_core_ops_deref_DerefMut_where_core_alloc_Allocator_A_for_alloc_vec_Vec_T_A.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run (T A : Set) `{Link T} `{Link A} : DerefMut.Run (Vec.t T A) (list T) := {}.
End Impl_DerefMut_for_Vec.
Export (hints) Impl_DerefMut_for_Vec.

Module Impl_Vec_T.
  Definition Self (T : Set) `{Link T} : Set :=
    Vec.t T Global.t.

  (*
    pub const fn new() -> Self 
  *)
  Instance run_new {T : Set} `{Link T} :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_alloc_alloc_Global.new (Φ T)) [] [] [] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_new.

  (* pub fn with_capacity(capacity: usize) -> Self *)
  Instance run_with_capacity {T : Set} `{Link T} (capacity : usize) :
    Run.Trait
      (vec.Impl_alloc_vec_Vec_T_alloc_alloc_Global.with_capacity (Φ T)) [] [] [φ capacity]
      (Self T).
  Admitted.
  Global Opaque run_with_capacity.
End Impl_Vec_T.
Export (hints) Impl_Vec_T.

Module Impl_Vec_T_A.
  Definition Self (T A : Set) `{Link T} `{Link A} : Set :=
    Vec.t T A.

  (*
    pub const fn len(&self) -> usize
  *)
  Instance run_len {T A : Set} `{Link T} `{Link A} (self : '& (Self T A)) :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.len (Φ T) (Φ A)) [] [] [φ self] usize.
  Admitted.
  Global Opaque run_len.

  (* pub const fn is_empty(&self) -> bool *)
  Instance run_is_empty {T A : Set} `{Link T} `{Link A} (self : '& (Self T A)) :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.is_empty (Φ T) (Φ A)) [] [] [φ self] bool.
  Admitted.
  Global Opaque run_is_empty.

  (* pub fn pop(&mut self) -> Option<T> *)
  Instance run_pop {T A : Set} `{Link T} `{Link A} (self : '&mut (Self T A)) :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.pop (Φ T) (Φ A)) [] [] [φ self] (option T).
  Admitted.
  Global Opaque run_pop.

  (* pub const fn capacity(&self) -> usize *)
  Instance run_capacity {T A : Set} `{Link T} `{Link A} (self : '& (Self T A)) :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.capacity (Φ T) (Φ A)) [] [] [φ self] usize.
  Admitted.
  Global Opaque run_capacity.

  (* pub fn push(&mut self, value: T) *)
  Instance run_push {T A : Set} `{Link T} `{Link A}
      (self : '&mut (Self T A))
      (value : T) :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.push (Φ T) (Φ A)) [] [] [φ self; φ value] unit.
  Admitted.
  Global Opaque run_push.
End Impl_Vec_T_A.
Export (hints) Impl_Vec_T_A.

Module Impl_Index_for_Vec_T_A.
  Definition Self := Vec.t.

  Instance run (T I A Output : Set) `{Link T} `{Link I} `{Link A} `{Link Output} :
    index.Index.Run (Self T A) I Output.
  Admitted.
End Impl_Index_for_Vec_T_A.
Export (hints) Impl_Index_for_Vec_T_A.
