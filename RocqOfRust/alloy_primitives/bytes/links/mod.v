Require Import links.RocqOfRust.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bytes.mod.
Require Import bytes.links.bytes.
Require Import core.convert.links.mod.
Require Import core.links.clone.
Require Import core.links.default.
Require Import core.ops.links.deref.

(* pub struct Bytes(pub bytes::Bytes); *)
Module Bytes.
  Record t : Set := {
    value : bytes.Bytes.t;
  }.

  Parameter to_value : t -> Value.t.

  Instance IsLink : Link t := {
    Φ := Ty.path "alloy_primitives::bytes_::Bytes";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "alloy_primitives::bytes_::Bytes").
  Proof.
    eapply OfTy.Make with (A := t); reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End Bytes.
Export (hints) Bytes.

Module Impl_Clone_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run_clone (self : '& Self) :
    Run.Trait
      bytes_.Impl_core_clone_Clone_for_alloy_primitives_bytes__Bytes.clone
      [] [] [φ self] Self.
  Admitted.
  Global Opaque run_clone.

  Instance method_clone : Clone.Method_clone Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply bytes_.Impl_core_clone_Clone_for_alloy_primitives_bytes__Bytes.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Clone.Run Self := {}.
End Impl_Clone_for_Bytes.
Export (hints) Impl_Clone_for_Bytes.

Module Impl_Default_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run_default :
    Run.Trait
      bytes_.Impl_core_default_Default_for_alloy_primitives_bytes__Bytes.default
      [] [] [] Self.
  Admitted.
  Global Opaque run_default.

  Instance method_default : Default.Method_default Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply bytes_.Impl_core_default_Default_for_alloy_primitives_bytes__Bytes.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Default.Run Self := {}.
End Impl_Default_for_Bytes.
Export (hints) Impl_Default_for_Bytes.

(* impl Deref for Bytes *)
Module Impl_Deref_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run : Deref.Run Self bytes.Bytes.t.
  Admitted.
End Impl_Deref_for_Bytes.
Export (hints) Impl_Deref_for_Bytes.

(* impl DerefMut for Bytes *)
Module Impl_DerefMut_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run : DerefMut.Run Self bytes.Bytes.t.
  Admitted.
End Impl_DerefMut_for_Bytes.
Export (hints) Impl_DerefMut_for_Bytes.

Module Impl_AsRef_slice_u8_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run_as_ref (self : '& Self) :
    Run.Trait
      bytes_.Impl_core_convert_AsRef_slice_u8_for_alloy_primitives_bytes__Bytes.as_ref
      [] [] [φ self] ('& (list u8)).
  Admitted.
  Global Opaque run_as_ref.

  Instance method_as_ref : AsRef.Method_as_ref Self (list u8).
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply bytes_.Impl_core_convert_AsRef_slice_u8_for_alloy_primitives_bytes__Bytes.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : AsRef.Run Self (list u8) := {}.
End Impl_AsRef_slice_u8_for_Bytes.
Export (hints) Impl_AsRef_slice_u8_for_Bytes.

Module Impl_Bytes.
  Definition Self : Set :=
    Bytes.t.

  (* pub const fn new() -> Self *)
  Instance run_new : Run.Trait bytes_.Impl_alloy_primitives_bytes__Bytes.new [] [] [] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_new.

  (* pub fn copy_from_slice(data: &[u8]) -> Self *)
  Instance run_copy_from_slice (data : '& (list u8)) :
    Run.Trait bytes_.Impl_alloy_primitives_bytes__Bytes.copy_from_slice [] [] [ φ data ] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_copy_from_slice.
End Impl_Bytes.
Export (hints) Impl_Bytes.

(* impl From<Vec<u8>> for Bytes *)
Module Impl_From_Vec_u8_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run : From.Run Self (Vec.t u8 Global.t).
  Admitted.
End Impl_From_Vec_u8_for_Bytes.
Export (hints) Impl_From_Vec_u8_for_Bytes.
