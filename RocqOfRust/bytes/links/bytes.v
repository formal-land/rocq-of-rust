Require Import links.RocqOfRust.
Require Import bytes.bytes.
Require Import core.convert.links.mod.
Require Import core.ops.links.deref.

(*
pub struct Bytes {
    ptr: *const u8,
    len: usize,
    // inlined "trait object"
    data: AtomicPtr<()>,
    vtable: &'static Vtable,
}
*)
Module Bytes.
  Record t : Set := {
    value : list u8;
  }.

  Parameter to_value : t -> Value.t.

  Instance IsLink : Link t := {
    Φ := Ty.path "bytes::bytes::Bytes";
    φ x := to_value x;
  }.

  Definition of_ty : OfTy.t (Ty.path "bytes::bytes::Bytes").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Bytes.
Export (hints) Bytes.

Module Impl_Bytes.
  Definition Self : Set :=
    Bytes.t.

  (* pub const fn len(&self) -> usize *)
  Instance run_len (self : '& Self) :
    Run.Trait
      bytes.Impl_bytes_bytes_Bytes.len [] [] [ φ self ]
      usize.
  Proof.
  Admitted.
  Global Opaque run_len.

  (* pub fn clear(&mut self) *)
  Instance run_clear (self : '&mut Self) :
    Run.Trait bytes.Impl_bytes_bytes_Bytes.clear [] [] [φ self] unit.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_clear.
End Impl_Bytes.
Export (hints) Impl_Bytes.

(*
impl Deref for Bytes {
type Target = [u8];
*)
Module Impl_Deref_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run_deref (self : '& Self) :
    Run.Trait
      bytes.Impl_core_ops_deref_Deref_for_bytes_bytes_Bytes.deref
      [] [] [φ self] ('& (list u8)).
  Proof.
  Admitted.
  Global Opaque run_deref.

  Instance method_deref : Deref.Method_deref Self (list u8).
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply bytes.Impl_core_ops_deref_Deref_for_bytes_bytes_Bytes.Implements. }
      { reflexivity. }
    }
    { exact run_deref. }
  Defined.

  Instance run : Deref.Run Self (list u8) := {}.
End Impl_Deref_for_Bytes.
Export (hints) Impl_Deref_for_Bytes.

Module Impl_AsRef_slice_u8_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run_as_ref (self : '& Self) :
    Run.Trait
      bytes.Impl_core_convert_AsRef_slice_u8_for_bytes_bytes_Bytes.as_ref
      [] [] [φ self] ('& (list u8)).
  Proof.
    exact (Impl_Deref_for_Bytes.run_deref self).
  Defined.
  Global Opaque run_as_ref.

  Instance method_as_ref : AsRef.Method_as_ref Self (list u8).
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply bytes.Impl_core_convert_AsRef_slice_u8_for_bytes_bytes_Bytes.Implements. }
      { reflexivity. }
    }
    { exact run_as_ref. }
  Defined.

  Instance run : AsRef.Run Self (list u8) := {}.
End Impl_AsRef_slice_u8_for_Bytes.
Export (hints) Impl_AsRef_slice_u8_for_Bytes.
