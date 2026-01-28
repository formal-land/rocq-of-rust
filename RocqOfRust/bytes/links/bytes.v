Require Import links.RocqOfRust.
Require Import bytes.bytes.
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
  Parameter t : Set.

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

  Instance run : Deref.Run Self (list u8).
  Admitted.
End Impl_Deref_for_Bytes.
Export (hints) Impl_Deref_for_Bytes.
