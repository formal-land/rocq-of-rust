Require Import links.RocqOfRust.
Require Import core.links.cmpOrdering.
Require Import core.intrinsics.mod.

Instance run_three_way_compare (integer_kind : IntegerKind.t) (x y : Integer.t integer_kind) :
  Run.Trait
    intrinsics.three_way_compare [] [ Φ (Integer.t integer_kind) ] [ φ x; φ y ]
    Ordering.t.
Proof.
Admitted.
Global Opaque run_three_way_compare.

Instance run_saturating_add (integer_kind : IntegerKind.t) (x y : Integer.t integer_kind) :
  Run.Trait
    intrinsics.saturating_add [] [ Φ (Integer.t integer_kind) ] [ φ x; φ y ]
    (Integer.t integer_kind).
Proof.
Admitted.
Global Opaque run_saturating_add.

Instance run_saturating_sub (integer_kind : IntegerKind.t) (x y : Integer.t integer_kind) :
  Run.Trait
    intrinsics.saturating_sub [] [ Φ (Integer.t integer_kind) ] [ φ x; φ y ]
    (Integer.t integer_kind).
Proof.
Admitted.
Global Opaque run_saturating_sub.

Instance run_sub_with_overflow
  (x y : Integer.t IntegerKind.U64) :
  Run.Trait
    intrinsics.sub_with_overflow
    []
    [ Φ (Integer.t IntegerKind.U64) ]
    [ φ x; φ y ]
    (Integer.t IntegerKind.U64 * bool).
Proof.
Admitted.
Global Opaque run_sub_with_overflow.

(* pub const unsafe fn transmute<Src, Dst>(_src: Src) -> Dst *)
Instance run_transmute (Src Dst : Set) `{Link Src} `{Link Dst} (src : Src) :
  Run.Trait
    intrinsics.transmute [] [ Φ Src; Φ Dst ] [ φ src ] Dst.
Proof.
Admitted.
Global Opaque run_transmute.

Instance run_discriminant_value (ref : '& Ordering.t) :
  Run.Trait intrinsics.discriminant_value [] [Φ Ordering.t] [φ ref]
             (Integer.t IntegerKind.I8).
Proof.
Admitted.
Global Opaque run_discriminant_value.

(* pub const unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) *)
Instance run_copy_nonoverlapping {T : Set} `{Link T}
  (src : '*const T)
  (dst : '*mut T)
  (count : usize) :
  Run.Trait
    intrinsics.copy_nonoverlapping [] [ Φ T ] [ φ src; φ dst; φ count ]
    unit.
Proof.
Admitted.
Global Opaque run_copy_nonoverlapping.

(** The compiler supplies pointer metadata. Only the slice instantiation is
    specified here. The model represents a readable slice as a list. *)
Module SliceMetadata.
  Import (hints) Slice.
  Axiom metadata_type : forall (T : Ty.t),
    Ty.associated_in_trait "core::ptr::metadata::Pointee" [] []
      (Ty.apply (Ty.path "slice") [] [T]) "Metadata" = Ty.path "usize".

  Axiom body : forall {T : Set} `{Link T} (p : '*const (list T)),
    intrinsics.ptr_metadata [] [Φ (list T); Φ usize] [φ p] =
    (let* xs := M.read (φ (Ref.cast_to Pointer.Kind.Raw p)) in
     match xs with
     | Value.Array values => M.pure (Value.Integer IntegerKind.Usize (Z.of_nat (List.length values)))
     | _ => M.impossible "expected a slice"
     end).

  Instance run_intrinsic {T : Set} `{Link T} (p : '*const (list T)) :
    Run.Trait intrinsics.ptr_metadata [] [Φ (list T); Φ usize] [φ p] usize.
  Proof.
    constructor. eapply Run.Rewrite; [apply body |].
    run_symbolic.
  Defined.
End SliceMetadata.
Export (hints) SliceMetadata.


Instance run_assume (b : bool) : Run.Trait intrinsics.assume [] [] [φ b] unit.
Proof. constructor. destruct b; run_symbolic. Defined.
