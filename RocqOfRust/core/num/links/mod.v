Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.intrinsics.links.mod.
Require Import core.links.array.
Require Import core.links.option.
Require Import core.num.mod.

Module Impl_u16.
  Definition Self : Set := U16.t.

  (* pub const fn to_be_bytes(self) -> [u8; 2] *)
  Instance run_to_be_bytes (self: Self) :
    Run.Trait num.Impl_u16.to_be_bytes [] [] [ φ self ] (array.t U8.t {| Integer.value := 2 |}).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_to_be_bytes.
End Impl_u16.
Export Impl_u16.

Module Impl_u64.
  Definition Self : Set := U64.t.

  (* pub const MIN: Self *)
  Instance run_min :
    Run.Trait num.Impl_u64.value_MIN [] [] [] (Ref.t Pointer.Kind.Raw Self).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_min.

  (* pub const MAX: Self *)
  Instance run_max :
    Run.Trait num.Impl_u64.value_MAX [] [] [] (Ref.t Pointer.Kind.Raw Self).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_max.

  (* pub const fn saturating_add(self, rhs: Self) -> Self *)
  Instance run_saturating_add (self rhs: Self) :
    Run.Trait num.Impl_u64.saturating_add [] [] [ φ self; φ rhs ] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_saturating_add.

  (* pub const fn saturating_sub(self, rhs: Self) -> Self *)
  Instance run_saturating_sub (self rhs: Self) :
    Run.Trait num.Impl_u64.saturating_sub [] [] [ φ self; φ rhs ] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_saturating_sub.

  Instance run_saturating_mul (self rhs: Self) :
    Run.Trait num.Impl_u64.saturating_mul [] [] [ φ self; φ rhs ] Self.
  Proof.
  Admitted.
  Global Opaque run_saturating_mul.

  (* pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) *)
  Instance run_overflowing_sub (self rhs: Self) :
    Run.Trait num.Impl_u64.overflowing_sub [] [] [ φ self; φ rhs ] (Self * bool).
  Proof.
  Admitted.
  Global Opaque run_overflowing_sub.

  (* pub const fn from_be_bytes(bytes: [u8; 8]) -> Self *)
  Instance run_from_be_bytes (bytes: array.t U8.t {| Integer.value := 8 |}) :
    Run.Trait num.Impl_u64.from_be_bytes [] [] [ φ bytes ] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_from_be_bytes.

  (* pub const fn checked_add(self, rhs: Self) -> Option<Self> *)
  Instance run_checked_add (self rhs: Self) :
    Run.Trait num.Impl_u64.checked_add [] [] [ φ self; φ rhs ] (option Self).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_checked_add.

  (* pub const fn checked_sub(self, rhs: Self) -> Option<Self> *)
  Instance run_checked_sub (self rhs: Self) :
    Run.Trait num.Impl_u64.checked_sub [] [] [ φ self; φ rhs ] (option Self).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_checked_sub.
End Impl_u64.
Export Impl_u64.

Module Impl_usize.
  Definition Self : Set := Usize.t.

  (* pub const MIN: Self *)
  Instance run_min :
    Run.Trait num.Impl_usize.value_MIN [] [] [] (Ref.t Pointer.Kind.Raw Self).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_min.

  (* pub const MAX: Self *)
  Instance run_max :
    Run.Trait num.Impl_usize.value_MAX [] [] [] (Ref.t Pointer.Kind.Raw Self).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_max.

  (* pub const fn checked_sub(self, rhs: Self) -> Option<Self> *)
  Instance run_checked_sub (self rhs: Self) :
    Run.Trait num.Impl_usize.checked_sub [] [] [ φ self; φ rhs ] (option Self).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_checked_sub.

  (* pub const fn saturating_add(self, rhs: Self) -> Self *)
  Instance run_saturating_add (self rhs: Self) :
    Run.Trait num.Impl_usize.saturating_add [] [] [ φ self; φ rhs ] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_saturating_add.

  Instance run_saturating_mul (self rhs: Self) :
    Run.Trait num.Impl_usize.saturating_mul [] [] [ φ self; φ rhs ] Self.
  Proof.
  Admitted.
  Global Opaque run_saturating_mul.

  (* pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) *)
  Instance run_overflowing_sub (self rhs: Self) :
    Run.Trait num.Impl_usize.overflowing_sub [] [] [ φ self; φ rhs ] (Self * bool).
  Proof.
  Admitted.
  Global Opaque run_overflowing_sub.
End Impl_usize.
Export Impl_usize.

Module Impl_isize.
  Import Impl_usize.

  Definition Self : Set := Isize.t.

  (* pub const MAX: Self *)
  Instance run_max :
    Run.Trait num.Impl_isize.value_MAX [] [] [] (Ref.t Pointer.Kind.Raw Self).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_max.

  (* pub const MIN: Self *)
  Instance run_min :
    Run.Trait num.Impl_isize.value_MIN [] [] [] (Ref.t Pointer.Kind.Raw Self).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_min.

  (* pub const fn saturating_add(self, rhs: Self) -> Self *)
  Instance run_saturating_add (self rhs: Self) :
    Run.Trait num.Impl_isize.saturating_add [] [] [ φ self; φ rhs ] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_saturating_add.

  Instance run_saturating_mul (self rhs: Self) :
    Run.Trait num.Impl_isize.saturating_mul [] [] [ φ self; φ rhs ] Self.
  Proof.
  Admitted.
  Global Opaque run_saturating_mul.

  (* pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) *)
  Instance run_overflowing_sub (self rhs: Self) :
    Run.Trait num.Impl_isize.overflowing_sub [] [] [ φ self; φ rhs ] (Self * bool).
  Proof.
  Admitted.
  Global Opaque run_overflowing_sub.
End Impl_isize.
Export Impl_isize.
