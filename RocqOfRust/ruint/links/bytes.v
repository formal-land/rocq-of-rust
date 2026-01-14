Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.links.array.
Require Import core.links.option.
Require Import ruint.bytes.
Require Import ruint.links.lib.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* pub const fn to_be_bytes<const BYTES: usize>(&self) -> [u8; BYTES] *)
  Instance run_to_be_bytes
      (BITS LIMBS BYTES : usize)
      (x : '& (Self BITS LIMBS)) :
    Run.Trait
      (bytes.Impl_ruint_Uint_BITS_LIMBS.to_be_bytes (φ BITS) (φ LIMBS)) [ φ BYTES ] [] [ φ x ]
      (array.t u8 BYTES).
  Admitted.
  Global Opaque run_to_be_bytes.

  (* pub const fn from_be_bytes<const BYTES: usize>(bytes: [u8; BYTES]) -> Self *)
  Instance run_from_be_bytes
      (BITS LIMBS BYTES : usize)
      (bytes : array.t u8 BYTES) :
    Run.Trait
      (bytes.Impl_ruint_Uint_BITS_LIMBS.from_be_bytes (φ BITS) (φ LIMBS)) [ φ BYTES ] [] [ φ bytes ]
      (Self BITS LIMBS).
  Admitted.
  Global Opaque run_from_be_bytes.

  (* pub const fn try_from_be_slice(bytes: &[u8]) -> Option<Self> *)
  Instance run_try_from_be_slice
      (BITS LIMBS : usize)
      (bytes : '& (list u8)) :
    Run.Trait
      (bytes.Impl_ruint_Uint_BITS_LIMBS.try_from_be_slice (φ BITS) (φ LIMBS)) [] [] [ φ bytes ]
      (option (Self BITS LIMBS)).
  Admitted.
  Global Opaque run_try_from_be_slice.
End Impl_Uint.
Export (hints) Impl_Uint.
