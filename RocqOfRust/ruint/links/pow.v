Require Import links.RocqOfRust.
Require Import ruint.links.lib.
Require Import ruint.pow.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* pub fn pow(self, exp: Self) -> Self *)
  Instance run_pow
    (BITS LIMBS : usize)
    (x1 x2 : Self BITS LIMBS) :
  Run.Trait
    (pow.Impl_ruint_Uint_BITS_LIMBS.pow (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
    (Self BITS LIMBS).
  Proof.
  Admitted.
  Global Opaque run_pow.

  (* pub fn wrapping_pow(mut self, mut exp: Self) -> Self *)
  Instance run_wrapping_pow
    (BITS LIMBS : usize)
    (x1 x2 : Self BITS LIMBS) :
  Run.Trait
    (pow.Impl_ruint_Uint_BITS_LIMBS.wrapping_pow (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
    (Self BITS LIMBS).
  Proof.
  Admitted.
  Global Opaque run_wrapping_pow.
End Impl_Uint.
Export (hints) Impl_Uint.
