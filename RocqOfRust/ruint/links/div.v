Require Import links.RocqOfRust.
Require Import ruint.links.lib.
Require Import ruint.div.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* pub fn wrapping_div(self, rhs: Self) -> Self *)
  Instance run_wrapping_div
    (BITS LIMBS : usize)
    (x1 x2 : Self BITS LIMBS) :
    Run.Trait
      (div.Impl_ruint_Uint_BITS_LIMBS.wrapping_div (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
      (Self BITS LIMBS).
  Proof.
  Admitted.
  Global Opaque run_wrapping_div.

  (* pub fn wrapping_rem(self, rhs: Self) -> Self *)
  Instance run_wrapping_rem
    (BITS LIMBS : usize)
    (x1 x2 : Self BITS LIMBS) :
    Run.Trait
      (div.Impl_ruint_Uint_BITS_LIMBS.wrapping_rem (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
      (Self BITS LIMBS).
  Proof.
  Admitted.
  Global Opaque run_wrapping_rem.
End Impl_Uint.
Export (hints) Impl_Uint.
