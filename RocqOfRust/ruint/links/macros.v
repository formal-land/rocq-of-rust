Require Import links.RocqOfRust.
Require Import core.ops.links.arith.
Require Import ruint.links.lib.
Require Import ruint.macros.

(* impl<const BITS: usize, const LIMBS: usize> Mul<Uint<BITS, LIMBS>> for Uint<BITS, LIMBS> *)
Module Impl_Mul_for_Uint_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : usize) :
    Mul.Run (Self BITS LIMBS) (Uint.t BITS LIMBS) (Uint.t BITS LIMBS).
  Proof.
  Admitted.
End Impl_Mul_for_Uint_Uint.
Export (hints) Impl_Mul_for_Uint_Uint.

Module Impl_Div_for_Uint_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : usize) :
    Div.Run (Self BITS LIMBS) (Uint.t BITS LIMBS) (Uint.t BITS LIMBS).
  Proof.
  Admitted.
End Impl_Div_for_Uint_Uint.
Export (hints) Impl_Div_for_Uint_Uint.

Module Impl_Rem_for_Uint_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : usize) :
    Rem.Run (Self BITS LIMBS) (Uint.t BITS LIMBS) (Uint.t BITS LIMBS).
  Proof.
  Admitted.
End Impl_Rem_for_Uint_Uint.
Export (hints) Impl_Rem_for_Uint_Uint.
