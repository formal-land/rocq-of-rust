Require Import links.RocqOfRust.
Require Import core.ops.links.arith.
Require Import ruint.links.lib.
Require Import ruint.macros.

Module Impl_Div_for_Uint_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : usize) :
    Div.Run (Self BITS LIMBS) (Uint.t BITS LIMBS) (Uint.t BITS LIMBS).
  Admitted.
End Impl_Div_for_Uint_Uint.
Export (hints) Impl_Div_for_Uint_Uint.

Module Impl_Rem_for_Uint_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : usize) :
    Rem.Run (Self BITS LIMBS) (Uint.t BITS LIMBS) (Uint.t BITS LIMBS).
  Admitted.
End Impl_Rem_for_Uint_Uint.
Export (hints) Impl_Rem_for_Uint_Uint.
