Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import core.ops.links.bit.
Require Import core.ops.simulate.bit.
Require Import ruint.links.bits.
Require Import ruint.links.lib.

Module Impl_Not_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* Bitwise NOT: flip all bits, equivalent to MAX - x *)
  Definition not {BITS LIMBS : usize} (x : Self BITS LIMBS) : Self BITS LIMBS :=
    {| Uint.value := (2 ^ BITS.(Integer.value) - 1 - x.(Uint.value)) mod (2 ^ BITS.(Integer.value)) |}.

  Global Instance I {BITS LIMBS : usize} : Not.C (Self BITS LIMBS) (Self BITS LIMBS) := {|
    Not.not := not;
  |}.

  Module Eq.
    Instance I {BITS LIMBS : usize} : Not.Eq.C (Self BITS LIMBS) (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Not_for_Uint.
Export (hints) Impl_Not_for_Uint.

Module Impl_BitAnd_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* Bitwise AND *)
  Definition bitand {BITS LIMBS : usize} (x y : Self BITS LIMBS) : Self BITS LIMBS :=
    {| Uint.value := Z.land x.(Uint.value) y.(Uint.value) |}.

  Global Instance I {BITS LIMBS : usize} : BitAnd.C (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS) := {|
    BitAnd.bitand := bitand;
  |}.

  Module Eq.
    Instance I {BITS LIMBS : usize} : BitAnd.Eq.C (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_BitAnd_for_Uint.
Export (hints) Impl_BitAnd_for_Uint.

Module Impl_BitOr_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* Bitwise OR *)
  Definition bitor {BITS LIMBS : usize} (x y : Self BITS LIMBS) : Self BITS LIMBS :=
    {| Uint.value := Z.lor x.(Uint.value) y.(Uint.value) |}.

  Global Instance I {BITS LIMBS : usize} : BitOr.C (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS) := {|
    BitOr.bitor := bitor;
  |}.

  Module Eq.
    Instance I {BITS LIMBS : usize} : BitOr.Eq.C (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_BitOr_for_Uint.
Export (hints) Impl_BitOr_for_Uint.

Module Impl_BitXor_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* Bitwise XOR *)
  Definition bitxor {BITS LIMBS : usize} (x y : Self BITS LIMBS) : Self BITS LIMBS :=
    {| Uint.value := Z.lxor x.(Uint.value) y.(Uint.value) |}.

  Global Instance I {BITS LIMBS : usize} : BitXor.C (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS) := {|
    BitXor.bitxor := bitxor;
  |}.

  Module Eq.
    Instance I {BITS LIMBS : usize} : BitXor.Eq.C (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_BitXor_for_Uint.
Export (hints) Impl_BitXor_for_Uint.

Module Impl_Shl_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* Left shift with modular wrap *)
  Definition shl {BITS LIMBS : usize} (x : Self BITS LIMBS) (n : usize) : Self BITS LIMBS :=
    {| Uint.value := (Z.shiftl x.(Uint.value) n.(Integer.value)) mod (2 ^ BITS.(Integer.value)) |}.

  Global Instance I {BITS LIMBS : usize} : Shl.C (Self BITS LIMBS) usize (Self BITS LIMBS) := {|
    Shl.shl := shl;
  |}.

  Module Eq.
    Instance I {BITS LIMBS : usize} : Shl.Eq.C (Self BITS LIMBS) usize (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Shl_for_Uint.
Export (hints) Impl_Shl_for_Uint.

Module Impl_Shr_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* Logical right shift *)
  Definition shr {BITS LIMBS : usize} (x : Self BITS LIMBS) (n : usize) : Self BITS LIMBS :=
    {| Uint.value := Z.shiftr x.(Uint.value) n.(Integer.value) |}.

  Global Instance I {BITS LIMBS : usize} : Shr.C (Self BITS LIMBS) usize (Self BITS LIMBS) := {|
    Shr.shr := shr;
  |}.

  Module Eq.
    Instance I {BITS LIMBS : usize} : Shr.Eq.C (Self BITS LIMBS) usize (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Shr_for_Uint.
Export (hints) Impl_Shr_for_Uint.

Module Impl_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* Get byte at index (big-endian, so index 0 is the most significant byte) *)
  Definition byte {BITS LIMBS : usize} (self : Self BITS LIMBS) (index : usize) : u8 :=
    let num_bytes := Z.div BITS.(Integer.value) 8 in
    if index.(Integer.value) >=? num_bytes then
      {| Integer.value := 0 |}
    else
      let shift_amount := Z.mul (num_bytes - 1 - index.(Integer.value)) 8 in
      {| Integer.value := Z.land (Z.shiftr self.(Uint.value) shift_amount) 255 |}.

  Lemma byte_eq (stack : Stack.t)
      {BITS LIMBS : usize} (ref_self : '& (Self BITS LIMBS)) (index : usize)
      (self : Self BITS LIMBS) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (ruint.links.bits.Impl_Uint.run_byte BITS LIMBS ref_self index)
        stack 🌲
      (
        Output.Success (byte self index),
        stack
      )
    }}.
  Admitted.

  (* Arithmetic (sign-extending) right shift *)
  Definition arithmetic_shr {BITS LIMBS : usize} (x : Self BITS LIMBS) (n : usize) : Self BITS LIMBS :=
    let sign_bit := 2 ^ (BITS.(Integer.value) - 1) in
    let is_negative := x.(Uint.value) >=? sign_bit in
    if is_negative then
      (* For negative values in two's complement, fill with 1s *)
      let shifted := Z.shiftr x.(Uint.value) n.(Integer.value) in
      let mask := (2 ^ BITS.(Integer.value) - 1) - (2 ^ (BITS.(Integer.value) - n.(Integer.value)) - 1) in
      {| Uint.value := Z.lor shifted mask |}
    else
      (* For non-negative values, same as logical shift *)
      {| Uint.value := Z.shiftr x.(Uint.value) n.(Integer.value) |}.

  Lemma arithmetic_shr_eq (stack : Stack.t)
      {BITS LIMBS : usize} (x : Self BITS LIMBS) (n : usize) :
    {{
      SimulateM.eval_f
        (ruint.links.bits.Impl_Uint.run_arithmetic_shr BITS LIMBS x n)
        stack 🌲
      (
        Output.Success (arithmetic_shr x n),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.
