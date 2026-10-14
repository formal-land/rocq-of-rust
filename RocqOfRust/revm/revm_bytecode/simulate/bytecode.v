From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.utils.simulate.keccak256.
Require Import bytes.links.bytes.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_primitives.simulate.lib.
Require Import simulate.RocqOfRust.

Module Impl_Bytecode.
  Definition original_byte_slice (self : Bytecode.t) : list u8 :=
    self.(Bytecode.original_bytes).(alloy_primitives.bytes.links.mod.Bytes.value)
      .(bytes.Bytes.value).

  Definition is_empty (self : Bytecode.t) : bool :=
    match original_byte_slice self with
    | nil => true
    | _ => false
    end.

  Definition hash_slow (self : Bytecode.t) : aliases.B256.t :=
    if is_empty self then KECCAK_EMPTY else
    FixedBytes.from_Z
      (List.fold_left (fun value byte => 256 * value + byte)%Z
        (Keccak256.hash (List.map Integer.value (original_byte_slice self))) 0%Z).
End Impl_Bytecode.
