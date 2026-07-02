(* Generated *)
Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_primitives.constants.
Require Import revm.revm_primitives.lib.

(* pub const BLOCK_HASH_HISTORY: u64 *)
Instance run_BLOCK_HASH_HISTORY :
  Run.Trait
    constants.value_BLOCK_HASH_HISTORY [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_BLOCK_HASH_HISTORY.

(* pub const KECCAK_EMPTY: B256 *)
Instance run_KECCAK_EMPTY :
  Run.Trait
    constants.value_KECCAK_EMPTY [] [] []
    ('* aliases.B256.t).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_KECCAK_EMPTY.
