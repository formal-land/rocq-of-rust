Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import core.links.result.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.links.journaled_state.

Module Database.
  (** Database::Error is explicit; each mutable receiver is returned with its
      result, including on failure. *)
  Class C (Self Error : Set) : Set := {
    basic : Self -> Address.t -> Result.t (option AccountInfo.t) Error * Self;
    code_by_hash : Self -> aliases.B256.t -> Result.t Bytecode.t Error * Self;
    storage : Self -> Address.t -> aliases.U256.t -> Result.t aliases.U256.t Error * Self;
    block_hash : Self -> u64 -> Result.t aliases.B256.t Error * Self;
  }.
End Database.
