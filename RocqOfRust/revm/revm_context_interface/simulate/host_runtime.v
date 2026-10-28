Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import core.links.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import ruint.links.lib.

(** Executable Host methods consumed by instructions. Unlike the older linked
    interface, execution needs no embedding of the host into translated values.
    The adapter below retains that interface for the existing proofs. *)
Module HostRuntime.
  Class C (Self : Set) : Set := {
    load_account_info_skip_cold_load : Self -> Address.t -> bool -> bool ->
      Result.t AccountInfoLoad.t LoadError.t * Self;
    load_account_code : Self -> Address.t -> option (StateLoad.t Bytes.t) * Self;
    block_hash : Self -> u64 -> option aliases.B256.t * Self;
    max_initcode_size : Self -> usize * Self;
    beneficiary : Self -> Address.t * Self;
    block_number : Self -> aliases.U256.t * Self;
    timestamp : Self -> aliases.U256.t * Self;
    gas_limit : Self -> aliases.U256.t * Self;
    chain_id : Self -> aliases.U256.t * Self;
    basefee : Self -> aliases.U256.t * Self;
    blob_gasprice : Self -> aliases.U256.t * Self;
    effective_gas_price : Self -> aliases.U256.t * Self;
    caller : Self -> Address.t * Self;
    blob_hash : Self -> usize -> option aliases.U256.t * Self;
    difficulty : Self -> aliases.U256.t * Self;
    prevrandao : Self -> option aliases.U256.t * Self;
    balance : Self -> Address.t -> option (StateLoad.t aliases.U256.t) * Self;
    sload : Self -> Address.t -> aliases.U256.t -> option (StateLoad.t aliases.U256.t) * Self;
    sload_skip_cold_load : Self -> Address.t -> aliases.U256.t -> bool ->
      Result.t (StateLoad.t aliases.U256.t) LoadError.t * Self;
    sstore : Self -> Address.t -> aliases.U256.t -> aliases.U256.t ->
      option (StateLoad.t SStoreResult.t) * Self;
    sstore_skip_cold_load : Self -> Address.t -> aliases.U256.t -> aliases.U256.t -> bool ->
      Result.t (StateLoad.t SStoreResult.t) LoadError.t * Self;
    tload : Self -> Address.t -> aliases.U256.t -> aliases.U256.t * Self;
    tstore : Self -> Address.t -> aliases.U256.t -> aliases.U256.t -> Self;
    log : Self -> Log.t LogData.t -> Self;
    selfdestruct : Self -> Address.t -> Address.t -> bool ->
      Result.t (StateLoad.t SelfDestructResult.t) LoadError.t * Self;
  }.

  Definition of_linked {Self : Set} `{Link Self}
      {types : Host.Types.t} `{Host.Types.AreLinks types} (host : Host.C Self types) : C Self := {|
    load_account_info_skip_cold_load := host.(Host.load_account_info_skip_cold_load);
    load_account_code := host.(Host.load_account_code);
    block_hash := host.(Host.block_hash);
    max_initcode_size := host.(Host.max_initcode_size);
    beneficiary := host.(Host.beneficiary);
    block_number := host.(Host.block_number);
    timestamp := host.(Host.timestamp);
    gas_limit := host.(Host.gas_limit);
    chain_id := host.(Host.chain_id);
    basefee := host.(Host.basefee);
    blob_gasprice := host.(Host.blob_gasprice);
    effective_gas_price := host.(Host.effective_gas_price);
    caller := host.(Host.caller);
    blob_hash := host.(Host.blob_hash);
    difficulty := host.(Host.difficulty);
    prevrandao := host.(Host.prevrandao);
    balance := host.(Host.balance);
    sload := host.(Host.sload);
    sload_skip_cold_load := host.(Host.sload_skip_cold_load);
    sstore := host.(Host.sstore);
    sstore_skip_cold_load := host.(Host.sstore_skip_cold_load);
    tload := host.(Host.tload);
    tstore := host.(Host.tstore);
    log := host.(Host.log);
    selfdestruct := host.(Host.selfdestruct);
  |}.
End HostRuntime.
