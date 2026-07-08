Require Import links.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.option.
Require Import core.num.mod.
Require Import core.num.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.gas.calc.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.

(* pub fn sstore_refund(spec_id: SpecId, vals: &SStoreResult) -> i64 *)
Instance run_sstore_refund
    (spec_id : SpecId.t)
    (vals : '& SStoreResult.t) :
  Run.Trait
    gas.calc.sstore_refund [] [] [ φ spec_id; φ vals ]
    i64.
Proof.
  constructor.
Admitted.
Global Opaque run_sstore_refund.

(* pub const fn create2_cost(len: usize) -> Option<u64> *)
Instance run_create2_cost (len : usize) :
  Run.Trait
    gas.calc.create2_cost [] [] [ φ len ]
    (option u64).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_create2_cost.

(* pub const fn log2floor(value: U256) -> u64 *)
Instance run_log2floor (value : aliases.U256.t) :
  Run.Trait
    gas.calc.log2floor [] [] [ φ value ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_log2floor.

(* pub fn exp_cost(spec_id: SpecId, power: U256) -> Option<u64> *)
Instance run_exp_cost (spec_id : SpecId.t) (power : aliases.U256.t) :
  Run.Trait
    gas.calc.exp_cost [] [] [ φ spec_id; φ power ]
    (option u64).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_exp_cost.

(* pub const fn copy_cost_verylow(len: usize) -> Option<u64> *)
Instance run_copy_cost_verylow (len : usize) :
  Run.Trait
    gas.calc.copy_cost_verylow [] [] [ φ len ]
    (option u64).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_copy_cost_verylow.

(* pub const fn extcodecopy_cost(
    spec_id: SpecId,
    len: usize,
    load: Eip7702CodeLoad<()>,
) -> Option<u64> *)
Instance run_extcodecopy_cost
    (spec_id : SpecId.t)
    (len : usize)
    (load : Eip7702CodeLoad.t unit) :
  Run.Trait
    gas.calc.extcodecopy_cost [] [] [ φ spec_id; φ len; φ load ]
    (option u64).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_extcodecopy_cost.

(* pub const fn copy_cost(base_cost: u64, len: usize) -> Option<u64> *)
Instance run_copy_cost (base_cost : u64) (len : usize) :
  Run.Trait
    gas.calc.copy_cost [] [] [ φ base_cost; φ len ]
    (option u64).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_copy_cost.

(* pub const fn log_cost(n: u8, len: u64) -> Option<u64> *)
Instance run_log_cost (n : u8) (len : u64) :
  Run.Trait
    gas.calc.log_cost [] [] [ φ n; φ len ]
    (option u64).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_log_cost.

(* pub const fn keccak256_cost(len: usize) -> Option<u64> *)
Instance run_keccak256_cost (len : usize) :
  Run.Trait
    gas.calc.keccak256_cost [] [] [ φ len ]
    (option u64).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_keccak256_cost.

(* pub const fn cost_per_word(len: usize, multiple: u64) -> Option<u64> *)
Instance run_cost_per_word (len : usize) (multiple : u64) :
  Run.Trait
    gas.calc.cost_per_word [] [] [ φ len; φ multiple ]
    (option u64).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_cost_per_word.

(* pub const fn initcode_cost(len: usize) -> u64 *)
Instance run_initcode_cost (len : usize) :
  Run.Trait
    gas.calc.initcode_cost [] [] [ φ len ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_initcode_cost.

(* pub const fn sload_cost(spec_id: SpecId, is_cold: bool) -> u64 *)
Instance run_sload_cost (spec_id : SpecId.t) (is_cold : bool) :
  Run.Trait
    gas.calc.sload_cost [] [] [ φ spec_id; φ is_cold ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_sload_cost.

(* pub const fn static_sstore_cost(spec_id: SpecId) -> u64 *)
Instance run_static_sstore_cost (spec_id : SpecId.t) :
  Run.Trait
    gas.calc.static_sstore_cost [] [] [ φ spec_id ]
    u64.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_static_sstore_cost.

(* pub const fn dyn_sstore_cost(spec_id: SpecId, vals: &SStoreResult, is_cold: bool) -> u64 *)
Instance run_dyn_sstore_cost
    (spec_id : SpecId.t)
    (vals : '& SStoreResult.t)
    (is_cold : bool) :
  Run.Trait
    gas.calc.dyn_sstore_cost [] [] [ φ spec_id; φ vals; φ is_cold ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_dyn_sstore_cost.

(* pub fn sstore_cost(spec_id: SpecId, vals: &SStoreResult, is_cold: bool) -> u64 *)
Instance run_sstore_cost
    (spec_id : SpecId.t)
    (vals : '& SStoreResult.t)
    (is_cold : bool) :
  Run.Trait
    gas.calc.sstore_cost [] [] [ φ spec_id; φ vals; φ is_cold ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_sstore_cost.

(* pub const fn istanbul_sstore_cost<const SLOAD_GAS: u64, const SSTORE_RESET_GAS: u64>(
    vals: &SStoreResult,
) -> u64 *)
Instance run_istanbul_sstore_cost (vals : '& SStoreResult.t) :
  Run.Trait
    gas.calc.istanbul_sstore_cost [] [] [ φ vals ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_istanbul_sstore_cost.

(* pub const fn frontier_sstore_cost(vals: &SStoreResult) -> u64 *)
Instance run_frontier_sstore_cost (vals : '& SStoreResult.t) :
  Run.Trait
    gas.calc.frontier_sstore_cost [] [] [ φ vals ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_frontier_sstore_cost.

(* pub const fn static_selfdestruct_cost(spec_id: SpecId) -> u64 *)
Instance run_static_selfdestruct_cost (spec_id : SpecId.t) :
  Run.Trait
    gas.calc.static_selfdestruct_cost [] [] [ φ spec_id ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_static_selfdestruct_cost.

(* pub const fn dyn_selfdestruct_cost(spec_id: SpecId, res: &StateLoad<SelfDestructResult>) -> u64 *)
Instance run_dyn_selfdestruct_cost
    (spec_id : SpecId.t)
    (res : '& (StateLoad.t SelfDestructResult.t)) :
  Run.Trait
    gas.calc.dyn_selfdestruct_cost [] [] [ φ spec_id; φ res ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_dyn_selfdestruct_cost.

(* pub const fn selfdestruct_cold_beneficiary_cost(spec_id: SpecId) -> u64 *)
Instance run_selfdestruct_cold_beneficiary_cost (spec_id : SpecId.t) :
  Run.Trait
    gas.calc.selfdestruct_cold_beneficiary_cost [] [] [ φ spec_id ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_selfdestruct_cold_beneficiary_cost.

(* pub const fn selfdestruct_cost(spec_id: SpecId, res: StateLoad<SelfDestructResult>) -> u64 *)
Instance run_selfdestruct_cost
    (spec_id : SpecId.t)
    (res : StateLoad.t SelfDestructResult.t) :
  Run.Trait
    gas.calc.selfdestruct_cost [] [] [ φ spec_id; φ res ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_selfdestruct_cost.

(* pub fn calc_call_static_gas(spec_id: SpecId, has_transfer: bool) -> u64 *)
Instance run_calc_call_static_gas
    (spec_id : SpecId.t)
    (has_transfer : bool) :
  Run.Trait
    gas.calc.calc_call_static_gas [] [] [ φ spec_id; φ has_transfer ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_calc_call_static_gas.

(* pub const fn warm_cold_cost(is_cold: bool) -> u64 *)
Instance run_warm_cold_cost (is_cold : bool) :
  Run.Trait
    gas.calc.warm_cold_cost [] [] [ φ is_cold ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_warm_cold_cost.

(* pub const fn warm_cold_cost_with_delegation(load: Eip7702CodeLoad<()>) -> u64 *)
Instance run_warm_cold_cost_with_delegation (load : Eip7702CodeLoad.t unit) :
  Run.Trait
    gas.calc.warm_cold_cost_with_delegation [] [] [ φ load ]
    u64.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_warm_cold_cost_with_delegation.

(* pub const fn memory_gas(num_words: usize) -> u64 *)
Instance run_memory_gas (num_words : usize) :
  Run.Trait
    gas.calc.memory_gas [] [] [ φ num_words ]
    u64.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_memory_gas.
