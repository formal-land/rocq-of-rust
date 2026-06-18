Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_primitives.links.hardfork.

Definition sstore_refund (spec_id : SpecId.t) (vals : '& SStoreResult.t) : i64 :=
  {| Integer.value := 0 |}.

Lemma sstore_refund_eq (stack : Stack.t)
    (spec_id : SpecId.t) (vals : '& SStoreResult.t) :
  {{
    SimulateM.eval_f
      (run_sstore_refund spec_id vals)
      stack 🌲
    (Output.Success (sstore_refund spec_id vals), stack)
  }}.
Admitted.

Definition create2_cost (len : usize) : option u64 :=
  Some {| Integer.value := 0 |}.

Lemma create2_cost_eq (stack : Stack.t) (len : usize) :
  {{
    SimulateM.eval_f
      (run_create2_cost len)
      stack 🌲
    (Output.Success (create2_cost len), stack)
  }}.
Admitted.

Definition log2floor (value : aliases.U256.t) : u64 :=
  {| Integer.value := 0 |}.

Lemma log2floor_eq (stack : Stack.t) (value : aliases.U256.t) :
  {{
    SimulateM.eval_f
      (run_log2floor value)
      stack 🌲
    (Output.Success (log2floor value), stack)
  }}.
Admitted.

Definition exp_cost (spec_id : SpecId.t) (power : aliases.U256.t) : option u64 :=
  Some {| Integer.value := 0 |}.

Lemma exp_cost_eq (stack : Stack.t)
    (spec_id : SpecId.t) (power : aliases.U256.t) :
  {{
    SimulateM.eval_f
      (run_exp_cost spec_id power)
      stack 🌲
    (Output.Success (exp_cost spec_id power), stack)
  }}.
Admitted.

Definition copy_cost_verylow (len : usize) : option u64 :=
  Some {| Integer.value := 0 |}.

Lemma copy_cost_verylow_eq (stack : Stack.t) (len : usize) :
  {{
    SimulateM.eval_f
      (run_copy_cost_verylow len)
      stack 🌲
    (Output.Success (copy_cost_verylow len), stack)
  }}.
Admitted.

Definition extcodecopy_cost
    (spec_id : SpecId.t)
    (len : usize)
    (load : Eip7702CodeLoad.t unit) :
    option u64 :=
  Some {| Integer.value := 0 |}.

Lemma extcodecopy_cost_eq (stack : Stack.t)
    (spec_id : SpecId.t) (len : usize) (load : Eip7702CodeLoad.t unit) :
  {{
    SimulateM.eval_f
      (run_extcodecopy_cost spec_id len load)
      stack 🌲
    (Output.Success (extcodecopy_cost spec_id len load), stack)
  }}.
Admitted.

Definition copy_cost (base_cost : u64) (len : usize) : option u64 :=
  Some {| Integer.value := 0 |}.

Lemma copy_cost_eq (stack : Stack.t) (base_cost : u64) (len : usize) :
  {{
    SimulateM.eval_f
      (run_copy_cost base_cost len)
      stack 🌲
    (Output.Success (copy_cost base_cost len), stack)
  }}.
Admitted.

Definition log_cost (n : u8) (len : u64) : option u64 :=
  Some {| Integer.value := 0 |}.

Lemma log_cost_eq (stack : Stack.t) (n : u8) (len : u64) :
  {{
    SimulateM.eval_f
      (run_log_cost n len)
      stack 🌲
    (Output.Success (log_cost n len), stack)
  }}.
Admitted.

Definition keccak256_cost (len : usize) : option u64 :=
  Some {| Integer.value := 0 |}.

Lemma keccak256_cost_eq (stack : Stack.t) (len : usize) :
  {{
    SimulateM.eval_f
      (run_keccak256_cost len)
      stack 🌲
    (Output.Success (keccak256_cost len), stack)
  }}.
Admitted.

Definition cost_per_word (len : usize) (multiple : u64) : option u64 :=
  Some {| Integer.value := 0 |}.

Lemma cost_per_word_eq (stack : Stack.t) (len : usize) (multiple : u64) :
  {{
    SimulateM.eval_f
      (run_cost_per_word len multiple)
      stack 🌲
    (Output.Success (cost_per_word len multiple), stack)
  }}.
Admitted.

Definition initcode_cost (len : usize) : u64 :=
  {| Integer.value := 0 |}.

Lemma initcode_cost_eq (stack : Stack.t) (len : usize) :
  {{
    SimulateM.eval_f
      (run_initcode_cost len)
      stack 🌲
    (Output.Success (initcode_cost len), stack)
  }}.
Admitted.

Definition sload_cost (spec_id : SpecId.t) (is_cold : bool) : u64 :=
  {| Integer.value := 0 |}.

Lemma sload_cost_eq (stack : Stack.t)
    (spec_id : SpecId.t) (is_cold : bool) :
  {{
    SimulateM.eval_f
      (run_sload_cost spec_id is_cold)
      stack 🌲
    (Output.Success (sload_cost spec_id is_cold), stack)
  }}.
Admitted.

Definition sstore_cost
    (spec_id : SpecId.t)
    (vals : '& SStoreResult.t)
    (is_cold : bool) :
    u64 :=
  {| Integer.value := 0 |}.

Lemma sstore_cost_eq (stack : Stack.t)
    (spec_id : SpecId.t) (vals : '& SStoreResult.t) (is_cold : bool) :
  {{
    SimulateM.eval_f
      (run_sstore_cost spec_id vals is_cold)
      stack 🌲
    (Output.Success (sstore_cost spec_id vals is_cold), stack)
  }}.
Admitted.

Definition istanbul_sstore_cost (vals : '& SStoreResult.t) : u64 :=
  {| Integer.value := 0 |}.

Lemma istanbul_sstore_cost_eq (stack : Stack.t)
    (vals : '& SStoreResult.t) :
  {{
    SimulateM.eval_f
      (run_istanbul_sstore_cost vals)
      stack 🌲
    (Output.Success (istanbul_sstore_cost vals), stack)
  }}.
Admitted.

Definition frontier_sstore_cost (vals : '& SStoreResult.t) : u64 :=
  {| Integer.value := 0 |}.

Lemma frontier_sstore_cost_eq (stack : Stack.t)
    (vals : '& SStoreResult.t) :
  {{
    SimulateM.eval_f
      (run_frontier_sstore_cost vals)
      stack 🌲
    (Output.Success (frontier_sstore_cost vals), stack)
  }}.
Admitted.

Definition selfdestruct_cost
    (spec_id : SpecId.t)
    (res : StateLoad.t SelfDestructResult.t) :
    u64 :=
  {| Integer.value := 0 |}.

Lemma selfdestruct_cost_eq (stack : Stack.t)
    (spec_id : SpecId.t) (res : StateLoad.t SelfDestructResult.t) :
  {{
    SimulateM.eval_f
      (run_selfdestruct_cost spec_id res)
      stack 🌲
    (Output.Success (selfdestruct_cost spec_id res), stack)
  }}.
Admitted.

Definition call_cost
    (spec_id : SpecId.t)
    (transfers_value : bool)
    (account_load : AccountLoad.t) :
    u64 :=
  {| Integer.value := 0 |}.

Lemma call_cost_eq (stack : Stack.t)
    (spec_id : SpecId.t) (transfers_value : bool) (account_load : AccountLoad.t) :
  {{
    SimulateM.eval_f
      (run_call_cost spec_id transfers_value account_load)
      stack 🌲
    (Output.Success (call_cost spec_id transfers_value account_load), stack)
  }}.
Admitted.

Definition warm_cold_cost (is_cold : bool) : u64 :=
  {| Integer.value := 0 |}.

Lemma warm_cold_cost_eq (stack : Stack.t) (is_cold : bool) :
  {{
    SimulateM.eval_f
      (run_warm_cold_cost is_cold)
      stack 🌲
    (Output.Success (warm_cold_cost is_cold), stack)
  }}.
Admitted.

Definition warm_cold_cost_with_delegation (load : Eip7702CodeLoad.t unit) : u64 :=
  {| Integer.value := 0 |}.

Lemma warm_cold_cost_with_delegation_eq (stack : Stack.t)
    (load : Eip7702CodeLoad.t unit) :
  {{
    SimulateM.eval_f
      (run_warm_cold_cost_with_delegation load)
      stack 🌲
    (Output.Success (warm_cold_cost_with_delegation load), stack)
  }}.
Admitted.

Definition memory_gas (num_words : usize) : u64 :=
  {| Integer.value := 0 |}.

Lemma memory_gas_eq (stack : Stack.t) (num_words : usize) :
  {{
    SimulateM.eval_f
      (run_memory_gas num_words)
      stack 🌲
    (Output.Success (memory_gas num_words), stack)
  }}.
Admitted.
