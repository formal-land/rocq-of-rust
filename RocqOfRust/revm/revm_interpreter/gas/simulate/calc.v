Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.num.simulate.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

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
Proof.
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
Proof.
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
Proof.
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
Proof.
Admitted.

Definition cost_per_word_impl (len : usize) (multiple : u64) : option u64 :=
  let num_words :=
    lib.BinOp.Wrap.div
      (Impl_usize.saturating_add len
        (@lib.Integer_of_Z IntegerKind.Usize 31))
      (@lib.Integer_of_Z IntegerKind.Usize 32) in
  BinOp.Checked.mul multiple
    {| Integer.value := num_words.(Integer.value) |}.

Definition copy_cost_impl (base_cost : u64) (len : usize) : option u64 :=
  match cost_per_word_impl len COPY with
  | Some word_cost => BinOp.Checked.add base_cost word_cost
  | None => None
  end.

Definition copy_cost_verylow (len : usize) : option u64 :=
  copy_cost_impl VERYLOW len.

Lemma copy_cost_verylow_eq (stack : Stack.t) (len : usize) :
  {{
    SimulateM.eval_f
      (run_copy_cost_verylow len)
      stack 🌲
    (Output.Success (copy_cost_verylow len), stack)
  }}.
Proof.
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
Proof.
Admitted.

Definition copy_cost (base_cost : u64) (len : usize) : option u64 :=
  copy_cost_impl base_cost len.

Lemma copy_cost_eq (stack : Stack.t) (base_cost : u64) (len : usize) :
  {{
    SimulateM.eval_f
      (run_copy_cost base_cost len)
      stack 🌲
    (Output.Success (copy_cost base_cost len), stack)
  }}.
Proof.
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
Proof.
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
Proof.
Admitted.

Definition cost_per_word (len : usize) (multiple : u64) : option u64 :=
  cost_per_word_impl len multiple.

Lemma cost_per_word_eq (stack : Stack.t) (len : usize) (multiple : u64) :
  {{
    SimulateM.eval_f
      (run_cost_per_word len multiple)
      stack 🌲
    (Output.Success (cost_per_word len multiple), stack)
  }}.
Proof.
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
Proof.
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
Proof.
Admitted.

Definition static_sstore_cost (spec_id : SpecId.t) : u64 :=
  if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
    WARM_STORAGE_READ_COST
  else if Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL then
    ISTANBUL_SLOAD_GAS
  else
    SSTORE_RESET.

Lemma static_sstore_cost_eq (stack : Stack.t) (spec_id : SpecId.t) :
  {{
    SimulateM.eval_f
      (run_static_sstore_cost spec_id)
      stack 🌲
    (Output.Success (static_sstore_cost spec_id), stack)
  }}.
Proof.
  with_strategy transparent [run_static_sstore_cost] unfold run_static_sstore_cost.
  cbn.
  s. {
    apply Impl_SpecId.is_enabled_in_eq.
  }
  destruct (Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN) eqn:H_berlin; cbn.
  - eapply Run.Call. {
      apply Run.Pure.
    }
    cbn.
    eapply Run.Call. {
      apply WARM_STORAGE_READ_COST_eq.
    }
    cbn.
    unfold static_sstore_cost.
    rewrite H_berlin.
    cbn.
    apply Run.Pure.
  - s. {
      apply Impl_SpecId.is_enabled_in_eq.
    }
    destruct (Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL) eqn:H_istanbul; cbn.
    + eapply Run.Call. {
        apply Run.Pure.
      }
      cbn.
      eapply Run.Call. {
        apply ISTANBUL_SLOAD_GAS_eq.
      }
      cbn.
      unfold static_sstore_cost.
      rewrite H_berlin, H_istanbul.
      cbn.
      apply Run.Pure.
    + eapply Run.Call. {
        apply Run.Pure.
      }
      cbn.
      eapply Run.Call. {
        apply SSTORE_RESET_eq.
      }
      cbn.
      unfold static_sstore_cost.
      rewrite H_berlin, H_istanbul.
      cbn.
      apply Run.Pure.
Qed.

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
Proof.
Admitted.

Definition dyn_sstore_cost
    (spec_id : SpecId.t)
    (vals : '& SStoreResult.t)
    (is_cold : bool) :
    u64 :=
  BinOp.Wrap.sub
    (sstore_cost spec_id vals is_cold)
    (static_sstore_cost spec_id).

Lemma dyn_sstore_cost_eq (stack : Stack.t)
    (spec_id : SpecId.t) (vals : '& SStoreResult.t) (is_cold : bool) :
  {{
    SimulateM.eval_f
      (run_dyn_sstore_cost spec_id vals is_cold)
      stack 🌲
    (Output.Success (dyn_sstore_cost spec_id vals is_cold), stack)
  }}.
Proof.
  with_strategy transparent [run_dyn_sstore_cost] unfold run_dyn_sstore_cost.
  cbn.
  eapply Run.Call. {
    apply sstore_cost_eq.
  }
  cbn.
  eapply Run.Call. {
    apply static_sstore_cost_eq.
  }
  cbn.
  eapply Run.Call. {
    apply Run.Pure.
  }
  cbn.
  unfold dyn_sstore_cost.
  cbn.
  apply Run.Pure.
Qed.

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
Proof.
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
Proof.
Admitted.

Definition static_selfdestruct_cost (spec_id : SpecId.t) : u64 :=
  {| Integer.value := 0 |}.

Lemma static_selfdestruct_cost_eq (stack : Stack.t) (spec_id : SpecId.t) :
  {{
    SimulateM.eval_f
      (run_static_selfdestruct_cost spec_id)
      stack 🌲
    (Output.Success (static_selfdestruct_cost spec_id), stack)
  }}.
Proof.
Admitted.

Definition dyn_selfdestruct_cost
    (spec_id : SpecId.t)
    (res : '& (StateLoad.t SelfDestructResult.t)) :
    u64 :=
  {| Integer.value := 0 |}.

Lemma dyn_selfdestruct_cost_eq (stack : Stack.t)
    (spec_id : SpecId.t) (res : '& (StateLoad.t SelfDestructResult.t)) :
  {{
    SimulateM.eval_f
      (run_dyn_selfdestruct_cost spec_id res)
      stack 🌲
    (Output.Success (dyn_selfdestruct_cost spec_id res), stack)
  }}.
Proof.
Admitted.

Definition selfdestruct_cold_beneficiary_cost (spec_id : SpecId.t) : u64 :=
  {| Integer.value := 0 |}.

Lemma selfdestruct_cold_beneficiary_cost_eq (stack : Stack.t) (spec_id : SpecId.t) :
  {{
    SimulateM.eval_f
      (run_selfdestruct_cold_beneficiary_cost spec_id)
      stack 🌲
    (Output.Success (selfdestruct_cold_beneficiary_cost spec_id), stack)
  }}.
Proof.
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
Proof.
Admitted.

Definition calc_call_static_gas
    (spec_id : SpecId.t)
    (has_transfer : bool) :
    u64 :=
  {| Integer.value := 0 |}.

Lemma calc_call_static_gas_eq (stack : Stack.t)
    (spec_id : SpecId.t) (has_transfer : bool) :
  {{
    SimulateM.eval_f
      (run_calc_call_static_gas spec_id has_transfer)
      stack 🌲
    (Output.Success (calc_call_static_gas spec_id has_transfer), stack)
  }}.
Proof.
Admitted.

Definition call_cost
    (spec_id : SpecId.t)
    (transfers_value : bool)
    (_account_load : AccountLoad.t) :
    u64 :=
  calc_call_static_gas spec_id transfers_value.

Definition warm_cold_cost (is_cold : bool) : u64 :=
  {| Integer.value := 0 |}.

Lemma warm_cold_cost_eq (stack : Stack.t) (is_cold : bool) :
  {{
    SimulateM.eval_f
      (run_warm_cold_cost is_cold)
      stack 🌲
    (Output.Success (warm_cold_cost is_cold), stack)
  }}.
Proof.
Admitted.

Definition warm_cold_cost_with_delegation (load : StateLoad.t AccountLoad.t) : u64 :=
  {| Integer.value := 0 |}.

Lemma warm_cold_cost_with_delegation_eq (stack : Stack.t)
    (load : StateLoad.t AccountLoad.t) :
  {{
    SimulateM.eval_f
      (run_warm_cold_cost_with_delegation load)
      stack 🌲
    (Output.Success (warm_cold_cost_with_delegation load), stack)
  }}.
Proof.
Admitted.

Definition memory_gas (num_words : usize) : u64 :=
  let num_words : u64 :=
    {| Integer.value := num_words.(Integer.value) |} in
  Impl_u64.saturating_add
    (Impl_u64.saturating_mul MEMORY num_words)
    (lib.BinOp.Wrap.div
      (Impl_u64.saturating_mul num_words num_words)
      (@lib.Integer_of_Z IntegerKind.U64 512)).

Lemma memory_gas_eq (stack : Stack.t) (num_words : usize) :
  {{
    SimulateM.eval_f
      (run_memory_gas num_words)
      stack 🌲
    (Output.Success (memory_gas num_words), stack)
  }}.
Proof.
Admitted.
