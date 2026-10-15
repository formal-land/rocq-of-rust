From Stdlib Require Import List ZArith.

Require Import revm.revm_handler.simulate.post_execution.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_context_interface.journaled_state.simulate.account.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_handler.tests.transaction_accounting.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

#[local] Existing Instance TransactionAccounting.fee_fields.

Import ListNotations.
Open Scope Z_scope.

Module PostExecutionTest.
  Definition tx (price : Z) := transaction_accounting.Test.tx 1000 price 0 [].

  Definition gas (remaining refunded : Z) : Gas.t :=
    (Impl_Gas.new 1000) <| Gas.remaining := {| Integer.value := remaining |} |>
      <| Gas.refunded := {| Integer.value := refunded |} |>.

  Definition floor (value : Z) : InitialAndFloorGas.t := {|
    InitialAndFloorGas.initial_gas := 0;
    InitialAndFloorGas.floor_gas := {| Integer.value := value |};
  |}.

  Definition gas_observation (value : Gas.t) :=
    (value.(Gas.remaining).(Integer.value), value.(Gas.refunded).(Integer.value)).

  Lemma london_refund_includes_authorization_before_cap :
    gas_observation (post_execution.refund SpecId.LONDON (gas 400 100) 50) = (400, 120).
  Proof. vm_compute. reflexivity. Qed.

  Lemma berlin_uses_half_spent_refund_cap :
    gas_observation (post_execution.refund SpecId.BERLIN (gas 400 280) 50) = (400, 300).
  Proof. vm_compute. reflexivity. Qed.

  Lemma negative_refund_cast_is_capped_as_unsigned :
    gas_observation (post_execution.refund SpecId.LONDON (gas 400 (-1)) 0) = (400, 120).
  Proof. vm_compute. reflexivity. Qed.

  Lemma floor_runs_after_refund_cap :
    gas_observation (post_execution.eip7623_check_gas_floor
      (post_execution.refund SpecId.PRAGUE (gas 400 300) 0) (floor 500)) = (500, 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma equal_floor_preserves_refund :
    gas_observation (post_execution.eip7623_check_gas_floor
      (post_execution.refund SpecId.PRAGUE (gas 400 300) 0) (floor 480)) = (400, 120).
  Proof. vm_compute. reflexivity. Qed.

  Lemma reimbursement_includes_remaining_refund_and_additional :
    (post_execution.caller_reimbursement (tx 10) 4 (gas 400 120)
      {| Uint.value := 7 |}).(Uint.value) = 5207.
  Proof. vm_compute. reflexivity. Qed.

  Lemma reimbursement_product_saturates_before_widening :
    (post_execution.caller_reimbursement (tx (2 ^ 128 - 1)) 0 (gas 2 0)
      {| Uint.value := 0 |}).(Uint.value) = 2 ^ 128 - 1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma additional_refund_wraps_at_u256 :
    (post_execution.caller_reimbursement (tx 1) 0 (gas 1 0)
      {| Uint.value := 2 ^ 256 - 1 |}).(Uint.value) = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma reimbursement_remaining_addition_wraps_at_u64 :
    (post_execution.caller_reimbursement (tx 1) 0
      ((Impl_Gas.new {| Integer.value := 2 ^ 64 - 1 |})
        <| Gas.refunded := 1 |>) {| Uint.value := 0 |}).(Uint.value) = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma london_reward_excludes_base_fee_and_refunded_gas :
    (post_execution.beneficiary_reward (tx 10) 4 SpecId.LONDON
      (gas 400 120)).(Uint.value) = 2880.
  Proof. vm_compute. reflexivity. Qed.

  Lemma berlin_reward_keeps_full_price :
    (post_execution.beneficiary_reward (tx 10) 4 SpecId.BERLIN
      (gas 400 120)).(Uint.value) = 4800.
  Proof. vm_compute. reflexivity. Qed.

  Lemma beneficiary_price_subtraction_saturates :
    (post_execution.beneficiary_reward (tx 3) 4 SpecId.LONDON
      (gas 400 0)).(Uint.value) = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma beneficiary_product_wraps_at_u128 :
    (post_execution.beneficiary_reward (tx (2 ^ 128 - 1)) 0 SpecId.BERLIN
      (gas 998 0)).(Uint.value) = 2 ^ 128 - 2.
  Proof. vm_compute. reflexivity. Qed.

  Definition authority := StatefulHost.rust_address 42.

  Definition account (balance : Z) := (StatefulHost.empty_account 42)
    <| StatefulHost.Account.balance := balance |>
    <| StatefulHost.Account.nonce := 7 |>
    <| StatefulHost.Account.code := [96; 1] |>
    <| StatefulHost.Account.code_hash := 99 |>
    <| StatefulHost.Account.storage := [(3, 5)] |>
    <| StatefulHost.Account.transient_storage := [(4, 6)] |>.

  Definition host (balance : Z) := StatefulHost.make
    (add11_input <| StatefulHost.Input.state := [account balance] |>).

  Definition balance (state : StatefulHost.t) :=
    option_map StatefulHost.Account.balance
      (StatefulHost.find_account 42 state.(StatefulHost.accounts)).

  Lemma increment_exact_max_preserves_account_fields :
    let '(success, state) := JournaledAccount.incr_balance authority
      {| Uint.value := 1 |} (host (2 ^ 256 - 2)) in
    (success, StatefulHost.find_account 42 state.(StatefulHost.accounts)) =
    (true, Some (account (2 ^ 256 - 1))).
  Proof. vm_compute. reflexivity. Qed.

  Lemma overflow_increment_touches_without_balance_change :
    let '(success, state) := JournaledAccount.incr_balance authority
      {| Uint.value := 1 |} (host (2 ^ 256 - 1)) in
    (success, balance state, state.(StatefulHost.touched_accounts),
      StatefulHost.observe_state_changes state) =
    (false, Some (2 ^ 256 - 1), [42], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_increment_touches_without_journal_entry :
    let '(success, state) := JournaledAccount.incr_balance authority
      {| Uint.value := 0 |} (host 7) in
    (success, balance state, state.(StatefulHost.touched_accounts),
      StatefulHost.observe_state_changes state) = (true, Some 7, [42], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma caller_reimbursement_updates_only_balance :
    let state := post_execution.reimburse_caller (tx 10) 4 authority
      (gas 400 120) {| Uint.value := 7 |} (host 100) in
    StatefulHost.find_account 42 state.(StatefulHost.accounts) = Some (account 5307).
  Proof. vm_compute. reflexivity. Qed.

  Lemma shared_caller_and_beneficiary_receive_sequential_increments :
    let state := post_execution.reimburse_caller (tx 10) 4 authority
      (gas 400 120) {| Uint.value := 7 |} (host 100) in
    let state := post_execution.reward_beneficiary (tx 10) 4 authority SpecId.LONDON
      (gas 400 120) state in
    (balance state, state.(StatefulHost.touched_accounts),
      StatefulHost.observe_state_changes state) =
    (Some 8187, [42], [StatefulHost.Change.Balance 42 5307;
      StatefulHost.Change.Balance 42 8187]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma reward_overflow_keeps_existing_balance :
    let state := post_execution.reward_beneficiary (tx 1) 0 authority SpecId.LONDON
      (gas 999 0) (host (2 ^ 256 - 1)) in
    (balance state, state.(StatefulHost.touched_accounts),
      StatefulHost.observe_state_changes state) =
    (Some (2 ^ 256 - 1), [42], []).
  Proof. vm_compute. reflexivity. Qed.
  Lemma zero_reward_loads_absent_beneficiary_without_balance_change :
    let state := StatefulHost.make
      (add11_input <| StatefulHost.Input.state := [] |>) in
    let state := post_execution.reward_beneficiary (tx 0) 0 authority SpecId.FRONTIER
      (gas 1000 0) state in
    (StatefulHost.find_account 42 state.(StatefulHost.accounts),
      state.(StatefulHost.touched_accounts), StatefulHost.account_is_warm state 42,
      StatefulHost.observe_state_changes state) =
    (Some (StatefulHost.empty_account 42), [42], true, []).
  Proof. vm_compute. reflexivity. Qed.

End PostExecutionTest.
