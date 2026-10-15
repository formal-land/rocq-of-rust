Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.journaled_state.simulate.account.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.simulate.add.
Require Import ruint.links.lib.

(** post_execution.rs with context projections supplied explicitly and mutable
    journal state passed in and out, as in pre_execution. The in-memory account
    loader cannot fail. Inputs satisfy Rust scalar and host validity. The amount
    helpers also serve the fixture accounting adapter; this is not a native
    ContextTr/JournalTr correspondence proof. *)
Module post_execution.
  Definition eip7623_check_gas_floor (gas : Gas.t)
      (init_and_floor_gas : InitialAndFloorGas.t) : Gas.t :=
    if Impl_Gas.spent_sub_refunded gas <i init_and_floor_gas.(InitialAndFloorGas.floor_gas)
    then Impl_Gas.set_refund
      (Impl_Gas.set_spent gas init_and_floor_gas.(InitialAndFloorGas.floor_gas)) 0
    else gas.

  Definition refund (spec : SpecId.t) (gas : Gas.t) (eip7702_refund : i64) : Gas.t :=
    Impl_Gas.set_final_refund (Impl_Gas.record_refund gas eip7702_refund)
      (Impl_SpecId.is_enabled_in spec SpecId.LONDON).

  Definition caller_reimbursement {Tx : Set} `{Transaction.Fees.C Tx}
      (tx : Tx) (basefee : u64) (gas : Gas.t) (additional_refund : aliases.U256.t)
      : aliases.U256.t :=
    let effective_gas_price := Transaction.Fees.effective_gas_price tx
      {| Integer.value := basefee.(Integer.value) |} in
    let remaining := Impl_Gas.remaining gas +i
      ({| Integer.value := (Impl_Gas.refunded gas).(Integer.value) mod 2 ^ 64 |} : u64) in
    let reimbursement := effective_gas_price *is
      ({| Integer.value := remaining.(Integer.value) |} : u128) in
    Impl_Uint.wrapping_add {| Uint.value := reimbursement.(Integer.value) |} additional_refund.

  Definition reimburse_caller {Tx : Set} `{Transaction.Fees.C Tx}
      (tx : Tx) (basefee : u64) (caller : Address.t) (gas : Gas.t)
      (additional_refund : aliases.U256.t) (state : StatefulHost.t) : StatefulHost.t :=
    let amount := caller_reimbursement tx basefee gas additional_refund in
    let state := StatefulHost.warm_account state caller.(Address.value) in
    let state := StatefulHost.with_accounts state
      (StatefulHost.update_account caller.(Address.value) (fun account => account)
        state.(StatefulHost.accounts)) in
    snd (JournaledAccount.incr_balance caller amount state).

  Definition beneficiary_reward {Tx : Set} `{Transaction.Fees.C Tx}
      (tx : Tx) (basefee : u64) (spec : SpecId.t) (gas : Gas.t) : aliases.U256.t :=
    let basefee : u128 := {| Integer.value := basefee.(Integer.value) |} in
    let effective_gas_price := Transaction.Fees.effective_gas_price tx basefee in
    let coinbase_gas_price := if Impl_SpecId.is_enabled_in spec SpecId.LONDON
      then effective_gas_price -is basefee else effective_gas_price in
    let reward := coinbase_gas_price *i
      ({| Integer.value := (Impl_Gas.used gas).(Integer.value) |} : u128) in
    {| Uint.value := reward.(Integer.value) |}.

  Definition reward_beneficiary {Tx : Set} `{Transaction.Fees.C Tx}
      (tx : Tx) (basefee : u64) (beneficiary : Address.t) (spec : SpecId.t)
      (gas : Gas.t) (state : StatefulHost.t) : StatefulHost.t :=
    let amount := beneficiary_reward tx basefee spec gas in
    let state := StatefulHost.warm_account state beneficiary.(Address.value) in
    let state := StatefulHost.with_accounts state
      (StatefulHost.update_account beneficiary.(Address.value) (fun account => account)
        state.(StatefulHost.accounts)) in
    snd (JournaledAccount.incr_balance beneficiary amount state).
End post_execution.
