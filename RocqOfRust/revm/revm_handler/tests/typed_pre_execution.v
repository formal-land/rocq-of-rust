Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.links.common.
Require Import core.links.result.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context.journal.simulate.warm_addresses.
Require Import revm.revm_context.simulate.block.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.simulate.tx.
Require Import revm.revm_context.tests.journal_load.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.result.
Require Import revm.revm_context_interface.simulate.execution_result.
Require Import revm.revm_context_interface.transaction.simulate.eip7702.
Require Import revm.revm_handler.simulate.pre_execution.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.initial_tx.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_state.simulate.account_info.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.types.
Require Import ruint.links.lib.

Import ListNotations.
Module Mock := journal_load.Test.
#[local] Existing Instance Mock.db_methods.

Module Test.
  Definition caller : Address.t := {| Address.value := 42 |}.

  Definition initial : Context.t Mock.Db unit :=
    let ctx := Impl_Context.new Mock.db SpecId.OSAKA in
    let info := Impl_Default_for_AccountInfo.default <| AccountInfo.balance := Mock.word 3005 |> <| AccountInfo.nonce := 3 |> in
    let account := Impl_Default_for_Account.default <| Account.info := info |> in
    ctx <| Context.journaled_state := ctx.(Context.journaled_state) <| Journal.inner :=
      ctx.(Context.journaled_state).(Journal.inner) <| JournalInner.state := [(caller, account)] |> |> |>
      <| Context.tx := ctx.(Context.tx) <| TxEnv.caller := caller |> <| TxEnv.nonce := 3 |>
        <| TxEnv.tx_type := 2 |> <| TxEnv.gas_limit := 100 |> <| TxEnv.gas_price := 30 |>
        <| TxEnv.gas_priority_fee := Some (3 : u128) |> <| TxEnv.value := Mock.word 5 |> |>
      <| Context.block := ctx.(Context.block) <| BlockEnv.basefee := 7 |> |>.

  Definition caller_state (ctx : Context.t Mock.Db unit) :=
    option_map (fun account => (account.(Account.info).(AccountInfo.balance).(Uint.value),
      account.(Account.info).(AccountInfo.nonce).(Integer.value)))
      (EvmState.get caller ctx.(Context.journaled_state).(Journal.inner).(JournalInner.state)).

  Example caller_pays_effective_fee_and_only_call_bumps_nonce :
    List.map (fun kind =>
      match PreExecution.validate_against_state_and_deduct_caller
        (initial <| Context.tx := initial.(Context.tx) <| TxEnv.kind := kind |> |>) with
      | Some (Result.Ok _, ctx) => caller_state ctx
      | _ => None
      end) [TxKind.Call Mock.target; TxKind.Create] = [Some (2005, 4); Some (2005, 3)].
  Proof. vm_compute. reflexivity. Qed.

  Example insufficient_max_fee_is_rejected_before_deduction :
    let ctx := initial <| Context.tx := initial.(Context.tx) <| TxEnv.gas_price := 31 |> |> in
    match PreExecution.validate_against_state_and_deduct_caller ctx with
    | Some (Result.Err (EVMError.Transaction (InvalidTransaction.LackOfFundForMaxFee fee balance)), ctx) =>
      Some (fee.(Uint.value), balance.(Uint.value), caller_state ctx)
    | _ => None
    end = Some (3105, 3005, Some (3005, 3)).
  Proof. vm_compute. reflexivity. Qed.

  Example nonce_error_does_not_deduct_or_touch_caller :
    let ctx := initial <| Context.tx := initial.(Context.tx) <| TxEnv.nonce := 4 |> |> in
    match PreExecution.validate_against_state_and_deduct_caller ctx with
    | Some (Result.Err (EVMError.Transaction error), ctx) => Some
        (error, caller_state ctx, option_map Impl_Account.is_touched
          (EvmState.get caller ctx.(Context.journaled_state).(Journal.inner).(JournalInner.state)))
    | _ => None
    end = Some (InvalidTransaction.NonceTooHigh 4 3, Some (3005, 3), Some false).
  Proof. vm_compute. reflexivity. Qed.

  Definition access_list := [
    {| AccessListItem.address := caller; AccessListItem.storage_keys := [FixedBytes.from_Z 1] |};
    {| AccessListItem.address := caller; AccessListItem.storage_keys := [FixedBytes.from_Z 2; FixedBytes.from_Z 1] |}].

  Example duplicate_access_entries_union_warm_slots_but_charge_each_occurrence :
    let tx := initial.(Context.tx) <| TxEnv.access_list := access_list |> in
    let ctx := PreExecution.load_accounts (initial <| Context.tx := tx |>) [] in
    let warm := ctx.(Context.journaled_state).(Journal.inner).(JournalInner.warm_addresses) in
    (Impl_WarmAddresses.is_storage_warm warm caller (Mock.word 1),
      Impl_WarmAddresses.is_storage_warm warm caller (Mock.word 2),
      (InitialTxGas.calculate_initial_tx_gas_for_tx tx SpecId.OSAKA).(InitialAndFloorGas.initial_gas).(Integer.value)) =
      (true, true, 31500).
  Proof. vm_compute. reflexivity. Qed.

  Module Authorization.
    Record t : Set := { chain_id : aliases.U256.t; nonce : u64; authority : option Address.t; address : Address.t }.

    #[local] Instance methods : AuthorizationTr.C t := {|
      AuthorizationTr.chain_id := chain_id;
      AuthorizationTr.nonce := nonce;
      AuthorizationTr.authority := authority;
      AuthorizationTr.address := address;
    |}.
  End Authorization.
  #[local] Existing Instance Authorization.methods.

  Definition auth (nonce : u64) : Authorization.t := {|
    Authorization.chain_id := Mock.word 1;
    Authorization.nonce := nonce;
    Authorization.authority := Some caller;
    Authorization.address := {| Address.value := 0 |};
  |}.

  Definition empty_journal := Impl_Journal.new (Mock.db <| Mock.info := None |>).

  Example repeated_authority_refunds_after_first_authorization_creates_account :
    match PreExecution.apply_authorizations 1 [auth 0; auth 1] 0 empty_journal with
    | Some (Result.Ok refund, journal) => Some (refund.(Integer.value),
      option_map (fun account => account.(Account.info).(AccountInfo.nonce).(Integer.value))
        (EvmState.get caller journal.(Journal.inner).(JournalInner.state)), journal.(Journal.database).(Mock.reads))
    | _ => None
    end = Some (12500, Some 2, [Mock.Basic]).
  Proof. vm_compute. reflexivity. Qed.

  Example invalid_authorization_nonce_still_warms_loaded_account :
    match PreExecution.apply_authorization 1 (auth 1) empty_journal with
    | Some (Result.Ok refunded, journal) => Some (refunded,
      option_map (fun account => (AccountStatus.contains account.(Account.status) AccountStatus.Cold, Impl_Account.is_touched account))
        (EvmState.get caller journal.(Journal.inner).(JournalInner.state)))
    | _ => None
    end = Some (false, Some (false, false)).
  Proof. vm_compute. reflexivity. Qed.

  Example invalid_authorization_chain_id_does_not_load :
    PreExecution.apply_authorization 1 ((auth 0) <| Authorization.chain_id := Mock.word (2 ^ 64 + 1) |>) empty_journal =
      Some (Result.Ok false, empty_journal).
  Proof. vm_compute. reflexivity. Qed.
End Test.
