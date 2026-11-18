Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.common.
Require Import core.links.result.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_bytecode.simulate.bytecode.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context.simulate.block.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.simulate.tx.
Require Import revm.revm_context.tests.journal_load.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_context_interface.simulate.execution_result.
Require Import revm.revm_context_interface.simulate.result.
Require Import revm.revm_handler.simulate.frame.
Require Import revm.revm_handler.simulate.handler.
Require Import revm.revm_state.simulate.account_info.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.

Import ListNotations.
Module Mock := journal_load.Test.
Module ContractBytecode := revm.revm_bytecode.links.bytecode.Bytecode.
#[local] Existing Instance Mock.db_methods.

Module Test.
  Definition caller : Address.t := {| Address.value := 100 |}.
  Definition target : Address.t := {| Address.value := 200 |}.
  Definition beneficiary : Address.t := {| Address.value := 300 |}.

  Definition bytes (values : list Z) := Impl_Bytes.copy_from_slice (List.map (fun value => {| Integer.value := value |}) values).

  Definition initial (code : list Z) : Context.t Mock.Db unit :=
    let ctx := Impl_Context.new Mock.db SpecId.OSAKA in
    let caller_info := Impl_Default_for_AccountInfo.default <| AccountInfo.balance := Mock.word 2000000 |> in
    let code := {| ContractBytecode.original_bytes := bytes code |} in
    let target_info := Impl_AccountInfo.set_code Impl_Default_for_AccountInfo.default code in
    let accounts := [(caller, Impl_Default_for_Account.default <| Account.info := caller_info |>);
      (target, Impl_Default_for_Account.default <| Account.info := target_info |>);
      (beneficiary, Impl_Default_for_Account.default)] in
    ctx <| Context.journaled_state := ctx.(Context.journaled_state) <| Journal.inner :=
      ctx.(Context.journaled_state).(Journal.inner) <| JournalInner.state := accounts |> |> |>
      <| Context.tx := ctx.(Context.tx) <| TxEnv.caller := caller |> <| TxEnv.kind := TxKind.Call target |>
        <| TxEnv.gas_limit := 100000 |> <| TxEnv.gas_price := 10 |> <| TxEnv.value := Mock.word 5 |> |>
      <| Context.block := ctx.(Context.block) <| BlockEnv.beneficiary := beneficiary |> <| BlockEnv.basefee := 7 |> |>.

  #[local] Instance no_precompiles : PrecompileProvider.C Mock.Db unit := {|
    PrecompileProvider.run ctx _ _ := Some (Result.Ok None, ctx);
  |}.

  Definition account (ctx : Context.t Mock.Db unit) (address : Address.t) :=
    EvmState.get address ctx.(Context.journaled_state).(Journal.inner).(JournalInner.state).

  Definition balances (ctx : Context.t Mock.Db unit) :=
    List.map (fun address => option_map (fun account => account.(Account.info).(AccountInfo.balance).(Uint.value))
      (account ctx address)) [caller; target; beneficiary].

  Definition nonce (ctx : Context.t Mock.Db unit) :=
    option_map (fun account => account.(Account.info).(AccountInfo.nonce).(Integer.value)) (account ctx caller).

  Example value_transfer_accounts_for_fees_and_commits_transaction :
    match Handler.run 100 [] (initial []) with
    | Some (Result.Ok result, ctx) => Some (result, balances ctx, nonce ctx,
        ctx.(Context.journaled_state).(Journal.inner).(JournalInner.transaction_id).(Integer.value),
        List.length ctx.(Context.journaled_state).(Journal.inner).(JournalInner.journal))
    | _ => None
    end = Some (ExecutionResult.Success SuccessReason.Stop 21000 0 [] (Output.Call Impl_Bytes.new),
      [Some 1789995; Some 5; Some 63000], Some 1, 1, 0%nat).
  Proof. vm_compute. reflexivity. Qed.

  Example calldata_floor_adjusts_reimbursement_and_beneficiary_reward :
    let ctx := initial [] in
    let ctx := ctx <| Context.tx := ctx.(Context.tx) <| TxEnv.data := bytes [1; 2; 0] |> |> in
    match Handler.run 100 [] ctx with
    | Some (Result.Ok (ExecutionResult.Success _ used refunded _ _), ctx) => Some
        (used.(Integer.value), refunded.(Integer.value), balances ctx)
    | _ => None
    end = Some (21090, 0, [Some 1789095; Some 5; Some 63270]).
  Proof. vm_compute. reflexivity. Qed.

  Example reverted_transfer_keeps_nonce_and_charges_execution_gas :
    match Handler.run 100 [] (initial [95; 95; 253]) with
    | Some (Result.Ok result, ctx) => Some (result, balances ctx, nonce ctx)
    | _ => None
    end = Some (ExecutionResult.Revert 21004 Impl_Bytes.new,
      [Some 1789960; Some 0; Some 63012], Some 1).
  Proof. vm_compute. reflexivity. Qed.

  Example exceptional_halt_spends_entire_transaction_limit :
    match Handler.run 100 [] (initial [254]) with
    | Some (Result.Ok result, ctx) => Some (result, balances ctx, nonce ctx)
    | _ => None
    end = Some (ExecutionResult.Halt HaltReason.InvalidFEOpcode 100000,
      [Some 1000000; Some 0; Some 300000], Some 1).
  Proof. vm_compute. reflexivity. Qed.

  Example nonce_rejection_cleans_journal_without_charging_fees :
    let ctx := initial [] in
    let ctx := ctx <| Context.tx := ctx.(Context.tx) <| TxEnv.nonce := 1 |> |> in
    match Handler.run 100 [] ctx with
    | Some (Result.Err error, ctx) => Some (error, balances ctx, nonce ctx,
      ctx.(Context.journaled_state).(Journal.inner).(JournalInner.transaction_id).(Integer.value))
    | _ => None
    end = Some (EVMError.Transaction (InvalidTransaction.NonceTooHigh 1 0),
      [Some 2000000; Some 0; Some 0], Some 0, 1).
  Proof. vm_compute. reflexivity. Qed.

  Example database_failure_discards_fees_and_nonce_after_frame_execution :
    let ctx := initial [95; 84; 0] in
    let ctx := ctx <| Context.journaled_state := ctx.(Context.journaled_state)
      <| Journal.database := Mock.db <| Mock.fail_storage := true |> |> |> in
    match Handler.run 100 [] ctx with
    | Some (Result.Err error, ctx) => Some (error, balances ctx, nonce ctx, ctx.(Context.error),
      ctx.(Context.journaled_state).(Journal.database).(Mock.reads))
    | _ => None
    end = Some (EVMError.Database tt, [Some 2000000; Some 0; Some 0], Some 0, Result.Ok tt, [Mock.Storage]).
  Proof. vm_compute. reflexivity. Qed.

  Example evaluator_exhaustion_is_not_an_evm_result :
    Handler.run 0 [] (initial [0]) = None.
  Proof. vm_compute. reflexivity. Qed.
End Test.
