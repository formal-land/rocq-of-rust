Require Import simulate.RocqOfRust.
From Stdlib Require Import List String.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.common.
Require Import core.links.result.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context.simulate.block.
Require Import revm.revm_context.simulate.cfg.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.simulate.tx.
Require Import revm.revm_context.tests.journal_load.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.account_info.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.

Import ListNotations.

Module Mock := journal_load.Test.

#[local] Existing Instance Mock.db_methods.

Module Test.
  Definition context : Context.t Mock.Db unit := Impl_Context.new Mock.db SpecId.OSAKA.

  Example block_database_error_retains_receiver_and_concrete_error :
    let '(result, context) := Impl_Host_for_Context.block_hash context 123 in
    (result, context.(Context.error), context.(Context.journaled_state).(Journal.database).(Mock.reads)) =
      (None, Result.Err (ContextError.Db tt), [Mock.Block]).
  Proof. vm_compute. reflexivity. Qed.

  Example cold_skip_keeps_previous_error_without_database_access :
    let context := context <| Context.error := Result.Err (ContextError.Custom "previous") |> in
    Impl_Host_for_Context.load_account_info_skip_cold_load context Mock.target true true =
      (Result.Err LoadError.ColdLoadSkipped, context).
  Proof. vm_compute. reflexivity. Qed.

  Example account_database_error_is_stored_for_handler :
    let context := context <| Context.journaled_state := Impl_Journal.new (Mock.db <| Mock.fail_basic := true |>) |> in
    let '(result, context) := Impl_Host_for_Context.load_account_info_skip_cold_load context Mock.target true false in
    (result, context.(Context.error), context.(Context.journaled_state).(Journal.database).(Mock.reads)) =
      (Result.Err LoadError.DBError, Result.Err (ContextError.Db tt), [Mock.Basic]).
  Proof. vm_compute. reflexivity. Qed.

  Example block_number_and_timestamp_preserve_u256_width :
    let block := context.(Context.block) <| BlockEnv.number := Mock.word (2 ^ 200) |>
      <| BlockEnv.timestamp := Mock.word (2 ^ 100) |> in
    let context := Impl_Context.set_block context block in
    (Impl_Host_for_Context.block_number context, Impl_Host_for_Context.timestamp context) =
      (Mock.word (2 ^ 200), Mock.word (2 ^ 100)).
  Proof. vm_compute. reflexivity. Qed.

  Example blob_hash_checks_index_before_unary_conversion :
    let tx := context.(Context.tx) <| TxEnv.tx_type := 3 |>
      <| TxEnv.blob_hashes := [FixedBytes.from_Z 17] |> in
    let context := Impl_Context.set_tx context tx in
    (Impl_Host_for_Context.blob_hash context 0,
      Impl_Host_for_Context.blob_hash context {| Integer.value := 2 ^ 64 - 1 |}) =
      (Some (Mock.word 17), None).
  Proof. vm_compute. reflexivity. Qed.

  Example osaka_gas_cap_and_saturating_initcode_override :
    let cfg := context.(Context.cfg) in
    (Impl_CfgEnv.tx_gas_limit_cap cfg,
      Impl_CfgEnv.tx_gas_limit_cap (cfg <| CfgEnv.spec := SpecId.PRAGUE |>),
      Impl_CfgEnv.max_initcode_size (cfg <| CfgEnv.limit_contract_code_size := Some {| Integer.value := 2 ^ 63 |} |>)) =
      ((16777216 : u64), ({| Integer.value := 2 ^ 64 - 1 |} : u64),
        ({| Integer.value := 2 ^ 64 - 1 |} : usize)).
  Proof. vm_compute. reflexivity. Qed.

  Example transaction_type_error_retains_earlier_type_update :
    let tx := context.(Context.tx) <| TxEnv.gas_priority_fee := Some (2 : u128) |>
      <| TxEnv.kind := TxKind.Create |> <| TxEnv.max_fee_per_blob_gas := 1 |> in
    Impl_TxEnv.derive_tx_type tx =
      (Result.Err DeriveTxTypeError.MissingTargetForEip4844, tx <| TxEnv.tx_type := 2 |>).
  Proof. vm_compute. reflexivity. Qed.

  Example effective_price_uses_transaction_and_block_fields :
    let tx := context.(Context.tx) <| TxEnv.tx_type := 2 |> <| TxEnv.gas_price := 19 |>
      <| TxEnv.gas_priority_fee := Some (7 : u128) |> in
    let block := context.(Context.block) <| BlockEnv.basefee := 17 |> in
    Impl_Host_for_Context.effective_gas_price
      (Impl_Context.set_tx (Impl_Context.set_block context block) tx) = Mock.word 19.
  Proof. vm_compute. reflexivity. Qed.
  Example host_delegation_reports_delegate_emptiness :
    let code := {| Bytecode.original_bytes := Impl_Bytes.copy_from_slice
      ([(239 : u8); (1 : u8); (0 : u8)] ++ List.repeat (0 : u8) 19 ++ [(11 : u8)]) |} in
    let account := Impl_Default_for_Account.default <| Account.info :=
      Impl_Default_for_AccountInfo.default <| AccountInfo.nonce := 1 |> <| AccountInfo.code := Some code |> |> in
    let journal := context.(Context.journaled_state) in
    let journal := journal <| Journal.inner := journal.(Journal.inner)
      <| JournalInner.state := [(Mock.target, account)] |> |> in
    let context := context <| Context.journaled_state := journal |> in
    match Impl_Host_for_Context.load_account_delegated context Mock.target with
    | Some (Some load, context) => Some
        (load.(StateLoad.data).(AccountLoad.is_empty),
         load.(StateLoad.data).(AccountLoad.is_delegate_account_cold),
         context.(Context.journaled_state).(Journal.database).(Mock.reads))
    | _ => None
    end = Some (true, Some true, [Mock.Basic]).
  Proof. vm_compute. reflexivity. Qed.
End Test.
