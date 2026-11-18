Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_state.simulate.account_info.
Require Import revm.revm_state.simulate.lib.
Require Import ruint.links.lib.

Import ListNotations.

Module Test.
  Definition word (value : Z) : aliases.U256.t := {| Uint.value := value |}.

  Example default_account_is_empty :
    Impl_Account.is_empty Impl_Default_for_Account.default = true.
  Proof. vm_compute. reflexivity. Qed.

  Example emptiness_uses_hash_balance_and_nonce :
    let account := Impl_Default_for_Account.default in
    let info := account.(Account.info) in
    (Impl_AccountInfo.is_empty (info <| AccountInfo.code_hash := FixedBytes.from_Z 0 |>),
     Impl_AccountInfo.is_empty (info <| AccountInfo.code_hash := FixedBytes.from_Z 1 |>),
     Impl_AccountInfo.is_empty (info <| AccountInfo.balance := word 1 |>),
     Impl_AccountInfo.is_empty (info <| AccountInfo.nonce := 1 |>)) =
    (true, false, false, false).
  Proof. vm_compute. reflexivity. Qed.

  Example clearing_local_creation_preserves_global_creation_and_touch :
    let account := Impl_Account.mark_touch Impl_Default_for_Account.default in
    let '(first, account) := Impl_Account.mark_created_locally account in
    let account := Impl_Account.unmark_created_locally account in
    let '(second, account) := Impl_Account.mark_created_locally account in
    (first, second, Impl_Account.is_created account,
      Impl_Account.is_created_locally account, Impl_Account.is_touched account) =
    (true, false, true, true, true).
  Proof. vm_compute. reflexivity. Qed.

  Example transaction_id_and_explicit_cold_flag_both_control_warming :
    let account := Impl_Default_for_Account.default in
    let '(new_transaction, account) := Impl_Account.mark_warm_with_transaction_id account 1 in
    let '(same_transaction, account) := Impl_Account.mark_warm_with_transaction_id account 1 in
    let '(explicit_cold, account) := Impl_Account.mark_warm_with_transaction_id (Impl_Account.mark_cold account) 1 in
    (new_transaction, same_transaction, explicit_cold, account.(Account.transaction_id)) =
      (true, false, true, (1 : usize)).
  Proof. vm_compute. reflexivity. Qed.

  Example caller_modification_saturates_nonce_and_returns_old_balance :
    let account := Impl_Default_for_Account.default in
    let account := account <| Account.info := account.(Account.info)
      <| AccountInfo.balance := word 10 |>
      <| AccountInfo.nonce := {| Integer.value := 2 ^ 64 - 1 |} |> |> in
    let '(old_balance, account) := Impl_Account.caller_initial_modification account (word 7) true in
    (old_balance, account.(Account.info).(AccountInfo.balance),
      account.(Account.info).(AccountInfo.nonce), Impl_Account.is_touched account) =
      (word 10, word 7, ({| Integer.value := 2 ^ 64 - 1 |} : u64), true).
  Proof. vm_compute. reflexivity. Qed.

  Example storage_warming_preserves_original_and_present_values :
    let slot := Impl_EvmStorageSlot.new_changed (word 8) (word 9) 0 in
    let '(cold, slot) := Impl_EvmStorageSlot.mark_warm_with_transaction_id slot 1 in
    let '(warm, slot) := Impl_EvmStorageSlot.mark_warm_with_transaction_id slot 1 in
    (cold, warm, Impl_EvmStorageSlot.is_changed slot,
      slot.(EvmStorageSlot.original_value), slot.(EvmStorageSlot.present_value)) =
      (true, false, true, word 8, word 9).
  Proof. vm_compute. reflexivity. Qed.
End Test.
