Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.journaled_state.simulate.entry.
Require Import revm.revm_primitives.simulate.lib.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.types.
Require Import ruint.links.lib.
Require Import revm.revm_context_interface.journaled_state.simulate.account.

Import ListNotations.

Module Test.
  Definition address : Address.t := {| Address.value := 10 |}.

  Definition word (value : Z) : aliases.U256.t := {| Uint.value := value |}.

  Definition initial : JournaledAccount.t :=
    Impl_JournaledAccount.new address Impl_Default_for_Account.default [].

  Example unchanged_balance_touches_only_once :
    let account := Impl_JournaledAccount.set_balance initial (word 0) in
    (account.(JournaledAccount.journal_entries),
      (Impl_JournaledAccount.set_balance account (word 0)).(JournaledAccount.journal_entries)) =
      ([JournalEntry.AccountTouched address], [JournalEntry.AccountTouched address]).
  Proof. vm_compute. reflexivity. Qed.

  Example balance_change_records_previous_value :
    let account := Impl_JournaledAccount.set_balance initial (word 7) in
    let account := Impl_JournaledAccount.set_balance account (word 9) in
    (Impl_JournaledAccount.balance account, account.(JournaledAccount.journal_entries)) =
      (word 9, [JournalEntry.AccountTouched address;
        JournalEntry.BalanceChange (word 0) address; JournalEntry.BalanceChange (word 7) address]).
  Proof. vm_compute. reflexivity. Qed.

  Example increment_overflow_keeps_touch_without_balance_entry :
    let account := initial.(JournaledAccount.account) in
    let account := account <| Account.info := account.(Account.info)
      <| AccountInfo.balance := word (2 ^ 256 - 1) |> |> in
    let '(success, account) := Impl_JournaledAccount.incr_balance
      (initial <| JournaledAccount.account := account |>) (word 1) in
    (success, Impl_JournaledAccount.balance account, account.(JournaledAccount.journal_entries)) =
      (false, word (2 ^ 256 - 1), [JournalEntry.AccountTouched address]).
  Proof. vm_compute. reflexivity. Qed.

  Example delegate_clears_code_before_attempting_nonce_bump :
    let account := initial.(JournaledAccount.account) in
    let account := account <| Account.info := account.(Account.info)
      <| AccountInfo.nonce := {| Integer.value := 2 ^ 64 - 1 |} |> |> in
    let account := Impl_JournaledAccount.delegate
      (initial <| JournaledAccount.account := account |>) {| Address.value := 0 |} in
    (Impl_JournaledAccount.code_hash account, Impl_JournaledAccount.nonce account,
      account.(JournaledAccount.journal_entries)) =
      (KECCAK_EMPTY, ({| Integer.value := 2 ^ 64 - 1 |} : u64),
        [JournalEntry.AccountTouched address; JournalEntry.CodeChange address]).
  Proof. vm_compute. reflexivity. Qed.

  Example nonce_change_restores_previous_value :
    let account := Impl_JournaledAccount.set_nonce initial 17 in
    let account := Impl_JournaledAccount.set_nonce account 23 in
    Impl_JournalEntry.revert (JournalEntry.NonceChange address 17)
      [(address, account.(JournaledAccount.account))] None true =
      Some ([(address, (Impl_JournaledAccount.set_nonce initial 17).(JournaledAccount.account))], None).
  Proof. vm_compute. reflexivity. Qed.
End Test.
