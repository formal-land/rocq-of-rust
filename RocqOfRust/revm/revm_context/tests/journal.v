Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context.journal.simulate.warm_addresses.
Require Import revm.revm_context_interface.journaled_state.simulate.entry.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.lib.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.types.
Require Import ruint.links.lib.
Require Import core.links.result.

Import ListNotations.

Module Test.
  Definition address (value : Z) : Address.t := {| Address.value := value |}.

  Definition word (value : Z) : aliases.U256.t := {| Uint.value := value |}.

  Definition account (balance : Z) : Account.t :=
    let account := Impl_Default_for_Account.default in
    account <| Account.info := account.(Account.info) <| AccountInfo.balance := word balance |> |>.

  Definition initial : JournalInner.t :=
    Impl_JournalInner.new <| JournalInner.spec := SpecId.OSAKA |>
      <| JournalInner.state := [(address 10, account 20); (address 11, account 5)] |>.

  Example transfer_then_revert_restores_balances_and_touch_flags :
    let '(checkpoint, state) := Impl_JournalInner.checkpoint initial in
    match Impl_JournalInner.transfer_loaded state (address 10) (address 11) (word 3) with
    | Some (None, state) => Impl_JournalInner.checkpoint_revert state checkpoint
    | _ => None
    end = Some initial.
  Proof. vm_compute. reflexivity. Qed.

  Example inner_commit_is_still_reverted_by_outer_checkpoint :
    let '(outer, state) := Impl_JournalInner.checkpoint initial in
    let state := Impl_JournalInner.tstore state (address 10) (word 1) (word 7) in
    let '(_, state) := Impl_JournalInner.checkpoint state in
    let state := Impl_JournalInner.tstore state (address 10) (word 1) (word 8) in
    let state := Impl_JournalInner.checkpoint_commit state in
    Impl_JournalInner.checkpoint_revert state outer = Some initial.
  Proof. vm_compute. reflexivity. Qed.

  Example inner_revert_preserves_outer_transient_value :
    let state := Impl_JournalInner.tstore initial (address 10) (word 1) (word 7) in
    let '(checkpoint, nested) := Impl_JournalInner.checkpoint state in
    let nested := Impl_JournalInner.tstore nested (address 10) (word 1) (word 0) in
    Impl_JournalInner.checkpoint_revert nested checkpoint = Some state.
  Proof. vm_compute. reflexivity. Qed.

  Example unchanged_transient_value_adds_no_entry :
    let state := Impl_JournalInner.tstore initial (address 10) (word 1) (word 7) in
    Impl_JournalInner.tstore state (address 10) (word 1) (word 7) = state.
  Proof. vm_compute. reflexivity. Qed.

  Example zero_transfer_touches_only_recipient :
    match Impl_JournalInner.transfer_loaded initial (address 10) (address 11) (word 0) with
    | Some (None, state) => Some state.(JournalInner.journal)
    | _ => None
    end = Some [JournalEntry.AccountTouched (address 11)].
  Proof. vm_compute. reflexivity. Qed.

  Example self_transfer_checks_balance_without_touching :
    (Impl_JournalInner.transfer_loaded initial (address 10) (address 10) (word 21),
     Impl_JournalInner.transfer_loaded initial (address 10) (address 10) (word 20)) =
    (Some (Some TransferError.OutOfFunds, initial), Some (None, initial)).
  Proof. vm_compute. reflexivity. Qed.

  Example recipient_overflow_keeps_rust_sender_debit_without_transfer_entry :
    let state := initial <| JournalInner.state :=
      [(address 10, account 20); (address 11, account (2 ^ 256 - 1))] |> in
    match Impl_JournalInner.transfer_loaded state (address 10) (address 11) (word 3) with
    | Some (error, state) => Some (error,
        option_map (fun account => account.(Account.info).(AccountInfo.balance))
          (EvmState.get (address 10) state.(JournalInner.state)), state.(JournalInner.journal))
    | None => None
    end = Some (Some TransferError.OverflowPayment, Some (word 17),
      [JournalEntry.AccountTouched (address 10); JournalEntry.AccountTouched (address 11)]).
  Proof. vm_compute. reflexivity. Qed.

  Example missing_account_is_an_invariant_failure :
    Impl_JournalEntry.revert (JournalEntry.NonceBump (address 12)) initial.(JournalInner.state)
      (Some []) true = None.
  Proof. vm_compute. reflexivity. Qed.

  Example create_checkpoint_sets_nonce_and_flags_and_reverts_transfer :
    let state := initial <| JournalInner.state :=
      [(address 10, account 20); (address 11, account 0)] |> in
    match Impl_JournalInner.create_account_checkpoint state (address 10) (address 11)
      (word 3) SpecId.OSAKA with
    | Some (Result.Ok checkpoint, created) =>
      match EvmState.get (address 11) created.(JournalInner.state),
        Impl_JournalInner.checkpoint_revert created checkpoint with
      | Some target, Some reverted => Some (
          target.(Account.info).(AccountInfo.nonce), Impl_Account.is_created_locally target,
          option_map (fun acc => (acc.(Account.info).(AccountInfo.balance),
            acc.(Account.info).(AccountInfo.nonce), Impl_Account.is_created acc))
            (EvmState.get (address 11) reverted.(JournalInner.state)),
          option_map (fun acc => acc.(Account.info).(AccountInfo.balance))
            (EvmState.get (address 10) reverted.(JournalInner.state)))
      | _, _ => None
      end
    | _ => None
    end = Some ((1 : u64), true, Some (word 0, (0 : u64), false), Some (word 20)).
  Proof. vm_compute. reflexivity. Qed.

  Example creation_collision_exits_its_checkpoint :
    let target := account 0 in
    let target := target <| Account.info := target.(Account.info) <| AccountInfo.nonce := 1 |> |> in
    let state := initial <| JournalInner.state := [(address 10, account 20); (address 11, target)] |> in
    Impl_JournalInner.create_account_checkpoint state (address 10) (address 11) (word 0) SpecId.OSAKA =
      Some (Result.Err TransferError.CreateCollision, state).
  Proof. vm_compute. reflexivity. Qed.

  Example destruction_revert_preserves_preexisting_global_status :
    let target := Impl_Account.mark_selfdestruct (account 0) in
    let '(_, target) := Impl_Account.mark_selfdestructed_locally target in
    let state := [(address 10, target); (address 11, account 8)] in
    match Impl_JournalEntry.revert
      (JournalEntry.AccountDestroyed (word 3) (address 10) (address 11)
        SelfdestructionRevertStatus.LocallySelfdestroyed) state None true with
    | Some (state, _) =>
      option_map (fun acc => (Impl_Account.is_selfdestructed acc,
        Impl_Account.is_selfdestructed_locally acc, acc.(Account.info).(AccountInfo.balance)))
        (EvmState.get (address 10) state)
    | None => None
    end = Some (true, false, word 3).
  Proof. vm_compute. reflexivity. Qed.

  Example storage_undo_restores_value_and_coldness_without_losing_original :
    let acc := (account 0) <| Account.storage :=
      [(word 1, Impl_EvmStorageSlot.new_changed (word 8) (word 10) 0)] |> in
    let state := [(address 10, acc)] in
    match Impl_JournalInner.revert_entries
      [JournalEntry.StorageChanged (word 1) (word 9) (address 10);
       JournalEntry.StorageWarmed (word 1) (address 10)] state (Some []) true with
    | Some (state, _) => option_map Account.storage (EvmState.get (address 10) state)
    | None => None
    end = Some [(word 1, Impl_EvmStorageSlot.mark_cold
      (Impl_EvmStorageSlot.new_changed (word 8) (word 9) 0))].
  Proof. vm_compute. reflexivity. Qed.

  Example code_undo_resets_hash_and_cached_code :
    let acc := account 0 in
    let acc := acc <| Account.info := acc.(Account.info)
      <| AccountInfo.code_hash := FixedBytes.from_Z 17 |> |> in
    match Impl_JournalEntry.revert (JournalEntry.CodeChange (address 10))
      [(address 10, acc)] None true with
    | Some (state, _) => option_map (fun acc =>
        (acc.(Account.info).(AccountInfo.code_hash), acc.(Account.info).(AccountInfo.code)))
        (EvmState.get (address 10) state)
    | None => None
    end = Some (KECCAK_EMPTY, None).
  Proof. vm_compute. reflexivity. Qed.

  Example discard_skips_transient_undo_then_clears_it :
    let state := Impl_JournalInner.tstore initial (address 10) (word 1) (word 7) in
    Impl_JournalInner.discard_tx state = Some (initial <| JournalInner.transaction_id := 1 |>).
  Proof. vm_compute. reflexivity. Qed.

  Example touch_revert_keeps_ripemd_exception_only_when_enabled :
    let state := [(address 3, Impl_Account.mark_touch (account 0))] in
    (Impl_JournalEntry.revert (JournalEntry.AccountTouched (address 3)) state None true,
     Impl_JournalEntry.revert (JournalEntry.AccountTouched (address 3)) state None false) =
    (Some (state, None), Some ([(address 3, account 0)], None)).
  Proof. vm_compute. reflexivity. Qed.

  Example warm_addresses_handle_long_precompile_and_reset_cached_bits :
    let warm := Impl_WarmAddresses.set_precompile_addresses Impl_WarmAddresses.new
      [address 1; address 256; address 300] in
    let reset := Impl_WarmAddresses.set_precompile_addresses warm [address 2] in
    (Impl_WarmAddresses.is_warm warm (address 256),
     Impl_WarmAddresses.is_warm warm (address 300),
     Impl_WarmAddresses.is_warm warm (address 299),
     Impl_WarmAddresses.is_warm reset (address 1),
     Impl_WarmAddresses.is_warm reset (address 2),
     Impl_WarmAddresses.is_warm reset (address 300)) =
    (true, true, false, false, true, false).
  Proof. vm_compute. reflexivity. Qed.

  Example commit_clears_transaction_data_but_preserves_precompiles_and_state :
    let warm := Impl_WarmAddresses.set_precompile_addresses Impl_WarmAddresses.new [address 1] in
    let warm := Impl_WarmAddresses.set_coinbase warm (address 2) in
    let warm := Impl_WarmAddresses.set_access_list warm [(address 10, [word 1])] in
    let state := initial <| JournalInner.warm_addresses := warm |> in
    let state := Impl_JournalInner.tstore state (address 10) (word 1) (word 7) in
    let state := Impl_JournalInner.commit_tx state in
    (state.(JournalInner.state), state.(JournalInner.transient_storage), state.(JournalInner.journal),
      state.(JournalInner.transaction_id),
      Impl_WarmAddresses.is_warm state.(JournalInner.warm_addresses) (address 1),
      Impl_WarmAddresses.is_warm state.(JournalInner.warm_addresses) (address 2),
      Impl_WarmAddresses.is_storage_warm state.(JournalInner.warm_addresses) (address 10) (word 1)) =
    (initial.(JournalInner.state), [], [], (1 : usize), true, false, false).
  Proof. vm_compute. reflexivity. Qed.

  Example large_checkpoint_indices_do_not_construct_large_unary_indices :
    let checkpoint := {|
      JournalCheckpoint.log_i := {| Integer.value := 2 ^ 64 - 1 |};
      JournalCheckpoint.journal_i := {| Integer.value := 2 ^ 64 - 1 |};
    |} in
    Impl_JournalInner.checkpoint_revert initial checkpoint = Some initial.
  Proof. vm_compute. reflexivity. Qed.
End Test.
