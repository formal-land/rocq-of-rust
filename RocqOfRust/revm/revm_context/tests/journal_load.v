Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.result.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context_interface.journaled_state.simulate.account.
Require Import revm.revm_context_interface.journaled_state.simulate.entry.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_state.simulate.account_info.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.types.
Require Import ruint.links.lib.

Import ListNotations.

Module Test.
  Inductive Event : Set := Basic | Code | Storage | Block.

  Record Db : Set := {
    info : option AccountInfo.t;
    value : aliases.U256.t;
    fail_basic : bool;
    fail_code : bool;
    fail_storage : bool;
    reads : list Event;
  }.

  Definition word (value : Z) : aliases.U256.t := {| Uint.value := value |}.

  Definition target : Address.t := {| Address.value := 10 |}.

  Definition empty_code : Bytecode.t := {| Bytecode.original_bytes := Impl_Bytes.copy_from_slice [] |}.

  #[local] Instance db_methods : Database.C Db unit := {|
    Database.basic db address :=
      (if db.(fail_basic) then Result.Err tt else Result.Ok db.(info),
       db <| reads := db.(reads) ++ [Basic] |>);
    Database.code_by_hash db hash :=
      (if db.(fail_code) then Result.Err tt else Result.Ok empty_code,
       db <| reads := db.(reads) ++ [Code] |>);
    Database.storage db address key :=
      (if db.(fail_storage) then Result.Err tt else Result.Ok db.(value),
       db <| reads := db.(reads) ++ [Storage] |>);
    Database.block_hash db number :=
      (Result.Err tt, db <| reads := db.(reads) ++ [Block] |>);
  |}.

  Definition db : Db := {|
    info := Some Impl_Default_for_AccountInfo.default;
    value := word 7;
    fail_basic := false;
    fail_code := false;
    fail_storage := false;
    reads := [];
  |}.

  Definition loaded : JournalInner.t :=
    Impl_JournalInner.new <| JournalInner.state := [(target, Impl_Default_for_Account.default)] |>.

  Example skip_cold_account_does_not_read_or_insert :
    Impl_JournalInner.load_account_optional Impl_JournalInner.new db target false true =
      (Result.Err JournalLoadError.ColdLoadSkipped, db, Impl_JournalInner.new).
  Proof. vm_compute. reflexivity. Qed.

  Example basic_error_retains_database_mutation_without_journal_changes :
    let db := db <| fail_basic := true |> in
    Impl_JournalInner.load_account_optional Impl_JournalInner.new db target false false =
      (Result.Err (JournalLoadError.DBError tt), db <| reads := [Basic] |>, Impl_JournalInner.new).
  Proof. vm_compute. reflexivity. Qed.

  Example code_error_retains_prior_account_load_and_warming :
    let account_info := Impl_Default_for_AccountInfo.default <| AccountInfo.code := None |>
      <| AccountInfo.code_hash := alloy_primitives.bits.simulate.fixed.FixedBytes.from_Z 17 |> in
    let db := db <| info := Some account_info |> <| fail_code := true |> in
    let '(result, db, state) := Impl_JournalInner.load_account_optional
      Impl_JournalInner.new db target true false in
    (match result with Result.Err (JournalLoadError.DBError _) => true | _ => false end,
      db.(reads), option_map Account.info (EvmState.get target state.(JournalInner.state)),
      state.(JournalInner.journal)) =
    (true, [Basic; Code], Some account_info, [JournalEntry.AccountWarmed target]).
  Proof. vm_compute. reflexivity. Qed.

  Example repeated_account_load_reads_database_once :
    let '(_, db, state) := Impl_JournalInner.load_account_optional
      Impl_JournalInner.new db target false false in
    let '(result, db, state) := Impl_JournalInner.load_account_optional state db target false false in
    (match result with Result.Ok (_, cold) => Some cold | _ => None end,
      db.(reads), state.(JournalInner.journal)) =
    (Some false, [Basic], [JournalEntry.AccountWarmed target]).
  Proof. vm_compute. reflexivity. Qed.

  Example skip_cold_storage_does_not_read_database :
    Impl_JournalInner.sload loaded db target (word 1) true =
      Some (Result.Err JournalLoadError.ColdLoadSkipped, db, loaded).
  Proof. vm_compute. reflexivity. Qed.

  Example newly_created_account_does_not_read_old_database_storage :
    let state := loaded <| JournalInner.state :=
      [(target, Impl_Account.mark_created Impl_Default_for_Account.default)] |> in
    match Impl_JournalInner.sload state db target (word 1) false with
    | Some (Result.Ok load, db, state) => Some (load.(StateLoad.data), db.(reads), state.(JournalInner.journal))
    | _ => None
    end = Some (word 0, [], [JournalEntry.StorageWarmed (word 1) target]).
  Proof. vm_compute. reflexivity. Qed.

  Example sstore_keeps_original_value_across_repeated_writes :
    match Impl_JournalInner.sstore loaded db target (word 1) (word 8) false with
    | Some (Result.Ok _, db, state) =>
      match Impl_JournalInner.sstore state db target (word 1) (word 9) false with
      | Some (Result.Ok load, db, state) => Some (
          load.(StateLoad.data).(SStoreResult.original_value),
          load.(StateLoad.data).(SStoreResult.present_value),
          load.(StateLoad.data).(SStoreResult.new_value), load.(StateLoad.is_cold),
          db.(reads), state.(JournalInner.journal))
      | _ => None
      end
    | _ => None
    end = Some (word 7, word 8, word 9, false, [Storage],
      [JournalEntry.StorageWarmed (word 1) target;
       JournalEntry.StorageChanged (word 1) (word 7) target;
       JournalEntry.StorageChanged (word 1) (word 8) target]).
  Proof. vm_compute. reflexivity. Qed.

  Example unchanged_sstore_only_journals_warming :
    match Impl_JournalInner.sstore loaded db target (word 1) (word 7) false with
    | Some (Result.Ok _, _, state) => Some state.(JournalInner.journal)
    | _ => None
    end = Some [JournalEntry.StorageWarmed (word 1) target].
  Proof. vm_compute. reflexivity. Qed.

  Example storage_error_retains_database_mutation_without_journal_changes :
    let db := db <| fail_storage := true |> in
    Impl_JournalInner.sload loaded db target (word 1) false =
      Some (Result.Err (JournalLoadError.DBError tt), db <| reads := [Storage] |>, loaded).
  Proof. vm_compute. reflexivity. Qed.

  Definition destruction_observation (created same_target : bool) :=
    let source := Impl_Default_for_Account.default in
    let source := source <| Account.info := source.(Account.info) <| AccountInfo.balance := word 5 |> |> in
    let source := if created then snd (Impl_Account.mark_created_locally source) else source in
    let recipient : Address.t := {| Address.value := 11 |} in
    let state := loaded <| JournalInner.spec := SpecId.OSAKA |>
      <| JournalInner.state := [(target, source); (recipient, Impl_Default_for_Account.default)] |> in
    match Impl_JournalInner.selfdestruct state db target (if same_target then target else recipient) false with
    | Some (Result.Ok load, _, state) =>
      match EvmState.get target state.(JournalInner.state), EvmState.get recipient state.(JournalInner.state) with
      | Some source, Some recipient => Some (source.(Account.info).(AccountInfo.balance),
          recipient.(Account.info).(AccountInfo.balance), Impl_Account.is_selfdestructed_locally source,
          load.(StateLoad.data).(SelfDestructResult.had_value))
      | _, _ => None
      end
    | _ => None
    end.

  Example osaka_selfdestruct_distinguishes_creation_and_self_target :
    (destruction_observation false true, destruction_observation false false,
     destruction_observation true true, destruction_observation true false) =
    (Some (word 5, word 0, false, true), Some (word 0, word 5, false, true),
     Some (word 0, word 0, true, true), Some (word 0, word 5, true, true)).
  Proof. vm_compute. reflexivity. Qed.

  Example next_transaction_clears_locally_destroyed_account_before_reloading_code :
    let account := Impl_Default_for_Account.default in
    let account := account <| Account.storage := [(word 1, Impl_EvmStorageSlot.new (word 7) 0)] |> in
    let '(_, account) := Impl_Account.mark_created_locally account in
    let '(_, account) := Impl_Account.mark_selfdestructed_locally account in
    let state := loaded <| JournalInner.transaction_id := 1 |>
      <| JournalInner.state := [(target, account)] |> in
    let '(result, db, state) := Impl_JournalInner.load_account_optional state db target true false in
    match result with
    | Result.Ok (account, cold) => Some (cold, account.(Account.storage),
        Impl_Account.is_created_locally account, Impl_Account.is_selfdestructed_locally account,
        Impl_Account.is_created account, Impl_Account.is_selfdestructed account, db.(reads))
    | _ => None
    end = Some (true, [], false, false, true, true, []).
  Proof. vm_compute. reflexivity. Qed.
  Example mutable_account_writeback_keeps_undo_entries :
    let '(checkpoint, state) := Impl_JournalInner.checkpoint loaded in
    let '(result, db, state) := Impl_JournalInner.load_account_mut_optional_code state db target false false in
    match result with
    | Result.Err _ => None
    | Result.Ok (account, _) =>
      match Impl_JournalInner.store_account state (Impl_JournaledAccount.set_balance account (word 19)) with
      | None => None
      | Some state => option_map (fun state =>
          (option_map Account.info (EvmState.get target state.(JournalInner.state)), state.(JournalInner.journal)))
          (Impl_JournalInner.checkpoint_revert state checkpoint)
      end
    end = Some (Some Impl_Default_for_AccountInfo.default, []).
  Proof. vm_compute. reflexivity. Qed.

  Example balance_increment_overflow_is_success_with_only_touch :
    let account := Impl_Default_for_Account.default <| Account.info :=
      Impl_Default_for_AccountInfo.default <| AccountInfo.balance := word (2 ^ 256 - 1) |> |> in
    let state := loaded <| JournalInner.state := [(target, account)] |> in
    match Impl_JournalInner.balance_incr state db target (word 1) with
    | Some (Result.Ok _, db, state) => Some
        (option_map (fun account => account.(Account.info).(AccountInfo.balance))
          (EvmState.get target state.(JournalInner.state)), db.(reads), state.(JournalInner.journal))
    | _ => None
    end = Some (Some (word (2 ^ 256 - 1)), [], [JournalEntry.AccountTouched target]).
  Proof. vm_compute. reflexivity. Qed.

  Example delegated_loading_warms_both_accounts :
    let code := {| Bytecode.original_bytes := Impl_Bytes.copy_from_slice
      ([(239 : u8); (1 : u8); (0 : u8)] ++ List.repeat (0 : u8) 19 ++ [(11 : u8)]) |} in
    let db := db <| info := Some (Impl_Default_for_AccountInfo.default
      <| AccountInfo.code := Some code |>) |> in
    match Impl_JournalInner.load_account_delegated Impl_JournalInner.new db target with
    | Some (Result.Ok load, db, state) =>
      match Impl_JournalInner.load_account_delegated state db target with
      | Some (Result.Ok second, db, _) => Some
          (load.(StateLoad.is_cold), load.(StateLoad.data).(AccountLoad.is_delegate_account_cold),
           second.(StateLoad.is_cold), second.(StateLoad.data).(AccountLoad.is_delegate_account_cold), db.(reads))
      | _ => None
      end
    | _ => None
    end = Some (true, Some true, false, Some false, [Basic; Basic]).
  Proof. vm_compute. reflexivity. Qed.
End Test.
