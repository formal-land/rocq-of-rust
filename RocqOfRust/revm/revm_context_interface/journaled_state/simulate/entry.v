Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.types.
Require Import revm.revm_primitives.simulate.lib.
Require Import ruint.simulate.add.
Require Import ruint.links.lib.

Module SelfdestructionRevertStatus.
  Inductive t : Set :=
  | GloballySelfdestroyed
  | LocallySelfdestroyed
  | RepeatedSelfdestruction.
End SelfdestructionRevertStatus.

Module JournalEntry.
  Inductive t : Set :=
  | AccountWarmed (address : Address.t)
  | AccountDestroyed (had_balance : aliases.U256.t) (address target : Address.t)
      (destroyed_status : SelfdestructionRevertStatus.t)
  | AccountTouched (address : Address.t)
  | BalanceChange (old_balance : aliases.U256.t) (address : Address.t)
  | BalanceTransfer (balance : aliases.U256.t) (from to : Address.t)
  | NonceChange (address : Address.t) (previous_nonce : u64)
  | NonceBump (address : Address.t)
  | AccountCreated (address : Address.t) (is_created_globally : bool)
  | StorageChanged (key had_value : aliases.U256.t) (address : Address.t)
  | StorageWarmed (key : aliases.U256.t) (address : Address.t)
  | TransientStorageChange (key had_value : aliases.U256.t) (address : Address.t)
  | CodeChange (address : Address.t).
End JournalEntry.

Module Impl_JournalEntry.
  Definition account_warmed (address : Address.t) := JournalEntry.AccountWarmed address.

  Definition account_destroyed (address target : Address.t)
      (destroyed_status : SelfdestructionRevertStatus.t) (had_balance : aliases.U256.t) :=
    JournalEntry.AccountDestroyed had_balance address target destroyed_status.

  Definition account_touched (address : Address.t) := JournalEntry.AccountTouched address.

  Definition balance_changed (address : Address.t) (old_balance : aliases.U256.t) :=
    JournalEntry.BalanceChange old_balance address.

  Definition balance_transfer (from to : Address.t) (balance : aliases.U256.t) :=
    JournalEntry.BalanceTransfer balance from to.

  Definition account_created (address : Address.t) (is_created_globally : bool) :=
    JournalEntry.AccountCreated address is_created_globally.

  Definition storage_changed (address : Address.t) (key had_value : aliases.U256.t) :=
    JournalEntry.StorageChanged key had_value address.

  Definition nonce_changed (address : Address.t) (previous_nonce : u64) :=
    JournalEntry.NonceChange address previous_nonce.

  Definition nonce_bumped (address : Address.t) := JournalEntry.NonceBump address.

  Definition storage_warmed (address : Address.t) (key : aliases.U256.t) :=
    JournalEntry.StorageWarmed key address.

  Definition transient_storage_changed (address : Address.t) (key had_value : aliases.U256.t) :=
    JournalEntry.TransientStorageChange key had_value address.

  Definition code_changed (address : Address.t) := JournalEntry.CodeChange address.

  (** [None] exposes a failed Rust unwrap. Valid journal entries refer to loaded
      accounts and slots; the execution boundary must keep failures incomplete. *)
  Definition revert (self : JournalEntry.t) (state : EvmState.t)
      (transient_storage : option TransientStorage.t) (is_spurious_dragon_enabled : bool)
      : option (EvmState.t * option TransientStorage.t) :=
    let with_state state := option_map (fun state => (state, transient_storage)) state in
    match self with
    | JournalEntry.AccountWarmed address =>
      with_state (EvmState.update address Impl_Account.mark_cold state)
    | JournalEntry.AccountTouched address =>
      if is_spurious_dragon_enabled && Z.eqb address.(Address.value) 3 then
        Some (state, transient_storage)
      else with_state (EvmState.update address Impl_Account.unmark_touch state)
    | JournalEntry.AccountDestroyed had_balance address target destroyed_status =>
      let restore account :=
        let account := match destroyed_status with
          | SelfdestructionRevertStatus.GloballySelfdestroyed =>
            Impl_Account.unmark_selfdestructed_locally (Impl_Account.unmark_selfdestruct account)
          | SelfdestructionRevertStatus.LocallySelfdestroyed =>
            Impl_Account.unmark_selfdestructed_locally account
          | SelfdestructionRevertStatus.RepeatedSelfdestruction => account
          end in
        account <| Account.info := account.(Account.info)
          <| AccountInfo.balance := Impl_Uint.wrapping_add account.(Account.info).(AccountInfo.balance) had_balance |> |> in
      match EvmState.update address restore state with
      | None => None
      | Some state =>
        if Z.eqb address.(Address.value) target.(Address.value) then Some (state, transient_storage)
        else with_state (EvmState.update target (fun account =>
          account <| Account.info := account.(Account.info)
            <| AccountInfo.balance := Impl_Uint.wrapping_sub account.(Account.info).(AccountInfo.balance) had_balance |> |>) state)
      end
    | JournalEntry.BalanceChange old_balance address =>
      with_state (EvmState.update address (fun account =>
        account <| Account.info := account.(Account.info) <| AccountInfo.balance := old_balance |> |>) state)
    | JournalEntry.BalanceTransfer balance from to =>
      match EvmState.update from (fun account =>
        account <| Account.info := account.(Account.info)
          <| AccountInfo.balance := Impl_Uint.wrapping_add account.(Account.info).(AccountInfo.balance) balance |> |>) state with
      | None => None
      | Some state => with_state (EvmState.update to (fun account =>
        account <| Account.info := account.(Account.info)
          <| AccountInfo.balance := Impl_Uint.wrapping_sub account.(Account.info).(AccountInfo.balance) balance |> |>) state)
      end
    | JournalEntry.NonceChange address previous_nonce =>
      with_state (EvmState.update address (fun account =>
        account <| Account.info := account.(Account.info) <| AccountInfo.nonce := previous_nonce |> |>) state)
    | JournalEntry.NonceBump address =>
      with_state (EvmState.update address (fun account =>
        account <| Account.info := account.(Account.info)
          <| AccountInfo.nonce := BinOp.Saturating.sub account.(Account.info).(AccountInfo.nonce) 1 |> |>) state)
    | JournalEntry.AccountCreated address is_created_globally =>
      with_state (EvmState.update address (fun account =>
        let account := Impl_Account.unmark_created_locally account in
        let account := if is_created_globally then Impl_Account.unmark_created account else account in
        account <| Account.info := account.(Account.info) <| AccountInfo.nonce := 0 |> |>) state)
    | JournalEntry.StorageWarmed key address
    | JournalEntry.StorageChanged key _ address =>
      let restore := match self with
        | JournalEntry.StorageChanged _ had_value _ =>
          fun slot => slot <| EvmStorageSlot.present_value := had_value |>
        | _ => Impl_EvmStorageSlot.mark_cold
        end in
      match EvmState.get address state with
      | None => None
      | Some account =>
        match EvmStorage.update key restore account.(Account.storage) with
        | None => None
        | Some storage => with_state (EvmState.update address
            (fun account => account <| Account.storage := storage |>) state)
        end
      end
    | JournalEntry.TransientStorageChange key had_value address =>
      match transient_storage with
      | None => Some (state, None)
      | Some storage => Some (state, Some (
        if Z.eqb had_value.(Uint.value) 0 then TransientStorage.remove (address, key) storage
        else TransientStorage.insert (address, key) had_value storage))
      end
    | JournalEntry.CodeChange address =>
      with_state (EvmState.update address (fun account =>
        account <| Account.info := account.(Account.info)
          <| AccountInfo.code_hash := KECCAK_EMPTY |> <| AccountInfo.code := None |> |>) state)
    end.
End Impl_JournalEntry.
