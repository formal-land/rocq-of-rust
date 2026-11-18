Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_bytecode.simulate.bytecode.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_context.journal.simulate.warm_addresses.
Require Import revm.revm_context_interface.journaled_state.simulate.entry.
Require Import revm.revm_context_interface.journaled_state.simulate.account.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import revm.revm_primitives.simulate.lib.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.account_info.
Require Import revm.revm_state.simulate.types.
Require Import ruint.links.lib.
Require Import ruint.simulate.add.
Require Import core.links.result.

Import ListNotations.

Module JournalInner.
  Record t : Set := {
    state : EvmState.t;
    transient_storage : TransientStorage.t;
    logs : list (Log.t LogData.t);
    depth : usize;
    journal : list JournalEntry.t;
    transaction_id : usize;
    spec : SpecId.t;
    warm_addresses : WarmAddresses.t;
  }.
End JournalInner.

Module Impl_JournalInner.
  Definition new : JournalInner.t := {|
    JournalInner.state := [];
    JournalInner.transient_storage := [];
    JournalInner.logs := [];
    JournalInner.depth := 0;
    JournalInner.journal := [];
    JournalInner.transaction_id := 0;
    JournalInner.spec := SpecId.PRAGUE;
    JournalInner.warm_addresses := Impl_WarmAddresses.new;
  |}.

  Definition take_logs (self : JournalInner.t) : list (Log.t LogData.t) * JournalInner.t :=
    (self.(JournalInner.logs), self <| JournalInner.logs := [] |>).

  Definition commit_tx (self : JournalInner.t) : JournalInner.t :=
    self <| JournalInner.transient_storage := [] |>
      <| JournalInner.depth := 0 |>
      <| JournalInner.journal := [] |>
      <| JournalInner.warm_addresses :=
        Impl_WarmAddresses.clear_coinbase_and_access_list self.(JournalInner.warm_addresses) |>
      <| JournalInner.transaction_id := self.(JournalInner.transaction_id) +i 1 |>
      <| JournalInner.logs := [] |>.

  (** Rust's drain(..).rev().for_each, carrying mutation explicitly. *)
  Fixpoint revert_entries (entries : list JournalEntry.t) (state : EvmState.t)
      (transient_storage : option TransientStorage.t) (is_spurious_dragon_enabled : bool)
      : option (EvmState.t * option TransientStorage.t) :=
    match entries with
    | [] => Some (state, transient_storage)
    | entry :: rest =>
      match Impl_JournalEntry.revert entry state transient_storage is_spurious_dragon_enabled with
      | None => None
      | Some (state, transient_storage) =>
        revert_entries rest state transient_storage is_spurious_dragon_enabled
      end
    end.

  Definition discard_tx (self : JournalInner.t) : option JournalInner.t :=
    let is_spurious_dragon_enabled := Impl_SpecId.is_enabled_in self.(JournalInner.spec) SpecId.SPURIOUS_DRAGON in
    match revert_entries (List.rev self.(JournalInner.journal)) self.(JournalInner.state)
      None is_spurious_dragon_enabled with
    | None => None
    | Some (state, _) => Some (self
        <| JournalInner.state := state |>
        <| JournalInner.journal := [] |>
        <| JournalInner.transient_storage := [] |>
        <| JournalInner.depth := 0 |>
        <| JournalInner.logs := [] |>
        <| JournalInner.transaction_id := self.(JournalInner.transaction_id) +i 1 |>
        <| JournalInner.warm_addresses :=
          Impl_WarmAddresses.clear_coinbase_and_access_list self.(JournalInner.warm_addresses) |>)
    end.

  Definition finalize (self : JournalInner.t) : EvmState.t * JournalInner.t :=
    (self.(JournalInner.state), self
      <| JournalInner.warm_addresses :=
        Impl_WarmAddresses.clear_coinbase_and_access_list self.(JournalInner.warm_addresses) |>
      <| JournalInner.state := [] |>
      <| JournalInner.logs := [] |>
      <| JournalInner.transient_storage := [] |>
      <| JournalInner.journal := [] |>
      <| JournalInner.depth := 0 |>
      <| JournalInner.transaction_id := 0 |>).

  Definition set_spec_id (self : JournalInner.t) (spec : SpecId.t) : JournalInner.t :=
    self <| JournalInner.spec := spec |>.

  Definition touch_account (journal : list JournalEntry.t) (address : Address.t)
      (account : Account.t) : list JournalEntry.t * Account.t :=
    if negb (Impl_Account.is_touched account) then
      (journal ++ [Impl_JournalEntry.account_touched address], Impl_Account.mark_touch account)
    else (journal, account).

  Definition touch (self : JournalInner.t) (address : Address.t) : JournalInner.t :=
    match EvmState.get address self.(JournalInner.state) with
    | None => self
    | Some account =>
      let '(journal, account) := touch_account self.(JournalInner.journal) address account in
      self <| JournalInner.journal := journal |>
        <| JournalInner.state := EvmState.insert address account self.(JournalInner.state) |>
    end.

  Definition account (self : JournalInner.t) (address : Address.t) : option Account.t :=
    EvmState.get address self.(JournalInner.state).

  Definition set_code_with_hash (self : JournalInner.t) (address : Address.t)
      (code : Bytecode.t) (hash : aliases.B256.t) : option JournalInner.t :=
    match account self address with
    | None => None
    | Some account =>
      let '(journal, account) := touch_account self.(JournalInner.journal) address account in
      let account := account <| Account.info := account.(Account.info)
        <| AccountInfo.code_hash := hash |> <| AccountInfo.code := Some code |> |> in
      Some (self <| JournalInner.state := EvmState.insert address account self.(JournalInner.state) |>
        <| JournalInner.journal := journal ++ [Impl_JournalEntry.code_changed address] |>)
    end.

  Definition set_code (self : JournalInner.t) (address : Address.t) (code : Bytecode.t)
      : option JournalInner.t :=
    match Impl_Bytecode.delegated_address code with
    | Some delegate =>
      if Z.eqb delegate.(Address.value) 0 then
        set_code_with_hash self address {| Bytecode.original_bytes := Impl_Bytes.copy_from_slice [] |} KECCAK_EMPTY
      else set_code_with_hash self address code (Impl_Bytecode.hash_slow code)
    | None => set_code_with_hash self address code (Impl_Bytecode.hash_slow code)
    end.

  Definition nonce_bump_journal_entry (self : JournalInner.t) (address : Address.t) : JournalInner.t :=
    self <| JournalInner.journal := self.(JournalInner.journal) ++
      [Impl_JournalEntry.nonce_bumped address] |>.

  Definition caller_accounting_journal_entry (self : JournalInner.t) (address : Address.t)
      (old_balance : aliases.U256.t) (bump_nonce : bool) : JournalInner.t :=
    let journal := self.(JournalInner.journal) ++
      [Impl_JournalEntry.balance_changed address old_balance;
       Impl_JournalEntry.account_touched address] in
    let journal := if bump_nonce then journal ++ [Impl_JournalEntry.nonce_bumped address]
      else journal in
    self <| JournalInner.journal := journal |>.

  Definition transfer_loaded (self : JournalInner.t) (from to : Address.t)
      (balance : aliases.U256.t) : option (option TransferError.t * JournalInner.t) :=
    if Z.eqb from.(Address.value) to.(Address.value) then
      match EvmState.get to self.(JournalInner.state) with
      | None => None
      | Some account => Some (
          if Z.gtb balance.(Uint.value) account.(Account.info).(AccountInfo.balance).(Uint.value)
          then Some TransferError.OutOfFunds else None, self)
      end
    else if Z.eqb balance.(Uint.value) 0 then
      match EvmState.get to self.(JournalInner.state) with
      | None => None
      | Some _ => Some (None, touch self to)
      end
    else match EvmState.get from self.(JournalInner.state) with
    | None => None
    | Some from_account =>
      let self := touch self from in
      match Impl_Uint.checked_sub from_account.(Account.info).(AccountInfo.balance) balance with
      | None => Some (Some TransferError.OutOfFunds, self)
      | Some from_balance_decr =>
        match EvmState.update from (fun account => account
          <| Account.info := account.(Account.info) <| AccountInfo.balance := from_balance_decr |> |>)
          self.(JournalInner.state) with
        | None => None
        | Some state =>
          let self := self <| JournalInner.state := state |> in
          match EvmState.get to self.(JournalInner.state) with
          | None => None
          | Some to_account =>
            let self := touch self to in
            match Impl_Uint.checked_add to_account.(Account.info).(AccountInfo.balance) balance with
            | None => Some (Some TransferError.OverflowPayment, self)
            | Some to_balance_incr =>
              match EvmState.update to (fun account => account
                <| Account.info := account.(Account.info) <| AccountInfo.balance := to_balance_incr |> |>)
                self.(JournalInner.state) with
              | None => None
              | Some state => Some (None, self <| JournalInner.state := state |>
                  <| JournalInner.journal := self.(JournalInner.journal) ++
                    [Impl_JournalEntry.balance_transfer from to balance] |>)
              end
            end
          end
        end
      end
    end.

  Definition checkpoint (self : JournalInner.t) : JournalCheckpoint.t * JournalInner.t :=
    let checkpoint := {|
      JournalCheckpoint.log_i := {| Integer.value := Z.of_nat (List.length self.(JournalInner.logs)) |};
      JournalCheckpoint.journal_i := {| Integer.value := Z.of_nat (List.length self.(JournalInner.journal)) |};
    |} in
    (checkpoint, self <| JournalInner.depth := self.(JournalInner.depth) +i 1 |>).

  Definition checkpoint_commit (self : JournalInner.t) : JournalInner.t :=
    self <| JournalInner.depth := BinOp.Saturating.sub self.(JournalInner.depth) 1 |>.

  Definition checkpoint_revert (self : JournalInner.t) (checkpoint : JournalCheckpoint.t)
      : option JournalInner.t :=
    let is_spurious_dragon_enabled := Impl_SpecId.is_enabled_in self.(JournalInner.spec) SpecId.SPURIOUS_DRAGON in
    let self := self <| JournalInner.depth := BinOp.Saturating.sub self.(JournalInner.depth) 1 |> in
    let log_i := checkpoint.(JournalCheckpoint.log_i).(Integer.value) in
    let self := if Z.ltb log_i (Z.of_nat (List.length self.(JournalInner.logs))) then
      self <| JournalInner.logs := List.firstn (Z.to_nat log_i) self.(JournalInner.logs) |> else self in
    let journal_i := checkpoint.(JournalCheckpoint.journal_i).(Integer.value) in
    if Z.ltb journal_i (Z.of_nat (List.length self.(JournalInner.journal))) then
      match revert_entries (List.rev (List.skipn (Z.to_nat journal_i) self.(JournalInner.journal)))
        self.(JournalInner.state) (Some self.(JournalInner.transient_storage)) is_spurious_dragon_enabled with
      | Some (state, Some transient_storage) => Some (self
          <| JournalInner.state := state |>
          <| JournalInner.transient_storage := transient_storage |>
          <| JournalInner.journal := List.firstn (Z.to_nat journal_i) self.(JournalInner.journal) |>)
      | _ => None
      end
    else Some self.

  Definition create_account_checkpoint (self : JournalInner.t) (caller target_address : Address.t)
      (balance : aliases.U256.t) (spec_id : SpecId.t)
      : option (Result.t JournalCheckpoint.t TransferError.t * JournalInner.t) :=
    let '(checkpoint, self) := checkpoint self in
    let reject error self := option_map (fun self => (Result.Err error, self))
      (checkpoint_revert self checkpoint) in
    match EvmState.get target_address self.(JournalInner.state) with
    | None => None
    | Some target_acc =>
      if negb (Z.eqb (FixedBytes.to_Z target_acc.(Account.info).(AccountInfo.code_hash))
          (FixedBytes.to_Z KECCAK_EMPTY)) || (target_acc.(Account.info).(AccountInfo.nonce) !=i 0)
      then reject TransferError.CreateCollision self else
      let '(is_created_globally, target_acc) := Impl_Account.mark_created_locally target_acc in
      let journal := self.(JournalInner.journal) ++
        [Impl_JournalEntry.account_created target_address is_created_globally] in
      let info := target_acc.(Account.info) <| AccountInfo.code := None |> in
      let info := if Impl_SpecId.is_enabled_in spec_id SpecId.SPURIOUS_DRAGON
        then info <| AccountInfo.nonce := 1 |> else info in
      let target_acc := target_acc <| Account.info := info |> in
      let '(journal, target_acc) := touch_account journal target_address target_acc in
      let self := self <| JournalInner.journal := journal |>
        <| JournalInner.state := EvmState.insert target_address target_acc self.(JournalInner.state) |> in
      match Impl_Uint.checked_add target_acc.(Account.info).(AccountInfo.balance) balance with
      | None => reject TransferError.OverflowPayment self
      | Some new_balance =>
        let target_acc := target_acc <| Account.info := target_acc.(Account.info)
          <| AccountInfo.balance := new_balance |> |> in
        let state := EvmState.insert target_address target_acc self.(JournalInner.state) in
        match EvmState.update caller (fun account => account <| Account.info := account.(Account.info)
          <| AccountInfo.balance := Impl_Uint.wrapping_sub account.(Account.info).(AccountInfo.balance) balance |> |>) state with
        | None => None
        | Some state => Some (Result.Ok checkpoint, self <| JournalInner.state := state |>
            <| JournalInner.journal := self.(JournalInner.journal) ++
              [Impl_JournalEntry.balance_transfer caller target_address balance] |>)
        end
      end
    end.

  (** The borrowed StateLoad<&Account> is an owned (account, is_cold) result.
      Database and journal mutations are returned separately. *)
  Definition load_account_optional {DB Error : Set} `{Database.C DB Error}
      (self : JournalInner.t) (db : DB) (address : Address.t) (load_code skip_cold_load : bool)
      : Result.t (Account.t * bool) (JournalLoadError.t Error) * DB * JournalInner.t :=
    let finish_load (account : Account.t) (is_cold : bool) (db : DB) :=
      let self := self <| JournalInner.state := EvmState.insert address account self.(JournalInner.state) |> in
      let self := if is_cold then self <| JournalInner.journal := self.(JournalInner.journal) ++
        [Impl_JournalEntry.account_warmed address] |> else self in
      let finish_code (result : Result.t Bytecode.t Error) (db : DB) :=
        match result with
        | Result.Err error => (Result.Err (JournalLoadError.DBError error), db, self)
        | Result.Ok code =>
          let account := account <| Account.info := account.(Account.info) <| AccountInfo.code := Some code |> |> in
          (Result.Ok (account, is_cold), db, self
            <| JournalInner.state := EvmState.insert address account self.(JournalInner.state) |>)
        end in
      match load_code, account.(Account.info).(AccountInfo.code) with
      | true, None =>
        if Z.eqb (FixedBytes.to_Z account.(Account.info).(AccountInfo.code_hash)) (FixedBytes.to_Z KECCAK_EMPTY)
        then finish_code (Result.Ok {| Bytecode.original_bytes := Impl_Bytes.copy_from_slice [] |}) db
        else let '(result, db) := Database.code_by_hash db account.(Account.info).(AccountInfo.code_hash) in
          finish_code result db
      | _, _ => (Result.Ok (account, is_cold), db, self)
      end in
    match EvmState.get address self.(JournalInner.state) with
    | Some account =>
      let is_cold := Impl_Account.is_cold_transaction_id account self.(JournalInner.transaction_id) in
      if is_cold then
        let should_be_cold := Impl_WarmAddresses.is_cold self.(JournalInner.warm_addresses) address in
        if should_be_cold && skip_cold_load then (Result.Err JournalLoadError.ColdLoadSkipped, db, self)
        else
          let '(_, account) := Impl_Account.mark_warm_with_transaction_id account self.(JournalInner.transaction_id) in
          let account := if Impl_Account.is_selfdestructed_locally account then
            Impl_Account.unmark_selfdestructed_locally (Impl_Account.selfdestruct account) else account in
          let account := Impl_Account.unmark_created_locally account in
          finish_load account should_be_cold db
      else finish_load account false db
    | None =>
      let is_cold := Impl_WarmAddresses.is_cold self.(JournalInner.warm_addresses) address in
      if is_cold && skip_cold_load then (Result.Err JournalLoadError.ColdLoadSkipped, db, self)
      else let '(result, db) := Database.basic db address in
        match result with
        | Result.Err error => (Result.Err (JournalLoadError.DBError error), db, self)
        | Result.Ok info =>
          let account := match info with
            | Some info => Impl_Default_for_Account.default <| Account.info := info |>
            | None => Impl_Account.new_not_existing self.(JournalInner.transaction_id)
            end in
          finish_load account is_cold db
        end
    end.

  Definition load_account_mut_optional_code {DB Error : Set} `{Database.C DB Error}
      (self : JournalInner.t) (db : DB) (address : Address.t) (load_code skip_cold_load : bool)
      : Result.t (JournaledAccount.t * bool) (JournalLoadError.t Error) * DB * JournalInner.t :=
    let '(result, db, self) := load_account_optional self db address load_code skip_cold_load in
    let result := match result with
      | Result.Err error => Result.Err error
      | Result.Ok (account, is_cold) => Result.Ok
          (Impl_JournaledAccount.new address account self.(JournalInner.journal), is_cold)
      end in
    (result, db, self).

  (** Return the mutations carried by Rust's two mutable borrows. The account
      must still be loaded, and no intervening journal mutation is permitted. *)
  Definition store_account (self : JournalInner.t) (account : JournaledAccount.t)
      : option JournalInner.t :=
    option_map (fun state => self <| JournalInner.state := state |>
      <| JournalInner.journal := account.(JournaledAccount.journal_entries) |>)
      (EvmState.update account.(JournaledAccount.address)
        (fun _ => account.(JournaledAccount.account)) self.(JournalInner.state)).

  Definition balance_incr {DB Error : Set} `{Database.C DB Error}
      (self : JournalInner.t) (db : DB) (address : Address.t) (balance : aliases.U256.t)
      : option (Result.t unit Error * DB * JournalInner.t) :=
    let '(result, db, self) := load_account_mut_optional_code self db address false false in
    match result with
    | Result.Err (JournalLoadError.DBError error) => Some (Result.Err error, db, self)
    | Result.Err JournalLoadError.ColdLoadSkipped => None
    | Result.Ok (account, _) =>
      let '(_, account) := Impl_JournaledAccount.incr_balance account balance in
      option_map (fun self => (Result.Ok tt, db, self)) (store_account self account)
    end.

  Definition load_account_delegated {DB Error : Set} `{Database.C DB Error}
      (self : JournalInner.t) (db : DB) (address : Address.t)
      : option (Result.t (StateLoad.t AccountLoad.t) Error * DB * JournalInner.t) :=
    let spec := self.(JournalInner.spec) in
    let is_eip7702_enabled := Impl_SpecId.is_enabled_in spec SpecId.PRAGUE in
    let '(result, db, self) := load_account_optional self db address is_eip7702_enabled false in
    match result with
    | Result.Err (JournalLoadError.DBError error) => Some (Result.Err error, db, self)
    | Result.Err JournalLoadError.ColdLoadSkipped => None
    | Result.Ok (account, is_cold) =>
      let account_load := {| StateLoad.data := {|
        AccountLoad.is_delegate_account_cold := None;
        AccountLoad.is_empty := Impl_Account.state_clear_aware_is_empty account spec |};
        StateLoad.is_cold := is_cold |} in
      let delegate := match account.(Account.info).(AccountInfo.code) with
        | Some code => Impl_Bytecode.delegated_address code
        | None => None
        end in
      match delegate with
      | None => Some (Result.Ok account_load, db, self)
      | Some address =>
        let '(result, db, self) := load_account_optional self db address true false in
        match result with
        | Result.Err (JournalLoadError.DBError error) => Some (Result.Err error, db, self)
        | Result.Err JournalLoadError.ColdLoadSkipped => None
        | Result.Ok (_, is_cold) => Some (Result.Ok (account_load
            <| StateLoad.data := account_load.(StateLoad.data)
              <| AccountLoad.is_delegate_account_cold := Some is_cold |> |>), db, self)
        end
      end
    end.

  Definition transfer {DB Error : Set} `{Database.C DB Error}
      (self : JournalInner.t) (db : DB) (from to : Address.t) (balance : aliases.U256.t)
      : option (Result.t (option TransferError.t) Error * DB * JournalInner.t) :=
    let '(result, db, self) := load_account_optional self db from false false in
    match result with
    | Result.Err (JournalLoadError.DBError error) => Some (Result.Err error, db, self)
    | Result.Err JournalLoadError.ColdLoadSkipped => None
    | Result.Ok _ =>
      let '(result, db, self) := load_account_optional self db to false false in
      match result with
      | Result.Err (JournalLoadError.DBError error) => Some (Result.Err error, db, self)
      | Result.Err JournalLoadError.ColdLoadSkipped => None
      | Result.Ok _ => option_map (fun '(result, self) => (Result.Ok result, db, self))
          (transfer_loaded self from to balance)
      end
    end.

  Definition selfdestruct {DB Error : Set} `{Database.C DB Error}
      (self : JournalInner.t) (db : DB) (address target : Address.t) (skip_cold_load : bool)
      : option (Result.t (StateLoad.t SelfDestructResult.t) (JournalLoadError.t Error) * DB * JournalInner.t) :=
    let spec := self.(JournalInner.spec) in
    let '(result, db, self) := load_account_optional self db target false skip_cold_load in
    match result with
    | Result.Err error => Some (Result.Err error, db, self)
    | Result.Ok (account_load, is_cold) =>
      let is_empty := Impl_Account.state_clear_aware_is_empty account_load spec in
      let moved := if negb (Z.eqb address.(Address.value) target.(Address.value)) then
        match EvmState.get address self.(JournalInner.state) with
        | None => None
        | Some acc =>
          let acc_balance := acc.(Account.info).(AccountInfo.balance) in
          let self := touch self target in
          option_map (fun state => self <| JournalInner.state := state |>)
            (EvmState.update target (fun account => account <| Account.info := account.(Account.info)
              <| AccountInfo.balance := Impl_Uint.wrapping_add account.(Account.info).(AccountInfo.balance) acc_balance |> |>)
              self.(JournalInner.state))
        end
        else Some self in
      match moved with
      | None => None
      | Some self =>
        match EvmState.get address self.(JournalInner.state) with
        | None => None
        | Some acc =>
          let balance := acc.(Account.info).(AccountInfo.balance) in
          let destroyed_status := if negb (Impl_Account.is_selfdestructed acc) then
              SelfdestructionRevertStatus.GloballySelfdestroyed
            else if negb (Impl_Account.is_selfdestructed_locally acc) then
              SelfdestructionRevertStatus.LocallySelfdestroyed
            else SelfdestructionRevertStatus.RepeatedSelfdestruction in
          let is_cancun_enabled := Impl_SpecId.is_enabled_in spec SpecId.CANCUN in
          let '(journal_entry, acc) :=
            if Impl_Account.is_created_locally acc || negb is_cancun_enabled then
              let '(_, acc) := Impl_Account.mark_selfdestructed_locally acc in
              let acc := acc <| Account.info := acc.(Account.info) <| AccountInfo.balance := {| Uint.value := 0 |} |> |> in
              (Some (Impl_JournalEntry.account_destroyed address target destroyed_status balance), acc)
            else if negb (Z.eqb address.(Address.value) target.(Address.value)) then
              let acc := acc <| Account.info := acc.(Account.info) <| AccountInfo.balance := {| Uint.value := 0 |} |> |> in
              (Some (Impl_JournalEntry.balance_transfer address target balance), acc)
            else (None, acc) in
          let self := self <| JournalInner.state := EvmState.insert address acc self.(JournalInner.state) |> in
          let self := match journal_entry with
            | Some entry => self <| JournalInner.journal := self.(JournalInner.journal) ++ [entry] |>
            | None => self
            end in
          Some (Result.Ok {| StateLoad.data := {|
            SelfDestructResult.had_value := negb (Z.eqb balance.(Uint.value) 0);
            SelfDestructResult.target_exists := negb is_empty;
            SelfDestructResult.previously_destroyed := match destroyed_status with
              | SelfdestructionRevertStatus.RepeatedSelfdestruction => true
              | _ => false
              end;
          |}; StateLoad.is_cold := is_cold |}, db, self)
        end
      end
    end.

  Definition sload {DB Error : Set} `{Database.C DB Error}
      (self : JournalInner.t) (db : DB) (address : Address.t) (key : aliases.U256.t)
      (skip_cold_load : bool)
      : option (Result.t (StateLoad.t aliases.U256.t) (JournalLoadError.t Error) * DB * JournalInner.t) :=
    match EvmState.get address self.(JournalInner.state) with
    | None => None
    | Some account =>
      let is_newly_created := Impl_Account.is_created account in
      let finish (slot : EvmStorageSlot.t) (is_cold : bool) (db : DB) :=
        let account := account <| Account.storage := EvmStorage.insert key slot account.(Account.storage) |> in
        let self := self <| JournalInner.state := EvmState.insert address account self.(JournalInner.state) |> in
        let self := if is_cold then self <| JournalInner.journal := self.(JournalInner.journal) ++
          [Impl_JournalEntry.storage_warmed address key] |> else self in
        Some (Result.Ok {| StateLoad.data := slot.(EvmStorageSlot.present_value); StateLoad.is_cold := is_cold |}, db, self) in
      match EvmStorage.get key account.(Account.storage) with
      | Some slot =>
        let is_cold := Impl_EvmStorageSlot.is_cold_transaction_id slot self.(JournalInner.transaction_id) in
        if skip_cold_load && is_cold then Some (Result.Err JournalLoadError.ColdLoadSkipped, db, self)
        else let '(_, slot) := Impl_EvmStorageSlot.mark_warm_with_transaction_id slot self.(JournalInner.transaction_id) in
          finish slot is_cold db
      | None =>
        let is_cold := negb (Impl_WarmAddresses.is_storage_warm self.(JournalInner.warm_addresses) address key) in
        if is_cold && skip_cold_load then Some (Result.Err JournalLoadError.ColdLoadSkipped, db, self)
        else let '(result, db) := if is_newly_created then (Result.Ok {| Uint.value := 0 |}, db)
          else Database.storage db address key in
          match result with
          | Result.Err error => Some (Result.Err (JournalLoadError.DBError error), db, self)
          | Result.Ok value => finish (Impl_EvmStorageSlot.new value self.(JournalInner.transaction_id)) is_cold db
          end
      end
    end.

  Definition sstore {DB Error : Set} `{Database.C DB Error}
      (self : JournalInner.t) (db : DB) (address : Address.t) (key new : aliases.U256.t)
      (skip_cold_load : bool)
      : option (Result.t (StateLoad.t SStoreResult.t) (JournalLoadError.t Error) * DB * JournalInner.t) :=
    match sload self db address key skip_cold_load with
    | None => None
    | Some (Result.Err error, db, self) => Some (Result.Err error, db, self)
    | Some (Result.Ok present, db, self) =>
      match EvmState.get address self.(JournalInner.state) with
      | None => None
      | Some account =>
        match EvmStorage.get key account.(Account.storage) with
        | None => None
        | Some slot =>
          let output := {| StateLoad.data := {|
            SStoreResult.original_value := slot.(EvmStorageSlot.original_value);
            SStoreResult.present_value := present.(StateLoad.data);
            SStoreResult.new_value := new;
          |}; StateLoad.is_cold := present.(StateLoad.is_cold) |} in
          if Z.eqb present.(StateLoad.data).(Uint.value) new.(Uint.value)
          then Some (Result.Ok output, db, self) else
          let self := self <| JournalInner.journal := self.(JournalInner.journal) ++
            [Impl_JournalEntry.storage_changed address key present.(StateLoad.data)] |> in
          let slot := slot <| EvmStorageSlot.present_value := new |> in
          let account := account <| Account.storage := EvmStorage.insert key slot account.(Account.storage) |> in
          Some (Result.Ok output, db, self
            <| JournalInner.state := EvmState.insert address account self.(JournalInner.state) |>)
        end
      end
    end.

  Definition tload (self : JournalInner.t) (address : Address.t) (key : aliases.U256.t) : aliases.U256.t :=
    match TransientStorage.get (address, key) self.(JournalInner.transient_storage) with
    | Some value => value
    | None => {| Uint.value := 0 |}
    end.

  Definition tstore (self : JournalInner.t) (address : Address.t) (key new : aliases.U256.t)
      : JournalInner.t :=
    let storage := self.(JournalInner.transient_storage) in
    let '(had_value, storage) := if Z.eqb new.(Uint.value) 0 then
        (TransientStorage.get (address, key) storage, TransientStorage.remove (address, key) storage)
      else
        let previous_value := tload self address key in
        (if negb (Z.eqb previous_value.(Uint.value) new.(Uint.value)) then Some previous_value else None,
          TransientStorage.insert (address, key) new storage) in
    let self := self <| JournalInner.transient_storage := storage |> in
    match had_value with
    | Some had_value => self <| JournalInner.journal := self.(JournalInner.journal) ++
        [Impl_JournalEntry.transient_storage_changed address key had_value] |>
    | None => self
    end.

  Definition log (self : JournalInner.t) (log : Log.t LogData.t) : JournalInner.t :=
    self <| JournalInner.logs := self.(JournalInner.logs) ++ [log] |>.
End Impl_JournalInner.
