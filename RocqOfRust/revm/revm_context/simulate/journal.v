Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import core.links.result.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context.journal.simulate.warm_addresses.
Require Import revm.revm_context_interface.journaled_state.simulate.account.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.types.

Module Journal.
  Record t (DB : Set) : Set := {
    database : DB;
    inner : JournalInner.t;
  }.

  Arguments database {DB}.

  Arguments inner {DB}.
End Journal.

Module Impl_Journal.
  Definition new {DB : Set} (database : DB) : Journal.t DB := {|
    Journal.database := database;
    Journal.inner := Impl_JournalInner.new;
  |}.

  Definition new_with_inner {DB : Set} (database : DB) (inner : JournalInner.t) : Journal.t DB := {|
    Journal.database := database;
    Journal.inner := inner;
  |}.

  Definition into_init {DB : Set} (self : Journal.t DB) : JournalInner.t := self.(Journal.inner).

  Definition to_inner {DB : Set} (self : Journal.t DB) : JournalInner.t := self.(Journal.inner).

  (** Reassemble the two mutable receivers returned by the inner operation. *)
  Definition finish {DB A : Set} (result : A * DB * JournalInner.t) : A * Journal.t DB :=
    let '(result, database, inner) := result in (result, new_with_inner database inner).

  (** [None] represents Rust's unreachable cold-skip unwrap, never a DB error. *)
  Definition unwrap_db_error {A Error : Set} (result : Result.t A (JournalLoadError.t Error))
      : option (Result.t A Error) :=
    match result with
    | Result.Ok value => Some (Result.Ok value)
    | Result.Err (JournalLoadError.DBError error) => Some (Result.Err error)
    | Result.Err JournalLoadError.ColdLoadSkipped => None
    end.

  Definition sload_skip_cold_load {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (address : Address.t) (key : aliases.U256.t) (skip_cold_load : bool) :=
    option_map finish (Impl_JournalInner.sload self.(Journal.inner) self.(Journal.database)
      address key skip_cold_load).

  Definition sload {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (address : Address.t) (key : aliases.U256.t) :=
    match sload_skip_cold_load self address key false with
    | None => None
    | Some (result, self) => option_map (fun result => (result, self)) (unwrap_db_error result)
    end.

  Definition sstore_skip_cold_load {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (address : Address.t) (key value : aliases.U256.t) (skip_cold_load : bool) :=
    option_map finish (Impl_JournalInner.sstore self.(Journal.inner) self.(Journal.database)
      address key value skip_cold_load).

  Definition sstore {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (address : Address.t) (key value : aliases.U256.t) :=
    match sstore_skip_cold_load self address key value false with
    | None => None
    | Some (result, self) => option_map (fun result => (result, self)) (unwrap_db_error result)
    end.

  Definition tload {DB : Set} (self : Journal.t DB) (address : Address.t) (key : aliases.U256.t) :=
    Impl_JournalInner.tload self.(Journal.inner) address key.

  Definition tstore {DB : Set} (self : Journal.t DB) (address : Address.t) (key value : aliases.U256.t) :=
    self <| Journal.inner := Impl_JournalInner.tstore self.(Journal.inner) address key value |>.

  Definition log {DB : Set} (self : Journal.t DB) (log : Log.t LogData.t) :=
    self <| Journal.inner := Impl_JournalInner.log self.(Journal.inner) log |>.

  Definition logs {DB : Set} (self : Journal.t DB) := self.(Journal.inner).(JournalInner.logs).

  Definition take_logs {DB : Set} (self : Journal.t DB) :=
    let '(logs, inner) := Impl_JournalInner.take_logs self.(Journal.inner) in
    (logs, self <| Journal.inner := inner |>).

  Definition selfdestruct {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (address target : Address.t) (skip_cold_load : bool) :=
    option_map finish (Impl_JournalInner.selfdestruct self.(Journal.inner) self.(Journal.database)
      address target skip_cold_load).

  Definition warm_access_list {DB : Set} (self : Journal.t DB)
      (access_list : list (Address.t * list aliases.U256.t)) :=
    self <| Journal.inner := self.(Journal.inner) <| JournalInner.warm_addresses :=
      Impl_WarmAddresses.set_access_list self.(Journal.inner).(JournalInner.warm_addresses) access_list |> |>.

  Definition warm_coinbase_account {DB : Set} (self : Journal.t DB) (address : Address.t) :=
    self <| Journal.inner := self.(Journal.inner) <| JournalInner.warm_addresses :=
      Impl_WarmAddresses.set_coinbase self.(Journal.inner).(JournalInner.warm_addresses) address |> |>.

  Definition warm_precompiles {DB : Set} (self : Journal.t DB) (precompiles : list Address.t) :=
    self <| Journal.inner := self.(Journal.inner) <| JournalInner.warm_addresses :=
      Impl_WarmAddresses.set_precompile_addresses self.(Journal.inner).(JournalInner.warm_addresses) precompiles |> |>.

  Definition precompile_addresses {DB : Set} (self : Journal.t DB) :=
    self.(Journal.inner).(JournalInner.warm_addresses).(WarmAddresses.precompile_set).

  Definition depth {DB : Set} (self : Journal.t DB) : usize := self.(Journal.inner).(JournalInner.depth).

  Definition set_spec_id {DB : Set} (self : Journal.t DB) (spec_id : SpecId.t) :=
    self <| Journal.inner := Impl_JournalInner.set_spec_id self.(Journal.inner) spec_id |>.

  Definition transfer {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (from to : Address.t) (balance : aliases.U256.t) :=
    option_map finish (Impl_JournalInner.transfer self.(Journal.inner) self.(Journal.database) from to balance).

  Definition transfer_loaded {DB : Set} (self : Journal.t DB) (from to : Address.t) (balance : aliases.U256.t) :=
    option_map (fun '(result, inner) => (result, self <| Journal.inner := inner |>))
      (Impl_JournalInner.transfer_loaded self.(Journal.inner) from to balance).

  Definition touch_account {DB : Set} (self : Journal.t DB) (address : Address.t) :=
    self <| Journal.inner := Impl_JournalInner.touch self.(Journal.inner) address |>.

  Definition caller_accounting_journal_entry {DB : Set} (self : Journal.t DB)
      (address : Address.t) (old_balance : aliases.U256.t) (bump_nonce : bool) :=
    self <| Journal.inner := Impl_JournalInner.caller_accounting_journal_entry
      self.(Journal.inner) address old_balance bump_nonce |>.

  Definition balance_incr {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (address : Address.t) (balance : aliases.U256.t) :=
    option_map finish (Impl_JournalInner.balance_incr self.(Journal.inner) self.(Journal.database) address balance).

  Definition nonce_bump_journal_entry {DB : Set} (self : Journal.t DB) (address : Address.t) :=
    self <| Journal.inner := Impl_JournalInner.nonce_bump_journal_entry self.(Journal.inner) address |>.

  Definition load_account {DB Error : Set} `{Database.C DB Error} (self : Journal.t DB) (address : Address.t) :=
    let '(result, self) := finish (Impl_JournalInner.load_account_optional
      self.(Journal.inner) self.(Journal.database) address false false) in
    option_map (fun result => (result, self)) (unwrap_db_error result).

  Definition load_account_mut_optional_code {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (address : Address.t) (load_code : bool) :=
    let '(result, self) := finish (Impl_JournalInner.load_account_mut_optional_code
      self.(Journal.inner) self.(Journal.database) address load_code false) in
    option_map (fun result => (result, self)) (unwrap_db_error result).

  Definition store_account {DB : Set} (self : Journal.t DB) (account : JournaledAccount.t) :=
    option_map (fun inner => self <| Journal.inner := inner |>)
      (Impl_JournalInner.store_account self.(Journal.inner) account).

  Definition load_account_with_code {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (address : Address.t) :=
    let '(result, self) := finish (Impl_JournalInner.load_account_optional
      self.(Journal.inner) self.(Journal.database) address true false) in
    option_map (fun result => (result, self)) (unwrap_db_error result).

  Definition load_account_delegated {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (address : Address.t) :=
    option_map finish (Impl_JournalInner.load_account_delegated self.(Journal.inner) self.(Journal.database) address).

  Definition load_account_info_skip_cold_load {DB Error : Set} `{Database.C DB Error}
      (self : Journal.t DB) (address : Address.t) (load_code skip_cold_load : bool) :=
    let spec := self.(Journal.inner).(JournalInner.spec) in
    let '(result, self) := finish (Impl_JournalInner.load_account_optional
      self.(Journal.inner) self.(Journal.database) address load_code skip_cold_load) in
    let result := match result with
      | Result.Err error => Result.Err error
      | Result.Ok (account, is_cold) => Result.Ok {|
          AccountInfoLoad.account := Cow.Owned account.(Account.info);
          AccountInfoLoad.is_cold := is_cold;
          AccountInfoLoad.is_empty := Impl_Account.state_clear_aware_is_empty account spec |}
      end in
    (result, self).

  Definition checkpoint {DB : Set} (self : Journal.t DB) :=
    let '(checkpoint, inner) := Impl_JournalInner.checkpoint self.(Journal.inner) in
    (checkpoint, self <| Journal.inner := inner |>).

  Definition checkpoint_commit {DB : Set} (self : Journal.t DB) :=
    self <| Journal.inner := Impl_JournalInner.checkpoint_commit self.(Journal.inner) |>.

  Definition checkpoint_revert {DB : Set} (self : Journal.t DB) (checkpoint : JournalCheckpoint.t) :=
    option_map (fun inner => self <| Journal.inner := inner |>)
      (Impl_JournalInner.checkpoint_revert self.(Journal.inner) checkpoint).

  Definition set_code_with_hash {DB : Set} (self : Journal.t DB) (address : Address.t)
      (code : Bytecode.t) (hash : aliases.B256.t) :=
    option_map (fun inner => self <| Journal.inner := inner |>)
      (Impl_JournalInner.set_code_with_hash self.(Journal.inner) address code hash).

  Definition create_account_checkpoint {DB : Set} (self : Journal.t DB) (caller address : Address.t)
      (balance : aliases.U256.t) (spec_id : SpecId.t) :=
    option_map (fun '(result, inner) => (result, self <| Journal.inner := inner |>))
      (Impl_JournalInner.create_account_checkpoint self.(Journal.inner) caller address balance spec_id).

  Definition commit_tx {DB : Set} (self : Journal.t DB) :=
    self <| Journal.inner := Impl_JournalInner.commit_tx self.(Journal.inner) |>.

  Definition discard_tx {DB : Set} (self : Journal.t DB) :=
    option_map (fun inner => self <| Journal.inner := inner |>) (Impl_JournalInner.discard_tx self.(Journal.inner)).

  Definition finalize {DB : Set} (self : Journal.t DB) :=
    let '(state, inner) := Impl_JournalInner.finalize self.(Journal.inner) in
    (state, self <| Journal.inner := inner |>).
End Impl_Journal.
