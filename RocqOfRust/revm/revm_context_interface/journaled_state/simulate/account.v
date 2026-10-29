Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import core.links.array.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_bytecode.simulate.bytecode.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.journaled_state.simulate.entry.
Require Import revm.revm_primitives.simulate.lib.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.account_info.
Require Import ruint.links.lib.
Require Import ruint.simulate.add.

Import ListNotations.

Module JournaledAccount.
  (** The two Rust mutable borrows are carried in and returned with [self]. *)
  Record t : Set := {
    address : Address.t;
    account : Account.t;
    journal_entries : list JournalEntry.t;
  }.
End JournaledAccount.

Module Impl_JournaledAccount.
  Definition into_account_ref (self : JournaledAccount.t) : Account.t :=
    self.(JournaledAccount.account).

  Definition new (address : Address.t) (account : Account.t) (journal_entries : list JournalEntry.t)
      : JournaledAccount.t := {|
    JournaledAccount.address := address;
    JournaledAccount.account := account;
    JournaledAccount.journal_entries := journal_entries;
  |}.

  Definition balance (self : JournaledAccount.t) : aliases.U256.t :=
    self.(JournaledAccount.account).(Account.info).(AccountInfo.balance).

  Definition nonce (self : JournaledAccount.t) : u64 :=
    self.(JournaledAccount.account).(Account.info).(AccountInfo.nonce).

  Definition code_hash (self : JournaledAccount.t) : aliases.B256.t :=
    self.(JournaledAccount.account).(Account.info).(AccountInfo.code_hash).

  Definition code (self : JournaledAccount.t) : option Bytecode.t :=
    self.(JournaledAccount.account).(Account.info).(AccountInfo.code).

  Definition touch (self : JournaledAccount.t) : JournaledAccount.t :=
    if negb (Impl_Account.is_touched self.(JournaledAccount.account)) then
      self <| JournaledAccount.account := Impl_Account.mark_touch self.(JournaledAccount.account) |>
        <| JournaledAccount.journal_entries := self.(JournaledAccount.journal_entries) ++
          [Impl_JournalEntry.account_touched self.(JournaledAccount.address)] |>
    else self.

  Definition unsafe_mark_cold (self : JournaledAccount.t) : JournaledAccount.t :=
    self <| JournaledAccount.account := Impl_Account.mark_cold self.(JournaledAccount.account) |>.

  Definition set_balance (self : JournaledAccount.t) (balance : aliases.U256.t) : JournaledAccount.t :=
    let self := touch self in
    let account := self.(JournaledAccount.account) in
    if negb (Z.eqb account.(Account.info).(AccountInfo.balance).(Uint.value) balance.(Uint.value)) then
      self <| JournaledAccount.journal_entries := self.(JournaledAccount.journal_entries) ++
        [Impl_JournalEntry.balance_changed self.(JournaledAccount.address) account.(Account.info).(AccountInfo.balance)] |>
        <| JournaledAccount.account := account
          <| Account.info := Impl_AccountInfo.set_balance account.(Account.info) balance |> |>
    else self.

  Definition incr_balance (self : JournaledAccount.t) (balance : aliases.U256.t)
      : bool * JournaledAccount.t :=
    let self := touch self in
    match Impl_Uint.checked_add self.(JournaledAccount.account).(Account.info).(AccountInfo.balance) balance with
    | None => (false, self)
    | Some balance => (true, set_balance self balance)
    end.

  Definition decr_balance (self : JournaledAccount.t) (balance : aliases.U256.t)
      : bool * JournaledAccount.t :=
    let self := touch self in
    match Impl_Uint.checked_sub self.(JournaledAccount.account).(Account.info).(AccountInfo.balance) balance with
    | None => (false, self)
    | Some balance => (true, set_balance self balance)
    end.

  Definition bump_nonce (self : JournaledAccount.t) : bool * JournaledAccount.t :=
    let self := touch self in
    let account := self.(JournaledAccount.account) in
    match BinOp.Checked.add account.(Account.info).(AccountInfo.nonce) 1 with
    | None => (false, self)
    | Some nonce => (true, self
        <| JournaledAccount.account := account <| Account.info := Impl_AccountInfo.set_nonce account.(Account.info) nonce |> |>
        <| JournaledAccount.journal_entries := self.(JournaledAccount.journal_entries) ++
          [Impl_JournalEntry.nonce_bumped self.(JournaledAccount.address)] |>)
    end.

  Definition set_nonce (self : JournaledAccount.t) (nonce : u64) : JournaledAccount.t :=
    let self := touch self in
    let account := self.(JournaledAccount.account) in
    let previous_nonce := account.(Account.info).(AccountInfo.nonce) in
    self <| JournaledAccount.account := account <| Account.info := Impl_AccountInfo.set_nonce account.(Account.info) nonce |> |>
      <| JournaledAccount.journal_entries := self.(JournaledAccount.journal_entries) ++
        [Impl_JournalEntry.nonce_changed self.(JournaledAccount.address) previous_nonce] |>.

  Definition unsafe_set_nonce (self : JournaledAccount.t) (nonce : u64) : JournaledAccount.t :=
    let account := self.(JournaledAccount.account) in
    self <| JournaledAccount.account := account <| Account.info := Impl_AccountInfo.set_nonce account.(Account.info) nonce |> |>.

  Definition set_code (self : JournaledAccount.t) (code_hash : aliases.B256.t) (code : Bytecode.t)
      : JournaledAccount.t :=
    let self := touch self in
    let account := self.(JournaledAccount.account) in
    let info := Impl_AccountInfo.set_code_hash account.(Account.info) code_hash in
    let info := Impl_AccountInfo.set_code info code in
    self <| JournaledAccount.account := account <| Account.info := info |> |>
      <| JournaledAccount.journal_entries := self.(JournaledAccount.journal_entries) ++
        [Impl_JournalEntry.code_changed self.(JournaledAccount.address)] |>.

  Definition set_code_and_hash_slow (self : JournaledAccount.t) (code : Bytecode.t) : JournaledAccount.t :=
    let code_hash := Impl_Bytecode.hash_slow code in
    set_code self code_hash code.

  Definition delegate (self : JournaledAccount.t) (address : Address.t) : JournaledAccount.t :=
    let '(bytecode, hash) := if Z.eqb address.(Address.value) 0 then
      ({| Bytecode.original_bytes := Impl_Bytes.copy_from_slice [] |}, KECCAK_EMPTY)
      else
        let bytecode := {| Bytecode.original_bytes := Impl_Bytes.copy_from_slice
          ([(239 : u8); (1 : u8); (0 : u8)] ++ ArrayPairs.to_list (FixedBytes.bytes_be 20 address.(Address.value))) |} in
        (bytecode, Impl_Bytecode.hash_slow bytecode) in
    let self := touch self in
    let self := set_code self hash bytecode in
    snd (bump_nonce self).
End Impl_JournaledAccount.
