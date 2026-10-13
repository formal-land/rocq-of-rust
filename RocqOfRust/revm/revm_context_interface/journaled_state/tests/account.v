From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.journaled_state.simulate.account.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import simulate.RocqOfRust.
Require Import revm.revm_state.simulate.account_info.
Require Import revm.revm_context_interface.links.journaled_state.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition authority := StatefulHost.rust_address 42.

  Definition host (nonce : Z) := StatefulHost.make
    (add11_input <| StatefulHost.Input.state :=
      [(StatefulHost.empty_account 42) <| StatefulHost.Account.nonce := nonce |>] |>).

  Definition nonce (state : StatefulHost.t) :=
    match StatefulHost.find_account 42 state.(StatefulHost.accounts) with
    | Some account => Some account.(StatefulHost.Account.nonce)
    | None => None
    end.

  Lemma bump_nonce_reaches_u64_max :
    let '(success, state) := JournaledAccount.bump_nonce authority (host (2 ^ 64 - 2)) in
    (success, nonce state, StatefulHost.observe_state_changes state) =
    (true, Some (2 ^ 64 - 1), [StatefulHost.Change.Nonce 42 (2 ^ 64 - 1)]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma bump_nonce_overflow_still_touches_without_journal_entry :
    let '(success, state) := JournaledAccount.bump_nonce authority (host (2 ^ 64 - 1)) in
    (success, nonce state, state.(StatefulHost.touched_accounts),
      StatefulHost.observe_state_changes state) =
    (false, Some (2 ^ 64 - 1), [42], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma set_code_preserves_nonce_and_records_code :
    let code : Bytecode.t := {| Bytecode.original_bytes :=
      Impl_Bytes.copy_from_slice (List.map StatefulHost.rust_byte [96; 1]) |} in
    let state := JournaledAccount.set_code authority (FixedBytes.from_Z 99) code (host 7) in
    (nonce state, state.(StatefulHost.touched_accounts),
      StatefulHost.observe_state_changes state) =
    (Some 7, [42], [StatefulHost.Change.Code 42 [96; 1]]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegate_records_code_before_nonce_and_touches_once :
    let state := JournaledAccount.delegate authority (StatefulHost.rust_address 0) (host 7) in
    (nonce state, state.(StatefulHost.touched_accounts),
      StatefulHost.observe_state_changes state) =
    (Some 8, [42], [StatefulHost.Change.Code 42 []; StatefulHost.Change.Nonce 42 8]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma set_code_recomputes_supplied_hash :
    let code : Bytecode.t := {| Bytecode.original_bytes :=
      Impl_Bytes.copy_from_slice [] |} in
    let state := JournaledAccount.set_code authority (FixedBytes.from_Z 99) code (host 7) in
    match StatefulHost.find_account 42 state.(StatefulHost.accounts) with
    | Some account => account.(StatefulHost.Account.code_hash)
    | None => 0
    end = StatefulHost.empty_code_hash.
  Proof. vm_compute. reflexivity. Qed.

  Lemma set_code_hash_clears_cached_code (info : AccountInfo.t) (hash : aliases.B256.t) :
    (Impl_AccountInfo.set_code_hash info hash).(AccountInfo.code) = None.
  Proof. reflexivity. Qed.

  Lemma set_nonce_preserves_other_fields (info : AccountInfo.t) (value : u64) :
    let updated := Impl_AccountInfo.set_nonce info value in
    (updated.(AccountInfo.nonce), updated.(AccountInfo.balance),
      updated.(AccountInfo.code), updated.(AccountInfo.code_hash)) =
    (value, info.(AccountInfo.balance), info.(AccountInfo.code), info.(AccountInfo.code_hash)).
  Proof. reflexivity. Qed.
  Lemma nonce_update_preserves_account_data :
    let account := (StatefulHost.empty_account 42)
      <| StatefulHost.Account.balance := 2 ^ 256 - 1 |>
      <| StatefulHost.Account.nonce := 7 |>
      <| StatefulHost.Account.code := [96; 1] |>
      <| StatefulHost.Account.code_hash := 99 |>
      <| StatefulHost.Account.storage := [(3, 5)] |>
      <| StatefulHost.Account.transient_storage := [(4, 6)] |> in
    let state := StatefulHost.make
      (add11_input <| StatefulHost.Input.state := [account] |>) in
    let '(success, state) := JournaledAccount.bump_nonce authority state in
    (success, StatefulHost.find_account 42 state.(StatefulHost.accounts)) =
    (true, Some (account <| StatefulHost.Account.nonce := 8 |>)).
  Proof. vm_compute. reflexivity. Qed.
End Test.
