From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import bytes.links.bytes.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_bytecode.simulate.bytecode.
Require Import ruint.links.lib.
Require Import lib.simulate.lib.
Require Import revm.revm_state.simulate.account_info.
Require Import revm.revm_interpreter.tests.stateful_host.

Require Import simulate.RocqOfRust.
Require Import revm.revm_context_interface.links.journaled_state.

Import ListNotations.
Open Scope Z_scope.

(** Concrete state adapter for journaled_state/account.rs. This is not yet
    a correspondence proof for the native journal. *)
Module AccountAdapter.
  Definition to_info (account : StatefulHost.Account.t) : AccountInfo.t := {|
    AccountInfo.balance := StatefulHost.rust_word account.(StatefulHost.Account.balance);
    AccountInfo.nonce := {| Integer.value := account.(StatefulHost.Account.nonce) |};
    AccountInfo.code_hash := FixedBytes.from_Z account.(StatefulHost.Account.code_hash);
    AccountInfo.code := Some {| Bytecode.original_bytes := Impl_Bytes.copy_from_slice
      (List.map StatefulHost.rust_byte account.(StatefulHost.Account.code)) |}
  |}.

  Definition with_info (account : StatefulHost.Account.t) (info : AccountInfo.t)
      : StatefulHost.Account.t :=
    account
      <| StatefulHost.Account.balance := info.(AccountInfo.balance).(Uint.value) |>
      <| StatefulHost.Account.nonce := info.(AccountInfo.nonce).(Integer.value) |>
      <| StatefulHost.Account.code_hash := FixedBytes.to_Z info.(AccountInfo.code_hash) |>
      <| StatefulHost.Account.code := match info.(AccountInfo.code) with
        | None => []
        | Some code => List.map Integer.value (Impl_Bytecode.original_byte_slice code)
        end |>.
End AccountAdapter.

Module JournaledAccount.
  Definition bump_nonce (authority : Address.t) (state : StatefulHost.t)
      : bool * StatefulHost.t :=
    let state := StatefulHost.touch_account state authority.(Address.value) in
    let account := match StatefulHost.find_account authority.(Address.value)
        state.(StatefulHost.accounts) with
      | Some account => account
      | None => StatefulHost.empty_account authority.(Address.value)
      end in
    let info := AccountAdapter.to_info account in
    let nonce := info.(AccountInfo.nonce) in
    match BinOp.Checked.add nonce {| Integer.value := 1 |} with
    | None => (false, state)
    | Some nonce =>
      let state := StatefulHost.with_accounts state
        (StatefulHost.update_account authority.(Address.value)
          (fun account => AccountAdapter.with_info account
            (Impl_AccountInfo.set_nonce (AccountAdapter.to_info account) nonce))
          state.(StatefulHost.accounts)) in
      (true, StatefulHost.append_change state
        (StatefulHost.Change.Nonce authority.(Address.value) nonce.(Integer.value)))
    end.

  Definition set_code (authority : Address.t) (code_hash : aliases.B256.t)
      (code : Bytecode.t) (state : StatefulHost.t) : StatefulHost.t :=
    let state := StatefulHost.touch_account state authority.(Address.value) in
    let state := StatefulHost.with_accounts state
      (StatefulHost.update_account authority.(Address.value)
        (fun account =>
          let info := AccountAdapter.to_info account in
          let info := Impl_AccountInfo.set_code_hash info code_hash in
          let info := Impl_AccountInfo.set_code info code in
          AccountAdapter.with_info account info)
        state.(StatefulHost.accounts)) in
    let code := List.map Integer.value (Impl_Bytecode.original_byte_slice code) in
    StatefulHost.append_change state
      (StatefulHost.Change.Code authority.(Address.value) code).

  Definition delegate (authority address : Address.t) (state : StatefulHost.t)
      : StatefulHost.t :=
    let code := if address.(Address.value) =? 0 then [] else
      [239; 1; 0] ++ List.map
        (fun index => (address.(Address.value) / 256 ^ Z.of_nat (19 - index)) mod 256)
        (List.seq 0 20) in
    let bytecode : Bytecode.t := {|
      Bytecode.original_bytes := Impl_Bytes.copy_from_slice
        (List.map StatefulHost.rust_byte code)
    |} in
    let state := StatefulHost.touch_account state authority.(Address.value) in
    let state := set_code authority (Impl_Bytecode.hash_slow bytecode) bytecode state in
    snd (bump_nonce authority state).
End JournaledAccount.
