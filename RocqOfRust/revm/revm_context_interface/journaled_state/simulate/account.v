From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.utils.simulate.keccak256.
Require Import lib.simulate.lib.
Require Import revm.revm_interpreter.tests.stateful_host.

Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

(** Concrete state adapter for journaled_state/account.rs. This is not yet
    a correspondence proof for the native journal. *)
Module JournaledAccount.
  Definition delegate (authority address : Address.t) (state : StatefulHost.t)
      : StatefulHost.t :=
    let code := if address.(Address.value) =? 0 then [] else
      [239; 1; 0] ++ List.map
        (fun index => (address.(Address.value) / 256 ^ Z.of_nat (19 - index)) mod 256)
        (List.seq 0 20) in
    let hash := List.fold_left (fun value byte => 256 * value + byte)
      (Keccak256.hash code) 0 in
    let state := StatefulHost.touch_account state authority.(Address.value) in
    let account := match StatefulHost.find_account authority.(Address.value)
        state.(StatefulHost.accounts) with
      | Some account => account
      | None => StatefulHost.empty_account authority.(Address.value)
      end in
    (* JournaledAccount::bump_nonce uses checked_add and leaves MAX unchanged. *)
    let nonce : u64 := {| Integer.value := account.(StatefulHost.Account.nonce) |} in
    let nonce := match BinOp.Checked.add nonce {| Integer.value := 1 |} with
      | Some nonce => nonce
      | None => nonce
      end in
    let state := StatefulHost.with_accounts state
      (StatefulHost.update_account authority.(Address.value)
        (fun account => account
          <| StatefulHost.Account.code := code |>
          <| StatefulHost.Account.code_hash := hash |>
          <| StatefulHost.Account.nonce := nonce.(Integer.value) |>)
        state.(StatefulHost.accounts)) in
    let state := StatefulHost.append_change state
      (StatefulHost.Change.Code authority.(Address.value) code) in
    if account.(StatefulHost.Account.nonce) =? nonce.(Integer.value) then state else
      StatefulHost.append_change state
        (StatefulHost.Change.Nonce authority.(Address.value) nonce.(Integer.value)).
End JournaledAccount.
