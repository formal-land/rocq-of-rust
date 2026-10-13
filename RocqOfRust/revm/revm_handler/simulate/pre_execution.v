From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import links.M.
Require Import ruint.links.lib.

Require Import lib.simulate.lib.
Require Import revm.revm_context_interface.journaled_state.simulate.account.
Require Import revm.revm_context_interface.transaction.simulate.eip7702.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.simulate.eip7702.

Import ListNotations.
Open Scope Z_scope.

(** pre_execution.rs::apply_eip7702_auth_list, with the transaction/config
    projections passed explicitly and &mut journal represented by state in/out.
    The concrete in-memory database cannot produce a database error. Inputs
    must satisfy the Rust integer/address invariants and host validity.
    This module does not assert native handler/journal correspondence. *)
Module pre_execution.
  Definition is_eip7702 (code : list Z) : bool :=
    match code with
    | 239 :: 1 :: 0 :: address => Nat.eqb (List.length address) 20
    | _ => false
    end.

  Definition apply_authorization {Authorization : Set} `{AuthorizationTr.C Authorization}
      (chain_id : u64) (authorization : Authorization) (state : StatefulHost.t)
      : bool * StatefulHost.t :=
    let auth_chain_id := (AuthorizationTr.chain_id authorization).(Uint.value) in
    if negb ((auth_chain_id =? 0) || (auth_chain_id =? chain_id.(Integer.value))) then
      (false, state)
    else if (AuthorizationTr.nonce authorization).(Integer.value) =? 2 ^ 64 - 1 then
      (false, state)
    else match AuthorizationTr.authority authorization with
    | None => (false, state)
    | Some authority =>
      (* Warming precedes both code and nonce validation, including on failure. *)
      let state := StatefulHost.warm_account state authority.(Address.value) in
      let loaded := StatefulHost.find_account authority.(Address.value)
        state.(StatefulHost.accounts) in
      let account := match loaded with
        | Some account => account
        | None => StatefulHost.empty_account authority.(Address.value)
        end in
      if negb (Nat.eqb (List.length account.(StatefulHost.Account.code)) 0 ||
        is_eip7702 account.(StatefulHost.Account.code)) then (false, state)
      else if negb ((AuthorizationTr.nonce authorization).(Integer.value) =?
        account.(StatefulHost.Account.nonce)) then (false, state)
      else
        (* Nonexistent accounts become present when delegated. A later
           authorization therefore sees the updated existence and nonce. *)
        let refund := match loaded with Some _ => true | None =>
          List.existsb (Z.eqb authority.(Address.value)) state.(StatefulHost.touched_accounts)
          end in
        (refund, JournaledAccount.delegate authority
          (AuthorizationTr.address authorization) state)
    end.

  Fixpoint apply_authorizations {Authorization : Set} `{AuthorizationTr.C Authorization}
      (chain_id : u64) (authorizations : list Authorization)
      (refunded_accounts : u64) (state : StatefulHost.t) : u64 * StatefulHost.t :=
    match authorizations with
    | [] => (refunded_accounts, state)
    | authorization :: rest =>
      let '(refund, state) := apply_authorization chain_id authorization state in
      let refunded_accounts := if refund then
        BinOp.Wrap.add refunded_accounts {| Integer.value := 1 |}
        else refunded_accounts in
      apply_authorizations chain_id rest refunded_accounts state
    end.

  Definition apply_eip7702_auth_list {Authorization : Set} `{AuthorizationTr.C Authorization}
      (tx_type : u8) (chain_id : u64) (authorizations : list Authorization)
      (state : StatefulHost.t) : u64 * StatefulHost.t :=
    if negb (tx_type.(Integer.value) =? 4) then ({| Integer.value := 0 |}, state) else
    let '(refunded_accounts, state) :=
      apply_authorizations chain_id authorizations {| Integer.value := 0 |} state in
    (BinOp.Wrap.mul refunded_accounts
      (BinOp.Wrap.sub PER_EMPTY_ACCOUNT_COST PER_AUTH_BASE_COST), state).
End pre_execution.
