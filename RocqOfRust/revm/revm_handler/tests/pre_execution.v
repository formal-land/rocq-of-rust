From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import links.M.
Require Import ruint.links.lib.

Require Import revm.revm_context_interface.transaction.simulate.eip7702.
Require Import revm.revm_handler.simulate.pre_execution.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.

Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Module Authorization.
    Record t : Set := {
      authority : option Address.t;
      chain_id : aliases.U256.t;
      nonce : u64;
      address : Address.t;
    }.

    Global Instance methods : AuthorizationTr.C t := {
      AuthorizationTr.authority := authority;
      AuthorizationTr.chain_id := chain_id;
      AuthorizationTr.nonce := nonce;
      AuthorizationTr.address := address;
    }.
  End Authorization.

  Definition auth (chain nonce target : Z) : Authorization.t := {|
    Authorization.authority := Some (StatefulHost.rust_address 42);
    Authorization.chain_id := StatefulHost.rust_word chain;
    Authorization.nonce := {| Integer.value := nonce |};
    Authorization.address := StatefulHost.rust_address target;
  |}.

  Definition host (accounts : list StatefulHost.Account.t) :=
    StatefulHost.make (add11_input <| StatefulHost.Input.state := accounts |>).

  Definition account := StatefulHost.empty_account 42.

  Definition run (authorizations : list Authorization.t) (state : StatefulHost.t) :=
    pre_execution.apply_eip7702_auth_list {| Integer.value := 4 |}
      {| Integer.value := 1 |} authorizations state.

  Definition nonce (state : StatefulHost.t) :=
    match StatefulHost.find_account 42 state.(StatefulHost.accounts) with
    | Some account => Some account.(StatefulHost.Account.nonce)
    | None => None
    end.

  Definition code (state : StatefulHost.t) :=
    match StatefulHost.find_account 42 state.(StatefulHost.accounts) with
    | Some account => account.(StatefulHost.Account.code)
    | None => []
    end.

  Definition refund (result : u64 * StatefulHost.t) := (fst result).(Integer.value).

  Lemma other_transaction_type_keeps_state :
    pre_execution.apply_eip7702_auth_list {| Integer.value := 2 |}
      {| Integer.value := 1 |} [auth 1 0 77] (host []) =
    ({| Integer.value := 0 |}, host []).
  Proof. reflexivity. Qed.

  Lemma wrong_chain_does_not_warm :
    run [auth 2 0 77] (host []) = ({| Integer.value := 0 |}, host []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma chain_id_is_not_truncated_to_u64 :
    run [auth (2 ^ 64 + 1) 0 77] (host []) = ({| Integer.value := 0 |}, host []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma maximum_nonce_does_not_warm :
    run [auth 1 (2 ^ 64 - 1) 77] (host []) = ({| Integer.value := 0 |}, host []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma failed_recovery_does_not_warm :
    run [(auth 1 0 77) <| Authorization.authority := None |>] (host []) =
    ({| Integer.value := 0 |}, host []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma wrong_nonce_warms_without_creating_account :
    let result := run [auth 1 1 77] (host []) in
    (refund result, nonce (snd result), (snd result).(StatefulHost.accessed_accounts)) =
    (0, None, [42]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma ordinary_code_warms_without_delegating :
    let state := host [account <| StatefulHost.Account.code := [0] |>] in
    let result := run [auth 1 0 77] state in
    (refund result, nonce (snd result), code (snd result),
      (snd result).(StatefulHost.accessed_accounts)) = (0, Some 0, [0], [42]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonexistent_authority_has_no_refund :
    let result := run [auth 1 0 77] (host []) in
    (refund result, nonce (snd result), code (snd result)) =
    (0, Some 1, [239; 1; 0] ++ List.repeat 0 19 ++ [77]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma existing_empty_authority_gets_refund :
    let result := run [auth 1 0 77] (host [account]) in
    (refund result, nonce (snd result)) = (12500, Some 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma chain_zero_is_valid :
    let result := run [auth 0 0 77] (host [account]) in
    (refund result, nonce (snd result)) = (12500, Some 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma repeated_authority_observes_updated_nonce_and_existence :
    let result := run [auth 1 0 77; auth 1 1 88] (host []) in
    (refund result, nonce (snd result), code (snd result)) =
    (12500, Some 2, [239; 1; 0] ++ List.repeat 0 19 ++ [88]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma repeated_nonce_is_skipped :
    let result := run [auth 1 0 77; auth 1 0 88] (host [account]) in
    (refund result, nonce (snd result), code (snd result)) =
    (12500, Some 1, [239; 1; 0] ++ List.repeat 0 19 ++ [77]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma clearing_delegation_resets_code_hash :
    let result := run [auth 1 0 77; auth 1 1 0] (host []) in
    match StatefulHost.find_account 42 (snd result).(StatefulHost.accounts) with
    | None => False
    | Some account => (refund result, account.(StatefulHost.Account.nonce),
        account.(StatefulHost.Account.code), account.(StatefulHost.Account.code_hash)) =
        (12500, 2, [], StatefulHost.empty_code_hash)
    end.
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonce_reaches_maximum_without_wrapping :
    let result := run [auth 1 (2 ^ 64 - 2) 77; auth 1 (2 ^ 64 - 1) 88]
      (host [account <| StatefulHost.Account.nonce := 2 ^ 64 - 2 |>]) in
    (refund result, nonce (snd result), code (snd result)) =
    (12500, Some (2 ^ 64 - 1), [239; 1; 0] ++ List.repeat 0 19 ++ [77]).
  Proof. vm_compute. reflexivity. Qed.
End Test.
