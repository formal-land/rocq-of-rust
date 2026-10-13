From Stdlib Require Import List ZArith.

Require Import alloy_eip7702.simulate.auth_list.
Require Import alloy_primitives.bits.links.address.
Require Import links.M.
Require Import ruint.links.lib.
Require Import revm.revm_precompile.simulate.secp256k1.
Require Import simulate.RocqOfRust.

Open Scope Z_scope.

Module Test.
  Definition check_authority (authorization : SignedAuthorization.t) (expected : Z) : bool :=
    match SignedAuthorization.recover_authority authorization with
    | Some address => address.(Address.value) =? expected
    | None => false
    end.

  (** Pinned EEST tests@v20.0.2 authorization 0:
      tests/istanbul/eip1344_chainid/test_chainid.py::test_chainid[fork_Osaka-typed_transaction_4-state_test] *)
  Definition authorization_0 : SignedAuthorization.t := {|
    SignedAuthorization.inner := {|
      Authorization.chain_id := {| Uint.value := 1 |};
      Authorization.address := {| Address.value := 1303281628687763440370184738944059152404142626799 |};
      Authorization.nonce := {| Integer.value := 0 |};
    |};
    SignedAuthorization.y_parity := {| Integer.value := 0 |};
    SignedAuthorization.r := {| Uint.value := 96441147760375158342689561914255649222396457585212932855587340860541175240979 |};
    SignedAuthorization.s := {| Uint.value := 18604699335720640772466787436572090116014427295385539085212610795302726268527 |};
  |}.

  Definition recover_pinned_authority_0 : bool :=
    check_authority authorization_0 1224202395603991734753052637045002294746042002390.

  (** Pinned EEST tests@v20.0.2 authorization 1:
      tests/istanbul/eip1344_chainid/test_chainid.py::test_chainid[fork_Osaka-typed_transaction_4-state_test] *)
  Definition authorization_1 : SignedAuthorization.t := {|
    SignedAuthorization.inner := {|
      Authorization.chain_id := {| Uint.value := 1 |};
      Authorization.address := {| Address.value := 1389338657723769452105660491984242519730668716572 |};
      Authorization.nonce := {| Integer.value := 0 |};
    |};
    SignedAuthorization.y_parity := {| Integer.value := 1 |};
    SignedAuthorization.r := {| Uint.value := 78567599448889316464418371236463515359322871175668591905074261103715712357286 |};
    SignedAuthorization.s := {| Uint.value := 47091425063878903369787433607998219688084595934162856604187361009912983799055 |};
  |}.

  Definition recover_pinned_authority_1 : bool :=
    check_authority authorization_1 1444285741296652659064081157335590409014750717241.

  (** Pinned EEST tests@v20.0.2 authorization 2:
      tests/frontier/eip2681_limit_account_nonce/test_nonce_reaching_max.py::test_set_code_self_authorization_reaching_nonce_max[fork_Osaka-state_test] *)
  Definition authorization_2 : SignedAuthorization.t := {|
    SignedAuthorization.inner := {|
      Authorization.chain_id := {| Uint.value := 0 |};
      Authorization.address := {| Address.value := 1101631429901792105632125985250094987657219250475 |};
      Authorization.nonce := {| Integer.value := 18446744073709551614 |};
    |};
    SignedAuthorization.y_parity := {| Integer.value := 1 |};
    SignedAuthorization.r := {| Uint.value := 78505712895134768093388646557634414914552025207430315140818190532466824100569 |};
    SignedAuthorization.s := {| Uint.value := 47486179487279748321080859161498984181368249325518534644524619601243134486305 |};
  |}.

  Definition recover_pinned_authority_2 : bool :=
    check_authority authorization_2 1058104566282912175953203128237539485146462826473.

  Lemma invalid_parity_is_rejected :
    SignedAuthorization.recover_authority
      (authorization_0 <| SignedAuthorization.y_parity := {| Integer.value := 2 |} |>) = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma high_s_is_rejected :
    SignedAuthorization.recover_authority
      (authorization_0 <| SignedAuthorization.s :=
        {| Uint.value := Secp256k1.scalar_modulus / 2 + 1 |} |>) = None.
  Proof. vm_compute. reflexivity. Qed.
End Test.
