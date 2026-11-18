Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_eip7702.simulate.auth_list.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.links.common.
Require Import core.links.result.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_context_interface.transaction.simulate.eip7702.
Require Import ruint.links.lib.

Import ListNotations.

Module AccessListItem.
  Record t : Set := {
    address : Address.t;
    storage_keys : list aliases.B256.t;
  }.
End AccessListItem.

(** EEST supplies signed authorizations. This specialization retains the Left
    case of Rust's Either<SignedAuthorization, RecoveredAuthorization>; recovery
    still runs in AuthorizationTr.authority, including signature rejection. *)
Module TxEnv.
  Record t : Set := {
    tx_type : u8;
    caller : Address.t;
    gas_limit : u64;
    gas_price : u128;
    kind : TxKind.t;
    value : aliases.U256.t;
    data : Bytes.t;
    nonce : u64;
    chain_id : option u64;
    access_list : list AccessListItem.t;
    gas_priority_fee : option u128;
    blob_hashes : list aliases.B256.t;
    max_fee_per_blob_gas : u128;
    authorization_list : list SignedAuthorization.t;
  }.
End TxEnv.

Module DeriveTxTypeError.
  Inductive t : Set := MissingTargetForEip4844 | MissingTargetForEip7702 | MissingTargetForEip7873.
End DeriveTxTypeError.

Module Impl_Default_for_TxEnv.
  Definition default : TxEnv.t := {|
    TxEnv.tx_type := 0;
    TxEnv.caller := {| Address.value := 0 |};
    TxEnv.gas_limit := 16777216;
    TxEnv.gas_price := 0;
    TxEnv.kind := TxKind.Call {| Address.value := 0 |};
    TxEnv.value := {| Uint.value := 0 |};
    TxEnv.data := Impl_Bytes.new;
    TxEnv.nonce := 0;
    TxEnv.chain_id := Some (1 : u64);
    TxEnv.access_list := [];
    TxEnv.gas_priority_fee := None;
    TxEnv.blob_hashes := [];
    TxEnv.max_fee_per_blob_gas := 0;
    TxEnv.authorization_list := [];
  |}.
End Impl_Default_for_TxEnv.

Module Impl_TxEnv.
  Definition derive_tx_type (self : TxEnv.t) : Result.t unit DeriveTxTypeError.t * TxEnv.t :=
    let self := match self.(TxEnv.access_list) with
      | [] => self | _ => self <| TxEnv.tx_type := 1 |>
      end in
    let self := match self.(TxEnv.gas_priority_fee) with
      | None => self | Some _ => self <| TxEnv.tx_type := 2 |>
      end in
    if negb (Nat.eqb (List.length self.(TxEnv.blob_hashes)) 0) ||
      Z.ltb 0 self.(TxEnv.max_fee_per_blob_gas).(Integer.value) then
      match self.(TxEnv.kind) with
      | TxKind.Call _ => (Result.Ok tt, self <| TxEnv.tx_type := 3 |>)
      | TxKind.Create => (Result.Err DeriveTxTypeError.MissingTargetForEip4844, self)
      end
    else match self.(TxEnv.authorization_list) with
      | [] => (Result.Ok tt, self)
      | _ => match self.(TxEnv.kind) with
          | TxKind.Call _ => (Result.Ok tt, self <| TxEnv.tx_type := 4 |>)
          | TxKind.Create => (Result.Err DeriveTxTypeError.MissingTargetForEip7702, self)
          end
      end.

  Definition set_signed_authorization (self : TxEnv.t) (auth : list SignedAuthorization.t) : TxEnv.t :=
    self <| TxEnv.authorization_list := auth |>.
End Impl_TxEnv.

Module Impl_Transaction_for_TxEnv.
  #[global] Instance fees : Transaction.Fees.C TxEnv.t := {|
    Transaction.Fees.tx_type := TxEnv.tx_type;
    Transaction.Fees.gas_limit := TxEnv.gas_limit;
    Transaction.Fees.value := TxEnv.value;
    Transaction.Fees.gas_price := TxEnv.gas_price;
    Transaction.Fees.blob_versioned_hashes := TxEnv.blob_hashes;
    Transaction.Fees.max_fee_per_blob_gas := TxEnv.max_fee_per_blob_gas;
    Transaction.Fees.max_priority_fee_per_gas := TxEnv.gas_priority_fee;
  |}.
End Impl_Transaction_for_TxEnv.

Module Impl_AuthorizationTr_for_SignedAuthorization.
  #[global] Instance methods : AuthorizationTr.C SignedAuthorization.t := {|
    AuthorizationTr.authority := SignedAuthorization.recover_authority;
    AuthorizationTr.chain_id auth := auth.(SignedAuthorization.inner).(Authorization.chain_id);
    AuthorizationTr.nonce auth := auth.(SignedAuthorization.inner).(Authorization.nonce);
    AuthorizationTr.address auth := auth.(SignedAuthorization.inner).(Authorization.address);
  |}.
End Impl_AuthorizationTr_for_SignedAuthorization.
