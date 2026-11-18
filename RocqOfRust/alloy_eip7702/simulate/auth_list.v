From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.utils.simulate.keccak256.
Require Import links.M.
Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_precompile.simulate.modexp.
Require Import revm.revm_precompile.simulate.secp256k1.
Require Import ruint.links.lib.

Import ListNotations.
Open Scope Z_scope.

(** alloy-eip7702 0.6.1, src/auth_list.rs, pinned by REVM's Cargo.toml.
    The error result of recovery is projected to option, as consumed by
    AuthorizationTr::authority. No cryptographic correspondence is claimed. *)
Module Authorization.
  Record t : Set := {
    chain_id : aliases.U256.t;
    address : Address.t;
    nonce : u64;
  }.

  Definition signature_hash (self : t) : aliases.B256.t :=
    FixedBytes.from_Z (Modexp.decode_be (Keccak256.hash
      (5 :: EthereumRlp.encode_list [
        EthereumRlp.encode_uint self.(chain_id).(Uint.value);
        EthereumRlp.encode_bytes (EthereumRlp.fixed_big_endian 20 self.(address).(Address.value));
        EthereumRlp.encode_uint self.(nonce).(Integer.value)]))).
End Authorization.

Module SignedAuthorization.
  Record t : Set := {
    inner : Authorization.t;
    y_parity : u8;
    r : aliases.U256.t;
    s : aliases.U256.t;
  }.

  Definition recover_authority (self : t) : option Address.t :=
    if negb ((self.(y_parity).(Integer.value) =? 0) ||
      (self.(y_parity).(Integer.value) =? 1)) then None else
    if Secp256k1.scalar_modulus / 2 <? self.(s).(Uint.value) then None else
    let hash := (Impl_From_FixedBytes_32_for_U256.from
      (Authorization.signature_hash self.(inner))).(Uint.value) in
    match Secp256k1.recover hash self.(r).(Uint.value) self.(s).(Uint.value)
      self.(y_parity).(Integer.value) with
    | Some bytes => Some {| Address.value := Modexp.decode_be bytes |}
    | None => None
    end.
End SignedAuthorization.
