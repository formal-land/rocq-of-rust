Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import links.M.

(** Executable methods of transaction/eip7702.rs::AuthorizationTr. The
    authority method must perform signature recovery, including parity and
    low-s checks; an invalid signature is represented by None. *)
Module AuthorizationTr.
  Class C (Self : Set) : Set := {
    authority : Self -> option Address.t;
    chain_id : Self -> aliases.U256.t;
    nonce : Self -> u64;
    address : Self -> Address.t;
  }.
End AuthorizationTr.
