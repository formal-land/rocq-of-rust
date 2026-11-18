Require Import alloy_eip7702.simulate.auth_list.
Require Import revm.revm_context_interface.transaction.simulate.eip7702.

(** transaction/alloy_types.rs::impl AuthorizationTr for SignedAuthorization *)
Module Impl_AuthorizationTr_for_SignedAuthorization.
  Global Instance methods : AuthorizationTr.C SignedAuthorization.t := {
    AuthorizationTr.authority := SignedAuthorization.recover_authority;
    AuthorizationTr.chain_id self := self.(SignedAuthorization.inner).(Authorization.chain_id);
    AuthorizationTr.nonce self := self.(SignedAuthorization.inner).(Authorization.nonce);
    AuthorizationTr.address self := self.(SignedAuthorization.inner).(Authorization.address);
  }.
End Impl_AuthorizationTr_for_SignedAuthorization.
