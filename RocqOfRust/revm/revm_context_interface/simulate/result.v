Require Import alloy_primitives.links.aliases.

(** The payment-error subset of result.rs::InvalidTransaction. *)
Module InvalidTransaction.
  Inductive t : Set :=
  | OverflowPaymentInTransaction
  | LackOfFundForMaxFee (fee balance : aliases.U256.t).
End InvalidTransaction.
