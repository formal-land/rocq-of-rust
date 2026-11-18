From Stdlib Require Import ZArith.

Require Import revm.revm_handler.simulate.eest_context.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.simulate.eest_types.
Require Import revm.revm_primitives.links.hardfork.

Open Scope Z_scope.

(** The EEST/Geth sender-nonce overflow rule is an adapter boundary.
    The native REVM call simulator deliberately allows the maximum nonce;
    keep that simulator unchanged and apply this rule only to EEST runs. *)
Module EestTransaction.
  Definition nonce_overflow (tx : TransactionAccounting.Transaction.t)
      (input : EestTypes.Input.t) : bool :=
    TransactionAccounting.transaction_fields_valid tx &&
    EestContext.input_valid input &&
    (tx.(TransactionAccounting.Transaction.nonce) =? 2 ^ 64 - 1) &&
    ((EestTypes.account_at tx.(TransactionAccounting.Transaction.caller)
      input.(EestTypes.Input.accounts)).(EestTypes.Account.nonce) =? 2 ^ 64 - 1).

  Definition run_with
      (run_transaction : nat -> SpecId.t -> TransactionAccounting.Transaction.t ->
        EestTypes.Input.t -> EestTypes.Result.t)
      (fuel : nat) (spec : SpecId.t)
      (tx : TransactionAccounting.Transaction.t) (input : EestTypes.Input.t)
      : EestTypes.Result.t :=
    if nonce_overflow tx input then
      EestTypes.Result.Rejected EestTypes.Rejection.NonceOverflow
    else run_transaction fuel spec tx input.

  Definition run := run_with EestContext.run.
End EestTransaction.
