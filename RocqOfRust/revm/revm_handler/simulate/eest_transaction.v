From Stdlib Require Import ZArith.

Require Import revm.revm_handler.simulate.legacy_call.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.

Open Scope Z_scope.

(** The EEST/Geth sender-nonce overflow rule is an adapter boundary.
    The native REVM call simulator deliberately allows the maximum nonce;
    keep that simulator unchanged and apply this rule only to EEST runs. *)
Module EestTransaction.
  Definition nonce_overflow (tx : TransactionAccounting.Transaction.t)
      (input : LegacyCall.Input.t) : bool :=
    TransactionAccounting.transaction_fields_valid tx &&
    LegacyCall.input_valid input &&
    (tx.(TransactionAccounting.Transaction.nonce) =? 2 ^ 64 - 1) &&
    ((LegacyCall.account_at tx.(TransactionAccounting.Transaction.caller)
      input.(LegacyCall.Input.accounts)).(StatefulHost.Account.nonce) =? 2 ^ 64 - 1).

  Definition run_with
      (run_transaction : nat -> SpecId.t -> TransactionAccounting.Transaction.t ->
        LegacyCall.Input.t -> LegacyCall.Result.t)
      (fuel : nat) (spec : SpecId.t)
      (tx : TransactionAccounting.Transaction.t) (input : LegacyCall.Input.t)
      : LegacyCall.Result.t :=
    if nonce_overflow tx input then
      LegacyCall.Result.Rejected LegacyCall.Rejection.NonceOverflow
    else run_transaction fuel spec tx input.

  Definition run := run_with LegacyCall.run.
End EestTransaction.
