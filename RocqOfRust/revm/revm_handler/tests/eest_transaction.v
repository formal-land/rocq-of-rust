From Stdlib Require Import ZArith.

Require Import revm.revm_handler.simulate.eest_transaction.
Require Import revm.revm_handler.simulate.legacy_call.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.tests.legacy_call.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Open Scope Z_scope.

Module LegacyTest := RocqOfRust.revm.revm_handler.tests.legacy_call.Test.

Module Test.
  Definition max_tx :=
    LegacyTest.tx <| TransactionAccounting.Transaction.nonce := 2 ^ 64 - 1 |>.

  Definition skipped (_ : nat) (_ : SpecId.t)
      (_ : TransactionAccounting.Transaction.t)
      (_ : LegacyCall.Input.t) : LegacyCall.Result.t :=
    LegacyCall.Result.Incomplete.

  Lemma matching_max_nonce_is_rejected :
    EestTransaction.run_with skipped 100 SpecId.CANCUN
      max_tx (LegacyTest.input_with_max_nonce [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.NonceOverflow.
  Proof. vm_compute. reflexivity. Qed.

  Lemma unmatched_max_nonce_still_checks_the_transaction :
    EestTransaction.run_with skipped 100 SpecId.CANCUN
      max_tx (LegacyTest.input [0]) = LegacyCall.Result.Incomplete.
  Proof. vm_compute. reflexivity. Qed.
End Test.
