From Stdlib Require Import ZArith.

Require Import revm.revm_handler.simulate.eest_transaction.
Require Import revm.revm_handler.simulate.eest_types.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.tests.transaction_cases.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Open Scope Z_scope.

Module Test.
  Lemma default_entrypoint_executes_osaka :
    TransactionCases.observation
      (EestTransaction.run 100 SpecId.OSAKA TransactionCases.tx (TransactionCases.input [0])) =
    Some (InstructionResult.Stop, 21000, 1, 789993, 7, 126000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Definition max_tx :=
    TransactionCases.tx <| TransactionAccounting.Transaction.nonce := 2 ^ 64 - 1 |>.

  Definition skipped (_ : nat) (_ : SpecId.t)
      (_ : TransactionAccounting.Transaction.t)
      (_ : EestTypes.Input.t) : EestTypes.Result.t :=
    EestTypes.Result.Incomplete.

  Lemma matching_max_nonce_is_rejected :
    EestTransaction.run_with skipped 100 SpecId.OSAKA
      max_tx (TransactionCases.input_with_max_nonce [0]) =
    EestTypes.Result.Rejected EestTypes.Rejection.NonceOverflow.
  Proof. vm_compute. reflexivity. Qed.

  Lemma unmatched_max_nonce_still_checks_the_transaction :
    EestTransaction.run_with skipped 100 SpecId.OSAKA
      max_tx (TransactionCases.input [0]) = EestTypes.Result.Incomplete.
  Proof. vm_compute. reflexivity. Qed.

  Lemma default_entrypoint_rejects_max_nonce :
    EestTransaction.run 100 SpecId.OSAKA max_tx (TransactionCases.input_with_max_nonce [0]) =
    EestTypes.Result.Rejected EestTypes.Rejection.NonceOverflow.
  Proof. vm_compute. reflexivity. Qed.
End Test.
