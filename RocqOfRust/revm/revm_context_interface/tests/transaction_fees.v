From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.links.result.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_context_interface.simulate.result.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Record transaction : Set := {
    tx_type : Z;
    gas_limit : Z;
    gas_price : Z;
    value : Z;
    priority : option Z;
    blobs : list aliases.B256.t;
    blob_price : Z;
  }.

  Global Instance transaction_fees : Transaction.Fees.C transaction := {
    Transaction.Fees.tx_type tx := {| Integer.value := tx.(tx_type) |};
    Transaction.Fees.gas_limit tx := {| Integer.value := tx.(gas_limit) |};
    Transaction.Fees.gas_price tx := {| Integer.value := tx.(gas_price) |};
    Transaction.Fees.value tx := {| Uint.value := tx.(value) |};
    Transaction.Fees.max_priority_fee_per_gas tx :=
      option_map (fun amount => {| Integer.value := amount |}) tx.(priority);
    Transaction.Fees.blob_versioned_hashes tx := tx.(blobs);
    Transaction.Fees.max_fee_per_blob_gas tx := {| Integer.value := tx.(blob_price) |};
  }.

  Definition tx (kind limit price amount : Z) (tip : option Z) : transaction := {|
    tx_type := kind;
    gas_limit := limit;
    gas_price := price;
    value := amount;
    priority := tip;
    blobs := [];
    blob_price := 0;
  |}.

  Definition blob_tx (limit price amount max_blob_price : Z) : transaction := {|
    tx_type := 3;
    gas_limit := limit;
    gas_price := price;
    value := amount;
    priority := None;
    blobs := [FixedBytes.from_Z 0];
    blob_price := max_blob_price;
  |}.

  Definition u128_max : Z := 2 ^ 128 - 1.

  Definition u256_max : Z := 2 ^ 256 - 1.

  Lemma legacy_ignores_priority_fee :
    Transaction.Fees.effective_gas_price (tx 0 1 10 0 (Some 1))
      {| Integer.value := 4 |} = {| Integer.value := 10 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_ignores_priority_fee :
    Transaction.Fees.effective_gas_price (tx 1 1 10 0 (Some 1))
      {| Integer.value := 4 |} = {| Integer.value := 10 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma absent_priority_returns_maximum_price :
    Transaction.Fees.effective_gas_price (tx 2 1 10 0 None)
      {| Integer.value := 4 |} = {| Integer.value := 10 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma priority_plus_base_fee_saturates :
    Transaction.Fees.effective_gas_price (tx 2 1 u128_max 0 (Some 2))
      {| Integer.value := u128_max - 1 |} = {| Integer.value := u128_max |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_price_is_capped :
    Transaction.Fees.effective_gas_price (tx 2 1 5 0 (Some 3))
      {| Integer.value := 4 |} = {| Integer.value := 5 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma execution_product_accepts_u128_max :
    Transaction.Fees.max_balance_spending (tx 0 1 u128_max 0 None) =
    Result.Ok {| Uint.value := u128_max |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma execution_product_rejects_one_past_u128_max :
    Transaction.Fees.max_balance_spending (tx 0 2 (2 ^ 127) 0 None) =
    Result.Err InvalidTransaction.OverflowPaymentInTransaction.
  Proof. vm_compute. reflexivity. Qed.

  Lemma payment_sum_accepts_u256_max :
    Transaction.Fees.max_balance_spending (tx 0 1 1 (u256_max - 1) None) =
    Result.Ok {| Uint.value := u256_max |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma payment_sum_rejects_one_past_u256_max :
    Transaction.Fees.max_balance_spending (tx 0 1 1 u256_max None) =
    Result.Err InvalidTransaction.OverflowPaymentInTransaction.
  Proof. vm_compute. reflexivity. Qed.

  Lemma effective_product_overflow_is_checked :
    Transaction.Fees.effective_balance_spending (tx 2 2 (2 ^ 127) 0 None)
      {| Integer.value := 0 |} {| Integer.value := 0 |} =
    Result.Err InvalidTransaction.OverflowPaymentInTransaction.
  Proof. vm_compute. reflexivity. Qed.

  Lemma effective_payment_can_fit_when_maximum_overflows :
    Transaction.Fees.effective_balance_spending (tx 2 2 (2 ^ 127) 0 (Some 0))
      {| Integer.value := 1 |} {| Integer.value := 0 |} =
    Result.Ok {| Uint.value := 2 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma maximum_blob_fee_saturates_before_widening :
    Transaction.Fees.calc_max_data_fee (blob_tx 1 1 0 u128_max) =
    {| Uint.value := u128_max |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_addition_can_overflow_after_execution_fits :
    Transaction.Fees.max_balance_spending (blob_tx 1 1 (u256_max - 1) 1) =
    Result.Err InvalidTransaction.OverflowPaymentInTransaction.
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonblob_payment_ignores_blob_fields :
    Transaction.Fees.max_balance_spending
      {| tx_type := 0; gas_limit := 1; gas_price := 1; value := 0;
         priority := None; blobs := [FixedBytes.from_Z 0]; blob_price := u128_max |} =
    Result.Ok {| Uint.value := 1 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma balance_equal_to_maximum_is_sufficient :
    Transaction.Fees.ensure_enough_balance (tx 0 2 3 4 None)
      {| Uint.value := 10 |} = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma balance_one_below_maximum_is_rejected :
    Transaction.Fees.ensure_enough_balance (tx 0 2 3 4 None)
      {| Uint.value := 9 |} =
    Result.Err (InvalidTransaction.LackOfFundForMaxFee
      {| Uint.value := 10 |} {| Uint.value := 9 |}).
  Proof. vm_compute. reflexivity. Qed.

  Lemma payment_overflow_precedes_balance_comparison :
    Transaction.Fees.ensure_enough_balance (tx 0 2 (2 ^ 127) 0 None)
      {| Uint.value := 0 |} =
    Result.Err InvalidTransaction.OverflowPaymentInTransaction.
  Proof. vm_compute. reflexivity. Qed.

  Lemma gas_payment_excludes_value_but_keeps_blob_fee :
    Transaction.Fees.gas_balance_spending (blob_tx 2 3 7 9)
      {| Integer.value := 0 |} {| Integer.value := 2 |} =
    Result.Ok {| Uint.value := 262150 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma effective_blob_fee_saturates_before_widening :
    Transaction.Fees.effective_balance_spending (blob_tx 1 1 0 u128_max)
      {| Integer.value := 0 |} {| Integer.value := u128_max |} =
    Result.Ok {| Uint.value := u128_max + 1 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma gas_payment_propagates_value_addition_overflow :
    Transaction.Fees.gas_balance_spending (tx 0 1 1 u256_max None)
      {| Integer.value := 0 |} {| Integer.value := 0 |} =
    Result.Err InvalidTransaction.OverflowPaymentInTransaction.
  Proof. vm_compute. reflexivity. Qed.
End Test.
