From Stdlib Require Import List ZArith.

Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_primitives.links.hardfork.

Import ListNotations.
Import TransactionAccounting.
Open Scope Z_scope.

Module Test.
  Definition transaction (tx_type : Z) (target : option Z)
      (limit price value : Z) (data : list Z) : Transaction.t := {|
    Transaction.tx_type := tx_type;
    Transaction.caller := 1;
    Transaction.target := target;
    Transaction.nonce := 0;
    Transaction.chain_id := Some 1;
    Transaction.gas_limit := limit;
    Transaction.gas_price := price;
    Transaction.max_priority_fee := None;
    Transaction.access_list := [];
    Transaction.max_fee_per_blob_gas := 0;
    Transaction.blob_hashes := [];
    Transaction.value := value;
    Transaction.data := data;
  |}.

  Definition tx := transaction 0 (Some 42).

  Definition block : Block.t := {|
    Block.gas_limit := 1000000;
    Block.base_fee := 4;
    Block.blob_base_fee := 0;
  |}.

  Definition frame (status : FrameStatus.t) (remaining refunded : Z) : FrameGas.t := {|
    FrameGas.status := status;
    FrameGas.remaining := remaining;
    FrameGas.refunded := refunded;
  |}.

  Definition observation (result : Result.t Settlement.t) :=
    match result with
    | Result.Ready settlement => Some
        (settlement.(Settlement.gas_remaining), settlement.(Settlement.gas_refunded),
         settlement.(Settlement.gas_used), settlement.(Settlement.caller_reimbursement),
         settlement.(Settlement.beneficiary_reward), settlement.(Settlement.base_fee_burn))
    | _ => None
    end.

  Lemma cancun_mixed_calldata_intrinsic :
    prepare SpecId.CANCUN (tx 50000 10 3 [0; 1; 255; 0]) block =
    Result.Ready {| InitialGas.intrinsic := 21040; InitialGas.floor := 0;
      InitialGas.execution := 28960; InitialGas.upfront_fee := 500000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_mixed_calldata_floor :
    prepare SpecId.PRAGUE (tx 50000 10 3 [0; 1; 255; 0]) block =
    Result.Ready {| InitialGas.intrinsic := 21040; InitialGas.floor := 21100;
      InitialGas.execution := 28960; InitialGas.upfront_fee := 500000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma intrinsic_gas_rejection_precedes_floor_rejection :
    prepare SpecId.PRAGUE (tx 21000 10 0 [1]) block =
    Result.Rejected (GasError.IntrinsicGasTooHigh 21016 21000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma sufficient_intrinsic_but_insufficient_floor_rejected :
    prepare SpecId.PRAGUE (tx 21016 10 0 [1]) block =
    Result.Rejected (GasError.FloorGasTooHigh 21040 21016).
  Proof. vm_compute. reflexivity. Qed.

  Lemma fee_multiplication_checks_u128 :
    prepare SpecId.CANCUN (tx 50000 (2 ^ 128 - 1) 0 []) block =
    Result.Rejected GasError.PaymentOverflow.
  Proof. vm_compute. reflexivity. Qed.

  Lemma value_addition_checks_u256 :
    prepare SpecId.CANCUN (tx 50000 10 (2 ^ 256 - 1) []) block =
    Result.Rejected GasError.PaymentOverflow.
  Proof. vm_compute. reflexivity. Qed.

  Lemma unsupported_fork_is_explicit :
    prepare SpecId.AMSTERDAM (tx 50000 10 0 []) block =
    Result.Unsupported (UnsupportedReason.Fork SpecId.AMSTERDAM).
  Proof. reflexivity. Qed.

  Lemma unsupported_transaction_type_is_explicit :
    prepare SpecId.CANCUN (transaction 4 (Some 42) 50000 10 0 []) block =
    Result.Unsupported (UnsupportedReason.TransactionType 4).
  Proof. vm_compute. reflexivity. Qed.

  Lemma creation_intrinsic_includes_create_stipend :
    prepare SpecId.PRAGUE (transaction 0 None 50000 10 0 []) block =
    Result.Rejected (GasError.IntrinsicGasTooHigh 53000 50000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma legacy_price_below_base_fee_rejected :
    prepare SpecId.CANCUN (tx 50000 3 0 []) block =
    Result.Rejected GasError.GasPriceBelowBaseFee.
  Proof. vm_compute. reflexivity. Qed.

  Lemma transaction_limit_above_block_rejected :
    prepare SpecId.PRAGUE (tx 1000001 10 0 []) block =
    Result.Rejected GasError.GasLimitAboveBlock.
  Proof. vm_compute. reflexivity. Qed.

  Lemma malformed_calldata_is_explicit :
    prepare SpecId.CANCUN (tx 50000 10 0 [256]) block =
    Result.Malformed MalformedReason.TransactionFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma success_reimburses_unused_gas :
    observation (settle SpecId.CANCUN (tx 50000 10 3 []) block
      (frame FrameStatus.Success 29000 0)) =
    Some (29000, 0, 21000, 290000, 126000, 84000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma success_refund_capped_at_one_fifth :
    observation (settle SpecId.CANCUN (tx 50000 10 3 []) block
      (frame FrameStatus.Success 20000 10000)) =
    Some (20000, 6000, 24000, 260000, 144000, 96000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_keeps_remaining_gas_but_discards_refund :
    observation (settle SpecId.PRAGUE (tx 50000 10 3 []) block
      (frame FrameStatus.Revert 20000 10000)) =
    Some (20000, 0, 30000, 200000, 180000, 120000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma halt_spends_full_transaction_limit :
    observation (settle SpecId.CANCUN (tx 50000 10 3 []) block
      (frame FrameStatus.Halt 20000 10000)) =
    Some (0, 0, 50000, 0, 300000, 200000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_floor_applies_after_refund_cap_and_clears_refund :
    observation (settle SpecId.PRAGUE (tx 100000 10 0 (List.repeat 1 1000)) block
      (frame FrameStatus.Success 60000 10000)) =
    Some (39000, 0, 61000, 390000, 366000, 244000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma frame_remaining_cannot_exceed_execution_budget :
    settle SpecId.CANCUN (tx 50000 10 0 []) block
      (frame FrameStatus.Success 30000 0) =
    Result.Malformed MalformedReason.FrameFields.
  Proof. vm_compute. reflexivity. Qed.

  (** The native gas cap casts a signed refund to u64 before taking the min.
      Real complete transaction executions should have a nonnegative refund. *)
  Lemma native_signed_refund_cast_preserved :
    observation (settle SpecId.CANCUN (tx 50000 10 0 []) block
      (frame FrameStatus.Success 20000 (-1))) =
    Some (20000, 6000, 24000, 260000, 144000, 96000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_preserves_prague_calldata_floor :
    prepare SpecId.OSAKA (tx 50000 10 3 [0; 1; 255; 0]) block =
    Result.Ready {| InitialGas.intrinsic := 21040; InitialGas.floor := 21100;
      InitialGas.execution := 28960; InitialGas.upfront_fee := 500000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_rejects_insufficient_floor :
    prepare SpecId.OSAKA (tx 21016 10 0 [1]) block =
    Result.Rejected (GasError.FloorGasTooHigh 21040 21016).
  Proof. vm_compute. reflexivity. Qed.

  Definition large_block : Block.t :=
    {| Block.gas_limit := 20000000; Block.base_fee := 0; Block.blob_base_fee := 0 |}.

  Lemma osaka_transaction_gas_cap_is_inclusive :
    prepare SpecId.OSAKA (tx 16777216 1 0 []) large_block =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 21000;
      InitialGas.execution := 16756216; InitialGas.upfront_fee := 16777216 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_transaction_gas_cap_rejects_next_value :
    prepare SpecId.OSAKA (tx 16777217 1 0 []) large_block =
    Result.Rejected (GasError.GasLimitAboveCap 16777217 16777216).
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_gas_cap_precedes_price_and_block_checks :
    prepare SpecId.OSAKA (tx 16777217 3 0 []) block =
    Result.Rejected (GasError.GasLimitAboveCap 16777217 16777216).
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_does_not_apply_osaka_transaction_cap :
    prepare SpecId.PRAGUE (tx 16777217 1 0 []) large_block =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 21000;
      InitialGas.execution := 16756217; InitialGas.upfront_fee := 16777217 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_floor_applies_after_refund_cap_and_clears_refund :
    observation (settle SpecId.OSAKA (tx 100000 10 0 (List.repeat 1 1000)) block
      (frame FrameStatus.Success 60000 10000)) =
    Some (39000, 0, 61000, 390000, 366000, 244000).
  Proof. vm_compute. reflexivity. Qed.

  Definition typed_transaction (tx_type limit max_fee : Z)
      (priority : option Z) (entries : list (Z * list Z))
      (value : Z) (data : list Z) : Transaction.t := {|
    Transaction.tx_type := tx_type;
    Transaction.caller := 1;
    Transaction.target := Some 42;
    Transaction.nonce := 0;
    Transaction.chain_id := Some 1;
    Transaction.gas_limit := limit;
    Transaction.gas_price := max_fee;
    Transaction.max_priority_fee := priority;
    Transaction.access_list := entries;
    Transaction.max_fee_per_blob_gas := 0;
    Transaction.blob_hashes := [];
    Transaction.value := value;
    Transaction.data := data;
  |}.

  Lemma access_list_duplicates_each_pay_intrinsic_gas :
    prepare SpecId.CANCUN
      (typed_transaction 1 50000 10 None [(42, [0; 0]); (42, [0])] 0 []) block =
    Result.Ready {| InitialGas.intrinsic := 31500; InitialGas.floor := 0;
      InitialGas.execution := 18500; InitialGas.upfront_fee := 500000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_does_not_increase_prague_calldata_floor :
    prepare SpecId.PRAGUE
      (typed_transaction 2 50000 10 (Some 2) [(42, [0; 0]); (42, [0])] 0 [1]) block =
    Result.Ready {| InitialGas.intrinsic := 31516; InitialGas.floor := 21040;
      InitialGas.execution := 18484; InitialGas.upfront_fee := 300000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_intrinsic_rejection_includes_every_duplicate :
    prepare SpecId.CANCUN
      (typed_transaction 1 30000 10 None [(42, [0; 0]); (42, [0])] 0 []) block =
    Result.Rejected (GasError.IntrinsicGasTooHigh 31500 30000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma legacy_ignores_typed_fee_and_access_list_fields :
    prepare SpecId.CANCUN
      (typed_transaction 0 50000 10 (Some 11) [(42, [0; 0])] 0 []) block =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 0;
      InitialGas.execution := 29000; InitialGas.upfront_fee := 500000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_deducts_effective_fee :
    prepare SpecId.CANCUN (typed_transaction 2 50000 10 (Some 2) [] 0 []) block =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 0;
      InitialGas.execution := 29000; InitialGas.upfront_fee := 300000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_reimbursement_and_tip_use_effective_price :
    observation (settle SpecId.CANCUN
      (typed_transaction 2 50000 10 (Some 2) [] 0 []) block
      (frame FrameStatus.Success 29000 0)) =
    Some (29000, 0, 21000, 174000, 42000, 84000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_effective_price_is_capped_by_max_fee :
    observation (settle SpecId.CANCUN
      (typed_transaction 2 50000 5 (Some 2) [] 0 []) block
      (frame FrameStatus.Success 29000 0)) =
    Some (29000, 0, 21000, 145000, 21000, 84000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma missing_priority_preserves_native_max_price_fallback :
    prepare SpecId.CANCUN (typed_transaction 2 50000 10 None [] 0 []) block =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 0;
      InitialGas.execution := 29000; InitialGas.upfront_fee := 500000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_base_plus_priority_saturates_u128 :
    effective_gas_price
      (typed_transaction 2 50000 (2 ^ 128 - 1) (Some (2 ^ 128 - 1)) [] 0 [])
      (2 ^ 64 - 1) = 2 ^ 128 - 1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma priority_above_max_fee_precedes_base_fee_rejection :
    prepare SpecId.CANCUN (typed_transaction 2 50000 3 (Some 5) [] 0 []) block =
    Result.Rejected GasError.PriorityFeeGreaterThanMaxFee.
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_cap_precedes_priority_fee_rejection :
    prepare SpecId.OSAKA (typed_transaction 2 16777217 3 (Some 5) [] 0 []) block =
    Result.Rejected (GasError.GasLimitAboveCap 16777217 16777216).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_max_fee_below_base_fee_is_rejected :
    prepare SpecId.CANCUN (typed_transaction 2 50000 3 (Some 1) [] 0 []) block =
    Result.Rejected GasError.GasPriceBelowBaseFee.
  Proof. vm_compute. reflexivity. Qed.

  Lemma maximum_fee_overflow_rejected_even_when_effective_fee_fits :
    prepare SpecId.CANCUN
      (typed_transaction 2 50000 (2 ^ 128 - 1) (Some 0) [] 0 []) block =
    Result.Rejected GasError.PaymentOverflow.
  Proof. vm_compute. reflexivity. Qed.

  Lemma maximum_fee_value_addition_checks_u256 :
    prepare SpecId.CANCUN
      (typed_transaction 2 50000 10 (Some 0) [] (2 ^ 256 - 1) []) block =
    Result.Rejected GasError.PaymentOverflow.
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_address_bounds_are_checked :
    prepare SpecId.CANCUN
      (typed_transaction 1 50000 10 None [(2 ^ 160, [])] 0 []) block =
    Result.Malformed MalformedReason.TransactionFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_storage_key_bounds_are_checked :
    prepare SpecId.CANCUN
      (typed_transaction 2 50000 10 (Some 2) [(42, [2 ^ 256])] 0 []) block =
    Result.Malformed MalformedReason.TransactionFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma priority_fee_bounds_are_checked :
    prepare SpecId.CANCUN
      (typed_transaction 2 50000 10 (Some (2 ^ 128)) [] 0 []) block =
    Result.Malformed MalformedReason.TransactionFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma authorization_transaction_remains_explicitly_unsupported :
    prepare SpecId.PRAGUE (transaction 4 (Some 42) 50000 10 0 []) block =
    Result.Unsupported (UnsupportedReason.TransactionType 4).
  Proof. vm_compute. reflexivity. Qed.

  Lemma creation_initcode_word_cost_rounds_up :
    prepare SpecId.PRAGUE (transaction 0 None 60000 10 0 (List.repeat 0 33)) block =
    Result.Ready {| InitialGas.intrinsic := 53136; InitialGas.floor := 21330;
      InitialGas.execution := 6864; InitialGas.upfront_fee := 600000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma creation_initcode_limit_is_checked_before_intrinsic_gas :
    prepare SpecId.CANCUN (transaction 0 None 21000 10 0 (List.repeat 0 49153)) block =
    Result.Rejected GasError.CreateInitCodeSizeLimit.
  Proof. vm_compute. reflexivity. Qed.

  Definition blob_block (price : Z) : Block.t := {|
    Block.gas_limit := 1000000;
    Block.base_fee := 4;
    Block.blob_base_fee := price;
  |}.

  Definition versioned_hash : Z := 2 ^ 248 + 17.

  Definition blob_transaction (target : option Z) (limit max_fee : Z)
      (priority : option Z) (max_blob_fee : Z) (hashes : list Z) (value : Z) : Transaction.t := {|
    Transaction.tx_type := 3;
    Transaction.caller := 1;
    Transaction.target := target;
    Transaction.nonce := 0;
    Transaction.chain_id := Some 1;
    Transaction.gas_limit := limit;
    Transaction.gas_price := max_fee;
    Transaction.max_priority_fee := priority;
    Transaction.access_list := [];
    Transaction.max_fee_per_blob_gas := max_blob_fee;
    Transaction.blob_hashes := hashes;
    Transaction.value := value;
    Transaction.data := [];
  |}.

  Definition blob_tx := blob_transaction (Some 42) 50000 10 (Some 2).

  Lemma blob_fee_deducted_in_addition_to_effective_execution_fee :
    prepare SpecId.CANCUN (blob_tx 3 [versioned_hash] 7) (blob_block 2) =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 0;
      InitialGas.execution := 29000; InitialGas.upfront_fee := 562144 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma duplicate_blob_hashes_each_pay_blob_fee :
    prepare SpecId.PRAGUE (blob_tx 3 [versioned_hash; versioned_hash] 7) (blob_block 2) =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 21000;
      InitialGas.execution := 29000; InitialGas.upfront_fee := 824288 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma maximum_payment_includes_maximum_blob_price :
    maximum_payment (blob_tx 3 [versioned_hash] 7) = 893223.
  Proof. vm_compute. reflexivity. Qed.

  Lemma execution_refund_does_not_refund_blob_fee :
    match settle SpecId.CANCUN (blob_tx 3 [versioned_hash] 7) (blob_block 2)
      (frame FrameStatus.Success 29000 0) with
    | Result.Ready gas => Some
        (gas.(Settlement.caller_reimbursement), gas.(Settlement.beneficiary_reward),
         gas.(Settlement.base_fee_burn), gas.(Settlement.blob_fee_burn), gas.(Settlement.gas_used))
    | _ => None
    end = Some (174000, 42000, 84000, 262144, 21000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma halt_keeps_blob_fee_and_spends_execution_limit :
    match settle SpecId.OSAKA (blob_tx 3 [versioned_hash] 7) (blob_block 2)
      (frame FrameStatus.Halt 29000 0) with
    | Result.Ready gas => Some
        (gas.(Settlement.caller_reimbursement), gas.(Settlement.beneficiary_reward),
         gas.(Settlement.base_fee_burn), gas.(Settlement.blob_fee_burn), gas.(Settlement.gas_used))
    | _ => None
    end = Some (0, 100000, 200000, 262144, 50000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_fee_multiplication_saturates_u128_and_combined_deduction_uses_u256 :
    prepare SpecId.CANCUN
      (blob_transaction (Some 42) 21000 4 (Some 0) (2 ^ 128 - 1) [versioned_hash] 0)
      (blob_block (2 ^ 128 - 1)) =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 0;
      InitialGas.execution := 0; InitialGas.upfront_fee := 2 ^ 128 - 1 + 84000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_fee_checked_addition_can_overflow_u256_after_execution_payment_fits :
    prepare SpecId.CANCUN
      (blob_tx 3 [versioned_hash] (2 ^ 256 - 1 - 500000)) (blob_block 2) =
    Result.Rejected GasError.PaymentOverflow.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_price_rejection_precedes_empty_hash_rejection :
    prepare SpecId.CANCUN (blob_tx 1 [] 0) (blob_block 2) =
    Result.Rejected (GasError.BlobGasPriceGreaterThanMax 2 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_hash_list_must_be_nonempty :
    prepare SpecId.CANCUN (blob_tx 3 [] 0) (blob_block 2) =
    Result.Rejected GasError.EmptyBlobs.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_hash_version_is_the_high_byte :
    prepare SpecId.PRAGUE (blob_tx 3 [17] 0) (blob_block 2) =
    Result.Rejected GasError.BlobVersionNotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma every_blob_hash_version_is_checked :
    prepare SpecId.OSAKA (blob_tx 3 [versioned_hash; 2 ^ 249] 0) (blob_block 2) =
    Result.Rejected GasError.BlobVersionNotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_hash_version_rejection_precedes_configured_count_limit :
    prepare_gas_with_blob_limit SpecId.CANCUN (blob_tx 3 [0] 0) (blob_block 2) (Some 0) =
    Result.Rejected GasError.BlobVersionNotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma configured_blob_limit_is_inclusive :
    prepare_gas_with_blob_limit SpecId.CANCUN (blob_tx 3 [versioned_hash] 0) (blob_block 2) (Some 1) =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 0;
      InitialGas.execution := 29000; InitialGas.upfront_fee := 562144 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma configured_blob_limit_rejects_extra_hashes :
    prepare_gas_with_blob_limit SpecId.CANCUN
      (blob_tx 3 [versioned_hash; versioned_hash] 0) (blob_block 2) (Some 1) =
    Result.Rejected (GasError.TooManyBlobs 2 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma native_default_has_no_implicit_blob_count_limit :
    prepare_gas SpecId.CANCUN (blob_tx 3 (List.repeat versioned_hash 7) 0) (blob_block 2) =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 0;
      InitialGas.execution := 29000; InitialGas.upfront_fee := 2135008 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_validation_precedes_block_gas_limit :
    prepare_gas_with_blob_limit SpecId.CANCUN
      (blob_transaction (Some 42) 1000001 10 (Some 2) 3 [versioned_hash; versioned_hash] 0)
      (blob_block 2) (Some 1) =
    Result.Rejected (GasError.TooManyBlobs 2 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma execution_priority_rejection_precedes_blob_price :
    prepare SpecId.CANCUN
      (blob_transaction (Some 42) 50000 3 (Some 5) 1 [] 0) (blob_block 2) =
    Result.Rejected GasError.PriorityFeeGreaterThanMaxFee.
  Proof. vm_compute. reflexivity. Qed.

  Lemma execution_base_fee_rejection_precedes_blob_price :
    prepare SpecId.CANCUN
      (blob_transaction (Some 42) 50000 3 (Some 0) 1 [] 0) (blob_block 2) =
    Result.Rejected GasError.GasPriceBelowBaseFee.
  Proof. vm_compute. reflexivity. Qed.

  Lemma normalized_blob_creation_preserves_native_handler_behavior :
    prepare SpecId.CANCUN
      (blob_transaction None 80000 10 (Some 2) 3 [versioned_hash] 7) (blob_block 2) =
    Result.Ready {| InitialGas.intrinsic := 53000; InitialGas.floor := 0;
      InitialGas.execution := 27000; InitialGas.upfront_fee := 742144 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_hash_numeric_bounds_are_checked :
    prepare SpecId.CANCUN (blob_tx 3 [2 ^ 256] 0) (blob_block 2) =
    Result.Malformed MalformedReason.TransactionFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_fee_numeric_bounds_are_checked :
    prepare SpecId.CANCUN (blob_tx (2 ^ 128) [versioned_hash] 0) (blob_block 2) =
    Result.Malformed MalformedReason.TransactionFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_configuration_numeric_bounds_are_checked :
    prepare_gas_with_blob_limit SpecId.CANCUN (blob_tx 3 [versioned_hash] 0) (blob_block 2) (Some (-1)) =
    Result.Malformed MalformedReason.ConfigurationFields.
  Proof. vm_compute. reflexivity. Qed.

  Definition pinned_state_forks : list SpecId.t := [
    SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.TANGERINE; SpecId.SPURIOUS_DRAGON;
    SpecId.BYZANTIUM; SpecId.PETERSBURG; SpecId.ISTANBUL; SpecId.BERLIN;
    SpecId.LONDON; SpecId.MERGE; SpecId.SHANGHAI; SpecId.CANCUN;
    SpecId.PRAGUE; SpecId.OSAKA
  ].

  Lemma empty_call_accounting_covers_all_pinned_state_forks :
    List.map (fun spec =>
      match prepare spec (tx 50000 10 0 []) block with
      | Result.Ready initial => Some (initial.(InitialGas.intrinsic), initial.(InitialGas.floor))
      | _ => None
      end) pinned_state_forks =
    List.repeat (Some (21000, 0)) 12 ++ List.repeat (Some (21000, 21000)) 2.
  Proof. vm_compute. reflexivity. Qed.

  Lemma petersburg_mixed_calldata_has_pre_istanbul_price :
    prepare SpecId.PETERSBURG (tx 50000 10 3 [0; 1; 255; 0]) block =
    Result.Ready {| InitialGas.intrinsic := 21144; InitialGas.floor := 0;
      InitialGas.execution := 28856; InitialGas.upfront_fee := 500000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_mixed_calldata_reduces_nonzero_price :
    prepare SpecId.ISTANBUL (tx 50000 10 3 [0; 1; 255; 0]) block =
    Result.Ready {| InitialGas.intrinsic := 21040; InitialGas.floor := 0;
      InitialGas.execution := 28960; InitialGas.upfront_fee := 500000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma frontier_creation_has_call_base_stipend :
    prepare SpecId.FRONTIER (transaction 0 None 60000 10 0 (List.repeat 0 33)) block =
    Result.Ready {| InitialGas.intrinsic := 21132; InitialGas.floor := 0;
      InitialGas.execution := 38868; InitialGas.upfront_fee := 600000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma homestead_creation_adds_creation_stipend :
    prepare SpecId.HOMESTEAD (transaction 0 None 60000 10 0 (List.repeat 0 33)) block =
    Result.Ready {| InitialGas.intrinsic := 53132; InitialGas.floor := 0;
      InitialGas.execution := 6868; InitialGas.upfront_fee := 600000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma paris_creation_has_no_initcode_word_cost :
    prepare SpecId.MERGE (transaction 0 None 60000 10 0 (List.repeat 0 33)) block =
    Result.Ready {| InitialGas.intrinsic := 53132; InitialGas.floor := 0;
      InitialGas.execution := 6868; InitialGas.upfront_fee := 600000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma shanghai_creation_adds_rounded_initcode_word_cost :
    prepare SpecId.SHANGHAI (transaction 0 None 60000 10 0 (List.repeat 0 33)) block =
    Result.Ready {| InitialGas.intrinsic := 53136; InitialGas.floor := 0;
      InitialGas.execution := 6864; InitialGas.upfront_fee := 600000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma paris_does_not_enforce_shanghai_initcode_limit :
    prepare SpecId.MERGE (transaction 0 None 300000 10 0 (List.repeat 0 49153)) block =
    Result.Ready {| InitialGas.intrinsic := 249612; InitialGas.floor := 0;
      InitialGas.execution := 50388; InitialGas.upfront_fee := 3000000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma shanghai_enforces_initcode_limit_before_intrinsic_gas :
    prepare SpecId.SHANGHAI (transaction 0 None 21000 10 0 (List.repeat 0 49153)) block =
    Result.Rejected GasError.CreateInitCodeSizeLimit.
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_activation_precedes_gas_price_validation :
    prepare SpecId.ISTANBUL (transaction 1 (Some 42) 50000 3 0 []) block =
    Result.Rejected GasError.Eip2930NotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma berlin_access_list_transaction_is_accepted :
    prepare SpecId.BERLIN (transaction 1 (Some 42) 50000 10 0 []) block =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 0;
      InitialGas.execution := 29000; InitialGas.upfront_fee := 500000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_activation_precedes_priority_validation :
    prepare SpecId.BERLIN (typed_transaction 2 50000 3 (Some 5) [] 0 []) block =
    Result.Rejected GasError.Eip1559NotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma london_dynamic_fee_transaction_is_accepted :
    prepare SpecId.LONDON (typed_transaction 2 50000 10 (Some 2) [] 0 []) block =
    Result.Ready {| InitialGas.intrinsic := 21000; InitialGas.floor := 0;
      InitialGas.execution := 29000; InitialGas.upfront_fee := 300000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_activation_precedes_priority_and_blob_validation :
    prepare SpecId.SHANGHAI
      (blob_transaction (Some 42) 50000 3 (Some 5) 0 [] 0) block =
    Result.Rejected GasError.Eip4844NotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma pre_london_native_handler_still_checks_supplied_base_fee :
    prepare SpecId.FRONTIER (tx 50000 3 0 []) block =
    Result.Rejected GasError.GasPriceBelowBaseFee.
  Proof. vm_compute. reflexivity. Qed.

  Lemma berlin_refund_is_capped_at_half_and_beneficiary_receives_full_fee :
    observation (settle SpecId.BERLIN (tx 50000 10 0 []) block
      (frame FrameStatus.Success 20000 20000)) =
    Some (20000, 15000, 15000, 350000, 150000, 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma london_refund_is_capped_at_fifth_and_base_fee_is_burned :
    observation (settle SpecId.LONDON (tx 50000 10 0 []) block
      (frame FrameStatus.Success 20000 20000)) =
    Some (20000, 6000, 24000, 260000, 144000, 96000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma frontier_halt_pays_all_execution_gas_to_beneficiary :
    observation (settle SpecId.FRONTIER (tx 50000 10 0 []) block
      (frame FrameStatus.Halt 20000 20000)) =
    Some (0, 0, 50000, 0, 500000, 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma berlin_revert_preserves_remaining_gas_and_discards_refund :
    observation (settle SpecId.BERLIN (tx 50000 10 0 []) block
      (frame FrameStatus.Revert 20000 20000)) =
    Some (20000, 0, 30000, 200000, 300000, 0).
  Proof. vm_compute. reflexivity. Qed.
End Test.
