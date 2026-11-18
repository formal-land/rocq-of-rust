From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.links.result.
Require Import alloy_primitives.links.common.
Require Import alloy_primitives.bits.links.address.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_context_interface.simulate.result.
Require Import revm.revm_handler.simulate.validation.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module ValidationTest.
  Record transaction : Set := {
    tx_type : Z;
    gas_limit : Z;
    gas_price : Z;
    priority : option Z;
    blobs : list aliases.B256.t;
    blob_price : Z;
  }.

  Global Instance transaction_fees : Transaction.Fees.C transaction := {
    Transaction.Fees.tx_type tx := {| Integer.value := tx.(tx_type) |};
    Transaction.Fees.gas_limit tx := {| Integer.value := tx.(gas_limit) |};
    Transaction.Fees.gas_price tx := {| Integer.value := tx.(gas_price) |};
    Transaction.Fees.value _ := {| Uint.value := 0 |};
    Transaction.Fees.max_priority_fee_per_gas tx :=
      option_map (fun amount => {| Integer.value := amount |}) tx.(priority);
    Transaction.Fees.blob_versioned_hashes tx := tx.(blobs);
    Transaction.Fees.max_fee_per_blob_gas tx := {| Integer.value := tx.(blob_price) |};
  }.

  Definition tx (kind : Z) : transaction := {|
    tx_type := kind;
    gas_limit := 100;
    gas_price := 10;
    priority := Some 2;
    blobs := [FixedBytes.from_Z (2 ^ 248)];
    blob_price := 3;
  |}.

  Definition extra : validation.TxFields.t := {|
    validation.TxFields.chain_id := Some {| Integer.value := 1 |};
    validation.TxFields.kind := TxKind.Call {| Address.value := 42 |};
    validation.TxFields.input_length := 0;
    validation.TxFields.authorization_list_len := 1;
  |}.

  Definition block : validation.BlockFields.t := {|
    validation.BlockFields.basefee := 4;
    validation.BlockFields.gas_limit := 1000;
    validation.BlockFields.blob_gasprice := 3;
    validation.BlockFields.prevrandao := Some (FixedBytes.from_Z 0);
    validation.BlockFields.blob_excess_gas := Some {| Integer.value := 0 |};
  |}.

  Definition cfg : validation.CfgFields.t := {|
    validation.CfgFields.chain_id := 1;
    validation.CfgFields.tx_chain_id_check := true;
    validation.CfgFields.tx_gas_limit_cap := 500;
    validation.CfgFields.is_base_fee_check_disabled := false;
    validation.CfgFields.is_priority_fee_check_disabled := false;
    validation.CfgFields.is_block_gas_limit_disabled := false;
    validation.CfgFields.max_blobs_per_tx := Some {| Integer.value := 2 |};
    validation.CfgFields.max_initcode_size := 32;
  |}.

  Lemma pre_merge_header_does_not_require_randao_or_blob_gas :
    validation.validate_header SpecId.LONDON
      (block <| validation.BlockFields.prevrandao := None |>
        <| validation.BlockFields.blob_excess_gas := None |>) = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma missing_randao_precedes_missing_blob_gas :
    validation.validate_header SpecId.CANCUN
      (block <| validation.BlockFields.prevrandao := None |>
        <| validation.BlockFields.blob_excess_gas := None |>) =
    Result.Err InvalidHeader.PrevrandaoNotSet.
  Proof. vm_compute. reflexivity. Qed.

  Lemma cancun_requires_blob_gas_header :
    validation.validate_header SpecId.CANCUN
      (block <| validation.BlockFields.blob_excess_gas := None |>) =
    Result.Err InvalidHeader.ExcessBlobGasNotSet.
  Proof. vm_compute. reflexivity. Qed.

  Lemma valid_osaka_environment :
    validation.validate_tx_env (tx 4) extra cfg block SpecId.OSAKA = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_chain_id_precedes_gas_cap :
    validation.validate_tx_env ((tx 0) <| gas_limit := 501 |>)
      (extra <| validation.TxFields.chain_id := Some {| Integer.value := 2 |} |>) cfg block SpecId.OSAKA =
    Result.Err InvalidTransaction.InvalidChainId.
  Proof. vm_compute. reflexivity. Qed.

  Lemma legacy_can_omit_chain_id :
    validation.validate_tx_env (tx 0)
      (extra <| validation.TxFields.chain_id := None |>) cfg block SpecId.OSAKA =
    Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma typed_transaction_requires_chain_id :
    validation.validate_tx_env (tx 2)
      (extra <| validation.TxFields.chain_id := None |>) cfg block SpecId.OSAKA =
    Result.Err InvalidTransaction.MissingChainId.
  Proof. vm_compute. reflexivity. Qed.

  Lemma disabled_chain_check_accepts_missing_chain_id :
    validation.validate_tx_env (tx 2)
      (extra <| validation.TxFields.chain_id := None |>)
      (cfg <| validation.CfgFields.tx_chain_id_check := false |>) block SpecId.OSAKA =
    Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma custom_type_omits_chain_and_skips_fee_validation :
    validation.validate_tx_env ((tx 255) <| gas_price := 0 |>)
      (extra <| validation.TxFields.chain_id := None |>) cfg block SpecId.OSAKA =
    Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma gas_cap_equality_is_accepted :
    validation.validate_tx_env ((tx 0) <| gas_limit := 500 |>)
      extra cfg block SpecId.OSAKA = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma cap_precedes_unsupported_transaction_type :
    validation.validate_tx_env ((tx 4) <| gas_limit := 501 |>)
      extra cfg block SpecId.BERLIN =
    Result.Err (InvalidTransaction.TxGasLimitGreaterThanCap 501 500).
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_activation_precedes_low_fee :
    validation.validate_tx_env ((tx 1) <| gas_price := 0 |>)
      extra cfg block SpecId.ISTANBUL = Result.Err InvalidTransaction.Eip2930NotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_requires_london :
    validation.validate_tx_env (tx 2) extra cfg block SpecId.BERLIN =
    Result.Err InvalidTransaction.Eip1559NotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blobs_require_cancun :
    validation.validate_tx_env (tx 3) extra cfg block SpecId.SHANGHAI =
    Result.Err InvalidTransaction.Eip4844NotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma authorization_requires_prague :
    validation.validate_tx_env (tx 4) extra cfg block SpecId.CANCUN =
    Result.Err InvalidTransaction.Eip7702NotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma priority_error_precedes_base_fee_error :
    validation.validate_tx_env ((tx 2) <| gas_price := 1 |> <| priority := Some 2 |>)
      extra cfg block SpecId.OSAKA = Result.Err InvalidTransaction.PriorityFeeGreaterThanMaxFee.
  Proof. vm_compute. reflexivity. Qed.

  Lemma disabled_priority_check_still_checks_base_fee :
    validation.validate_tx_env ((tx 2) <| gas_price := 1 |> <| priority := Some 2 |>)
      extra (cfg <| validation.CfgFields.is_priority_fee_check_disabled := true |>)
      block SpecId.OSAKA = Result.Err InvalidTransaction.GasPriceLessThanBasefee.
  Proof. vm_compute. reflexivity. Qed.

  Lemma disabled_base_fee_check_still_checks_priority :
    validation.validate_tx_env ((tx 2) <| gas_price := 1 |> <| priority := Some 2 |>)
      extra (cfg <| validation.CfgFields.is_base_fee_check_disabled := true |>)
      block SpecId.OSAKA = Result.Err InvalidTransaction.PriorityFeeGreaterThanMaxFee.
  Proof. vm_compute. reflexivity. Qed.

  Lemma both_fee_checks_can_be_disabled :
    validation.validate_tx_env ((tx 2) <| gas_price := 1 |> <| priority := Some 2 |>)
      extra (cfg <| validation.CfgFields.is_base_fee_check_disabled := true |>
        <| validation.CfgFields.is_priority_fee_check_disabled := true |>)
      block SpecId.OSAKA = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma priority_plus_base_fee_saturates_u128 :
    validation.validate_priority_fee_tx
      {| Integer.value := 2 ^ 128 - 1 |} {| Integer.value := 2 ^ 128 - 1 |}
      (Some {| Integer.value := 4 |}) false = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_fee_error_precedes_empty_blobs :
    validation.validate_tx_env ((tx 3) <| blob_price := 2 |> <| blobs := [] |>)
      extra cfg block SpecId.OSAKA =
    Result.Err (InvalidTransaction.BlobGasPriceGreaterThanMax 3 2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_blob_list_is_rejected :
    validation.validate_tx_env ((tx 3) <| blobs := [] |>) extra cfg block SpecId.OSAKA =
    Result.Err InvalidTransaction.EmptyBlobs.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_version_error_precedes_blob_count :
    validation.validate_tx_env ((tx 3) <| blobs := List.repeat (FixedBytes.from_Z 0) 3 |>)
      extra cfg block SpecId.OSAKA = Result.Err InvalidTransaction.BlobVersionNotSupported.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_count_equality_is_accepted :
    validation.validate_tx_env ((tx 3) <| blobs := List.repeat (FixedBytes.from_Z (2 ^ 248)) 2 |>)
      extra cfg block SpecId.OSAKA = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_count_above_limit_is_rejected :
    validation.validate_tx_env ((tx 3) <| blobs := List.repeat (FixedBytes.from_Z (2 ^ 248)) 3 |>)
      extra cfg block SpecId.OSAKA = Result.Err (InvalidTransaction.TooManyBlobs 3 2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma absent_blob_count_limit_accepts_more_blobs :
    validation.validate_tx_env ((tx 3) <| blobs := List.repeat (FixedBytes.from_Z (2 ^ 248)) 3 |>)
      extra (cfg <| validation.CfgFields.max_blobs_per_tx := None |>)
      block SpecId.OSAKA = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_authorizations_precede_block_gas_limit :
    validation.validate_tx_env (tx 4)
      (extra <| validation.TxFields.authorization_list_len := 0 |>) cfg
      (block <| validation.BlockFields.gas_limit := 99 |>) SpecId.OSAKA =
    Result.Err InvalidTransaction.EmptyAuthorizationList.
  Proof. vm_compute. reflexivity. Qed.

  Lemma block_gas_equality_is_accepted :
    validation.validate_tx_env (tx 0) extra cfg
      (block <| validation.BlockFields.gas_limit := 100 |>) SpecId.OSAKA = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma block_gas_error_precedes_initcode_size :
    validation.validate_tx_env (tx 0)
      (extra <| validation.TxFields.kind := TxKind.Create |>
        <| validation.TxFields.input_length := 33 |>) cfg
      (block <| validation.BlockFields.gas_limit := 99 |>) SpecId.OSAKA =
    Result.Err InvalidTransaction.CallerGasLimitMoreThanBlock.
  Proof. vm_compute. reflexivity. Qed.

  Lemma disabled_block_gas_check_preserves_initcode_check :
    validation.validate_tx_env (tx 0)
      (extra <| validation.TxFields.kind := TxKind.Create |>
        <| validation.TxFields.input_length := 33 |>)
      (cfg <| validation.CfgFields.is_block_gas_limit_disabled := true |>)
      (block <| validation.BlockFields.gas_limit := 99 |>) SpecId.OSAKA =
    Result.Err InvalidTransaction.CreateInitCodeSizeLimit.
  Proof. vm_compute. reflexivity. Qed.

  Lemma initcode_equality_is_accepted :
    validation.validate_tx_env (tx 0)
      (extra <| validation.TxFields.kind := TxKind.Create |>
        <| validation.TxFields.input_length := 32 |>) cfg block SpecId.OSAKA = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma initcode_limit_does_not_apply_to_calls :
    validation.validate_tx_env (tx 0)
      (extra <| validation.TxFields.input_length := 33 |>) cfg block SpecId.OSAKA = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma initcode_limit_starts_at_shanghai :
    validation.validate_tx_env (tx 0)
      (extra <| validation.TxFields.kind := TxKind.Create |>
        <| validation.TxFields.input_length := 33 |>) cfg block SpecId.MERGE = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma full_environment_checks_header_before_chain :
    validation.validate_env (tx 0)
      (extra <| validation.TxFields.chain_id := Some {| Integer.value := 2 |} |>) cfg
      (block <| validation.BlockFields.prevrandao := None |>) SpecId.OSAKA =
    Result.Err (validation.EnvironmentError.Header InvalidHeader.PrevrandaoNotSet).
  Proof. vm_compute. reflexivity. Qed.

  Lemma full_environment_propagates_transaction_error :
    validation.validate_env (tx 0)
      (extra <| validation.TxFields.chain_id := Some {| Integer.value := 2 |} |>) cfg block SpecId.OSAKA =
    Result.Err (validation.EnvironmentError.Transaction InvalidTransaction.InvalidChainId).
  Proof. vm_compute. reflexivity. Qed.

  Lemma full_environment_accepts_valid_inputs :
    validation.validate_env (tx 4) extra cfg block SpecId.OSAKA = Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.

  Lemma rust_environment_does_not_impose_adapter_authorization_create_restriction :
    validation.validate_tx_env (tx 4)
      (extra <| validation.TxFields.kind := TxKind.Create |>) cfg block SpecId.OSAKA =
    Result.Ok tt.
  Proof. vm_compute. reflexivity. Qed.
End ValidationTest.
