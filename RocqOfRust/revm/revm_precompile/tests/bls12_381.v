Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.g1_add.
Require Import revm.revm_precompile.simulate.bls12_381.g1_msm.
Require Import revm.revm_precompile.simulate.bls12_381.g2_add.
Require Import revm.revm_precompile.simulate.bls12_381.g2_msm.
Require Import revm.revm_precompile.simulate.bls12_381.map_fp2_to_g2.
Require Import revm.revm_precompile.simulate.bls12_381.map_fp_to_g1.
Require Import revm.revm_precompile.simulate.bls12_381.pairing.
Require Import revm.revm_precompile.simulate.bls12_381.utils.
Require Import revm.revm_precompile.simulate.bls12_381_const.
Require Import revm.revm_precompile.simulate.bls12_381_utils.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module BlsBoundaryTests.
  Definition bytes (count : nat) (byte : u8) : list u8 := List.repeat byte count.

  Example g1_add_gas_precedes_length :
    g1_add.g1_add [] 0 = Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_add_length_at_exact_gas :
    g1_add.g1_add [] 375 = Some (Result.Err PrecompileError.Bls12381G1AddInputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_add_invalid_padding :
    g1_add.g1_add (bytes 256 17) 375 = Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_add_valid_encoding_stays_unsupported :
    g1_add.g1_add (bytes 256 0) 375 = None.
  Proof. vm_compute. reflexivity. Qed.

  Example g2_add_gas_precedes_length :
    g2_add.g2_add [] 0 = Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_add_length_at_exact_gas :
    g2_add.g2_add [] 600 = Some (Result.Err PrecompileError.Bls12381G2AddInputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_add_invalid_padding :
    g2_add.g2_add (bytes 512 17) 600 = Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_add_valid_encoding_stays_unsupported :
    g2_add.g2_add (bytes 512 0) 600 = None.
  Proof. vm_compute. reflexivity. Qed.

  Example map_fp_to_g1_gas_precedes_length :
    map_fp_to_g1.map_fp_to_g1 [] 0 = Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example map_fp_to_g1_length_at_exact_gas :
    map_fp_to_g1.map_fp_to_g1 [] 5500 = Some (Result.Err PrecompileError.Bls12381MapFpToG1InputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example map_fp_to_g1_invalid_padding :
    map_fp_to_g1.map_fp_to_g1 (bytes 64 17) 5500 = Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example map_fp_to_g1_valid_encoding_stays_unsupported :
    map_fp_to_g1.map_fp_to_g1 (bytes 64 0) 5500 = None.
  Proof. vm_compute. reflexivity. Qed.

  Example map_fp2_to_g2_gas_precedes_length :
    map_fp2_to_g2.map_fp2_to_g2 [] 0 = Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example map_fp2_to_g2_length_at_exact_gas :
    map_fp2_to_g2.map_fp2_to_g2 [] 23800 = Some (Result.Err PrecompileError.Bls12381MapFp2ToG2InputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example map_fp2_to_g2_invalid_padding :
    map_fp2_to_g2.map_fp2_to_g2 (bytes 128 17) 23800 = Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example map_fp2_to_g2_valid_encoding_stays_unsupported :
    map_fp2_to_g2.map_fp2_to_g2 (bytes 128 0) 23800 = None.
  Proof. vm_compute. reflexivity. Qed.

  Example g1_msm_length_precedes_gas :
    g1_msm.g1_msm [] 0 = Some (Result.Err PrecompileError.Bls12381G1MsmInputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_msm_valid_length_insufficient_gas :
    g1_msm.g1_msm (bytes 160 17) 11999 = Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_msm_padding_at_exact_gas :
    g1_msm.g1_msm (bytes 160 17) 12000 = Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_msm_valid_encoding_stays_unsupported :
    g1_msm.g1_msm (bytes 160 0) 12000 = None.
  Proof. vm_compute. reflexivity. Qed.

  Example g2_msm_length_precedes_gas :
    g2_msm.g2_msm [] 0 = Some (Result.Err PrecompileError.Bls12381G2MsmInputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_msm_valid_length_insufficient_gas :
    g2_msm.g2_msm (bytes 288 17) 22499 = Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_msm_padding_at_exact_gas :
    g2_msm.g2_msm (bytes 288 17) 22500 = Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_msm_valid_encoding_stays_unsupported :
    g2_msm.g2_msm (bytes 288 0) 22500 = None.
  Proof. vm_compute. reflexivity. Qed.

  Example pairing_length_precedes_gas :
    pairing.pairing [] 0 = Some (Result.Err PrecompileError.Bls12381PairingInputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example pairing_valid_length_insufficient_gas :
    pairing.pairing (bytes 384 17) 70299 = Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example pairing_padding_at_exact_gas :
    pairing.pairing (bytes 384 17) 70300 = Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example pairing_valid_encoding_stays_unsupported :
    pairing.pairing (bytes 384 0) 70300 = None.
  Proof. vm_compute. reflexivity. Qed.

  Example g1_msm_does_not_skip_unknown_first_point :
    g1_msm.g1_msm (bytes 160 0 ++ bytes 160 17) 22776 = None.
  Proof. vm_compute. reflexivity. Qed.

  Example g2_msm_does_not_skip_unknown_first_point :
    g2_msm.g2_msm (bytes 288 0 ++ bytes 288 17) 45000 = None.
  Proof. vm_compute. reflexivity. Qed.

  Example pairing_checks_later_padding_before_crypto :
    pairing.pairing (bytes 384 0 ++ bytes 384 17) 102900 = Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_discount_two_pairs :
    bls12_381_utils.msm_required_gas 2 bls12_381_const.DISCOUNT_TABLE_G1_MSM 12000 = {| Integer.value := 22776 |}.
  Proof. vm_compute. reflexivity. Qed.

  Example g2_discount_two_pairs :
    bls12_381_utils.msm_required_gas 2 bls12_381_const.DISCOUNT_TABLE_G2_MSM 22500 = {| Integer.value := 45000 |}.
  Proof. vm_compute. reflexivity. Qed.

  Example fp_padding_wrong_length :
    bls_utils.remove_fp_padding [] =
      Result.Err PrecompileError.Bls12381FpPaddingLength.
  Proof. vm_compute. reflexivity. Qed.

  Example g1_padding_wrong_length :
    bls_utils.remove_g1_padding [] =
      Result.Err PrecompileError.Bls12381G1PaddingLength.
  Proof. vm_compute. reflexivity. Qed.

  Example g2_padding_wrong_length :
    bls_utils.remove_g2_padding [] =
      Result.Err PrecompileError.Bls12381G2PaddingLength.
  Proof. vm_compute. reflexivity. Qed.

  Example fp_padding_preserves_payload :
    bls_utils.remove_fp_padding (bytes 16 0 ++ bytes 48 17) =
      Result.Ok (bytes 48 17).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_padding_preserves_coordinates :
    bls_utils.remove_g1_padding
      (bytes 16 0 ++ bytes 48 17 ++ bytes 16 0 ++ bytes 48 18) =
      Result.Ok (bytes 48 17, bytes 48 18).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_padding_preserves_coordinates :
    bls_utils.remove_g2_padding
      (bytes 16 0 ++ bytes 48 17 ++ bytes 16 0 ++ bytes 48 18 ++
       bytes 16 0 ++ bytes 48 19 ++ bytes 16 0 ++ bytes 48 20) =
      Result.Ok (bytes 48 17, bytes 48 18, bytes 48 19, bytes 48 20).
  Proof. vm_compute. reflexivity. Qed.
End BlsBoundaryTests.
