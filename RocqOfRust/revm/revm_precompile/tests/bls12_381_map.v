From Stdlib Require Import List ZArith.
Require Import alloy_primitives.bytes.links.mod.
Require Import bytes.links.bytes.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.map_fp_to_g1.
Require Import revm.revm_precompile.simulate.bls12_381.map_fp2_to_g2.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  (* Test-only encoding permits values outside the field to test rejection. *)
  Definition fp_bytes (value : Z) : list u8 :=
    List.map (fun index => {| Integer.value :=
      (value / 256 ^ Z.of_nat index) mod 256 |}) (List.rev (List.seq 0 64)).

  Definition modulus : Z :=
    4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787.

  Example g1_field_must_be_canonical :
    map_fp_to_g1.map_fp_to_g1 (fp_bytes modulus) 5500 =
      Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_gas_precedes_field_validation :
    map_fp_to_g1.map_fp_to_g1 (fp_bytes modulus) 5499 =
      Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_length_precedes_padding :
    map_fp_to_g1.map_fp_to_g1 (List.repeat (1 : u8) 63) 5500 =
      Some (Result.Err PrecompileError.Bls12381MapFpToG1InputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_first_coefficient_must_be_canonical :
    map_fp2_to_g2.map_fp2_to_g2 (fp_bytes modulus ++ fp_bytes 0) 23800 =
      Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_second_coefficient_must_be_canonical :
    map_fp2_to_g2.map_fp2_to_g2 (fp_bytes 0 ++ fp_bytes modulus) 23800 =
      Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_second_padding_precedes_first_field_validation :
    map_fp2_to_g2.map_fp2_to_g2
      (fp_bytes modulus ++ List.repeat (1 : u8) 64) 23800 =
      Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_gas_precedes_field_validation :
    map_fp2_to_g2.map_fp2_to_g2 (fp_bytes 0 ++ fp_bytes modulus) 23799 =
      Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_length_precedes_padding :
    map_fp2_to_g2.map_fp2_to_g2 (List.repeat (1 : u8) 127) 23800 =
      Some (Result.Err PrecompileError.Bls12381MapFp2ToG2InputLength).
  Proof. vm_compute. reflexivity. Qed.
  Definition observe (result : option PrecompileResult.t) :=
    match result with
    | Some (Result.Ok output) =>
      Some (output.(PrecompileOutput.gas_used), output.(PrecompileOutput.gas_refunded),
        output.(PrecompileOutput.reverted),
        List.length output.(PrecompileOutput.bytes)
          .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
    | _ => None
    end.

  (* Exact output hashes are checked by the pinned Osaka mapping fixtures. *)
  Example g1_zero_input_returns_point_at_exact_gas :
    observe (map_fp_to_g1.map_fp_to_g1 (fp_bytes 0) 5500) =
      Some ((5500 : u64), (0 : i64), false, 128%nat).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_zero_input_returns_point_at_exact_gas :
    observe (map_fp2_to_g2.map_fp2_to_g2 (fp_bytes 0 ++ fp_bytes 0) 23800) =
      Some ((23800 : u64), (0 : i64), false, 256%nat).
  Proof. vm_compute. reflexivity. Qed.
End Test.
