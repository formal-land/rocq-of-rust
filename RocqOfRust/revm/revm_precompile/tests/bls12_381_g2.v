From Stdlib Require Import List ZArith.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.bls12_381.g2_add.
Require Import revm.revm_precompile.simulate.bls12_381.g2_msm.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
Import ListNotations.
Open Scope Z_scope.

Module Test.
  (* Wire encoding is test-only and deliberately allows non-canonical fields. *)
  Definition bytes (width : nat) (value : Z) : list u8 :=
    List.map (fun index => {| Integer.value :=
      (value / 256 ^ Z.of_nat index) mod 256 |}) (List.rev (List.seq 0 width)).

  Definition point (x0 x1 y0 y1 : Z) : list u8 :=
    bytes 64 x0 ++ bytes 64 x1 ++ bytes 64 y0 ++ bytes 64 y1.

  Definition modulus : Z :=
    4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787.

  Definition infinity : list u8 := point 0 0 0 0.

  Definition invalid_point : list u8 := point 1 0 1 0.

  Example first_x0_must_be_canonical :
    g2_add.g2_add (point modulus 0 0 0 ++ infinity) 600 =
      Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example first_x1_must_be_canonical :
    g2_add.g2_add (point 0 modulus 0 0 ++ infinity) 600 =
      Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example first_y0_must_be_canonical :
    g2_add.g2_add (point 0 0 modulus 0 ++ infinity) 600 =
      Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example first_y1_must_be_canonical :
    g2_add.g2_add (point 0 0 0 modulus ++ infinity) 600 =
      Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example infinity_does_not_skip_second_curve_check :
    g2_add.g2_add (infinity ++ invalid_point) 600 =
      Some (Result.Err PrecompileError.Bls12381G2NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example infinity_does_not_skip_second_field_check :
    g2_add.g2_add (infinity ++ point 0 0 0 modulus) 600 =
      Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example earlier_curve_error_precedes_later_field_error :
    g2_add.g2_add (invalid_point ++ point modulus 0 0 0) 600 =
      Some (Result.Err PrecompileError.Bls12381G2NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example later_padding_error_precedes_first_curve_error :
    g2_add.g2_add (invalid_point ++ List.repeat (1 : u8) 256) 600 =
      Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example zero_scalar_does_not_skip_curve_check :
    g2_msm.g2_msm (invalid_point ++ bytes 32 0) 22500 =
      Some (Result.Err PrecompileError.Bls12381G2NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example earlier_curve_error_precedes_later_padding :
    g2_msm.g2_msm
      (invalid_point ++ bytes 32 0 ++ List.repeat (1 : u8) 288) 45000 =
      Some (Result.Err PrecompileError.Bls12381G2NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example gas_precedes_point_validation :
    g2_msm.g2_msm (invalid_point ++ bytes 32 0) 22499 =
      Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example length_precedes_gas :
    g2_msm.g2_msm (bytes 287 0) 0 =
      Some (Result.Err PrecompileError.Bls12381G2MsmInputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example nonzero_scalar_times_infinity :
    g2_msm.g2_msm (infinity ++ bytes 32 1) 22500 =
      Some (Result.Ok (Impl_PrecompileOutput.new 22500
        (alloy_primitives.bytes.simulate.mod.Impl_Bytes.copy_from_slice infinity))).
  Proof. vm_compute. reflexivity. Qed.

  Example mismatched_provider_vectors_are_explicit :
    arkworks.p2_msm [arkworks.G2Affine.zero] [] = None.
  Proof. vm_compute. reflexivity. Qed.
End Test.
