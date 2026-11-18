From Stdlib Require Import List ZArith.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.interface.
Require Import revm.revm_precompile.simulate.kzg_point_evaluation.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  (** Exact versioned hash and z from the pinned Cancun EEST
      point_evaluation_precompile/tx_entry_point.json family. *)
  Definition versioned_hash : list Z :=
    [1; 6; 87; 243; 117; 84; 199; 129; 64; 42; 34; 145; 125; 238; 47; 117;
     222; 247; 171; 150; 109; 123; 119; 9; 5; 57; 142; 186; 60; 68; 64; 20].

  Definition z : list Z :=
    [98; 60; 227; 28; 249; 117; 154; 92; 141; 175; 58; 53; 121; 146; 249; 243;
     221; 127; 147; 57; 216; 153; 139; 200; 230; 131; 115; 229; 79; 0; 183; 94].

  Definition good_input : list Z :=
    versioned_hash ++ z ++ List.repeat 0 32 ++
    KzgPointEvaluation.infinity ++ KzgPointEvaluation.infinity.

  (** Malformed proof encoding; finite false proofs are checked by the native
      EEST vectors rather than repeated large vm_compute evaluations. *)
  Definition bad_input : list Z :=
    versioned_hash ++ z ++ List.repeat 0 31 ++ [1] ++
    KzgPointEvaluation.infinity ++ List.repeat 0 48.

  Lemma pinned_versioned_hash :
    KzgPointEvaluation.versioned_hash KzgPointEvaluation.infinity = versioned_hash.
  Proof. vm_compute. reflexivity. Qed.

  Lemma eip4844_return_value : KzgPointEvaluation.return_value =
    List.repeat 0 30 ++ [16; 0] ++
    [115; 237; 167; 83; 41; 157; 125; 72; 51; 57; 216; 8; 9; 161; 216; 5;
     83; 189; 164; 2; 255; 254; 91; 254; 255; 255; 255; 255; 0; 0; 0; 1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma correct_proof_insufficient_gas :
    KzgPointEvaluation.run good_input 49999 = KzgPointEvaluation.Result.OutOfGas.
  Proof. vm_compute. reflexivity. Qed.

  Lemma correct_proof_exact_gas :
    KzgPointEvaluation.run good_input 50000 =
      KzgPointEvaluation.Result.Success 50000 KzgPointEvaluation.return_value.
  Proof. vm_compute. reflexivity. Qed.

  Lemma correct_proof_extra_gas :
    KzgPointEvaluation.run good_input 50001 =
      KzgPointEvaluation.Result.Success 50000 KzgPointEvaluation.return_value.
  Proof. vm_compute. reflexivity. Qed.

  Lemma incorrect_proof_insufficient_gas :
    KzgPointEvaluation.run bad_input 49999 = KzgPointEvaluation.Result.OutOfGas.
  Proof. vm_compute. reflexivity. Qed.

  Lemma incorrect_proof_exact_gas :
    KzgPointEvaluation.run bad_input 50000 = KzgPointEvaluation.Result.InvalidInput.
  Proof. vm_compute. reflexivity. Qed.

  Lemma incorrect_proof_extra_gas :
    KzgPointEvaluation.run bad_input 50001 = KzgPointEvaluation.Result.InvalidInput.
  Proof. vm_compute. reflexivity. Qed.

  Lemma wrong_length_after_gas :
    KzgPointEvaluation.run [] 50000 = KzgPointEvaluation.Result.InvalidInput.
  Proof. vm_compute. reflexivity. Qed.

  Lemma wrong_versioned_hash :
    KzgPointEvaluation.run (0 :: List.tl good_input) 50000 =
      KzgPointEvaluation.Result.InvalidInput.
  Proof. vm_compute. reflexivity. Qed.

  Lemma noncanonical_z :
    KzgPointEvaluation.run
      (versioned_hash ++ KzgPointEvaluation.encode_be 32 KzgPointEvaluation.scalar_modulus ++
       List.repeat 0 32 ++ KzgPointEvaluation.infinity ++ KzgPointEvaluation.infinity)
      50000 = KzgPointEvaluation.Result.InvalidInput.
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_compressed_points_are_rejected :
    KzgPointEvaluation.run
      (KzgPointEvaluation.versioned_hash (List.repeat 0 48) ++ z ++ List.repeat 0 32 ++
       List.repeat 0 48 ++ List.repeat 0 48) 50000 =
      KzgPointEvaluation.Result.InvalidInput.
  Proof. vm_compute. reflexivity. Qed.
End Test.

Module TypedTest.
  Definition bytes (input : list Z) : list u8 :=
    List.map (fun byte => {| Integer.value := byte |}) input.

  Example gas_error_precedes_length_error :
    kzg_point_evaluation.run [] 49999 =
      Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example length_error_is_distinct :
    kzg_point_evaluation.run [] 50000 =
      Some (Result.Err PrecompileError.BlobInvalidInputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example hash_error_precedes_proof_error :
    kzg_point_evaluation.run (List.repeat (0 : u8) 192) 50000 =
      Some (Result.Err PrecompileError.BlobMismatchedVersion).
  Proof. vm_compute. reflexivity. Qed.

  Example malformed_proof_reports_verification_error :
    kzg_point_evaluation.run (bytes Test.bad_input) 50000 =
      Some (Result.Err PrecompileError.BlobVerifyKzgProofFailed).
  Proof. vm_compute. reflexivity. Qed.

  Example successful_output_preserves_rust_fields :
    match kzg_point_evaluation.run (bytes Test.good_input) 50000 with
    | Some (Result.Ok output) =>
      Some (output.(PrecompileOutput.gas_used).(Integer.value),
        output.(PrecompileOutput.gas_refunded).(Integer.value),
        output.(PrecompileOutput.reverted))
    | _ => None
    end = Some (50000, 0, false).
  Proof. vm_compute. reflexivity. Qed.

  Example success_accepts_maximum_u64_gas :
    kzg_point_evaluation.run (bytes Test.good_input)
      {| Integer.value := 2 ^ 64 - 1 |} =
    kzg_point_evaluation.run (bytes Test.good_input) 50000.
  Proof. vm_compute. reflexivity. Qed.
End TypedTest.
