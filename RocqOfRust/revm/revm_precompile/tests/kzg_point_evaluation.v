From Stdlib Require Import List ZArith.
Require Import revm.revm_precompile.simulate.kzg_point_evaluation.

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

  Definition bad_input : list Z :=
    versioned_hash ++ z ++ List.repeat 0 31 ++ [1] ++
    KzgPointEvaluation.infinity ++ KzgPointEvaluation.infinity.

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

  Lemma other_proofs_stay_incomplete :
    KzgPointEvaluation.run
      (KzgPointEvaluation.versioned_hash (List.repeat 0 48) ++ z ++ List.repeat 0 32 ++
       List.repeat 0 48 ++ List.repeat 0 48) 50000 =
      KzgPointEvaluation.Result.Unsupported.
  Proof. vm_compute. reflexivity. Qed.
End Test.
