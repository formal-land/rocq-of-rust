From Stdlib Require Import List ZArith.

Require Import revm.revm_precompile.simulate.bn254.
Require Import revm.revm_precompile.simulate.bn254_pairing.
Require Import revm.revm_precompile.simulate.modexp.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition word := Modexp.encode_be 32.
  Definition encoded_g2 (x_imag x_real y_imag y_real : Z) : list Z :=
    word x_imag ++ word x_real ++ word y_imag ++ word y_real.

  (** The G2 generator from go-ethereum/crypto/bn256/google/twist.go. *)
  Definition generator : list Z := encoded_g2
    11559732032986387107991004021392285783925812861821192530917403151452391805634
    10857046999023057135944570762232829481370756359578518086990519993285655852781
    4082367875863433681332203403145435568316851327593401208105741076214120093531
    8495653923123431417604973247489272438418190587263600148770280649306958101930.

  (** Independently generated on-curve point with [r]Q nonzero. *)
  Definition non_subgroup : list Z := encoded_g2 0 1
    5912654199736721486680175016176231956195085055698687135131307249486702594212
    18278151005453108793778860132295291098363647455926340152056652516292830556603.

  Lemma fq2_i_squared :
    Bn254Pairing.Fq2.square (Bn254Pairing.Fq2.make 0 1) =
      Bn254Pairing.Fq2.make (-1) 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma fq2_inverse :
    Bn254Pairing.Fq2.mul (Bn254Pairing.Fq2.make 17 9)
      (Bn254Pairing.Fq2.inverse (Bn254Pairing.Fq2.make 17 9)) =
      Bn254Pairing.Fq2.one.
  Proof. vm_compute. reflexivity. Qed.

  Lemma twist_coefficient :
    Bn254Pairing.Fq2.mul Bn254Pairing.G2.twist_b Bn254Pairing.Fq2.xi =
      Bn254Pairing.Fq2.of_z 3.
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_point_is_infinity :
    Bn254Pairing.decode_g2 (List.repeat 0 128) =
      Bn254Pairing.Decoded.Valid Bn254Pairing.G2.infinity.
  Proof. vm_compute. reflexivity. Qed.

  Lemma short_input_is_invalid :
    Bn254Pairing.decode_g2 (List.repeat 0 127) =
      Bn254Pairing.Decoded.Invalid Bn254Pairing.Error.InvalidLength.
  Proof. vm_compute. reflexivity. Qed.

  Lemma long_input_is_invalid :
    Bn254Pairing.decode_g2 (List.repeat 0 129) =
      Bn254Pairing.Decoded.Invalid Bn254Pairing.Error.InvalidLength.
  Proof. vm_compute. reflexivity. Qed.

  Lemma field_modulus_is_not_a_coordinate :
    Bn254Pairing.decode_g2 (encoded_g2 Bn254.field_modulus 0 0 0) =
      Bn254Pairing.Decoded.Invalid Bn254Pairing.Error.FieldPointNotAMember.
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_byte_is_rejected :
    Bn254Pairing.decode_g2 (256 :: List.repeat 0 127) =
      Bn254Pairing.Decoded.Invalid Bn254Pairing.Error.FieldPointNotAMember.
  Proof. vm_compute. reflexivity. Qed.

  Lemma off_curve_is_rejected :
    Bn254Pairing.decode_g2 (encoded_g2 0 1 0 1) =
      Bn254Pairing.Decoded.Invalid Bn254Pairing.Error.AffineGFailedToCreate.
  Proof. vm_compute. reflexivity. Qed.

  Lemma generator_is_accepted :
    match Bn254Pairing.decode_g2 generator with
    | Bn254Pairing.Decoded.Valid _ => true
    | Bn254Pairing.Decoded.Invalid _ => false
    end = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma non_subgroup_is_on_curve :
    Bn254Pairing.G2.on_curve
      (Bn254Pairing.Fq2.make 1 0)
      (Bn254Pairing.Fq2.make
        18278151005453108793778860132295291098363647455926340152056652516292830556603
        5912654199736721486680175016176231956195085055698687135131307249486702594212) = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma non_subgroup_is_rejected :
    Bn254Pairing.decode_g2 non_subgroup =
      Bn254Pairing.Decoded.Invalid Bn254Pairing.Error.AffineGFailedToCreate.
  Proof. vm_compute. reflexivity. Qed.
End Test.
