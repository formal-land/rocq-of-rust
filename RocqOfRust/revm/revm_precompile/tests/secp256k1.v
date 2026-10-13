From Stdlib Require Import Bool List ZArith.

Require Import revm.revm_precompile.simulate.modexp.
Require Import revm.revm_precompile.simulate.secp256k1.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition input_words (message_hash v r s : Z) : list Z :=
    Modexp.encode_be 32 message_hash ++ Modexp.encode_be 32 v ++
      Modexp.encode_be 32 r ++ Modexp.encode_be 32 s.
  (* Verbatim input/output vectors from core/vm/testdata/precompiles/ecRecover.json;
     source SHA256 58c02c28fbe2739e13d77444fa6cd44b1109b3eed6a92926681bcbf032576e7d. *)
  Definition unrecoverable_key_input : list Z :=
    input_words
      76308771101189865858773040735548556514771034068782654508421667113286807614081
      27
      21923406900483114781061012570467692391673252791540568341688561129267246753331
      46229908194527038764579694863741984340438360895208252939003838631272339814498 ++
      [17; 34; 51; 68; 85; 102; 119; 136; 153; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 48; 49; 50].

  Lemma native_vector_unrecoverable_key :
    Secp256k1.run unrecoverable_key_input 3000 = Secp256k1.Result.Success 3000 [].
  Proof. vm_compute. reflexivity. Qed.

  Definition valid_key_input : list Z :=
    input_words
      11204073434703126239360601449605274408032426064740315997824993450506659380508
      28
      52329435726054258068913521377694398967437550295927220651609223543968680486751
      107977771175407438531332636947368915089807383206072068856821314736756549764425.

  Definition valid_output : list Z :=
    [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 169; 79; 83; 116; 252; 229; 237; 188; 142; 42; 134; 151; 193; 83; 49; 103; 126; 110; 191; 11].

  Lemma native_vector_valid_key :
    Secp256k1.run valid_key_input 3000 = Secp256k1.Result.Success 3000 valid_output.
  Proof. vm_compute. reflexivity. Qed.

  Definition invalid_high_v_1_input : list Z :=
    input_words
      11204073434703126239360601449605274408032426064740315997824993450506659380508
      7237005577332262213973186563042994240829374041602535252466099000494570602524
      52329435726054258068913521377694398967437550295927220651609223543968680486751
      107977771175407438531332636947368915089807383206072068856821314736756549764425.

  Lemma native_vector_invalid_high_v_1 :
    Secp256k1.run invalid_high_v_1_input 3000 = Secp256k1.Result.Success 3000 [].
  Proof. vm_compute. reflexivity. Qed.

  Definition invalid_high_v_2_input : list Z :=
    input_words
      11204073434703126239360601449605274408032426064740315997824993450506659380508
      1267650600228229401496703205404
      52329435726054258068913521377694398967437550295927220651609223543968680486751
      107977771175407438531332636947368915089807383206072068856821314736756549764425.

  Lemma native_vector_invalid_high_v_2 :
    Secp256k1.run invalid_high_v_2_input 3000 = Secp256k1.Result.Success 3000 [].
  Proof. vm_compute. reflexivity. Qed.

  Definition invalid_high_v_3_input : list Z :=
    input_words
      11204073434703126239360601449605274408032426064740315997824993450506659380508
      1267650600228229401496703205660
      52329435726054258068913521377694398967437550295927220651609223543968680486751
      107977771175407438531332636947368915089807383206072068856821314736756549764425.

  Lemma native_vector_invalid_high_v_3 :
    Secp256k1.run invalid_high_v_3_input 3000 = Secp256k1.Result.Success 3000 [].
  Proof. vm_compute. reflexivity. Qed.

  Definition valid_message_hash : Z := 11204073434703126239360601449605274408032426064740315997824993450506659380508.

  Definition valid_r : Z := 52329435726054258068913521377694398967437550295927220651609223543968680486751.

  Definition valid_s : Z := 107977771175407438531332636947368915089807383206072068856821314736756549764425.

  Lemma existing_valid_vector_has_high_s :
    Secp256k1.scalar_modulus / 2 <? valid_s = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma high_s_normalization_and_parity_flip_preserve_recovery :
    Secp256k1.run
      (input_words valid_message_hash 27 valid_r (Secp256k1.scalar_modulus - valid_s)) 3000 =
    Secp256k1.Result.Success 3000 valid_output.
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_gas_precedes_recovery :
    Secp256k1.run valid_key_input 2999 = Secp256k1.Result.OutOfGas.
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_invalid_input_succeeds_with_empty_output :
    Secp256k1.run [] 3000 = Secp256k1.Result.Success 3000 [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_input_still_requires_full_gas :
    Secp256k1.run [] 2999 = Secp256k1.Result.OutOfGas.
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_signature_cost_is_independent_of_available_gas :
    Secp256k1.run invalid_high_v_1_input 100000 = Secp256k1.Result.Success 3000 [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma trailing_input_bytes_are_ignored :
    Secp256k1.run (valid_key_input ++ [255; 0; 17]) 3000 =
    Secp256k1.Result.Success 3000 valid_output.
  Proof. vm_compute. reflexivity. Qed.

  Lemma short_signature_input_is_zero_padded :
    Secp256k1.run (input_words valid_message_hash 28 valid_r 0) 3000 =
    Secp256k1.Result.Success 3000 [] /\
    Secp256k1.run (List.firstn 96 valid_key_input) 3000 =
    Secp256k1.Result.Success 3000 [].
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma invalid_v_is_successful_empty_output :
    List.map (fun v => Secp256k1.run (input_words valid_message_hash v valid_r valid_s) 3000)
      [0; 1; 26; 29; 255; 256] =
    List.repeat (Secp256k1.Result.Success 3000 []) 6.
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_scalar_bounds_are_successful_empty_output :
    List.map (fun scalars =>
      Secp256k1.run (input_words valid_message_hash 28 (fst scalars) (snd scalars)) 3000)
      [(0, valid_s); (Secp256k1.scalar_modulus, valid_s);
       (valid_r, 0); (valid_r, Secp256k1.scalar_modulus)] =
    List.repeat (Secp256k1.Result.Success 3000 []) 4.
  Proof. vm_compute. reflexivity. Qed.

  Lemma non_square_recovery_coordinate_is_invalid :
    Secp256k1.run (input_words 1 27 5 1) 3000 =
    Secp256k1.Result.Success 3000 [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma field_inverse_agrees_with_modular_multiplication :
    Secp256k1.Field.mul 7 (Secp256k1.Field.inverse 7) = 1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma generator_is_on_curve :
    Secp256k1.Point.on_curve Secp256k1.generator_x Secp256k1.generator_y = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma point_identity_preserves_generator :
    Secp256k1.Point.add Secp256k1.Point.infinity Secp256k1.generator = Secp256k1.generator /\
    Secp256k1.Point.add Secp256k1.generator Secp256k1.Point.infinity = Secp256k1.generator.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma equal_point_addition_is_doubling :
    Secp256k1.Point.add Secp256k1.generator Secp256k1.generator =
    Secp256k1.Point.double Secp256k1.generator.
  Proof. vm_compute. reflexivity. Qed.

  Lemma inverse_points_add_to_infinity :
    Secp256k1.Point.add Secp256k1.generator
      (Secp256k1.Point.of_affine Secp256k1.generator_x
        (Secp256k1.Field.negate Secp256k1.generator_y)) =
    Secp256k1.Point.infinity.
  Proof. vm_compute. reflexivity. Qed.

  Lemma generator_has_given_scalar_order :
    Secp256k1.Point.is_infinity
      (Secp256k1.Point.mul Secp256k1.generator Secp256k1.scalar_modulus) = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma recovered_infinity_is_invalid :
    Secp256k1.recover_public_key Secp256k1.generator_x
      Secp256k1.generator_x Secp256k1.generator_x 0 = None.
  Proof. vm_compute. reflexivity. Qed.
End Test.
