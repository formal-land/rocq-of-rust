From Stdlib Require Import Bool List ZArith.

Import ListNotations.
Open Scope Z_scope.

(** Executable modular exponentiation for byte-valued inputs and u64 gas,
    following revm_precompile/modexp.rs on a 64-bit target. Berlin pricing
    applies to Cancun and Prague; Osaka pricing and limits are not modeled.
    Computation checks do not prove correspondence with the native provider. *)
Module Modexp.
  Module Result.
    Inductive t :=
    | Success (cost : Z) (output : list Z)
    | OutOfGas
    | InvalidLength.
  End Result.

  Definition u64_max : Z := 2 ^ 64 - 1.
  Definition saturating_u64 (value : Z) : Z := Z.min value u64_max.

  Definition decode_be (input : list Z) : Z :=
    List.fold_left (fun value byte => value * 256 + byte) input 0.

  (** Test the offset before converting it to unary list indexing. Declared
      lengths can be far larger than the actual, finite input. *)
  Definition suffix (input : list Z) (offset : Z) : list Z :=
    if Z.of_nat (List.length input) <=? offset then []
    else List.skipn (Z.to_nat offset) input.

  Definition read_padded (input : list Z) (offset size : Z) : list Z :=
    let present := List.firstn (Z.to_nat size) (suffix input offset) in
    present ++ List.repeat 0 (Z.to_nat (size - Z.of_nat (List.length present))).

  Fixpoint encode_le (size : nat) (value : Z) : list Z :=
    match size with
    | O => []
    | S rest => value mod 256 :: encode_le rest (value / 256)
    end.

  Definition encode_be (size value : Z) : list Z :=
    List.rev (encode_le (Z.to_nat size) value).

  Fixpoint pow_positive (base : Z) (exponent : positive) (modulus : Z) : Z :=
    match exponent with
    | xH => base mod modulus
    | xO rest =>
        let half := pow_positive base rest modulus in
        (half * half) mod modulus
    | xI rest =>
        let half := pow_positive base rest modulus in
        ((half * half) mod modulus * base) mod modulus
    end.

  Definition pow_mod (base exponent modulus : Z) : Z :=
    if modulus =? 0 then 0 else
    match exponent with
    | Zpos power => pow_positive (base mod modulus) power modulus
    | _ => 1 mod modulus
    end.

  Definition iteration_count (exp_len exp_high : Z) : Z :=
    let high_iterations := Z.log2 exp_high in
    Z.max 1
      (if exp_len <=? 32 then high_iterations
       else saturating_u64
         (saturating_u64 (8 * (exp_len - 32)) + high_iterations)).

  Definition berlin_gas (base_len exp_len mod_len exp_high : Z) : Z :=
    let words := (Z.max base_len mod_len + 7) / 8 in
    Z.max 200 (saturating_u64
      (words * words * iteration_count exp_len exp_high / 3)).

  Definition run_berlin (input : list Z) (gas_limit : Z) : Result.t :=
    if gas_limit <? 200 then Result.OutOfGas else
    let base_len := decode_be (read_padded input 0 32) in
    let exp_len := decode_be (read_padded input 32 32) in
    let mod_len := decode_be (read_padded input 64 32) in
    if (u64_max <? base_len) || (u64_max <? mod_len)
    then Result.InvalidLength else
    let exp_len := saturating_u64 exp_len in
    let body := List.skipn 96 input in
    let exp_high := decode_be (read_padded body base_len (Z.min exp_len 32)) in
    let cost := berlin_gas base_len exp_len mod_len exp_high in
    if gas_limit <? cost then Result.OutOfGas else
    if (base_len =? 0) && (mod_len =? 0) then Result.Success cost [] else
    let modulus := decode_be (read_padded body (base_len + exp_len) mod_len) in
    let output :=
      if modulus =? 0 then List.repeat 0 (Z.to_nat mod_len) else
      let base := decode_be (read_padded body 0 base_len) in
      let exponent := decode_be (read_padded body base_len exp_len) in
      encode_be mod_len (pow_mod base exponent modulus) in
    Result.Success cost output.

  Module Test.
    Definition header (base_len exp_len mod_len : Z) : list Z :=
      encode_be 32 base_len ++ encode_be 32 exp_len ++ encode_be 32 mod_len.

    Lemma empty_minimum : run_berlin [] 200 = Result.Success 200 [].
    Proof. vm_compute. reflexivity. Qed.

    Lemma empty_out_of_gas : run_berlin [] 199 = Result.OutOfGas.
    Proof. vm_compute. reflexivity. Qed.

    Lemma small_power :
      run_berlin (header 1 1 1 ++ [3; 4; 5]) 200 = Result.Success 200 [1].
    Proof. vm_compute. reflexivity. Qed.

    Lemma output_padding :
      run_berlin (header 1 1 2 ++ [2; 3; 1; 1]) 200 = Result.Success 200 [0; 8].
    Proof. vm_compute. reflexivity. Qed.

    Lemma zero_exponent :
      run_berlin (header 1 0 1 ++ [5; 7]) 200 = Result.Success 200 [1].
    Proof. vm_compute. reflexivity. Qed.

    Lemma zero_modulus :
      run_berlin (header 1 1 2 ++ [5; 7; 0; 0]) 200 = Result.Success 200 [0; 0].
    Proof. vm_compute. reflexivity. Qed.

    Lemma unit_modulus_zero_exponent :
      run_berlin (header 1 0 1 ++ [5; 1]) 200 = Result.Success 200 [0].
    Proof. vm_compute. reflexivity. Qed.

    Lemma zero_length_modulus :
      run_berlin (header 1 1 0 ++ [5; 7]) 200 = Result.Success 200 [].
    Proof. vm_compute. reflexivity. Qed.

    Lemma zero_base_zero_exponent :
      run_berlin (header 0 0 1 ++ [7]) 200 = Result.Success 200 [1].
    Proof. vm_compute. reflexivity. Qed.

    Lemma partial_header :
      run_berlin (List.firstn 95 (header 0 0 2)) 200 = Result.Success 200 [].
    Proof. vm_compute. reflexivity. Qed.

    Lemma truncated_body :
      run_berlin (header 1 1 2 ++ [2; 3; 1]) 200 = Result.Success 200 [0; 8].
    Proof. vm_compute. reflexivity. Qed.

    Lemma trailing_bytes_ignored :
      run_berlin (header 1 1 1 ++ [3; 4; 5; 255; 255]) 200 = Result.Success 200 [1].
    Proof. vm_compute. reflexivity. Qed.

    Lemma gas_word_boundary :
      berlin_gas 8 32 8 (2 ^ 255) = 200 /\
      berlin_gas 9 32 8 (2 ^ 255) = 340.
    Proof. vm_compute. split; reflexivity. Qed.

    Lemma exponent_length_boundary :
      iteration_count 32 0 = 1 /\ iteration_count 33 0 = 8 /\
      iteration_count 33 128 = 15.
    Proof. vm_compute. repeat split; reflexivity. Qed.

    Lemma saturated_iteration_count :
      iteration_count u64_max (2 ^ 255) = u64_max.
    Proof. vm_compute. reflexivity. Qed.

    Lemma saturated_gas :
      berlin_gas u64_max u64_max u64_max 0 = u64_max.
    Proof. vm_compute. reflexivity. Qed.

    Lemma base_length_overflow :
      run_berlin (header (2 ^ 64) 0 0) 200 = Result.InvalidLength.
    Proof. vm_compute. reflexivity. Qed.

    Lemma modulus_length_overflow :
      run_berlin (header 0 0 (2 ^ 64)) 200 = Result.InvalidLength.
    Proof. vm_compute. reflexivity. Qed.

    Lemma minimum_gas_before_length_error :
      run_berlin (header (2 ^ 64) 0 0) 199 = Result.OutOfGas.
    Proof. vm_compute. reflexivity. Qed.

    Lemma huge_exponent_empty_operands :
      run_berlin (header 0 (2 ^ 256 - 1) 0) 200 = Result.Success 200 [].
    Proof. vm_compute. reflexivity. Qed.

    Lemma huge_base_out_of_gas :
      run_berlin (header u64_max 1 1) 200 = Result.OutOfGas.
    Proof. vm_compute. reflexivity. Qed.

    Definition eip198_input : list Z :=
      header 1 32 32 ++ [3] ++ encode_be 32 (2 ^ 256 - 2 ^ 32 - 978) ++
      encode_be 32 (2 ^ 256 - 2 ^ 32 - 977).

    Lemma eip198_exact_gas :
      run_berlin eip198_input 1360 = Result.Success 1360 (encode_be 32 1).
    Proof. vm_compute. reflexivity. Qed.

    Lemma eip198_insufficient_gas :
      run_berlin eip198_input 1359 = Result.OutOfGas.
    Proof. vm_compute. reflexivity. Qed.
  End Test.
End Modexp.
