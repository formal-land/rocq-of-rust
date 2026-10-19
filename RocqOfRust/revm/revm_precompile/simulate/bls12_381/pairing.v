Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.utils.
Require Import revm.revm_precompile.simulate.bls12_381_const.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module pairing.
  (** Structural loop corresponding to Rust's collection of pairs before crypto.
      The entry function has checked that the input length is exactly 384*k. *)
  Definition collect_pairs (count : usize) (input : list u8)
      : Result.t unit PrecompileError.t :=
    let fix loop (remaining : nat) (bytes : list u8) : Result.t unit PrecompileError.t :=
    match remaining with
    | O => Result.Ok tt
    | S rest =>
      let g1_width := Z.to_nat bls12_381_const.PADDED_G1_LENGTH.(Integer.value) in
      let g2_width := Z.to_nat bls12_381_const.PADDED_G2_LENGTH.(Integer.value) in
      let pair_width := Z.to_nat bls12_381_const.PAIRING_INPUT_LENGTH.(Integer.value) in
      match bls_utils.remove_g1_padding (List.firstn g1_width bytes) with
      | Result.Err error => Result.Err error
      | Result.Ok _ =>
        match bls_utils.remove_g2_padding (List.firstn g2_width (List.skipn g1_width bytes)) with
        | Result.Err error => Result.Err error
        | Result.Ok _ => loop rest (List.skipn pair_width bytes)
        end
      end
    end in
    loop (Z.to_nat count.(Integer.value)) input.

  Definition pairing (input : list u8) (gas_limit : u64) : option PrecompileResult.t :=
    let input_len := bls_utils.input_length input in
    if Z.eqb input_len.(Integer.value) 0 ||
        negb (Z.eqb (input_len.(Integer.value) mod
          bls12_381_const.PAIRING_INPUT_LENGTH.(Integer.value)) 0) then
      Some (Result.Err PrecompileError.Bls12381PairingInputLength)
    else
      let k : usize := {| Integer.value := input_len.(Integer.value) /
        bls12_381_const.PAIRING_INPUT_LENGTH.(Integer.value) |} in
      (** Explicit release-mode wrapping for the Rust u64 multiplication/addition. *)
      let required_gas : u64 := {| Integer.value :=
        (bls12_381_const.PAIRING_MULTIPLIER_BASE.(Integer.value) *
          (k.(Integer.value) mod 2 ^ 64) +
          bls12_381_const.PAIRING_OFFSET_BASE.(Integer.value)) mod 2 ^ 64 |} in
      if gas_limit.(Integer.value) <? required_gas.(Integer.value) then
        Some (Result.Err PrecompileError.OutOfGas)
      else
        match collect_pairs k input with
        | Result.Err error => Some (Result.Err error)
        | Result.Ok _ => None
        end.
End pairing.
