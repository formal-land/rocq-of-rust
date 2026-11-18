Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.bls12_381.bls12.
Require Import revm.revm_precompile.simulate.bls12_381.utils.
Require Import revm.revm_precompile.simulate.bls12_381_const.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module pairing.
  Definition PairingPair : Set :=
    (list u8 * list u8) * (list u8 * list u8 * list u8 * list u8).

  (** Structural loop corresponding to Rust's collection of pairs before crypto.
      The entry function has checked that the input length is exactly 384*k. *)
  Definition collect_pairs (count : usize) (input : list u8)
      : Result.t (list PairingPair) PrecompileError.t :=
    let fix loop (remaining : nat) (bytes : list u8) : Result.t (list PairingPair) PrecompileError.t :=
    match remaining with
    | O => Result.Ok []
    | S rest =>
      let g1_width := Z.to_nat bls12_381_const.PADDED_G1_LENGTH.(Integer.value) in
      let g2_width := Z.to_nat bls12_381_const.PADDED_G2_LENGTH.(Integer.value) in
      let pair_width := Z.to_nat bls12_381_const.PAIRING_INPUT_LENGTH.(Integer.value) in
      match bls_utils.remove_g1_padding (List.firstn g1_width bytes) with
      | Result.Err error => Result.Err error
      | Result.Ok g1 =>
        match bls_utils.remove_g2_padding (List.firstn g2_width (List.skipn g1_width bytes)) with
        | Result.Err error => Result.Err error
        | Result.Ok g2 =>
          match loop rest (List.skipn pair_width bytes) with
          | Result.Err error => Result.Err error
          | Result.Ok pairs => Result.Ok ((g1, g2) :: pairs)
          end
        end
      end
    end in
    loop (Z.to_nat count.(Integer.value)) input.

  (** arkworks.rs validates nonzero partners even when an infinity point
      makes their pairing contribution the identity. All padding has already
      been checked by collect_pairs, before any provider parsing. *)
  Fixpoint read_pairs (pairs : list PairingPair)
      : Result.t (list (arkworks.G1Affine.t * arkworks.G2Affine.t)) PrecompileError.t :=
    match pairs with
    | [] => Result.Ok []
    | ((x, y), (x0, x1, y0, y1)) :: rest =>
      match arkworks.read_g1 x y with
      | Result.Err error => Result.Err error
      | Result.Ok p =>
        match arkworks.read_g2 x0 x1 y0 y1 with
        | Result.Err error => Result.Err error
        | Result.Ok q =>
          match read_pairs rest with
          | Result.Err error => Result.Err error
          | Result.Ok parsed => Result.Ok
            (if p.(arkworks.G1Affine.infinity) || q.(arkworks.G2Affine.infinity)
             then parsed else (p, q) :: parsed)
          end
        end
      end
    end.

  Definition pairing_check_bytes (pairs : list PairingPair)
      : option (Result.t bool PrecompileError.t) :=
    match read_pairs pairs with
    | Result.Err error => Some (Result.Err error)
    | Result.Ok [] => Some (Result.Ok true)
    | Result.Ok parsed => option_map (fun result => Result.Ok result)
        (Bls12.pairing_check parsed)
    end.

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
        | Result.Ok pairs =>
          match pairing_check_bytes pairs with
          | None => None
          | Some (Result.Err error) => Some (Result.Err error)
          | Some (Result.Ok valid) => Some (Result.Ok (Impl_PrecompileOutput.new
              required_gas (alloy_primitives.bytes.simulate.mod.Impl_Bytes.copy_from_slice
                (List.repeat (0 : u8) 31 ++ [if valid then (1 : u8) else (0 : u8)]))))
          end
        end.
End pairing.
