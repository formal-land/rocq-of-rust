Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381_const.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module bls_utils.
  Definition input_length (input : list u8) : usize :=
    {| Integer.value := Z.of_nat (List.length input) |}.

  (** Lists project Rust byte slices, and tuples project fixed-size arrays.
      The successful results retain the exact bytes, without their padding. *)
  Definition remove_fp_padding (input : list u8)
      : Result.t (list u8) PrecompileError.t :=
    if negb (Z.eqb (input_length input).(Integer.value)
        bls12_381_const.PADDED_FP_LENGTH.(Integer.value)) then
      Result.Err PrecompileError.Bls12381FpPaddingLength
    else if negb (List.forallb (fun byte => Z.eqb byte.(Integer.value) 0)
        (List.firstn (Z.to_nat bls12_381_const.FP_PAD_BY.(Integer.value)) input)) then
      Result.Err PrecompileError.Bls12381FpPaddingInvalid
    else Result.Ok (List.skipn (Z.to_nat bls12_381_const.FP_PAD_BY.(Integer.value)) input).

  Definition remove_g1_padding (input : list u8)
      : Result.t (list u8 * list u8) PrecompileError.t :=
    if negb (Z.eqb (input_length input).(Integer.value)
        bls12_381_const.PADDED_G1_LENGTH.(Integer.value)) then
      Result.Err PrecompileError.Bls12381G1PaddingLength
    else
      let width := Z.to_nat bls12_381_const.PADDED_FP_LENGTH.(Integer.value) in
      match remove_fp_padding (List.firstn width input) with
      | Result.Err error => Result.Err error
      | Result.Ok x =>
        match remove_fp_padding (List.skipn width input) with
        | Result.Err error => Result.Err error
        | Result.Ok y => Result.Ok (x, y)
        end
      end.

  Definition remove_g2_padding (input : list u8)
      : Result.t (list u8 * list u8 * list u8 * list u8) PrecompileError.t :=
    if negb (Z.eqb (input_length input).(Integer.value)
        bls12_381_const.PADDED_G2_LENGTH.(Integer.value)) then
      Result.Err PrecompileError.Bls12381G2PaddingLength
    else
      let width := Z.to_nat bls12_381_const.PADDED_FP_LENGTH.(Integer.value) in
      match remove_fp_padding (List.firstn width input) with
      | Result.Err error => Result.Err error
      | Result.Ok x0 =>
        match remove_fp_padding (List.firstn width (List.skipn width input)) with
        | Result.Err error => Result.Err error
        | Result.Ok x1 =>
          match remove_fp_padding (List.firstn width (List.skipn (2 * width) input)) with
          | Result.Err error => Result.Err error
          | Result.Ok y0 =>
            match remove_fp_padding (List.skipn (3 * width) input) with
            | Result.Err error => Result.Err error
            | Result.Ok y1 => Result.Ok (x0, x1, y0, y1)
            end
          end
        end
      end.

  (** The provider returns exactly 96 bytes, as the Rust array type requires. *)
  Definition pad_g1_point (unpadded : list u8) : list u8 :=
    let padding := List.repeat ({| Integer.value := 0 |} : u8)
      (Z.to_nat bls12_381_const.FP_PAD_BY.(Integer.value)) in
    let width := Z.to_nat bls12_381_const.FP_LENGTH.(Integer.value) in
    padding ++ List.firstn width unpadded ++ padding ++ List.skipn width unpadded.

  (** The provider returns the four field coordinates as 192 bytes. *)
  Definition pad_g2_point (unpadded : list u8) : list u8 :=
    let padding := List.repeat ({| Integer.value := 0 |} : u8)
      (Z.to_nat bls12_381_const.FP_PAD_BY.(Integer.value)) in
    let width := Z.to_nat bls12_381_const.FP_LENGTH.(Integer.value) in
    padding ++ List.firstn width unpadded ++
    padding ++ List.firstn width (List.skipn width unpadded) ++
    padding ++ List.firstn width (List.skipn (2 * width) unpadded) ++
    padding ++ List.skipn (3 * width) unpadded.
End bls_utils.
