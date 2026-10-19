Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.utils.
Require Import revm.revm_precompile.simulate.bls12_381_const.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module map_fp2_to_g2.
  (** Entry checks in map_fp2_to_g2.rs, stopping before the crypto-provider call.
      Inputs satisfy Rust byte, length and u64 validity bounds. *)
  Definition map_fp2_to_g2 (input : list u8) (gas_limit : u64) : option PrecompileResult.t :=
    if gas_limit.(Integer.value) <? bls12_381_const.MAP_FP2_TO_G2_BASE_GAS_FEE.(Integer.value) then
      Some (Result.Err PrecompileError.OutOfGas)
    else if negb (Z.eqb (bls_utils.input_length input).(Integer.value)
        bls12_381_const.PADDED_FP2_LENGTH.(Integer.value)) then
      Some (Result.Err PrecompileError.Bls12381MapFp2ToG2InputLength)
    else let width := Z.to_nat bls12_381_const.PADDED_FP_LENGTH.(Integer.value) in
      match bls_utils.remove_fp_padding (List.firstn width input) with
      | Result.Err error => Some (Result.Err error)
      | Result.Ok _ =>
        match bls_utils.remove_fp_padding (List.skipn width input) with
        | Result.Err error => Some (Result.Err error)
        | Result.Ok _ => None
        end
      end.
End map_fp2_to_g2.
