Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.bls12_381.g1_swu_iso.
Require Import revm.revm_precompile.simulate.bls12_381.utils.
Require Import revm.revm_precompile.simulate.bls12_381_const.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module map_fp_to_g1.
  (** Entry checks in map_fp_to_g1.rs, including the crypto-provider call.
      Inputs satisfy Rust byte, length and u64 validity bounds. *)
  Definition map_fp_to_g1 (input : list u8) (gas_limit : u64) : option PrecompileResult.t :=
    if gas_limit.(Integer.value) <? bls12_381_const.MAP_FP_TO_G1_BASE_GAS_FEE.(Integer.value) then
      Some (Result.Err PrecompileError.OutOfGas)
    else if negb (Z.eqb (bls_utils.input_length input).(Integer.value)
        bls12_381_const.PADDED_FP_LENGTH.(Integer.value)) then
      Some (Result.Err PrecompileError.Bls12381MapFpToG1InputLength)
    else match bls_utils.remove_fp_padding input with
      | Result.Err error => Some (Result.Err error)
      | Result.Ok fp_bytes =>
        match arkworks.read_fp fp_bytes with
        | Result.Err error => Some (Result.Err error)
        | Result.Ok fp =>
          match g1_swu_iso.map_fp_to_g1 fp with
          | None => None
          | Some point => Some (Result.Ok (Impl_PrecompileOutput.new
              bls12_381_const.MAP_FP_TO_G1_BASE_GAS_FEE
              (alloy_primitives.bytes.simulate.mod.Impl_Bytes.copy_from_slice
                (bls_utils.pad_g1_point (arkworks.encode_g1_point point)))))
          end
        end
      end.
End map_fp_to_g1.
