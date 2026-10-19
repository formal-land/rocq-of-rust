Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.utils.
Require Import revm.revm_precompile.simulate.bls12_381_const.
Require Import revm.revm_precompile.simulate.bls12_381_utils.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module g2_msm.
  (** Only the first iterator element is inspected: the crypto provider may
      reject its curve coordinates before consuming later elements. *)
  Definition g2_msm (input : list u8) (gas_limit : u64) : option PrecompileResult.t :=
    let input_len := bls_utils.input_length input in
    if Z.eqb input_len.(Integer.value) 0 ||
        negb (Z.eqb (input_len.(Integer.value) mod bls12_381_const.G2_MSM_INPUT_LENGTH.(Integer.value)) 0) then
      Some (Result.Err PrecompileError.Bls12381G2MsmInputLength)
    else
      let k : usize := {| Integer.value := input_len.(Integer.value) / bls12_381_const.G2_MSM_INPUT_LENGTH.(Integer.value) |} in
      let required_gas := bls12_381_utils.msm_required_gas k
        bls12_381_const.DISCOUNT_TABLE_G2_MSM bls12_381_const.G2_MSM_BASE_GAS_FEE in
      if gas_limit.(Integer.value) <? required_gas.(Integer.value) then
        Some (Result.Err PrecompileError.OutOfGas)
      else
        match bls_utils.remove_g2_padding
            (List.firstn (Z.to_nat bls12_381_const.PADDED_G2_LENGTH.(Integer.value)) input) with
        | Result.Err error => Some (Result.Err error)
        | Result.Ok _ => None
        end.
End g2_msm.
