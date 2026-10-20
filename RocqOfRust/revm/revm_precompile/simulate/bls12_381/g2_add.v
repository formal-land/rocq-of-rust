Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.bls12_381.utils.
Require Import revm.revm_precompile.simulate.bls12_381_const.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module g2_add.
  (** Entry checks and provider call in g2_add.rs.
      Inputs satisfy Rust byte, length and u64 validity bounds. *)
  Definition g2_add (input : list u8) (gas_limit : u64) : option PrecompileResult.t :=
    if gas_limit.(Integer.value) <? bls12_381_const.G2_ADD_BASE_GAS_FEE.(Integer.value) then
      Some (Result.Err PrecompileError.OutOfGas)
    else if negb (Z.eqb (bls_utils.input_length input).(Integer.value)
        bls12_381_const.G2_ADD_INPUT_LENGTH.(Integer.value)) then
      Some (Result.Err PrecompileError.Bls12381G2AddInputLength)
    else let width := Z.to_nat bls12_381_const.PADDED_G2_LENGTH.(Integer.value) in
      match bls_utils.remove_g2_padding (List.firstn width input) with
      | Result.Err error => Some (Result.Err error)
      | Result.Ok a =>
        match bls_utils.remove_g2_padding (List.skipn width input) with
        | Result.Err error => Some (Result.Err error)
        | Result.Ok b =>
          match arkworks.p2_add_affine_bytes a b with
          | Result.Err error => Some (Result.Err error)
          | Result.Ok output => Some (Result.Ok (Impl_PrecompileOutput.new
              bls12_381_const.G2_ADD_BASE_GAS_FEE
              (alloy_primitives.bytes.simulate.mod.Impl_Bytes.copy_from_slice
                (bls_utils.pad_g2_point output))))
          end
        end
      end.
End g2_add.
