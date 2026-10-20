Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.bls12_381.utils.
Require Import revm.revm_precompile.simulate.bls12_381_const.
Require Import revm.revm_precompile.simulate.bls12_381_utils.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module g2_msm.
  (* Iterator items retain errors as values. The provider consumes them in
     order, so earlier point errors take precedence over later padding errors. *)
  Definition valid_pairs_iter (input : list u8) (k : usize) :=
    List.map (fun index =>
      let start := (index * Z.to_nat bls12_381_const.G2_MSM_INPUT_LENGTH.(Integer.value))%nat in
      let chunk := List.skipn start input in
      let point_width := Z.to_nat bls12_381_const.PADDED_G2_LENGTH.(Integer.value) in
      match bls_utils.remove_g2_padding (List.firstn point_width chunk) with
      | Result.Err error => Result.Err error
      | Result.Ok point => Result.Ok (point,
          List.firstn (Z.to_nat bls12_381_const.SCALAR_LENGTH.(Integer.value))
            (List.skipn point_width chunk))
      end) (List.seq 0 (Z.to_nat k.(Integer.value))).

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
        match arkworks.p2_msm_bytes (valid_pairs_iter input k) with
        | None => None
        | Some (Result.Err error) => Some (Result.Err error)
        | Some (Result.Ok output) => Some (Result.Ok (Impl_PrecompileOutput.new
            required_gas (alloy_primitives.bytes.simulate.mod.Impl_Bytes.copy_from_slice
              (bls_utils.pad_g2_point output))))
        end.
End g2_msm.
