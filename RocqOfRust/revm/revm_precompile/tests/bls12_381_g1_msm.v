From Stdlib Require Import List ZArith.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.bls12_381.g1_msm.
Require Import revm.revm_precompile.simulate.interface.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.
Import ListNotations.
Open Scope Z_scope.

Module Test.
  (* Wire encoding for test inputs, including scalar values above the order. *)
  Definition bytes (width : nat) (value : Z) : list u8 :=
    List.map (fun index => {| Integer.value :=
      (value / 256 ^ Z.of_nat index) mod 256 |}) (List.rev (List.seq 0 width)).

  Definition pair (x y scalar : Z) : list u8 :=
    bytes 64 x ++ bytes 64 y ++ bytes 32 scalar.

  Definition scalar_value (input : list u8) : option Z :=
    match arkworks.read_scalar input with
    | Result.Ok value => Some value.(arkworks.Fr.repr).(Uint.value)
    | _ => None
    end.

  Definition order : Z :=
    52435875175126190479447740508185965837690552500527637822603658699938581184513.

  Example scalar_order_reduces_to_zero : scalar_value (bytes 32 order) = Some 0.
  Proof. vm_compute. reflexivity. Qed.

  Example scalar_above_order_reduces : scalar_value (bytes 32 (order + 1)) = Some 1.
  Proof. vm_compute. reflexivity. Qed.

  Example scalar_maximum_is_accepted : scalar_value (bytes 32 (2^256 - 1)) =
    Some ((2^256 - 1) mod order).
  Proof. vm_compute. reflexivity. Qed.

  Example short_scalar_rejects : arkworks.read_scalar (bytes 31 0) =
    Result.Err PrecompileError.Bls12381ScalarInputLength.
  Proof. vm_compute. reflexivity. Qed.

  Example invalid_byte_rejects : arkworks.read_scalar
    (({| Integer.value := 256 |} : u8) :: bytes 31 0) =
    Result.Err PrecompileError.Bls12381ScalarInputLength.
  Proof. vm_compute. reflexivity. Qed.

  Example zero_scalar_does_not_skip_curve_check :
    g1_msm.g1_msm (pair 1 1 0) 12000 =
    Some (Result.Err PrecompileError.Bls12381G1NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  (* (0,2) has order three, not the required prime subgroup order. *)
  Example zero_scalar_does_not_skip_subgroup_check :
    g1_msm.g1_msm (pair 0 2 0) 12000 =
    Some (Result.Err PrecompileError.Bls12381G1NotInSubgroup).
  Proof. vm_compute. reflexivity. Qed.

  Example curve_error_precedes_later_padding :
    g1_msm.g1_msm (pair 1 1 0 ++ List.repeat (1 : u8) 160) 22776 =
    Some (Result.Err PrecompileError.Bls12381G1NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example gas_precedes_point_validation :
    g1_msm.g1_msm (pair 1 1 0) 11999 = Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example length_precedes_gas :
    g1_msm.g1_msm (bytes 159 0) 0 =
    Some (Result.Err PrecompileError.Bls12381G1MsmInputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example mismatched_provider_vectors_are_explicit :
    arkworks.p1_msm [arkworks.G1Affine.zero] [] = None.
  Proof. vm_compute. reflexivity. Qed.
End Test.
