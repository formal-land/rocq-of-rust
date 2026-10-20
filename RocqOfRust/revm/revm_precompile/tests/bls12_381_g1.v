From Stdlib Require Import List ZArith.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.g1_add.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
Import ListNotations.
Open Scope Z_scope.

Module Test.
  (* Test-only encoding of wire coordinates, including non-canonical values. *)
  Definition coordinate (value : Z) : list u8 :=
    List.map (fun index => {| Integer.value :=
      (value / 256 ^ Z.of_nat index) mod 256 |}) (List.rev (List.seq 0 64)).

  Definition modulus : Z :=
    4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787.

  Definition run (ax ay bx by_ : Z) :=
    g1_add.g1_add (coordinate ax ++ coordinate ay ++ coordinate bx ++ coordinate by_) 375.

  Definition output (x y : Z) : option PrecompileResult.t := Some (Result.Ok (Impl_PrecompileOutput.new 375
    (alloy_primitives.bytes.simulate.mod.Impl_Bytes.copy_from_slice
      (coordinate x ++ coordinate y)))).

  Example infinity_plus_infinity : run 0 0 0 0 = output 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (* (0,2) lies on the curve but has order three. G1ADD must not demand
     subgroup membership, unlike G1MSM and pairing. *)
  Example left_infinity_preserves_non_subgroup_point : run 0 0 0 2 = output 0 2.
  Proof. vm_compute. reflexivity. Qed.

  Example right_infinity_preserves_non_subgroup_point : run 0 2 0 0 = output 0 2.
  Proof. vm_compute. reflexivity. Qed.

  Example doubling_non_subgroup_point : run 0 2 0 2 = output 0 (modulus - 2).
  Proof. vm_compute. reflexivity. Qed.

  Example opposite_points_cancel : run 0 2 0 (modulus - 2) = output 0 0.
  Proof. vm_compute. reflexivity. Qed.

  Example infinity_does_not_skip_second_curve_check : run 0 0 1 1 =
    Some (Result.Err PrecompileError.Bls12381G1NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example infinity_does_not_skip_second_field_check : run 0 0 modulus 0 =
    Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example first_x_must_be_canonical : run modulus 0 0 0 =
    Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example first_y_must_be_canonical : run 0 modulus 0 0 =
    Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example second_y_must_be_canonical : run 0 2 0 modulus =
    Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example first_curve_error_precedes_second_field_error : run 1 1 modulus 0 =
    Some (Result.Err PrecompileError.Bls12381G1NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example later_padding_error_precedes_first_curve_error :
    g1_add.g1_add (coordinate 1 ++ coordinate 1 ++ List.repeat (1 : u8) 128) 375 =
    Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.
End Test.
