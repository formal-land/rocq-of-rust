From Stdlib Require Import List ZArith.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.pairing.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
Import ListNotations.
Open Scope Z_scope.

Module Test.
  (* Test-only wire encoding also permits non-canonical field inputs. *)
  Definition bytes (width : nat) (value : Z) : list u8 :=
    List.map (fun index => {| Integer.value :=
      (value / 256 ^ Z.of_nat index) mod 256 |}) (List.rev (List.seq 0 width)).

  Definition g1 (x y : Z) : list u8 := bytes 64 x ++ bytes 64 y.

  Definition g2 (x0 x1 y0 y1 : Z) : list u8 :=
    bytes 64 x0 ++ bytes 64 x1 ++ bytes 64 y0 ++ bytes 64 y1.

  Definition modulus : Z :=
    4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787.

  Example nonmultiple_length_precedes_gas :
    pairing.pairing (bytes 383 0) 0 =
      Some (Result.Err PrecompileError.Bls12381PairingInputLength).
  Proof. vm_compute. reflexivity. Qed.

  Example gas_precedes_curve_validation :
    pairing.pairing (g1 1 1 ++ g2 0 0 0 0) 70299 =
      Some (Result.Err PrecompileError.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Example later_pair_padding_precedes_first_curve_error :
    pairing.pairing
      (g1 1 1 ++ g2 0 0 0 0 ++ List.repeat (1 : u8) 384) 102900 =
      Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example same_pair_g2_padding_precedes_g1_curve_error :
    pairing.pairing (g1 1 1 ++ List.repeat (1 : u8) 256) 70300 =
      Some (Result.Err PrecompileError.Bls12381FpPaddingInvalid).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_infinity_does_not_skip_g1_field_check :
    pairing.pairing (g1 modulus 0 ++ g2 0 0 0 0) 70300 =
      Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example g2_infinity_does_not_skip_g1_curve_check :
    pairing.pairing (g1 1 1 ++ g2 0 0 0 0) 70300 =
      Some (Result.Err PrecompileError.Bls12381G1NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  (* (0,2) has order three, outside the required prime-order subgroup. *)
  Example g2_infinity_does_not_skip_g1_subgroup_check :
    pairing.pairing (g1 0 2 ++ g2 0 0 0 0) 70300 =
      Some (Result.Err PrecompileError.Bls12381G1NotInSubgroup).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_infinity_does_not_skip_g2_field_check :
    pairing.pairing (g1 0 0 ++ g2 0 0 0 modulus) 70300 =
      Some (Result.Err PrecompileError.NonCanonicalFp).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_infinity_does_not_skip_g2_curve_check :
    pairing.pairing (g1 0 0 ++ g2 1 0 1 0) 70300 =
      Some (Result.Err PrecompileError.Bls12381G2NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example g1_curve_error_precedes_g2_field_error :
    pairing.pairing (g1 1 1 ++ g2 modulus 0 0 0) 70300 =
      Some (Result.Err PrecompileError.Bls12381G1NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example first_pair_curve_error_precedes_later_field_error :
    pairing.pairing
      (g1 1 1 ++ g2 0 0 0 0 ++ g1 modulus 0 ++ g2 0 0 0 0) 102900 =
      Some (Result.Err PrecompileError.Bls12381G1NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example infinity_pair_does_not_skip_later_curve_check :
    pairing.pairing (bytes 384 0 ++ g1 0 0 ++ g2 1 0 1 0) 102900 =
      Some (Result.Err PrecompileError.Bls12381G2NotOnCurve).
  Proof. vm_compute. reflexivity. Qed.

  Example two_infinity_pairs_charge_both_pairs :
    pairing.pairing (bytes 768 0) 102900 =
      Some (Result.Ok (Impl_PrecompileOutput.new 102900
        (alloy_primitives.bytes.simulate.mod.Impl_Bytes.copy_from_slice
          (List.repeat (0 : u8) 31 ++ [(1 : u8)])))).
  Proof. vm_compute. reflexivity. Qed.
End Test.
