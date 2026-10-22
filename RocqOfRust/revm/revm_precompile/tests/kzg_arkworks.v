From Stdlib Require Import List ZArith.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.interface.
Require Import revm.revm_precompile.simulate.kzg_point_evaluation.arkworks.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.
Import ListNotations.
Import revm.revm_precompile.simulate.bls12_381.arkworks.arkworks.
Open Scope Z_scope.

Module Test.
  (** Test-only encoding permits intentionally noncanonical field values. *)
  Definition bytes (width : nat) (value : Z) : list u8 :=
    List.map (fun index => {| Integer.value :=
      (value / 256 ^ Z.of_nat index) mod 256 |}) (List.rev (List.seq 0 width)).

  Definition compressed (flags : u8) (x : Uint.t 384 6) : list u8 :=
    match bytes 48 x.(Uint.value) with
    | [] => []
    | first :: rest =>
      {| Integer.value := Z.lor first.(Integer.value) flags.(Integer.value) |} :: rest
    end.

  Definition infinity : list u8 := (192 : u8) :: List.repeat (0 : u8) 47.

  Example infinity_is_accepted :
    arkworks.parse_g1_compressed infinity = Result.Ok G1Affine.zero.
  Proof. vm_compute. reflexivity. Qed.

  Example compression_flag_required :
    arkworks.parse_g1_compressed ((64 : u8) :: List.repeat (0 : u8) 47) =
      Result.Err PrecompileError.KzgInvalidG1Point.
  Proof. vm_compute. reflexivity. Qed.

  Example infinity_sort_flag_rejected :
    arkworks.parse_g1_compressed ((224 : u8) :: List.repeat (0 : u8) 47) =
      Result.Err PrecompileError.KzgInvalidG1Point.
  Proof. vm_compute. reflexivity. Qed.

  Example infinity_nonzero_coordinate_rejected :
    arkworks.parse_g1_compressed ((192 : u8) :: bytes 47 1) =
      Result.Err PrecompileError.KzgInvalidG1Point.
  Proof. vm_compute. reflexivity. Qed.

  Example malformed_compressed_length_rejected :
    arkworks.parse_g1_compressed (infinity ++ [(0 : u8)]) =
      Result.Err PrecompileError.KzgInvalidG1Point.
  Proof. vm_compute. reflexivity. Qed.

  Example invalid_byte_rejected :
    arkworks.parse_g1_compressed ((448 : u8) :: List.repeat (0 : u8) 47) =
      Result.Err PrecompileError.KzgInvalidG1Point.
  Proof. vm_compute. reflexivity. Qed.

  Example noncanonical_x_rejected_after_flags_removed :
    arkworks.parse_g1_compressed (compressed 128 Fq.MODULUS) =
      Result.Err PrecompileError.KzgInvalidG1Point.
  Proof. vm_compute. reflexivity. Qed.

  Example scalar_zero_accepted :
    arkworks.read_scalar_canonical (bytes 32 0) =
      Result.Ok {| Fr.repr := {| Uint.value := 0 |} |}.
  Proof. vm_compute. reflexivity. Qed.

  Example last_canonical_scalar_accepted :
    arkworks.read_scalar_canonical (bytes 32 (Fr.MODULUS.(Uint.value) - 1)) =
      Result.Ok {| Fr.repr := {| Uint.value := Fr.MODULUS.(Uint.value) - 1 |} |}.
  Proof. vm_compute. reflexivity. Qed.

  Example scalar_modulus_rejected :
    arkworks.read_scalar_canonical (bytes 32 Fr.MODULUS.(Uint.value)) =
      Result.Err PrecompileError.NonCanonicalFp.
  Proof. vm_compute. reflexivity. Qed.

  Example scalar_length_rejected :
    arkworks.read_scalar_canonical (bytes 31 0) =
      Result.Err PrecompileError.NonCanonicalFp.
  Proof. vm_compute. reflexivity. Qed.

  Example trusted_setup_is_on_curve :
    G2Affine.is_on_curve arkworks.get_trusted_setup_g2 = true.
  Proof. vm_compute. reflexivity. Qed.
End Test.
