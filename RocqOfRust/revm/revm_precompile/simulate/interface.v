Require Import alloy_primitives.bytes.links.mod.
Require Import core.links.result.
Require Import simulate.RocqOfRust.

(** Executable subset of interface.rs used by the P256 and BLS boundary paths.
    The older linked interface does not contain the current BLS errors. This
    module supplies no native-provider or linked-interface correspondence proof. *)
Module PrecompileError.
  Inductive t : Set :=
  | OutOfGas
  | Bls12381G1AddInputLength
  | Bls12381G2AddInputLength
  | Bls12381G1MsmInputLength
  | Bls12381G2MsmInputLength
  | Bls12381PairingInputLength
  | Bls12381MapFpToG1InputLength
  | Bls12381MapFp2ToG2InputLength
  | Bls12381FpPaddingInvalid
  | Bls12381FpPaddingLength
  | Bls12381G1PaddingLength
  | Bls12381G2PaddingLength
  | NonCanonicalFp
  | Bls12381G1NotOnCurve
  | Bls12381G1NotInSubgroup
  | Bls12381ScalarInputLength.
End PrecompileError.

Module PrecompileOutput.
  Record t : Set := {
    gas_used : u64;
    gas_refunded : i64;
    bytes : alloy_primitives.bytes.links.mod.Bytes.t;
    reverted : bool;
  }.
End PrecompileOutput.

Module Impl_PrecompileOutput.
  Definition new (gas_used : u64) (bytes : alloy_primitives.bytes.links.mod.Bytes.t)
      : PrecompileOutput.t := {|
    PrecompileOutput.gas_used := gas_used;
    PrecompileOutput.gas_refunded := {| Integer.value := 0 |};
    PrecompileOutput.bytes := bytes;
    PrecompileOutput.reverted := false;
  |}.
End Impl_PrecompileOutput.

Module PrecompileResult.
  Definition t : Set := Result.t PrecompileOutput.t PrecompileError.t.
End PrecompileResult.
