Require Import alloy_primitives.bytes.links.mod.
Require Import core.links.result.
Require Import simulate.RocqOfRust.
From Stdlib Require Import String.
Open Scope string_scope.

(** Executable types from interface.rs, shared by cryptographic primitives and
    the Ethereum precompile provider. *)
Module PrecompileError.
  Inductive t : Set :=
  | OutOfGas
  | BlobInvalidInputLength
  | BlobMismatchedVersion
  | BlobVerifyKzgProofFailed
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
  | KzgInvalidG1Point
  | Bls12381G2NotOnCurve
  | Bls12381G1NotOnCurve
  | Bls12381G1NotInSubgroup
  | Bls12381ScalarInputLength
  | Blake2WrongLength
  | Blake2WrongFinalIndicatorFlag
  | ModexpExpOverflow
  | ModexpBaseOverflow
  | ModexpModOverflow
  | ModexpEip7823LimitSize
  | Bn254FieldPointNotAMember
  | Bn254AffineGFailedToCreate
  | Bn254PairLength
  | Bls12381G2NotInSubgroup
  | KzgG1PointNotOnCurve
  | KzgG1PointNotInSubgroup
  | KzgInvalidInputLength
  | Secp256k1RecoverFailed
  | Fatal (message : string)
  | Other (message : string).

End PrecompileError.

Module Impl_PrecompileError.
  Definition is_oog (self : PrecompileError.t) : bool :=
    match self with PrecompileError.OutOfGas => true | _ => false end.

  Definition to_string (self : PrecompileError.t) : string :=
    match self with
    | PrecompileError.OutOfGas => "out of gas"
    | PrecompileError.Blake2WrongLength => "wrong input length for blake2"
    | PrecompileError.Blake2WrongFinalIndicatorFlag => "wrong final indicator flag for blake2"
    | PrecompileError.ModexpExpOverflow => "modexp exp overflow"
    | PrecompileError.ModexpBaseOverflow => "modexp base overflow"
    | PrecompileError.ModexpModOverflow => "modexp mod overflow"
    | PrecompileError.ModexpEip7823LimitSize => "Modexp limit all input sizes."
    | PrecompileError.Bn254FieldPointNotAMember => "field point not a member of bn254 curve"
    | PrecompileError.Bn254AffineGFailedToCreate => "failed to create affine g point for bn254 curve"
    | PrecompileError.Bn254PairLength => "bn254 invalid pair length"
    | PrecompileError.BlobInvalidInputLength => "invalid blob input length"
    | PrecompileError.BlobMismatchedVersion => "mismatched blob version"
    | PrecompileError.BlobVerifyKzgProofFailed => "verifying blob kzg proof failed"
    | PrecompileError.NonCanonicalFp => "non-canonical field element"
    | PrecompileError.Bls12381G1NotOnCurve => "bls12-381 g1 point not on curve"
    | PrecompileError.Bls12381G1NotInSubgroup => "bls12-381 g1 point not in correct subgroup"
    | PrecompileError.Bls12381G2NotOnCurve => "bls12-381 g2 point not on curve"
    | PrecompileError.Bls12381G2NotInSubgroup => "bls12-381 g2 point not in correct subgroup"
    | PrecompileError.Bls12381ScalarInputLength => "bls12-381 scalar input length error"
    | PrecompileError.Bls12381G1AddInputLength => "bls12-381 g1 add input length error"
    | PrecompileError.Bls12381G1MsmInputLength => "bls12-381 g1 msm input length error"
    | PrecompileError.Bls12381G2AddInputLength => "bls12-381 g2 add input length error"
    | PrecompileError.Bls12381G2MsmInputLength => "bls12-381 g2 msm input length error"
    | PrecompileError.Bls12381PairingInputLength => "bls12-381 pairing input length error"
    | PrecompileError.Bls12381MapFpToG1InputLength => "bls12-381 map fp to g1 input length error"
    | PrecompileError.Bls12381MapFp2ToG2InputLength => "bls12-381 map fp2 to g2 input length error"
    | PrecompileError.Bls12381FpPaddingInvalid => "bls12-381 fp 64 top bytes of input are not zero"
    | PrecompileError.Bls12381FpPaddingLength => "bls12-381 fp padding length error"
    | PrecompileError.Bls12381G1PaddingLength => "bls12-381 g1 padding length error"
    | PrecompileError.Bls12381G2PaddingLength => "bls12-381 g2 padding length error"
    | PrecompileError.KzgInvalidG1Point => "kzg invalid g1 point"
    | PrecompileError.KzgG1PointNotOnCurve => "kzg g1 point not on curve"
    | PrecompileError.KzgG1PointNotInSubgroup => "kzg g1 point not in correct subgroup"
    | PrecompileError.KzgInvalidInputLength => "kzg invalid input length"
    | PrecompileError.Secp256k1RecoverFailed => "secp256k1 signature recovery failed"
    | PrecompileError.Fatal message | PrecompileError.Other message => message
    end.
End Impl_PrecompileError.

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
