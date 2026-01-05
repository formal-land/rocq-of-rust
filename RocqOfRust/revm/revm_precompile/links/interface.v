Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import alloc.links.string.
Require Import revm.revm_precompile.interface.

Module PrecompileError.
  Inductive t : Set :=
  | OutOfGas
  | Blake2WrongLength
  | Blake2WrongFinalIndicatorFlag
  | ModexpExpOverflow
  | ModexpBaseOverflow
  | ModexpModOverflow
  | Bn128FieldPointNotAMember
  | Bn128AffineGFailedToCreate
  | Bn128PairLength
  | BlobInvalidInputLength
  | BlobMismatchedVersion
  | BlobVerifyKzgProofFailed
  | Other
    (_ : alloc.links.string.String.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::interface::PrecompileError";
    φ x :=
      match x with
      | OutOfGas =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::OutOfGas" [] [] []
      | Blake2WrongLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongLength" [] [] []
      | Blake2WrongFinalIndicatorFlag =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongFinalIndicatorFlag" [] [] []
      | ModexpExpOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpExpOverflow" [] [] []
      | ModexpBaseOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpBaseOverflow" [] [] []
      | ModexpModOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpModOverflow" [] [] []
      | Bn128FieldPointNotAMember =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128FieldPointNotAMember" [] [] []
      | Bn128AffineGFailedToCreate =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128AffineGFailedToCreate" [] [] []
      | Bn128PairLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128PairLength" [] [] []
      | BlobInvalidInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobInvalidInputLength" [] [] []
      | BlobMismatchedVersion =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobMismatchedVersion" [] [] []
      | BlobVerifyKzgProofFailed =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobVerifyKzgProofFailed" [] [] []
      | Other γ0 =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Other" [] [] [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_precompile::interface::PrecompileError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.
End PrecompileError.

Module Impl_PrecompileError.
  Definition Self : Set :=
    PrecompileError.t.

  (* pub fn is_oog(&self) -> bool *)
  Definition run_is_oog (self : '& Self) :
    {{
      interface.Impl_revm_precompile_interface_PrecompileError.is_oog [] [] [ φ self ] 🔽
      bool
    }}.
  Proof.
    run_symbolic.
  Defined.
End Impl_PrecompileError.
