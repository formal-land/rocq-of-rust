Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import anza_xyz_solana_sdk.program_error.links.lib.
Require Import core.convert.links.mod.
Require Import solana_program_token.interface.error.

(*
  pub enum TokenError {
      NotRentExempt,
      InsufficientFunds,
      InvalidMint,
      MintMismatch,
      OwnerMismatch,
      FixedSupply,
      AlreadyInUse,
      InvalidNumberOfProvidedSigners,
      InvalidNumberOfRequiredSigners,
      UninitializedState,
      NativeNotSupported,
      NonNativeHasBalance,
      InvalidInstruction,
      InvalidState,
      Overflow,
      AuthorityTypeNotSupported,
      MintCannotFreeze,
      AccountFrozen,
      MintDecimalsMismatch,
      NonNativeNotSupported,
  }
*)
Module TokenError.
  Inductive t : Set :=
  | NotRentExempt
  | InsufficientFunds
  | InvalidMint
  | MintMismatch
  | OwnerMismatch
  | FixedSupply
  | AlreadyInUse
  | InvalidNumberOfProvidedSigners
  | InvalidNumberOfRequiredSigners
  | UninitializedState
  | NativeNotSupported
  | NonNativeHasBalance
  | InvalidInstruction
  | InvalidState
  | Overflow
  | AuthorityTypeNotSupported
  | MintCannotFreeze
  | AccountFrozen
  | MintDecimalsMismatch
  | NonNativeNotSupported.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "spl_token_interface::error::TokenError";
    φ x :=
      match x with
      | NotRentExempt =>
          Value.StructTuple "spl_token_interface::error::TokenError::NotRentExempt" [] [] []
      | InsufficientFunds =>
          Value.StructTuple "spl_token_interface::error::TokenError::InsufficientFunds" [] [] []
      | InvalidMint =>
          Value.StructTuple "spl_token_interface::error::TokenError::InvalidMint" [] [] []
      | MintMismatch =>
          Value.StructTuple "spl_token_interface::error::TokenError::MintMismatch" [] [] []
      | OwnerMismatch =>
          Value.StructTuple "spl_token_interface::error::TokenError::OwnerMismatch" [] [] []
      | FixedSupply =>
          Value.StructTuple "spl_token_interface::error::TokenError::FixedSupply" [] [] []
      | AlreadyInUse =>
          Value.StructTuple "spl_token_interface::error::TokenError::AlreadyInUse" [] [] []
      | InvalidNumberOfProvidedSigners =>
          Value.StructTuple "spl_token_interface::error::TokenError::InvalidNumberOfProvidedSigners" [] [] []
      | InvalidNumberOfRequiredSigners =>
          Value.StructTuple "spl_token_interface::error::TokenError::InvalidNumberOfRequiredSigners" [] [] []
      | UninitializedState =>
          Value.StructTuple "spl_token_interface::error::TokenError::UninitializedState" [] [] []
      | NativeNotSupported =>
          Value.StructTuple "spl_token_interface::error::TokenError::NativeNotSupported" [] [] []
      | NonNativeHasBalance =>
          Value.StructTuple "spl_token_interface::error::TokenError::NonNativeHasBalance" [] [] []
      | InvalidInstruction =>
          Value.StructTuple "spl_token_interface::error::TokenError::InvalidInstruction" [] [] []
      | InvalidState =>
          Value.StructTuple "spl_token_interface::error::TokenError::InvalidState" [] [] []
      | Overflow =>
          Value.StructTuple "spl_token_interface::error::TokenError::Overflow" [] [] []
      | AuthorityTypeNotSupported =>
          Value.StructTuple "spl_token_interface::error::TokenError::AuthorityTypeNotSupported" [] [] []
      | MintCannotFreeze =>
          Value.StructTuple "spl_token_interface::error::TokenError::MintCannotFreeze" [] [] []
      | AccountFrozen =>
          Value.StructTuple "spl_token_interface::error::TokenError::AccountFrozen" [] [] []
      | MintDecimalsMismatch =>
          Value.StructTuple "spl_token_interface::error::TokenError::MintDecimalsMismatch" [] [] []
      | NonNativeNotSupported =>
          Value.StructTuple "spl_token_interface::error::TokenError::NonNativeNotSupported" [] [] []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "spl_token_interface::error::TokenError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_NotRentExempt :
    Value.StructTuple "spl_token_interface::error::TokenError::NotRentExempt" [] [] [] =
    φ NotRentExempt.
  Proof. reflexivity. Qed.
  Definition of_value_NotRentExempt :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::NotRentExempt" [] [] []).
  Proof. econstructor; apply of_value_with_NotRentExempt. Defined.
  Smpl Add apply of_value_NotRentExempt : of_value.

  Lemma of_value_with_InsufficientFunds :
    Value.StructTuple "spl_token_interface::error::TokenError::InsufficientFunds" [] [] [] =
    φ InsufficientFunds.
  Proof. reflexivity. Qed.
  Definition of_value_InsufficientFunds :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::InsufficientFunds" [] [] []).
  Proof. econstructor; apply of_value_with_InsufficientFunds. Defined.
  Smpl Add apply of_value_InsufficientFunds : of_value.

  Lemma of_value_with_InvalidMint :
    Value.StructTuple "spl_token_interface::error::TokenError::InvalidMint" [] [] [] =
    φ InvalidMint.
  Proof. reflexivity. Qed.
  Definition of_value_InvalidMint :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::InvalidMint" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidMint. Defined.
  Smpl Add apply of_value_InvalidMint : of_value.

  Lemma of_value_with_MintMismatch :
    Value.StructTuple "spl_token_interface::error::TokenError::MintMismatch" [] [] [] =
    φ MintMismatch.
  Proof. reflexivity. Qed.
  Definition of_value_MintMismatch :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::MintMismatch" [] [] []).
  Proof. econstructor; apply of_value_with_MintMismatch. Defined.
  Smpl Add apply of_value_MintMismatch : of_value.

  Lemma of_value_with_OwnerMismatch :
    Value.StructTuple "spl_token_interface::error::TokenError::OwnerMismatch" [] [] [] =
    φ OwnerMismatch.
  Proof. reflexivity. Qed.
  Definition of_value_OwnerMismatch :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::OwnerMismatch" [] [] []).
  Proof. econstructor; apply of_value_with_OwnerMismatch. Defined.
  Smpl Add apply of_value_OwnerMismatch : of_value.

  Lemma of_value_with_FixedSupply :
    Value.StructTuple "spl_token_interface::error::TokenError::FixedSupply" [] [] [] =
    φ FixedSupply.
  Proof. reflexivity. Qed.
  Definition of_value_FixedSupply :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::FixedSupply" [] [] []).
  Proof. econstructor; apply of_value_with_FixedSupply. Defined.
  Smpl Add apply of_value_FixedSupply : of_value.

  Lemma of_value_with_AlreadyInUse :
    Value.StructTuple "spl_token_interface::error::TokenError::AlreadyInUse" [] [] [] =
    φ AlreadyInUse.
  Proof. reflexivity. Qed.
  Definition of_value_AlreadyInUse :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::AlreadyInUse" [] [] []).
  Proof. econstructor; apply of_value_with_AlreadyInUse. Defined.
  Smpl Add apply of_value_AlreadyInUse : of_value.

  Lemma of_value_with_InvalidNumberOfProvidedSigners :
    Value.StructTuple "spl_token_interface::error::TokenError::InvalidNumberOfProvidedSigners" [] [] [] =
    φ InvalidNumberOfProvidedSigners.
  Proof. reflexivity. Qed.
  Definition of_value_InvalidNumberOfProvidedSigners :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::InvalidNumberOfProvidedSigners" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidNumberOfProvidedSigners. Defined.
  Smpl Add apply of_value_InvalidNumberOfProvidedSigners : of_value.

  Lemma of_value_with_InvalidNumberOfRequiredSigners :
    Value.StructTuple "spl_token_interface::error::TokenError::InvalidNumberOfRequiredSigners" [] [] [] =
    φ InvalidNumberOfRequiredSigners.
  Proof. reflexivity. Qed.
  Definition of_value_InvalidNumberOfRequiredSigners :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::InvalidNumberOfRequiredSigners" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidNumberOfRequiredSigners. Defined.
  Smpl Add apply of_value_InvalidNumberOfRequiredSigners : of_value.

  Lemma of_value_with_UninitializedState :
    Value.StructTuple "spl_token_interface::error::TokenError::UninitializedState" [] [] [] =
    φ UninitializedState.
  Proof. reflexivity. Qed.
  Definition of_value_UninitializedState :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::UninitializedState" [] [] []).
  Proof. econstructor; apply of_value_with_UninitializedState. Defined.
  Smpl Add apply of_value_UninitializedState : of_value.

  Lemma of_value_with_NativeNotSupported :
    Value.StructTuple "spl_token_interface::error::TokenError::NativeNotSupported" [] [] [] =
    φ NativeNotSupported.
  Proof. reflexivity. Qed.
  Definition of_value_NativeNotSupported :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::NativeNotSupported" [] [] []).
  Proof. econstructor; apply of_value_with_NativeNotSupported. Defined.
  Smpl Add apply of_value_NativeNotSupported : of_value.

  Lemma of_value_with_NonNativeHasBalance :
    Value.StructTuple "spl_token_interface::error::TokenError::NonNativeHasBalance" [] [] [] =
    φ NonNativeHasBalance.
  Proof. reflexivity. Qed.
  Definition of_value_NonNativeHasBalance :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::NonNativeHasBalance" [] [] []).
  Proof. econstructor; apply of_value_with_NonNativeHasBalance. Defined.
  Smpl Add apply of_value_NonNativeHasBalance : of_value.

  Lemma of_value_with_InvalidInstruction :
    Value.StructTuple "spl_token_interface::error::TokenError::InvalidInstruction" [] [] [] =
    φ InvalidInstruction.
  Proof. reflexivity. Qed.
  Definition of_value_InvalidInstruction :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::InvalidInstruction" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidInstruction. Defined.
  Smpl Add apply of_value_InvalidInstruction : of_value.

  Lemma of_value_with_InvalidState :
    Value.StructTuple "spl_token_interface::error::TokenError::InvalidState" [] [] [] =
    φ InvalidState.
  Proof. reflexivity. Qed.
  Definition of_value_InvalidState :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::InvalidState" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidState. Defined.
  Smpl Add apply of_value_InvalidState : of_value.

  Lemma of_value_with_Overflow :
    Value.StructTuple "spl_token_interface::error::TokenError::Overflow" [] [] [] =
    φ Overflow.
  Proof. reflexivity. Qed.
  Definition of_value_Overflow :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::Overflow" [] [] []).
  Proof. econstructor; apply of_value_with_Overflow. Defined.
  Smpl Add apply of_value_Overflow : of_value.

  Lemma of_value_with_AuthorityTypeNotSupported :
    Value.StructTuple "spl_token_interface::error::TokenError::AuthorityTypeNotSupported" [] [] [] =
    φ AuthorityTypeNotSupported.
  Proof. reflexivity. Qed.
  Definition of_value_AuthorityTypeNotSupported :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::AuthorityTypeNotSupported" [] [] []).
  Proof. econstructor; apply of_value_with_AuthorityTypeNotSupported. Defined.
  Smpl Add apply of_value_AuthorityTypeNotSupported : of_value.

  Lemma of_value_with_MintCannotFreeze :
    Value.StructTuple "spl_token_interface::error::TokenError::MintCannotFreeze" [] [] [] =
    φ MintCannotFreeze.
  Proof. reflexivity. Qed.
  Definition of_value_MintCannotFreeze :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::MintCannotFreeze" [] [] []).
  Proof. econstructor; apply of_value_with_MintCannotFreeze. Defined.
  Smpl Add apply of_value_MintCannotFreeze : of_value.

  Lemma of_value_with_AccountFrozen :
    Value.StructTuple "spl_token_interface::error::TokenError::AccountFrozen" [] [] [] =
    φ AccountFrozen.
  Proof. reflexivity. Qed.
  Definition of_value_AccountFrozen :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::AccountFrozen" [] [] []).
  Proof. econstructor; apply of_value_with_AccountFrozen. Defined.
  Smpl Add apply of_value_AccountFrozen : of_value.

  Lemma of_value_with_MintDecimalsMismatch :
    Value.StructTuple "spl_token_interface::error::TokenError::MintDecimalsMismatch" [] [] [] =
    φ MintDecimalsMismatch.
  Proof. reflexivity. Qed.
  Definition of_value_MintDecimalsMismatch :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::MintDecimalsMismatch" [] [] []).
  Proof. econstructor; apply of_value_with_MintDecimalsMismatch. Defined.
  Smpl Add apply of_value_MintDecimalsMismatch : of_value.

  Lemma of_value_with_NonNativeNotSupported :
    Value.StructTuple "spl_token_interface::error::TokenError::NonNativeNotSupported" [] [] [] =
    φ NonNativeNotSupported.
  Proof. reflexivity. Qed.
  Definition of_value_NonNativeNotSupported :
    OfValue.t (Value.StructTuple "spl_token_interface::error::TokenError::NonNativeNotSupported" [] [] []).
  Proof. econstructor; apply of_value_with_NonNativeNotSupported. Defined.
  Smpl Add apply of_value_NonNativeNotSupported : of_value.
End TokenError.

(* impl From<TokenError> for ProgramError *)
Module Impl_From_TokenError_for_ProgramError.
  Instance run : From.Run ProgramError.t TokenError.t.
  Admitted.
End Impl_From_TokenError_for_ProgramError.
Export Impl_From_TokenError_for_ProgramError.
