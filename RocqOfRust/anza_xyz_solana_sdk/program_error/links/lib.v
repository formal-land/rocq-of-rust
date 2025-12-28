Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.links.result.
Require Import anza_xyz_solana_sdk.program_error.lib.

Module ProgramError.
  Inductive t : Set :=
  | Custom (n : U32.t)
  | InvalidArgument
  | InvalidInstructionData
  | InvalidAccountData
  | AccountDataTooSmall
  | InsufficientFunds
  | IncorrectProgramId
  | MissingRequiredSignature
  | AccountAlreadyInitialized
  | UninitializedAccount
  | NotEnoughAccountKeys
  | AccountBorrowFailed
  | MaxSeedLengthExceeded
  | InvalidSeeds
  | BorshIoError
  | AccountNotRentExempt
  | UnsupportedSysvar
  | IllegalOwner
  | MaxAccountsDataAllocationsExceeded
  | InvalidRealloc
  | MaxInstructionTraceLengthExceeded
  | BuiltinProgramsMustConsumeComputeUnits
  | InvalidAccountOwner
  | ArithmeticOverflow
  | Immutable
  | IncorrectAuthority
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "solana_program_error::ProgramError";
    φ x :=
      match x with
      | Custom n =>
          Value.StructTuple "solana_program_error::ProgramError::Custom" [] [] [φ n]
      | InvalidArgument =>
          Value.StructTuple "solana_program_error::ProgramError::InvalidArgument" [] [] []
      | InvalidInstructionData =>
          Value.StructTuple "solana_program_error::ProgramError::InvalidInstructionData" [] [] []
      | InvalidAccountData =>
          Value.StructTuple "solana_program_error::ProgramError::InvalidAccountData" [] [] []
      | AccountDataTooSmall =>
          Value.StructTuple "solana_program_error::ProgramError::AccountDataTooSmall" [] [] []
      | InsufficientFunds =>
          Value.StructTuple "solana_program_error::ProgramError::InsufficientFunds" [] [] []
      | IncorrectProgramId =>
          Value.StructTuple "solana_program_error::ProgramError::IncorrectProgramId" [] [] []
      | MissingRequiredSignature =>
          Value.StructTuple "solana_program_error::ProgramError::MissingRequiredSignature" [] [] []
      | AccountAlreadyInitialized =>
          Value.StructTuple "solana_program_error::ProgramError::AccountAlreadyInitialized" [] [] []
      | UninitializedAccount =>
          Value.StructTuple "solana_program_error::ProgramError::UninitializedAccount" [] [] []
      | NotEnoughAccountKeys =>
          Value.StructTuple "solana_program_error::ProgramError::NotEnoughAccountKeys" [] [] []
      | AccountBorrowFailed =>
          Value.StructTuple "solana_program_error::ProgramError::AccountBorrowFailed" [] [] []
      | MaxSeedLengthExceeded =>
          Value.StructTuple "solana_program_error::ProgramError::MaxSeedLengthExceeded" [] [] []
      | InvalidSeeds =>
          Value.StructTuple "solana_program_error::ProgramError::InvalidSeeds" [] [] []
      | BorshIoError =>
          Value.StructTuple "solana_program_error::ProgramError::BorshIoError" [] [] []
      | AccountNotRentExempt =>
          Value.StructTuple "solana_program_error::ProgramError::AccountNotRentExempt" [] [] []
      | UnsupportedSysvar =>
          Value.StructTuple "solana_program_error::ProgramError::UnsupportedSysvar" [] [] []
      | IllegalOwner =>
          Value.StructTuple "solana_program_error::ProgramError::IllegalOwner" [] [] []
      | MaxAccountsDataAllocationsExceeded =>
          Value.StructTuple "solana_program_error::ProgramError::MaxAccountsDataAllocationsExceeded" [] [] []
      | InvalidRealloc =>
          Value.StructTuple "solana_program_error::ProgramError::InvalidRealloc" [] [] []
      | MaxInstructionTraceLengthExceeded =>
          Value.StructTuple "solana_program_error::ProgramError::MaxInstructionTraceLengthExceeded" [] [] []
      | BuiltinProgramsMustConsumeComputeUnits =>
          Value.StructTuple "solana_program_error::ProgramError::BuiltinProgramsMustConsumeComputeUnits" [] [] []
      | InvalidAccountOwner =>
          Value.StructTuple "solana_program_error::ProgramError::InvalidAccountOwner" [] [] []
      | ArithmeticOverflow =>
          Value.StructTuple "solana_program_error::ProgramError::ArithmeticOverflow" [] [] []
      | Immutable =>
          Value.StructTuple "solana_program_error::ProgramError::Immutable" [] [] []
      | IncorrectAuthority =>
          Value.StructTuple "solana_program_error::ProgramError::IncorrectAuthority" [] [] []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "solana_program_error::ProgramError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Custom (n : U32.t) :
    Value.StructTuple "solana_program_error::ProgramError::Custom" [] [] [φ n]
    = φ (Custom n).
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Custom : of_value.
  Definition of_value_Custom (n : U32.t) :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::Custom" [] [] [φ n]).
  Proof. econstructor; apply of_value_with_Custom. Defined.
  Smpl Add apply of_value_Custom : of_value.

  Lemma of_value_with_InvalidArgument :
    Value.StructTuple "solana_program_error::ProgramError::InvalidArgument" [] [] [] = φ InvalidArgument.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_InvalidArgument : of_value.
  Definition of_value_InvalidArgument :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::InvalidArgument" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidArgument. Defined.
  Smpl Add apply of_value_InvalidArgument : of_value.

  Lemma of_value_with_InvalidInstructionData :
    Value.StructTuple "solana_program_error::ProgramError::InvalidInstructionData" [] [] [] = φ InvalidInstructionData.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_InvalidInstructionData : of_value.
  Definition of_value_InvalidInstructionData :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::InvalidInstructionData" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidInstructionData. Defined.
  Smpl Add apply of_value_InvalidInstructionData : of_value.

  Lemma of_value_with_InvalidAccountData :
    Value.StructTuple "solana_program_error::ProgramError::InvalidAccountData" [] [] [] = φ InvalidAccountData.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_InvalidAccountData : of_value.
  Definition of_value_InvalidAccountData :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::InvalidAccountData" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidAccountData. Defined.
  Smpl Add apply of_value_InvalidAccountData : of_value.

  Lemma of_value_with_AccountDataTooSmall :
    Value.StructTuple "solana_program_error::ProgramError::AccountDataTooSmall" [] [] [] = φ AccountDataTooSmall.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_AccountDataTooSmall : of_value.
  Definition of_value_AccountDataTooSmall :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::AccountDataTooSmall" [] [] []).
  Proof. econstructor; apply of_value_with_AccountDataTooSmall. Defined.
  Smpl Add apply of_value_AccountDataTooSmall : of_value.

  Lemma of_value_with_InsufficientFunds :
    Value.StructTuple "solana_program_error::ProgramError::InsufficientFunds" [] [] [] = φ InsufficientFunds.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_InsufficientFunds : of_value.
  Definition of_value_InsufficientFunds :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::InsufficientFunds" [] [] []).
  Proof. econstructor; apply of_value_with_InsufficientFunds. Defined.
  Smpl Add apply of_value_InsufficientFunds : of_value.

  Lemma of_value_with_IncorrectProgramId :
    Value.StructTuple "solana_program_error::ProgramError::IncorrectProgramId" [] [] [] = φ IncorrectProgramId.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_IncorrectProgramId : of_value.
  Definition of_value_IncorrectProgramId :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::IncorrectProgramId" [] [] []).
  Proof. econstructor; apply of_value_with_IncorrectProgramId. Defined.
  Smpl Add apply of_value_IncorrectProgramId : of_value.

  Lemma of_value_with_MissingRequiredSignature :
    Value.StructTuple "solana_program_error::ProgramError::MissingRequiredSignature" [] [] [] = φ MissingRequiredSignature.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_MissingRequiredSignature : of_value.
  Definition of_value_MissingRequiredSignature :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::MissingRequiredSignature" [] [] []).
  Proof. econstructor; apply of_value_with_MissingRequiredSignature. Defined.
  Smpl Add apply of_value_MissingRequiredSignature : of_value.

  Lemma of_value_with_AccountAlreadyInitialized :
    Value.StructTuple "solana_program_error::ProgramError::AccountAlreadyInitialized" [] [] [] = φ AccountAlreadyInitialized.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_AccountAlreadyInitialized : of_value.
  Definition of_value_AccountAlreadyInitialized :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::AccountAlreadyInitialized" [] [] []).
  Proof. econstructor; apply of_value_with_AccountAlreadyInitialized. Defined.
  Smpl Add apply of_value_AccountAlreadyInitialized : of_value.

  Lemma of_value_with_UninitializedAccount :
    Value.StructTuple "solana_program_error::ProgramError::UninitializedAccount" [] [] [] = φ UninitializedAccount.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_UninitializedAccount : of_value.
  Definition of_value_UninitializedAccount :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::UninitializedAccount" [] [] []).
  Proof. econstructor; apply of_value_with_UninitializedAccount. Defined.
  Smpl Add apply of_value_UninitializedAccount : of_value.

  Lemma of_value_with_NotEnoughAccountKeys :
    Value.StructTuple "solana_program_error::ProgramError::NotEnoughAccountKeys" [] [] [] = φ NotEnoughAccountKeys.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_NotEnoughAccountKeys : of_value.
  Definition of_value_NotEnoughAccountKeys :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::NotEnoughAccountKeys" [] [] []).
  Proof. econstructor; apply of_value_with_NotEnoughAccountKeys. Defined.
  Smpl Add apply of_value_NotEnoughAccountKeys : of_value.

  Lemma of_value_with_AccountBorrowFailed :
    Value.StructTuple "solana_program_error::ProgramError::AccountBorrowFailed" [] [] [] = φ AccountBorrowFailed.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_AccountBorrowFailed : of_value.
  Definition of_value_AccountBorrowFailed :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::AccountBorrowFailed" [] [] []).
  Proof. econstructor; apply of_value_with_AccountBorrowFailed. Defined.
  Smpl Add apply of_value_AccountBorrowFailed : of_value.

  Lemma of_value_with_MaxSeedLengthExceeded :
    Value.StructTuple "solana_program_error::ProgramError::MaxSeedLengthExceeded" [] [] [] = φ MaxSeedLengthExceeded.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_MaxSeedLengthExceeded : of_value.
  Definition of_value_MaxSeedLengthExceeded :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::MaxSeedLengthExceeded" [] [] []).
  Proof. econstructor; apply of_value_with_MaxSeedLengthExceeded. Defined.
  Smpl Add apply of_value_MaxSeedLengthExceeded : of_value.

  Lemma of_value_with_InvalidSeeds :
    Value.StructTuple "solana_program_error::ProgramError::InvalidSeeds" [] [] [] = φ InvalidSeeds.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_InvalidSeeds : of_value.
  Definition of_value_InvalidSeeds :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::InvalidSeeds" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidSeeds. Defined.
  Smpl Add apply of_value_InvalidSeeds : of_value.

  Lemma of_value_with_BorshIoError :
    Value.StructTuple "solana_program_error::ProgramError::BorshIoError" [] [] [] = φ BorshIoError.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_BorshIoError : of_value.
  Definition of_value_BorshIoError :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::BorshIoError" [] [] []).
  Proof. econstructor; apply of_value_with_BorshIoError. Defined.
  Smpl Add apply of_value_BorshIoError : of_value.

  Lemma of_value_with_AccountNotRentExempt :
    Value.StructTuple "solana_program_error::ProgramError::AccountNotRentExempt" [] [] [] = φ AccountNotRentExempt.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_AccountNotRentExempt : of_value.
  Definition of_value_AccountNotRentExempt :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::AccountNotRentExempt" [] [] []).
  Proof. econstructor; apply of_value_with_AccountNotRentExempt. Defined.
  Smpl Add apply of_value_AccountNotRentExempt : of_value.

  Lemma of_value_with_UnsupportedSysvar :
    Value.StructTuple "solana_program_error::ProgramError::UnsupportedSysvar" [] [] [] = φ UnsupportedSysvar.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_UnsupportedSysvar : of_value.
  Definition of_value_UnsupportedSysvar :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::UnsupportedSysvar" [] [] []).
  Proof. econstructor; apply of_value_with_UnsupportedSysvar. Defined.
  Smpl Add apply of_value_UnsupportedSysvar : of_value.

  Lemma of_value_with_IllegalOwner :
    Value.StructTuple "solana_program_error::ProgramError::IllegalOwner" [] [] [] = φ IllegalOwner.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_IllegalOwner : of_value.
  Definition of_value_IllegalOwner :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::IllegalOwner" [] [] []).
  Proof. econstructor; apply of_value_with_IllegalOwner. Defined.
  Smpl Add apply of_value_IllegalOwner : of_value.

  Lemma of_value_with_MaxAccountsDataAllocationsExceeded :
    Value.StructTuple "solana_program_error::ProgramError::MaxAccountsDataAllocationsExceeded" [] [] [] =
    φ MaxAccountsDataAllocationsExceeded.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_MaxAccountsDataAllocationsExceeded : of_value.
  Definition of_value_MaxAccountsDataAllocationsExceeded :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::MaxAccountsDataAllocationsExceeded" [] [] []).
  Proof. econstructor; apply of_value_with_MaxAccountsDataAllocationsExceeded. Defined.
  Smpl Add apply of_value_MaxAccountsDataAllocationsExceeded : of_value.

  Lemma of_value_with_InvalidRealloc :
    Value.StructTuple "solana_program_error::ProgramError::InvalidRealloc" [] [] [] = φ InvalidRealloc.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_InvalidRealloc : of_value.
  Definition of_value_InvalidRealloc :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::InvalidRealloc" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidRealloc. Defined.
  Smpl Add apply of_value_InvalidRealloc : of_value.

  Lemma of_value_with_MaxInstructionTraceLengthExceeded :
    Value.StructTuple "solana_program_error::ProgramError::MaxInstructionTraceLengthExceeded" [] [] [] =
    φ MaxInstructionTraceLengthExceeded.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_MaxInstructionTraceLengthExceeded : of_value.
  Definition of_value_MaxInstructionTraceLengthExceeded :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::MaxInstructionTraceLengthExceeded" [] [] []).
  Proof. econstructor; apply of_value_with_MaxInstructionTraceLengthExceeded. Defined.
  Smpl Add apply of_value_MaxInstructionTraceLengthExceeded : of_value.

  Lemma of_value_with_BuiltinProgramsMustConsumeComputeUnits :
    Value.StructTuple "solana_program_error::ProgramError::BuiltinProgramsMustConsumeComputeUnits" [] [] [] =
    φ BuiltinProgramsMustConsumeComputeUnits.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_BuiltinProgramsMustConsumeComputeUnits : of_value.
  Definition of_value_BuiltinProgramsMustConsumeComputeUnits :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::BuiltinProgramsMustConsumeComputeUnits" [] [] []).
  Proof. econstructor; apply of_value_with_BuiltinProgramsMustConsumeComputeUnits. Defined.
  Smpl Add apply of_value_BuiltinProgramsMustConsumeComputeUnits : of_value.

  Lemma of_value_with_InvalidAccountOwner :
    Value.StructTuple "solana_program_error::ProgramError::InvalidAccountOwner" [] [] [] = φ InvalidAccountOwner.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_InvalidAccountOwner : of_value.
  Definition of_value_InvalidAccountOwner :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::InvalidAccountOwner" [] [] []).
  Proof. econstructor; apply of_value_with_InvalidAccountOwner. Defined.
  Smpl Add apply of_value_InvalidAccountOwner : of_value.

  Lemma of_value_with_ArithmeticOverflow :
    Value.StructTuple "solana_program_error::ProgramError::ArithmeticOverflow" [] [] [] = φ ArithmeticOverflow.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_ArithmeticOverflow : of_value.
  Definition of_value_ArithmeticOverflow :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::ArithmeticOverflow" [] [] []).
  Proof. econstructor; apply of_value_with_ArithmeticOverflow. Defined.
  Smpl Add apply of_value_ArithmeticOverflow : of_value.

  Lemma of_value_with_Immutable :
    Value.StructTuple "solana_program_error::ProgramError::Immutable" [] [] [] = φ Immutable.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Immutable : of_value.
  Definition of_value_Immutable :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::Immutable" [] [] []).
  Proof. econstructor; apply of_value_with_Immutable. Defined.
  Smpl Add apply of_value_Immutable : of_value.

  Lemma of_value_with_IncorrectAuthority :
    Value.StructTuple "solana_program_error::ProgramError::IncorrectAuthority" [] [] [] = φ IncorrectAuthority.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_IncorrectAuthority : of_value.
  Definition of_value_IncorrectAuthority :
    OfValue.t (Value.StructTuple "solana_program_error::ProgramError::IncorrectAuthority" [] [] []).
  Proof. econstructor; apply of_value_with_IncorrectAuthority. Defined.
  Smpl Add apply of_value_IncorrectAuthority : of_value.

  Module SubPointer.
    Definition get_Custom_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "solana_program_error::ProgramError::Custom" 0) :=
    {|
      SubPointer.Runner.projection x :=
        match x with
        | Custom n => Some n
        | _ => None
        end;
      SubPointer.Runner.injection x y :=
        match x with
        | Custom _ => Some (Custom y)
        | _ => None
        end;
    |}.

    Lemma get_Custom_0_is_valid :
      SubPointer.Runner.Valid.t get_Custom_0.
    Proof.
      constructor; intros; destruct a; try reflexivity; discriminate.
    Qed.
    Smpl Add apply get_Custom_0_is_valid : run_sub_pointer.
  End SubPointer.
End ProgramError.

(* ProgramResult = Result<(), ProgramError> *)
Module ProgramResult.
  Definition t : Set := Result.t unit ProgramError.t.
End ProgramResult.
