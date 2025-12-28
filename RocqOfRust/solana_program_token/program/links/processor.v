Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import anza_xyz_solana_sdk.account_info.links.lib.
Require Import anza_xyz_solana_sdk.address.links.lib.
Require Import anza_xyz_solana_sdk.program_error.links.lib.
Require Import core.cell.links.mod.
Require Import core.convert.links.mod.
Require Import core.links.option.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import core.ops.links.try_trait.
Require Import core.ops.links.control_flow.
Require Import core.slice.links.iter.
Require Import core.slice.links.mod.
Require Import solana_program_token.interface.links.error.
Require Import solana_program_token.interface.links.state.
Require Import solana_program_token.program.processor.

Module Impl_Processor.
  (* pub fn cmp_pubkeys(a: &Pubkey, b: &Pubkey) -> bool *)
  Instance run_cmp_pubkeys
      (a : M.Ref.t Pointer.Kind.Ref Address.t)
      (b : M.Ref.t Pointer.Kind.Ref Address.t) :
    Run.Trait processor.Impl_spl_token_processor_Processor.cmp_pubkeys
      [] [] [φ a; φ b]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_cmp_pubkeys.

  (* pub fn check_account_owner(program_id: &Pubkey, account_info: &AccountInfo) -> ProgramResult *)
  Instance run_check_account_owner
      (program_id : M.Ref.t Pointer.Kind.Ref Address.t)
      (account_info : M.Ref.t Pointer.Kind.Ref AccountInfo.t) :
    Run.Trait processor.Impl_spl_token_processor_Processor.check_account_owner
      [] [] [φ program_id; φ account_info]
      ProgramResult.t.
  Proof.
    constructor.
    run_symbolic.
    all: change (Ty.tuple []) with (Φ unit).
    all: change (Ty.path "solana_program_error::ProgramError") with (Φ ProgramError.t).
    all: unshelve (repeat smpl of_value).
    exact tt.
  Defined.
  Global Opaque run_check_account_owner.

  (*
    pub fn validate_owner(
        program_id: &Pubkey,
        expected_owner: &Pubkey,
        owner_account_info: &AccountInfo,
        signers: &[AccountInfo],
    ) -> ProgramResult
  *)
  Instance run_validate_owner
      (program_id : M.Ref.t Pointer.Kind.Ref Address.t)
      (expected_owner : M.Ref.t Pointer.Kind.Ref Address.t)
      (owner_account_info : M.Ref.t Pointer.Kind.Ref AccountInfo.t)
      (signers : M.Ref.t Pointer.Kind.Ref (list AccountInfo.t)) :
    Run.Trait processor.Impl_spl_token_processor_Processor.validate_owner
      [] [] [φ program_id; φ expected_owner; φ owner_account_info; φ signers]
      ProgramResult.t.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_validate_owner.

  (*
    pub fn process_transfer(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
        expected_decimals: Option<u8>,
    ) -> ProgramResult
  *)
  Instance run_process_transfer
      (program_id : M.Ref.t Pointer.Kind.Ref Address.t)
      (accounts : M.Ref.t Pointer.Kind.Ref (list AccountInfo.t))
      (amount : U64.t)
      (expected_decimals : option U8.t) :
    Run.Trait processor.Impl_spl_token_processor_Processor.process_transfer
      [] [] [φ program_id; φ accounts; φ amount; φ expected_decimals]
      ProgramResult.t.
  Proof.
    constructor.
    destruct (Impl_Try_for_Result.run (M.Ref.t Pointer.Kind.Ref AccountInfo.t) ProgramError.t).
    destruct (Impl_Try_for_Result.run Account.t ProgramError.t).
    destruct (Impl_Try_for_Result.run Mint.t ProgramError.t).
    destruct (Impl_Try_for_Result.run U64.t TokenError.t).
    destruct (Impl_Try_for_Result.run unit ProgramError.t).
    destruct (Impl_FromResidual_for_Result.run unit ProgramError.t).
    destruct (Impl_Into_for_From_T.run Impl_From_TokenError_for_ProgramError.run).
    destruct Impl_Pack_for_Account.run.
    destruct Impl_Pack_for_Mint.run.
    destruct (Impl_Deref_for_Ref.run (M.Ref.t Pointer.Kind.MutRef (list U8.t))).
    Time run_symbolic.
  Admitted.
  Global Opaque run_process_transfer.
End Impl_Processor.
