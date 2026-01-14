//! Program entrypoint

use {
    crate::processor::Processor, solana_account_info::AccountInfo, solana_msg::msg,
    solana_program_error::ProgramResult, solana_pubkey::Pubkey,
    spl_token_interface::error::TokenError,
};

solana_program_entrypoint::entrypoint!(process_instruction);
fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if let Err(error) = Processor::process(program_id, accounts, instruction_data) {
        // catch the error so we can print it
        msg!(error.to_str::<TokenError>());
        return Err(error);
    }
    Ok(())
}
