use {
    crate::{entrypoint::inner_process_instruction, processor::check_account_owner},
    pinocchio::{account_info::AccountInfo, program_error::ProgramError, ProgramResult},
    pinocchio_token_interface::error::TokenError,
};

/// The size of the batch instruction header.
///
/// The header of each instruction consists of two `u8` values:
///  * number of the accounts
///  * length of the instruction data
const IX_HEADER_SIZE: usize = 2;

#[allow(clippy::arithmetic_side_effects)]
pub fn process_batch(mut accounts: &[AccountInfo], mut instruction_data: &[u8]) -> ProgramResult {
    loop {
        // Validates the instruction data and accounts offset.

        if instruction_data.len() < IX_HEADER_SIZE {
            // The instruction data must have at least two bytes.
            return Err(TokenError::InvalidInstruction.into());
        }

        // SAFETY: The instruction data is guaranteed to have at least two bytes
        // (header) + one byte (discriminator) and the values are within the bounds
        // of an `usize`.
        let expected_accounts = unsafe { *instruction_data.get_unchecked(0) as usize };
        let data_offset = IX_HEADER_SIZE + unsafe { *instruction_data.get_unchecked(1) as usize };

        if instruction_data.len() < data_offset || data_offset == IX_HEADER_SIZE {
            return Err(TokenError::InvalidInstruction.into());
        }

        if accounts.len() < expected_accounts {
            return Err(ProgramError::NotEnoughAccountKeys);
        }

        // Process the instruction.

        // SAFETY: The instruction data and accounts lengths are already validated so
        // all slices are guaranteed to be valid.
        let (ix_accounts, ix_data) = unsafe {
            (
                accounts.get_unchecked(..expected_accounts),
                instruction_data.get_unchecked(IX_HEADER_SIZE..data_offset),
            )
        };

        // Few Instructions require specific account ownership checks when executed
        // in a batch since ownership is only enforced by the runtime at the end of
        // the batch processing.
        //
        // Instructions that do not appear in the list below do not require
        // ownership checks since they either do not modify accounts or the ownership
        // is already checked explicitly.
        if let Some(&discriminator) = ix_data.first() {
            match discriminator {
                // 3 - Transfer
                // 7 - MintTo
                // 8 - Burn
                // 14 - MintToChecked
                // 15 - BurnChecked
                3 | 7 | 8 | 14 | 15 => {
                    let [a0, a1, ..] = ix_accounts else {
                        return Err(ProgramError::NotEnoughAccountKeys);
                    };
                    check_account_owner(a0)?;
                    check_account_owner(a1)?;
                }
                // 12 - TransferChecked
                12 => {
                    let [a0, _, a2, ..] = ix_accounts else {
                        return Err(ProgramError::NotEnoughAccountKeys);
                    };
                    check_account_owner(a0)?;
                    check_account_owner(a2)?;
                }
                // 4 - Approve
                // 5 - Revoke
                // 6 - SetAuthority
                // 9 - CloseAccount
                // 10 - FreezeAccount
                // 11 - ThawAccount
                // 13 - ApproveChecked
                // 22 - InitializeImmutableOwner
                // 38 - WithdrawExcessLamports
                // 45 - UnwrapLamports
                4..=13 | 22 | 38 | 45 => {
                    let [a0, ..] = ix_accounts else {
                        return Err(ProgramError::NotEnoughAccountKeys);
                    };
                    check_account_owner(a0)?;
                }
                _ => {}
            }
        }

        inner_process_instruction(ix_accounts, ix_data)?;

        if data_offset == instruction_data.len() {
            // The batch is complete.
            break;
        }

        accounts = &accounts[expected_accounts..];
        instruction_data = &instruction_data[data_offset..];
    }

    Ok(())
}
