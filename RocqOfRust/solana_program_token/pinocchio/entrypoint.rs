use {
    crate::processor::*,
    core::{
        mem::{size_of, transmute, MaybeUninit},
        slice::from_raw_parts,
    },
    pinocchio::{
        account_info::AccountInfo,
        entrypoint::{deserialize, NON_DUP_MARKER},
        hint::likely,
        log::sol_log,
        no_allocator, nostd_panic_handler,
        program_error::{ProgramError, ToStr},
        ProgramResult, MAX_TX_ACCOUNTS, SUCCESS,
    },
    pinocchio_token_interface::{
        error::TokenError,
        instruction::TokenInstruction,
        state::{account::Account, mint::Mint, Transmutable},
    },
};

// Do not allocate memory.
no_allocator!();
// Use the no_std panic handler.
nostd_panic_handler!();

/// Custom program entrypoint to give priority to `transfer` and
/// `transfer_checked` instructions.
///
/// The entrypoint prioritizes the transfer instruction by validating
/// account data lengths and instruction data. When it can reliably
/// determine that the instruction is a transfer, it will invoke the
/// processor directly.
#[no_mangle]
#[allow(clippy::arithmetic_side_effects)]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // Constants that apply to both `transfer` and `transfer_checked`.

    /// Offset for the first account.
    const ACCOUNT1_HEADER_OFFSET: usize = 0x0008;

    /// Offset for the first account data length. This is
    /// expected to be a token account (165 bytes).
    const ACCOUNT1_DATA_LEN: usize = 0x0058;

    /// Offset for the second account.
    const ACCOUNT2_HEADER_OFFSET: usize = 0x2910;

    /// Offset for the second account data length. This is
    /// expected to be a token account for `transfer` (165 bytes)
    /// or a mint account for `transfer_checked` (82 bytes).
    const ACCOUNT2_DATA_LEN: usize = 0x2960;

    // Constants that apply to `transfer_checked` (instruction 12).

    /// Offset for the third account.
    const IX12_ACCOUNT3_HEADER_OFFSET: usize = 0x51c8;

    /// Offset for the third account data length. This is
    /// expected to be a token account (165 bytes).
    const IX12_ACCOUNT3_DATA_LEN: usize = 0x5218;

    /// Offset for the fourth account.
    const IX12_ACCOUNT4_HEADER_OFFSET: usize = 0x7ad0;

    /// Offset for the fourth account data length.
    ///
    /// This is expected to be an account with variable data
    /// length.
    const IX12_ACCOUNT4_DATA_LEN: usize = 0x7b20;

    /// Expected offset for the instruction data in the case the
    /// fourth (authority) account has zero data.
    ///
    /// This value is adjusted before it is used.
    const IX12_EXPECTED_INSTRUCTION_DATA_LEN_OFFSET: usize = 0xa330;

    // Constants that apply to `transfer` (instruction 3).

    /// Offset for the third account.
    ///
    /// Note that this assumes that both first and second accounts
    /// have zero data, which is being validated before the offset
    /// is used.
    const IX3_ACCOUNT3_HEADER_OFFSET: usize = 0x5218;

    /// Offset for the third account data length.
    ///
    /// This is expected to be an account with variable data
    /// length.
    const IX3_ACCOUNT3_DATA_LEN: usize = 0x5268;

    /// Expected offset for the instruction data in the case the
    /// third (authority) account has zero data.
    ///
    /// This value is adjusted before it is used.
    const IX3_INSTRUCTION_DATA_LEN_OFFSET: usize = 0x7a78;

    /// Align an address to the next multiple of 8.
    #[inline(always)]
    fn align(input: u64) -> u64 {
        (input + 7) & (!7)
    }

    // Fast path for `transfer_checked`.
    //
    // It expects 4 accounts:
    //   1. source: must be a token account (165 length)
    //   2. mint: must be a mint account (82 length)
    //   3. destination: must be a token account (165 length)
    //   4. authority: can be any account (variable length)
    //
    // Instruction data is expected to be at least 9 bytes
    // and discriminator equal to 12.
    if *input == 4
        && (*input.add(ACCOUNT1_DATA_LEN).cast::<u64>() == Account::LEN as u64)
        && (*input.add(ACCOUNT2_HEADER_OFFSET) == NON_DUP_MARKER)
        && (*input.add(ACCOUNT2_DATA_LEN).cast::<u64>() == Mint::LEN as u64)
        && (*input.add(IX12_ACCOUNT3_HEADER_OFFSET) == NON_DUP_MARKER)
        && (*input.add(IX12_ACCOUNT3_DATA_LEN).cast::<u64>() == Account::LEN as u64)
        && (*input.add(IX12_ACCOUNT4_HEADER_OFFSET) == NON_DUP_MARKER)
    {
        // The `authority` account can have variable data length.
        let account_4_data_len_aligned =
            align(*input.add(IX12_ACCOUNT4_DATA_LEN).cast::<u64>()) as usize;
        let offset = IX12_EXPECTED_INSTRUCTION_DATA_LEN_OFFSET + account_4_data_len_aligned;

        // Check that we have enough instruction data.
        //
        // Expected: instruction discriminator (u8) + amount (u64) + decimals (u8)
        if input.add(offset).cast::<u64>().read() >= 10 {
            let discriminator = input.add(offset + size_of::<u64>()).cast::<u8>().read();

            // Check for transfer discriminator.
            if likely(discriminator == TokenInstruction::TransferChecked as u8) {
                // instruction data length (u64) + discriminator (u8)
                let instruction_data = unsafe { from_raw_parts(input.add(offset + 9), 9) };

                let accounts = unsafe {
                    [
                        transmute::<*mut u8, AccountInfo>(input.add(ACCOUNT1_HEADER_OFFSET)),
                        transmute::<*mut u8, AccountInfo>(input.add(ACCOUNT2_HEADER_OFFSET)),
                        transmute::<*mut u8, AccountInfo>(input.add(IX12_ACCOUNT3_HEADER_OFFSET)),
                        transmute::<*mut u8, AccountInfo>(input.add(IX12_ACCOUNT4_HEADER_OFFSET)),
                    ]
                };

                #[cfg(feature = "logging")]
                pinocchio::msg!("Instruction: TransferChecked");

                return match process_transfer_checked(&accounts, instruction_data) {
                    Ok(()) => SUCCESS,
                    Err(error) => {
                        log_error(&error);
                        error.into()
                    }
                };
            }
        }
    }
    // Fast path for `transfer`.
    //
    // It expects 3 accounts:
    //   1. source: must be a token account (165 length)
    //   2. destination: must be a token account (165 length)
    //   3. authority: can be any account (variable length)
    //
    // Instruction data is expected to be at least 8 bytes
    // and discriminator equal to 3.
    else if *input == 3
        && (*input.add(ACCOUNT1_DATA_LEN).cast::<u64>() == Account::LEN as u64)
        && (*input.add(ACCOUNT2_HEADER_OFFSET) == NON_DUP_MARKER)
        && (*input.add(ACCOUNT2_DATA_LEN).cast::<u64>() == Account::LEN as u64)
        && (*input.add(IX3_ACCOUNT3_HEADER_OFFSET) == NON_DUP_MARKER)
    {
        // The `authority` account can have variable data length.
        let account_3_data_len_aligned =
            align(*input.add(IX3_ACCOUNT3_DATA_LEN).cast::<u64>()) as usize;
        let offset = IX3_INSTRUCTION_DATA_LEN_OFFSET + account_3_data_len_aligned;

        // Check that we have enough instruction data.
        if likely(input.add(offset).cast::<u64>().read() >= 9) {
            let discriminator = input.add(offset + size_of::<u64>()).cast::<u8>().read();

            // Check for transfer discriminator.
            if likely(discriminator == TokenInstruction::Transfer as u8) {
                let instruction_data =
                    unsafe { from_raw_parts(input.add(offset + 9), size_of::<u64>()) };

                let accounts = unsafe {
                    [
                        transmute::<*mut u8, AccountInfo>(input.add(ACCOUNT1_HEADER_OFFSET)),
                        transmute::<*mut u8, AccountInfo>(input.add(ACCOUNT2_HEADER_OFFSET)),
                        transmute::<*mut u8, AccountInfo>(input.add(IX3_ACCOUNT3_HEADER_OFFSET)),
                    ]
                };

                #[cfg(feature = "logging")]
                pinocchio::msg!("Instruction: Transfer");

                return match process_transfer(&accounts, instruction_data) {
                    Ok(()) => SUCCESS,
                    Err(error) => {
                        log_error(&error);
                        error.into()
                    }
                };
            }
        }
    }

    // Entrypoint for the remaining instructions.

    const UNINIT: MaybeUninit<AccountInfo> = MaybeUninit::<AccountInfo>::uninit();
    let mut accounts = [UNINIT; { MAX_TX_ACCOUNTS }];

    let (_, count, instruction_data) = deserialize(input, &mut accounts);

    match process_instruction(
        from_raw_parts(accounts.as_ptr() as _, count),
        instruction_data,
    ) {
        Ok(()) => SUCCESS,
        Err(error) => error.into(),
    }
}

/// Log an error.
#[cold]
fn log_error(error: &ProgramError) {
    sol_log(error.to_str::<TokenError>());
}

/// Process an instruction.
///
/// In the first stage, the entrypoint checks the discriminator of the
/// instruction data to determine whether the instruction is a "batch"
/// instruction or a "regular" instruction. This avoids nesting of "batch"
/// instructions, since it is not sound to have a "batch" instruction inside
/// another "batch" instruction.
#[inline(always)]
pub fn process_instruction(accounts: &[AccountInfo], instruction_data: &[u8]) -> ProgramResult {
    let [discriminator, remaining @ ..] = instruction_data else {
        return Err(TokenError::InvalidInstruction.into());
    };

    let result = if *discriminator == 255 {
        // 255 - Batch
        #[cfg(feature = "logging")]
        pinocchio::msg!("Instruction: Batch");

        process_batch(accounts, remaining)
    } else {
        inner_process_instruction(accounts, instruction_data)
    };

    result.inspect_err(log_error)
}

/// Process a "regular" instruction.
///
/// The processor of the token program is divided into two parts to reduce the
/// overhead of having a large `match` statement. The first part of the
/// processor handles the most common instructions, while the second part
/// handles the remaining instructions.
///
/// The rationale is to reduce the overhead of making multiple comparisons for
/// popular instructions.
///
/// Instructions on the first part of the inner processor:
///
/// - `0`: `InitializeMint`
/// - `1`: `InitializeAccount`
/// - `3`: `Transfer`
/// - `7`: `MintTo`
/// - `9`: `CloseAccount`
/// - `16`: `InitializeAccount2`
/// - `18`: `InitializeAccount3`
/// - `20`: `InitializeMint2`
#[inline(always)]
pub(crate) fn inner_process_instruction(
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let [discriminator, instruction_data @ ..] = instruction_data else {
        return Err(TokenError::InvalidInstruction.into());
    };

    match *discriminator {
        // 0 - InitializeMint
        0 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: InitializeMint");

            process_initialize_mint(accounts, instruction_data)
        }
        // 1 - InitializeAccount
        1 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: InitializeAccount");

            process_initialize_account(accounts)
        }
        // 3 - Transfer
        3 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: Transfer");

            process_transfer(accounts, instruction_data)
        }
        // 7 - MintTo
        7 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: MintTo");

            process_mint_to(accounts, instruction_data)
        }
        // 8 - Burn
        8 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: Burn");

            process_burn(accounts, instruction_data)
        }
        // 9 - CloseAccount
        9 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: CloseAccount");

            process_close_account(accounts)
        }
        // 12 - TransferChecked
        12 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: TransferChecked");

            process_transfer_checked(accounts, instruction_data)
        }
        // 15 - BurnChecked
        15 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: BurnChecked");

            process_burn_checked(accounts, instruction_data)
        }
        // 17 - SyncNative
        17 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: SyncNative");

            process_sync_native(accounts)
        }
        // 18 - InitializeAccount3
        18 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: InitializeAccount3");

            process_initialize_account3(accounts, instruction_data)
        }
        // 20 - InitializeMint2
        20 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: InitializeMint2");

            process_initialize_mint2(accounts, instruction_data)
        }
        // 22 - InitializeImmutableOwner
        22 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: InitializeImmutableOwner");

            process_initialize_immutable_owner(accounts)
        }
        d => inner_process_remaining_instruction(accounts, instruction_data, d),
    }
}

/// Process a remaining "regular" instruction.
///
/// This function is called by the [`inner_process_instruction`] function if the
/// discriminator does not match any of the common instructions. This function
/// is used to reduce the overhead of having a large `match` statement in the
/// [`inner_process_instruction`] function.
fn inner_process_remaining_instruction(
    accounts: &[AccountInfo],
    instruction_data: &[u8],
    discriminator: u8,
) -> ProgramResult {
    match discriminator {
        // 2 - InitializeMultisig
        2 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: InitializeMultisig");

            process_initialize_multisig(accounts, instruction_data)
        }
        // 4 - Approve
        4 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: Approve");

            process_approve(accounts, instruction_data)
        }
        // 5 - Revoke
        5 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: Revoke");

            process_revoke(accounts)
        }
        // 6 - SetAuthority
        6 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: SetAuthority");

            process_set_authority(accounts, instruction_data)
        }
        // 10 - FreezeAccount
        10 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: FreezeAccount");

            process_freeze_account(accounts)
        }
        // 11 - ThawAccount
        11 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: ThawAccount");

            process_thaw_account(accounts)
        }
        // 13 - ApproveChecked
        13 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: ApproveChecked");

            process_approve_checked(accounts, instruction_data)
        }
        // 14 - MintToChecked
        14 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: MintToChecked");

            process_mint_to_checked(accounts, instruction_data)
        }
        // 16 - InitializeAccount2
        16 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: InitializeAccount2");

            process_initialize_account2(accounts, instruction_data)
        }
        // 19 - InitializeMultisig2
        19 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: InitializeMultisig2");

            process_initialize_multisig2(accounts, instruction_data)
        }
        // 21 - GetAccountDataSize
        21 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: GetAccountDataSize");

            process_get_account_data_size(accounts)
        }
        // 23 - AmountToUiAmount
        23 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: AmountToUiAmount");

            process_amount_to_ui_amount(accounts, instruction_data)
        }
        // 24 - UiAmountToAmount
        24 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: UiAmountToAmount");

            process_ui_amount_to_amount(accounts, instruction_data)
        }
        // 38 - WithdrawExcessLamports
        38 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: WithdrawExcessLamports");

            process_withdraw_excess_lamports(accounts)
        }
        // 45 - UnwrapLamports
        45 => {
            #[cfg(feature = "logging")]
            pinocchio::msg!("Instruction: UnwrapLamports");

            process_unwrap_lamports(accounts, instruction_data)
        }
        _ => Err(TokenError::InvalidInstruction.into()),
    }
}
