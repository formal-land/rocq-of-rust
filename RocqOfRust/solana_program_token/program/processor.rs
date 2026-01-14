//! Program state processor

use {
    crate::{
        amount_to_ui_amount_string_trimmed,
        error::TokenError,
        instruction::{is_valid_signer_index, AuthorityType, TokenInstruction, MAX_SIGNERS},
        state::{Account, AccountState, Mint, Multisig},
        try_ui_amount_into_amount,
    },
    solana_account_info::{next_account_info, AccountInfo},
    solana_cpi::set_return_data,
    solana_msg::msg,
    solana_program_error::{ProgramError, ProgramResult},
    solana_program_memory::sol_memcmp,
    solana_program_option::COption,
    solana_program_pack::{IsInitialized, Pack},
    solana_pubkey::{Pubkey, PUBKEY_BYTES},
    solana_rent::Rent,
    solana_sdk_ids::system_program,
    solana_sysvar::{Sysvar, SysvarSerialize},
};

/// Program state handler.
pub struct Processor {}
impl Processor {
    fn _process_initialize_mint(
        accounts: &[AccountInfo],
        decimals: u8,
        mint_authority: Pubkey,
        freeze_authority: COption<Pubkey>,
        rent_sysvar_account: bool,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let mint_info = next_account_info(account_info_iter)?;
        let mint_data_len = mint_info.data_len();
        let rent = if rent_sysvar_account {
            Rent::from_account_info(next_account_info(account_info_iter)?)?
        } else {
            Rent::get()?
        };

        let mut mint = Mint::unpack_unchecked(&mint_info.data.borrow())?;
        if mint.is_initialized {
            return Err(TokenError::AlreadyInUse.into());
        }

        if !rent.is_exempt(mint_info.lamports(), mint_data_len) {
            return Err(TokenError::NotRentExempt.into());
        }

        mint.mint_authority = COption::Some(mint_authority);
        mint.decimals = decimals;
        mint.is_initialized = true;
        mint.freeze_authority = freeze_authority;

        Mint::pack(mint, &mut mint_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes an [`InitializeMint`](enum.TokenInstruction.html) instruction.
    pub fn process_initialize_mint(
        accounts: &[AccountInfo],
        decimals: u8,
        mint_authority: Pubkey,
        freeze_authority: COption<Pubkey>,
    ) -> ProgramResult {
        Self::_process_initialize_mint(accounts, decimals, mint_authority, freeze_authority, true)
    }

    /// Processes an [`InitializeMint2`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_mint2(
        accounts: &[AccountInfo],
        decimals: u8,
        mint_authority: Pubkey,
        freeze_authority: COption<Pubkey>,
    ) -> ProgramResult {
        Self::_process_initialize_mint(accounts, decimals, mint_authority, freeze_authority, false)
    }

    fn _process_initialize_account(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        owner: Option<&Pubkey>,
        rent_sysvar_account: bool,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let new_account_info = next_account_info(account_info_iter)?;
        let mint_info = next_account_info(account_info_iter)?;
        let owner = if let Some(owner) = owner {
            owner
        } else {
            next_account_info(account_info_iter)?.key
        };
        let new_account_info_data_len = new_account_info.data_len();
        let rent = if rent_sysvar_account {
            Rent::from_account_info(next_account_info(account_info_iter)?)?
        } else {
            Rent::get()?
        };

        let mut account = Account::unpack_unchecked(&new_account_info.data.borrow())?;
        if account.is_initialized() {
            return Err(TokenError::AlreadyInUse.into());
        }

        if !rent.is_exempt(new_account_info.lamports(), new_account_info_data_len) {
            return Err(TokenError::NotRentExempt.into());
        }

        let is_native_mint = Self::cmp_pubkeys(mint_info.key, &crate::native_mint::id());
        if !is_native_mint {
            Self::check_account_owner(program_id, mint_info)?;
            let _ = Mint::unpack(&mint_info.data.borrow_mut())
                .map_err(|_| Into::<ProgramError>::into(TokenError::InvalidMint))?;
        }

        account.mint = *mint_info.key;
        account.owner = *owner;
        account.close_authority = COption::None;
        account.delegate = COption::None;
        account.delegated_amount = 0;
        account.state = AccountState::Initialized;
        if is_native_mint {
            let rent_exempt_reserve = rent.minimum_balance(new_account_info_data_len);
            account.is_native = COption::Some(rent_exempt_reserve);
            account.amount = new_account_info
                .lamports()
                .checked_sub(rent_exempt_reserve)
                .ok_or(TokenError::Overflow)?;
        } else {
            account.is_native = COption::None;
            account.amount = 0;
        };

        Account::pack(account, &mut new_account_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes an [`InitializeAccount`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_account(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
    ) -> ProgramResult {
        Self::_process_initialize_account(program_id, accounts, None, true)
    }

    /// Processes an [`InitializeAccount2`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_account2(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        owner: Pubkey,
    ) -> ProgramResult {
        Self::_process_initialize_account(program_id, accounts, Some(&owner), true)
    }

    /// Processes an [`InitializeAccount3`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_account3(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        owner: Pubkey,
    ) -> ProgramResult {
        Self::_process_initialize_account(program_id, accounts, Some(&owner), false)
    }

    fn _process_initialize_multisig(
        accounts: &[AccountInfo],
        m: u8,
        rent_sysvar_account: bool,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let multisig_info = next_account_info(account_info_iter)?;
        let multisig_info_data_len = multisig_info.data_len();
        let rent = if rent_sysvar_account {
            Rent::from_account_info(next_account_info(account_info_iter)?)?
        } else {
            Rent::get()?
        };

        let mut multisig = Multisig::unpack_unchecked(&multisig_info.data.borrow())?;
        if multisig.is_initialized {
            return Err(TokenError::AlreadyInUse.into());
        }

        if !rent.is_exempt(multisig_info.lamports(), multisig_info_data_len) {
            return Err(TokenError::NotRentExempt.into());
        }

        let signer_infos = account_info_iter.as_slice();
        multisig.m = m;
        multisig.n = signer_infos.len() as u8;
        if !is_valid_signer_index(multisig.n as usize) {
            return Err(TokenError::InvalidNumberOfProvidedSigners.into());
        }
        if !is_valid_signer_index(multisig.m as usize) {
            return Err(TokenError::InvalidNumberOfRequiredSigners.into());
        }
        for (i, signer_info) in signer_infos.iter().enumerate() {
            multisig.signers[i] = *signer_info.key;
        }
        multisig.is_initialized = true;

        Multisig::pack(multisig, &mut multisig_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes a [`InitializeMultisig`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_multisig(accounts: &[AccountInfo], m: u8) -> ProgramResult {
        Self::_process_initialize_multisig(accounts, m, true)
    }

    /// Processes a [`InitializeMultisig2`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_multisig2(accounts: &[AccountInfo], m: u8) -> ProgramResult {
        Self::_process_initialize_multisig(accounts, m, false)
    }

    /// Processes a [`Transfer`](enum.TokenInstruction.html) instruction.
    pub fn process_transfer(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
        expected_decimals: Option<u8>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();

        let source_account_info = next_account_info(account_info_iter)?;

        let expected_mint_info = if let Some(expected_decimals) = expected_decimals {
            Some((next_account_info(account_info_iter)?, expected_decimals))
        } else {
            None
        };

        let destination_account_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;

        let mut source_account = Account::unpack(&source_account_info.data.borrow())?;
        let mut destination_account = Account::unpack(&destination_account_info.data.borrow())?;

        if source_account.is_frozen() || destination_account.is_frozen() {
            return Err(TokenError::AccountFrozen.into());
        }
        if source_account.amount < amount {
            return Err(TokenError::InsufficientFunds.into());
        }
        if !Self::cmp_pubkeys(&source_account.mint, &destination_account.mint) {
            return Err(TokenError::MintMismatch.into());
        }

        if let Some((mint_info, expected_decimals)) = expected_mint_info {
            if !Self::cmp_pubkeys(mint_info.key, &source_account.mint) {
                return Err(TokenError::MintMismatch.into());
            }

            let mint = Mint::unpack(&mint_info.data.borrow_mut())?;
            if expected_decimals != mint.decimals {
                return Err(TokenError::MintDecimalsMismatch.into());
            }
        }

        let self_transfer =
            Self::cmp_pubkeys(source_account_info.key, destination_account_info.key);

        match source_account.delegate {
            COption::Some(ref delegate) if Self::cmp_pubkeys(authority_info.key, delegate) => {
                Self::validate_owner(
                    program_id,
                    delegate,
                    authority_info,
                    account_info_iter.as_slice(),
                )?;
                if source_account.delegated_amount < amount {
                    return Err(TokenError::InsufficientFunds.into());
                }
                if !self_transfer {
                    source_account.delegated_amount = source_account
                        .delegated_amount
                        .checked_sub(amount)
                        .ok_or(TokenError::Overflow)?;
                    if source_account.delegated_amount == 0 {
                        source_account.delegate = COption::None;
                    }
                }
            }
            _ => Self::validate_owner(
                program_id,
                &source_account.owner,
                authority_info,
                account_info_iter.as_slice(),
            )?,
        };

        if self_transfer || amount == 0 {
            Self::check_account_owner(program_id, source_account_info)?;
            Self::check_account_owner(program_id, destination_account_info)?;
        }

        // This check MUST occur just before the amounts are manipulated
        // to ensure self-transfers are fully validated
        if self_transfer {
            return Ok(());
        }

        source_account.amount = source_account
            .amount
            .checked_sub(amount)
            .ok_or(TokenError::Overflow)?;
        destination_account.amount = destination_account
            .amount
            .checked_add(amount)
            .ok_or(TokenError::Overflow)?;

        if source_account.is_native() {
            let source_starting_lamports = source_account_info.lamports();
            **source_account_info.lamports.borrow_mut() = source_starting_lamports
                .checked_sub(amount)
                .ok_or(TokenError::Overflow)?;

            let destination_starting_lamports = destination_account_info.lamports();
            **destination_account_info.lamports.borrow_mut() = destination_starting_lamports
                .checked_add(amount)
                .ok_or(TokenError::Overflow)?;
        }

        Account::pack(source_account, &mut source_account_info.data.borrow_mut())?;
        Account::pack(
            destination_account,
            &mut destination_account_info.data.borrow_mut(),
        )?;

        Ok(())
    }

    /// Processes an [`Approve`](enum.TokenInstruction.html) instruction.
    pub fn process_approve(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
        expected_decimals: Option<u8>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();

        let source_account_info = next_account_info(account_info_iter)?;

        let expected_mint_info = if let Some(expected_decimals) = expected_decimals {
            Some((next_account_info(account_info_iter)?, expected_decimals))
        } else {
            None
        };
        let delegate_info = next_account_info(account_info_iter)?;
        let owner_info = next_account_info(account_info_iter)?;

        let mut source_account = Account::unpack(&source_account_info.data.borrow())?;

        if source_account.is_frozen() {
            return Err(TokenError::AccountFrozen.into());
        }

        if let Some((mint_info, expected_decimals)) = expected_mint_info {
            if !Self::cmp_pubkeys(mint_info.key, &source_account.mint) {
                return Err(TokenError::MintMismatch.into());
            }

            let mint = Mint::unpack(&mint_info.data.borrow_mut())?;
            if expected_decimals != mint.decimals {
                return Err(TokenError::MintDecimalsMismatch.into());
            }
        }

        Self::validate_owner(
            program_id,
            &source_account.owner,
            owner_info,
            account_info_iter.as_slice(),
        )?;

        source_account.delegate = COption::Some(*delegate_info.key);
        source_account.delegated_amount = amount;

        Account::pack(source_account, &mut source_account_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes an [`Revoke`](enum.TokenInstruction.html) instruction.
    pub fn process_revoke(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let source_account_info = next_account_info(account_info_iter)?;

        let mut source_account = Account::unpack(&source_account_info.data.borrow())?;

        let owner_info = next_account_info(account_info_iter)?;

        if source_account.is_frozen() {
            return Err(TokenError::AccountFrozen.into());
        }

        Self::validate_owner(
            program_id,
            &source_account.owner,
            owner_info,
            account_info_iter.as_slice(),
        )?;

        source_account.delegate = COption::None;
        source_account.delegated_amount = 0;

        Account::pack(source_account, &mut source_account_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes a [`SetAuthority`](enum.TokenInstruction.html) instruction.
    pub fn process_set_authority(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        authority_type: AuthorityType,
        new_authority: COption<Pubkey>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let account_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;

        if account_info.data_len() == Account::get_packed_len() {
            let mut account = Account::unpack(&account_info.data.borrow())?;

            if account.is_frozen() {
                return Err(TokenError::AccountFrozen.into());
            }

            match authority_type {
                AuthorityType::AccountOwner => {
                    Self::validate_owner(
                        program_id,
                        &account.owner,
                        authority_info,
                        account_info_iter.as_slice(),
                    )?;

                    if let COption::Some(authority) = new_authority {
                        account.owner = authority;
                    } else {
                        return Err(TokenError::InvalidInstruction.into());
                    }

                    account.delegate = COption::None;
                    account.delegated_amount = 0;

                    if account.is_native() {
                        account.close_authority = COption::None;
                    }
                }
                AuthorityType::CloseAccount => {
                    let authority = account.close_authority.unwrap_or(account.owner);
                    Self::validate_owner(
                        program_id,
                        &authority,
                        authority_info,
                        account_info_iter.as_slice(),
                    )?;
                    account.close_authority = new_authority;
                }
                _ => {
                    return Err(TokenError::AuthorityTypeNotSupported.into());
                }
            }
            Account::pack(account, &mut account_info.data.borrow_mut())?;
        } else if account_info.data_len() == Mint::get_packed_len() {
            let mut mint = Mint::unpack(&account_info.data.borrow())?;
            match authority_type {
                AuthorityType::MintTokens => {
                    // Once a mint's supply is fixed, it cannot be undone by setting a new
                    // mint_authority
                    let mint_authority = mint
                        .mint_authority
                        .ok_or(Into::<ProgramError>::into(TokenError::FixedSupply))?;
                    Self::validate_owner(
                        program_id,
                        &mint_authority,
                        authority_info,
                        account_info_iter.as_slice(),
                    )?;
                    mint.mint_authority = new_authority;
                }
                AuthorityType::FreezeAccount => {
                    // Once a mint's freeze authority is disabled, it cannot be re-enabled by
                    // setting a new freeze_authority
                    let freeze_authority = mint
                        .freeze_authority
                        .ok_or(Into::<ProgramError>::into(TokenError::MintCannotFreeze))?;
                    Self::validate_owner(
                        program_id,
                        &freeze_authority,
                        authority_info,
                        account_info_iter.as_slice(),
                    )?;
                    mint.freeze_authority = new_authority;
                }
                _ => {
                    return Err(TokenError::AuthorityTypeNotSupported.into());
                }
            }
            Mint::pack(mint, &mut account_info.data.borrow_mut())?;
        } else {
            return Err(ProgramError::InvalidArgument);
        }

        Ok(())
    }

    /// Processes a [`MintTo`](enum.TokenInstruction.html) instruction.
    pub fn process_mint_to(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
        expected_decimals: Option<u8>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let mint_info = next_account_info(account_info_iter)?;
        let destination_account_info = next_account_info(account_info_iter)?;
        let owner_info = next_account_info(account_info_iter)?;

        let mut destination_account = Account::unpack(&destination_account_info.data.borrow())?;
        if destination_account.is_frozen() {
            return Err(TokenError::AccountFrozen.into());
        }

        if destination_account.is_native() {
            return Err(TokenError::NativeNotSupported.into());
        }
        if !Self::cmp_pubkeys(mint_info.key, &destination_account.mint) {
            return Err(TokenError::MintMismatch.into());
        }

        let mut mint = Mint::unpack(&mint_info.data.borrow())?;
        if let Some(expected_decimals) = expected_decimals {
            if expected_decimals != mint.decimals {
                return Err(TokenError::MintDecimalsMismatch.into());
            }
        }

        match mint.mint_authority {
            COption::Some(mint_authority) => Self::validate_owner(
                program_id,
                &mint_authority,
                owner_info,
                account_info_iter.as_slice(),
            )?,
            COption::None => return Err(TokenError::FixedSupply.into()),
        }

        if amount == 0 {
            Self::check_account_owner(program_id, mint_info)?;
            Self::check_account_owner(program_id, destination_account_info)?;
        }

        destination_account.amount = destination_account
            .amount
            .checked_add(amount)
            .ok_or(TokenError::Overflow)?;

        mint.supply = mint
            .supply
            .checked_add(amount)
            .ok_or(TokenError::Overflow)?;

        Account::pack(
            destination_account,
            &mut destination_account_info.data.borrow_mut(),
        )?;
        Mint::pack(mint, &mut mint_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes a [`Burn`](enum.TokenInstruction.html) instruction.
    pub fn process_burn(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
        expected_decimals: Option<u8>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();

        let source_account_info = next_account_info(account_info_iter)?;
        let mint_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;

        let mut source_account = Account::unpack(&source_account_info.data.borrow())?;
        let mut mint = Mint::unpack(&mint_info.data.borrow())?;

        if source_account.is_frozen() {
            return Err(TokenError::AccountFrozen.into());
        }
        if source_account.is_native() {
            return Err(TokenError::NativeNotSupported.into());
        }
        if source_account.amount < amount {
            return Err(TokenError::InsufficientFunds.into());
        }
        if !Self::cmp_pubkeys(mint_info.key, &source_account.mint) {
            return Err(TokenError::MintMismatch.into());
        }

        if let Some(expected_decimals) = expected_decimals {
            if expected_decimals != mint.decimals {
                return Err(TokenError::MintDecimalsMismatch.into());
            }
        }

        if !source_account.is_owned_by_system_program_or_incinerator() {
            match source_account.delegate {
                COption::Some(ref delegate) if Self::cmp_pubkeys(authority_info.key, delegate) => {
                    Self::validate_owner(
                        program_id,
                        delegate,
                        authority_info,
                        account_info_iter.as_slice(),
                    )?;

                    if source_account.delegated_amount < amount {
                        return Err(TokenError::InsufficientFunds.into());
                    }
                    source_account.delegated_amount = source_account
                        .delegated_amount
                        .checked_sub(amount)
                        .ok_or(TokenError::Overflow)?;
                    if source_account.delegated_amount == 0 {
                        source_account.delegate = COption::None;
                    }
                }
                _ => Self::validate_owner(
                    program_id,
                    &source_account.owner,
                    authority_info,
                    account_info_iter.as_slice(),
                )?,
            }
        }

        if amount == 0 {
            Self::check_account_owner(program_id, source_account_info)?;
            Self::check_account_owner(program_id, mint_info)?;
        }

        source_account.amount = source_account
            .amount
            .checked_sub(amount)
            .ok_or(TokenError::Overflow)?;
        mint.supply = mint
            .supply
            .checked_sub(amount)
            .ok_or(TokenError::Overflow)?;

        Account::pack(source_account, &mut source_account_info.data.borrow_mut())?;
        Mint::pack(mint, &mut mint_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes a [`CloseAccount`](enum.TokenInstruction.html) instruction.
    pub fn process_close_account(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let source_account_info = next_account_info(account_info_iter)?;
        let destination_account_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;

        if Self::cmp_pubkeys(source_account_info.key, destination_account_info.key) {
            return Err(ProgramError::InvalidAccountData);
        }

        let source_account = Account::unpack(&source_account_info.data.borrow())?;
        if !source_account.is_native() && source_account.amount != 0 {
            return Err(TokenError::NonNativeHasBalance.into());
        }

        let authority = source_account
            .close_authority
            .unwrap_or(source_account.owner);
        if !source_account.is_owned_by_system_program_or_incinerator() {
            Self::validate_owner(
                program_id,
                &authority,
                authority_info,
                account_info_iter.as_slice(),
            )?;
        } else if !solana_sdk_ids::incinerator::check_id(destination_account_info.key) {
            return Err(ProgramError::InvalidAccountData);
        }

        let destination_starting_lamports = destination_account_info.lamports();
        **destination_account_info.lamports.borrow_mut() = destination_starting_lamports
            .checked_add(source_account_info.lamports())
            .ok_or(TokenError::Overflow)?;

        **source_account_info.lamports.borrow_mut() = 0;
        delete_account(source_account_info)?;

        Ok(())
    }

    /// Processes a [`FreezeAccount`](enum.TokenInstruction.html) or a
    /// [`ThawAccount`](enum.TokenInstruction.html) instruction.
    pub fn process_toggle_freeze_account(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        freeze: bool,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let source_account_info = next_account_info(account_info_iter)?;
        let mint_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;

        let mut source_account = Account::unpack(&source_account_info.data.borrow())?;
        if freeze && source_account.is_frozen() || !freeze && !source_account.is_frozen() {
            return Err(TokenError::InvalidState.into());
        }
        if source_account.is_native() {
            return Err(TokenError::NativeNotSupported.into());
        }
        if !Self::cmp_pubkeys(mint_info.key, &source_account.mint) {
            return Err(TokenError::MintMismatch.into());
        }

        let mint = Mint::unpack(&mint_info.data.borrow_mut())?;
        match mint.freeze_authority {
            COption::Some(authority) => Self::validate_owner(
                program_id,
                &authority,
                authority_info,
                account_info_iter.as_slice(),
            ),
            COption::None => Err(TokenError::MintCannotFreeze.into()),
        }?;

        source_account.state = if freeze {
            AccountState::Frozen
        } else {
            AccountState::Initialized
        };

        Account::pack(source_account, &mut source_account_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes a [`SyncNative`](enum.TokenInstruction.html) instruction
    pub fn process_sync_native(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let native_account_info = next_account_info(account_info_iter)?;
        Self::check_account_owner(program_id, native_account_info)?;

        let mut native_account = Account::unpack(&native_account_info.data.borrow())?;

        if let COption::Some(rent_exempt_reserve) = native_account.is_native {
            let new_amount = native_account_info
                .lamports()
                .checked_sub(rent_exempt_reserve)
                .ok_or(TokenError::Overflow)?;
            if new_amount < native_account.amount {
                return Err(TokenError::InvalidState.into());
            }
            native_account.amount = new_amount;
        } else {
            return Err(TokenError::NonNativeNotSupported.into());
        }

        Account::pack(native_account, &mut native_account_info.data.borrow_mut())?;
        Ok(())
    }

    /// Processes a [`GetAccountDataSize`](enum.TokenInstruction.html)
    /// instruction
    pub fn process_get_account_data_size(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        // make sure the mint is valid
        let mint_info = next_account_info(account_info_iter)?;
        Self::check_account_owner(program_id, mint_info)?;
        let _ = Mint::unpack(&mint_info.data.borrow())
            .map_err(|_| Into::<ProgramError>::into(TokenError::InvalidMint))?;
        set_return_data(&Account::LEN.to_le_bytes());
        Ok(())
    }

    /// Processes an [`InitializeImmutableOwner`](enum.TokenInstruction.html)
    /// instruction
    pub fn process_initialize_immutable_owner(accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let token_account_info = next_account_info(account_info_iter)?;
        let account = Account::unpack_unchecked(&token_account_info.data.borrow())?;
        if account.is_initialized() {
            return Err(TokenError::AlreadyInUse.into());
        }
        msg!("Please upgrade to SPL Token 2022 for immutable owner support");
        Ok(())
    }

    /// Processes an [`AmountToUiAmount`](enum.TokenInstruction.html)
    /// instruction
    pub fn process_amount_to_ui_amount(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let mint_info = next_account_info(account_info_iter)?;
        Self::check_account_owner(program_id, mint_info)?;

        let mint = Mint::unpack(&mint_info.data.borrow_mut())
            .map_err(|_| Into::<ProgramError>::into(TokenError::InvalidMint))?;
        let ui_amount = amount_to_ui_amount_string_trimmed(amount, mint.decimals);

        set_return_data(&ui_amount.into_bytes());
        Ok(())
    }

    /// Processes an [`AmountToUiAmount`](enum.TokenInstruction.html)
    /// instruction
    pub fn process_ui_amount_to_amount(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        ui_amount: &str,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let mint_info = next_account_info(account_info_iter)?;
        Self::check_account_owner(program_id, mint_info)?;

        let mint = Mint::unpack(&mint_info.data.borrow_mut())
            .map_err(|_| Into::<ProgramError>::into(TokenError::InvalidMint))?;
        let amount = try_ui_amount_into_amount(ui_amount.to_string(), mint.decimals)?;

        set_return_data(&amount.to_le_bytes());
        Ok(())
    }

    /// Processes an [`Instruction`](enum.Instruction.html).
    pub fn process(program_id: &Pubkey, accounts: &[AccountInfo], input: &[u8]) -> ProgramResult {
        let instruction = TokenInstruction::unpack(input)?;

        match instruction {
            TokenInstruction::InitializeMint {
                decimals,
                mint_authority,
                freeze_authority,
            } => {
                msg!("Instruction: InitializeMint");
                Self::process_initialize_mint(accounts, decimals, mint_authority, freeze_authority)
            }
            TokenInstruction::InitializeMint2 {
                decimals,
                mint_authority,
                freeze_authority,
            } => {
                msg!("Instruction: InitializeMint2");
                Self::process_initialize_mint2(accounts, decimals, mint_authority, freeze_authority)
            }
            TokenInstruction::InitializeAccount => {
                msg!("Instruction: InitializeAccount");
                Self::process_initialize_account(program_id, accounts)
            }
            TokenInstruction::InitializeAccount2 { owner } => {
                msg!("Instruction: InitializeAccount2");
                Self::process_initialize_account2(program_id, accounts, owner)
            }
            TokenInstruction::InitializeAccount3 { owner } => {
                msg!("Instruction: InitializeAccount3");
                Self::process_initialize_account3(program_id, accounts, owner)
            }
            TokenInstruction::InitializeMultisig { m } => {
                msg!("Instruction: InitializeMultisig");
                Self::process_initialize_multisig(accounts, m)
            }
            TokenInstruction::InitializeMultisig2 { m } => {
                msg!("Instruction: InitializeMultisig2");
                Self::process_initialize_multisig2(accounts, m)
            }
            TokenInstruction::Transfer { amount } => {
                msg!("Instruction: Transfer");
                Self::process_transfer(program_id, accounts, amount, None)
            }
            TokenInstruction::Approve { amount } => {
                msg!("Instruction: Approve");
                Self::process_approve(program_id, accounts, amount, None)
            }
            TokenInstruction::Revoke => {
                msg!("Instruction: Revoke");
                Self::process_revoke(program_id, accounts)
            }
            TokenInstruction::SetAuthority {
                authority_type,
                new_authority,
            } => {
                msg!("Instruction: SetAuthority");
                Self::process_set_authority(program_id, accounts, authority_type, new_authority)
            }
            TokenInstruction::MintTo { amount } => {
                msg!("Instruction: MintTo");
                Self::process_mint_to(program_id, accounts, amount, None)
            }
            TokenInstruction::Burn { amount } => {
                msg!("Instruction: Burn");
                Self::process_burn(program_id, accounts, amount, None)
            }
            TokenInstruction::CloseAccount => {
                msg!("Instruction: CloseAccount");
                Self::process_close_account(program_id, accounts)
            }
            TokenInstruction::FreezeAccount => {
                msg!("Instruction: FreezeAccount");
                Self::process_toggle_freeze_account(program_id, accounts, true)
            }
            TokenInstruction::ThawAccount => {
                msg!("Instruction: ThawAccount");
                Self::process_toggle_freeze_account(program_id, accounts, false)
            }
            TokenInstruction::TransferChecked { amount, decimals } => {
                msg!("Instruction: TransferChecked");
                Self::process_transfer(program_id, accounts, amount, Some(decimals))
            }
            TokenInstruction::ApproveChecked { amount, decimals } => {
                msg!("Instruction: ApproveChecked");
                Self::process_approve(program_id, accounts, amount, Some(decimals))
            }
            TokenInstruction::MintToChecked { amount, decimals } => {
                msg!("Instruction: MintToChecked");
                Self::process_mint_to(program_id, accounts, amount, Some(decimals))
            }
            TokenInstruction::BurnChecked { amount, decimals } => {
                msg!("Instruction: BurnChecked");
                Self::process_burn(program_id, accounts, amount, Some(decimals))
            }
            TokenInstruction::SyncNative => {
                msg!("Instruction: SyncNative");
                Self::process_sync_native(program_id, accounts)
            }
            TokenInstruction::GetAccountDataSize => {
                msg!("Instruction: GetAccountDataSize");
                Self::process_get_account_data_size(program_id, accounts)
            }
            TokenInstruction::InitializeImmutableOwner => {
                msg!("Instruction: InitializeImmutableOwner");
                Self::process_initialize_immutable_owner(accounts)
            }
            TokenInstruction::AmountToUiAmount { amount } => {
                msg!("Instruction: AmountToUiAmount");
                Self::process_amount_to_ui_amount(program_id, accounts, amount)
            }
            TokenInstruction::UiAmountToAmount { ui_amount } => {
                msg!("Instruction: UiAmountToAmount");
                Self::process_ui_amount_to_amount(program_id, accounts, ui_amount)
            }
        }
    }

    /// Checks that the account is owned by the expected program
    pub fn check_account_owner(program_id: &Pubkey, account_info: &AccountInfo) -> ProgramResult {
        if !Self::cmp_pubkeys(program_id, account_info.owner) {
            Err(ProgramError::IncorrectProgramId)
        } else {
            Ok(())
        }
    }

    /// Checks two pubkeys for equality in a computationally cheap way using
    /// `sol_memcmp`
    pub fn cmp_pubkeys(a: &Pubkey, b: &Pubkey) -> bool {
        unsafe { sol_memcmp(a.as_ref(), b.as_ref(), PUBKEY_BYTES) == 0 }
    }

    /// Validates owner(s) are present
    pub fn validate_owner(
        program_id: &Pubkey,
        expected_owner: &Pubkey,
        owner_account_info: &AccountInfo,
        signers: &[AccountInfo],
    ) -> ProgramResult {
        if !Self::cmp_pubkeys(expected_owner, owner_account_info.key) {
            return Err(TokenError::OwnerMismatch.into());
        }
        if Self::cmp_pubkeys(program_id, owner_account_info.owner)
            && owner_account_info.data_len() == Multisig::get_packed_len()
        {
            let multisig = Multisig::unpack(&owner_account_info.data.borrow())?;
            let mut num_signers = 0;
            let mut matched = [false; MAX_SIGNERS];
            for signer in signers.iter() {
                for (position, key) in multisig.signers[0..multisig.n as usize].iter().enumerate() {
                    if Self::cmp_pubkeys(key, signer.key) && !matched[position] {
                        if !signer.is_signer {
                            return Err(ProgramError::MissingRequiredSignature);
                        }
                        matched[position] = true;
                        num_signers += 1;
                    }
                }
            }
            if num_signers < multisig.m {
                return Err(ProgramError::MissingRequiredSignature);
            }
            return Ok(());
        } else if !owner_account_info.is_signer {
            return Err(ProgramError::MissingRequiredSignature);
        }
        Ok(())
    }
}

/// Helper function to mostly delete an account in a test environment.  We could
/// potentially muck around the bytes assuming that a vec is passed in, but that
/// would be more trouble than it's worth.
#[cfg(not(target_os = "solana"))]
fn delete_account(account_info: &AccountInfo) -> Result<(), ProgramError> {
    account_info.assign(&system_program::id());
    let mut account_data = account_info.data.borrow_mut();
    let data_len = account_data.len();
    unsafe {
        solana_program_memory::sol_memset(*account_data, 0, data_len);
    }
    Ok(())
}

/// Helper function to totally delete an account on-chain
#[cfg(target_os = "solana")]
fn delete_account(account_info: &AccountInfo) -> Result<(), ProgramError> {
    account_info.assign(&system_program::id());
    account_info.resize(0)
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        std::sync::{Arc, RwLock},
    };

    lazy_static::lazy_static! {
        static ref EXPECTED_DATA: Arc<RwLock<Vec<u8>>> = Arc::new(RwLock::new(Vec::new()));
    }

    fn return_token_error_as_program_error() -> ProgramError {
        TokenError::MintMismatch.into()
    }

    #[test]
    fn test_print_error() {
        let error = return_token_error_as_program_error();
        error.to_str::<TokenError>();
    }

    #[test]
    fn test_error_as_custom() {
        assert_eq!(
            return_token_error_as_program_error(),
            ProgramError::Custom(3)
        );
    }

    #[test]
    fn test_unique_account_sizes() {
        assert_ne!(Mint::get_packed_len(), 0);
        assert_ne!(Mint::get_packed_len(), Account::get_packed_len());
        assert_ne!(Mint::get_packed_len(), Multisig::get_packed_len());
        assert_ne!(Account::get_packed_len(), 0);
        assert_ne!(Account::get_packed_len(), Multisig::get_packed_len());
        assert_ne!(Multisig::get_packed_len(), 0);
    }

    #[test]
    fn test_pack_unpack() {
        // Mint
        let check = Mint {
            mint_authority: COption::Some(Pubkey::new_from_array([1; 32])),
            supply: 42,
            decimals: 7,
            is_initialized: true,
            freeze_authority: COption::Some(Pubkey::new_from_array([2; 32])),
        };
        let mut packed = vec![0; Mint::get_packed_len() + 1];
        assert_eq!(
            Err(ProgramError::InvalidAccountData),
            Mint::pack(check, &mut packed)
        );
        let mut packed = vec![0; Mint::get_packed_len() - 1];
        assert_eq!(
            Err(ProgramError::InvalidAccountData),
            Mint::pack(check, &mut packed)
        );
        let mut packed = vec![0; Mint::get_packed_len()];
        Mint::pack(check, &mut packed).unwrap();
        let expect = vec![
            1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 42, 0, 0, 0, 0, 0, 0, 0, 7, 1, 1, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
        ];
        assert_eq!(packed, expect);
        let unpacked = Mint::unpack(&packed).unwrap();
        assert_eq!(unpacked, check);

        // Account
        let check = Account {
            mint: Pubkey::new_from_array([1; 32]),
            owner: Pubkey::new_from_array([2; 32]),
            amount: 3,
            delegate: COption::Some(Pubkey::new_from_array([4; 32])),
            state: AccountState::Frozen,
            is_native: COption::Some(5),
            delegated_amount: 6,
            close_authority: COption::Some(Pubkey::new_from_array([7; 32])),
        };
        let mut packed = vec![0; Account::get_packed_len() + 1];
        assert_eq!(
            Err(ProgramError::InvalidAccountData),
            Account::pack(check, &mut packed)
        );
        let mut packed = vec![0; Account::get_packed_len() - 1];
        assert_eq!(
            Err(ProgramError::InvalidAccountData),
            Account::pack(check, &mut packed)
        );
        let mut packed = vec![0; Account::get_packed_len()];
        Account::pack(check, &mut packed).unwrap();
        let expect = vec![
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 2, 2, 2, 2, 2, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
            4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 2, 1, 0, 0, 0, 5, 0, 0,
            0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
            7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
        ];
        assert_eq!(packed, expect);
        let unpacked = Account::unpack(&packed).unwrap();
        assert_eq!(unpacked, check);

        // Multisig
        let check = Multisig {
            m: 1,
            n: 2,
            is_initialized: true,
            signers: [Pubkey::new_from_array([3; 32]); MAX_SIGNERS],
        };
        let mut packed = vec![0; Multisig::get_packed_len() + 1];
        assert_eq!(
            Err(ProgramError::InvalidAccountData),
            Multisig::pack(check, &mut packed)
        );
        let mut packed = vec![0; Multisig::get_packed_len() - 1];
        assert_eq!(
            Err(ProgramError::InvalidAccountData),
            Multisig::pack(check, &mut packed)
        );
        let mut packed = vec![0; Multisig::get_packed_len()];
        Multisig::pack(check, &mut packed).unwrap();
        let expect = vec![
            1, 2, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3,
        ];
        assert_eq!(packed, expect);
        let unpacked = Multisig::unpack(&packed).unwrap();
        assert_eq!(unpacked, check);
    }

    #[test]
    fn test_validate_owner() {
        let program_id = crate::id();
        let owner_key = Pubkey::new_unique();
        let mut signer_keys = [Pubkey::default(); MAX_SIGNERS];
        for signer_key in signer_keys.iter_mut().take(MAX_SIGNERS) {
            *signer_key = Pubkey::new_unique();
        }
        let mut signer_lamports = 0;
        let mut signer_data = vec![];
        let mut signers = vec![
            AccountInfo::new(
                &owner_key,
                true,
                false,
                &mut signer_lamports,
                &mut signer_data,
                &program_id,
                false,
            );
            MAX_SIGNERS + 1
        ];
        for (signer, key) in signers.iter_mut().zip(&signer_keys) {
            signer.key = key;
        }
        let mut lamports = 0;
        let mut data = vec![0; Multisig::get_packed_len()];
        let mut multisig = Multisig::unpack_unchecked(&data).unwrap();
        multisig.m = MAX_SIGNERS as u8;
        multisig.n = MAX_SIGNERS as u8;
        multisig.signers = signer_keys;
        multisig.is_initialized = true;
        Multisig::pack(multisig, &mut data).unwrap();
        let owner_account_info = AccountInfo::new(
            &owner_key,
            false,
            false,
            &mut lamports,
            &mut data,
            &program_id,
            false,
        );

        // full 11 of 11
        Processor::validate_owner(&program_id, &owner_key, &owner_account_info, &signers).unwrap();

        // 1 of 11
        {
            let mut multisig =
                Multisig::unpack_unchecked(&owner_account_info.data.borrow()).unwrap();
            multisig.m = 1;
            Multisig::pack(multisig, &mut owner_account_info.data.borrow_mut()).unwrap();
        }
        Processor::validate_owner(&program_id, &owner_key, &owner_account_info, &signers).unwrap();

        // 2:1
        {
            let mut multisig =
                Multisig::unpack_unchecked(&owner_account_info.data.borrow()).unwrap();
            multisig.m = 2;
            multisig.n = 1;
            Multisig::pack(multisig, &mut owner_account_info.data.borrow_mut()).unwrap();
        }
        assert_eq!(
            Err(ProgramError::MissingRequiredSignature),
            Processor::validate_owner(&program_id, &owner_key, &owner_account_info, &signers)
        );

        // 0:11
        {
            let mut multisig =
                Multisig::unpack_unchecked(&owner_account_info.data.borrow()).unwrap();
            multisig.m = 0;
            multisig.n = 11;
            Multisig::pack(multisig, &mut owner_account_info.data.borrow_mut()).unwrap();
        }
        Processor::validate_owner(&program_id, &owner_key, &owner_account_info, &signers).unwrap();

        // 2:11 but 0 provided
        {
            let mut multisig =
                Multisig::unpack_unchecked(&owner_account_info.data.borrow()).unwrap();
            multisig.m = 2;
            multisig.n = 11;
            Multisig::pack(multisig, &mut owner_account_info.data.borrow_mut()).unwrap();
        }
        assert_eq!(
            Err(ProgramError::MissingRequiredSignature),
            Processor::validate_owner(&program_id, &owner_key, &owner_account_info, &[])
        );
        // 2:11 but 1 provided
        {
            let mut multisig =
                Multisig::unpack_unchecked(&owner_account_info.data.borrow()).unwrap();
            multisig.m = 2;
            multisig.n = 11;
            Multisig::pack(multisig, &mut owner_account_info.data.borrow_mut()).unwrap();
        }
        assert_eq!(
            Err(ProgramError::MissingRequiredSignature),
            Processor::validate_owner(&program_id, &owner_key, &owner_account_info, &signers[0..1])
        );

        // 2:11, 2 from middle provided
        {
            let mut multisig =
                Multisig::unpack_unchecked(&owner_account_info.data.borrow()).unwrap();
            multisig.m = 2;
            multisig.n = 11;
            Multisig::pack(multisig, &mut owner_account_info.data.borrow_mut()).unwrap();
        }
        Processor::validate_owner(&program_id, &owner_key, &owner_account_info, &signers[5..7])
            .unwrap();

        // 11:11, one is not a signer
        {
            let mut multisig =
                Multisig::unpack_unchecked(&owner_account_info.data.borrow()).unwrap();
            multisig.m = 11;
            multisig.n = 11;
            Multisig::pack(multisig, &mut owner_account_info.data.borrow_mut()).unwrap();
        }
        signers[5].is_signer = false;
        assert_eq!(
            Err(ProgramError::MissingRequiredSignature),
            Processor::validate_owner(&program_id, &owner_key, &owner_account_info, &signers)
        );
        signers[5].is_signer = true;

        // 11:11, single signer signs multiple times
        {
            let mut signer_lamports = 0;
            let mut signer_data = vec![];
            let signers = vec![
                AccountInfo::new(
                    &signer_keys[5],
                    true,
                    false,
                    &mut signer_lamports,
                    &mut signer_data,
                    &program_id,
                    false,
                );
                MAX_SIGNERS + 1
            ];
            let mut multisig =
                Multisig::unpack_unchecked(&owner_account_info.data.borrow()).unwrap();
            multisig.m = 11;
            multisig.n = 11;
            Multisig::pack(multisig, &mut owner_account_info.data.borrow_mut()).unwrap();
            assert_eq!(
                Err(ProgramError::MissingRequiredSignature),
                Processor::validate_owner(&program_id, &owner_key, &owner_account_info, &signers)
            );
        }
    }
}
