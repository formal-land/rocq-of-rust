#![allow(clippy::arithmetic_side_effects)]
#![deny(missing_docs)]
#![cfg_attr(not(test), warn(unsafe_code))]

//! An ERC20-like Token program for the Solana blockchain

use {
    solana_program_error::{ProgramError, ProgramResult},
    solana_pubkey::Pubkey,
};

pub mod error;
pub mod instruction;
pub mod native_mint;
pub mod state;

solana_pubkey::declare_id!("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA");

/// Checks that the supplied program ID is the correct one for SPL-token
pub fn check_program_account(spl_token_program_id: &Pubkey) -> ProgramResult {
    if spl_token_program_id != &id() {
        return Err(ProgramError::IncorrectProgramId);
    }
    Ok(())
}
