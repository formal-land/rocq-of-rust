//! Error types

use {
    num_derive::FromPrimitive,
    solana_program_error::{ProgramError, ToStr},
    thiserror::Error,
};

/// Errors that may be returned by the Token program.
#[cfg_attr(test, derive(strum_macros::FromRepr, strum_macros::EnumIter))]
#[derive(Clone, Debug, Eq, Error, FromPrimitive, PartialEq)]
pub enum TokenError {
    // 0
    /// Lamport balance below rent-exempt threshold.
    #[error("Lamport balance below rent-exempt threshold")]
    NotRentExempt,
    /// Insufficient funds for the operation requested.
    #[error("Insufficient funds")]
    InsufficientFunds,
    /// Invalid Mint.
    #[error("Invalid Mint")]
    InvalidMint,
    /// Account not associated with this Mint.
    #[error("Account not associated with this Mint")]
    MintMismatch,
    /// Owner does not match.
    #[error("Owner does not match")]
    OwnerMismatch,

    // 5
    /// This token's supply is fixed and new tokens cannot be minted.
    #[error("Fixed supply")]
    FixedSupply,
    /// The account cannot be initialized because it is already being used.
    #[error("Already in use")]
    AlreadyInUse,
    /// Invalid number of provided signers.
    #[error("Invalid number of provided signers")]
    InvalidNumberOfProvidedSigners,
    /// Invalid number of required signers.
    #[error("Invalid number of required signers")]
    InvalidNumberOfRequiredSigners,
    /// State is uninitialized.
    #[error("State is uninitialized")]
    UninitializedState,

    // 10
    /// Instruction does not support native tokens
    #[error("Instruction does not support native tokens")]
    NativeNotSupported,
    /// Non-native account can only be closed if its balance is zero
    #[error("Non-native account can only be closed if its balance is zero")]
    NonNativeHasBalance,
    /// Invalid instruction
    #[error("Invalid instruction")]
    InvalidInstruction,
    /// State is invalid for requested operation.
    #[error("State is invalid for requested operation")]
    InvalidState,
    /// Operation overflowed
    #[error("Operation overflowed")]
    Overflow,

    // 15
    /// Account does not support specified authority type.
    #[error("Account does not support specified authority type")]
    AuthorityTypeNotSupported,
    /// This token mint cannot freeze accounts.
    #[error("This token mint cannot freeze accounts")]
    MintCannotFreeze,
    /// Account is frozen; all account operations will fail
    #[error("Account is frozen")]
    AccountFrozen,
    /// Mint decimals mismatch between the client and mint
    #[error("The provided decimals value different from the Mint decimals")]
    MintDecimalsMismatch,
    /// Instruction does not support non-native tokens
    #[error("Instruction does not support non-native tokens")]
    NonNativeNotSupported,
}
impl From<TokenError> for ProgramError {
    fn from(e: TokenError) -> Self {
        ProgramError::Custom(e as u32)
    }
}

impl TryFrom<u32> for TokenError {
    type Error = ProgramError;
    fn try_from(error: u32) -> Result<Self, Self::Error> {
        match error {
            0 => Ok(TokenError::NotRentExempt),
            1 => Ok(TokenError::InsufficientFunds),
            2 => Ok(TokenError::InvalidMint),
            3 => Ok(TokenError::MintMismatch),
            4 => Ok(TokenError::OwnerMismatch),
            5 => Ok(TokenError::FixedSupply),
            6 => Ok(TokenError::AlreadyInUse),
            7 => Ok(TokenError::InvalidNumberOfProvidedSigners),
            8 => Ok(TokenError::InvalidNumberOfRequiredSigners),
            9 => Ok(TokenError::UninitializedState),
            10 => Ok(TokenError::NativeNotSupported),
            11 => Ok(TokenError::NonNativeHasBalance),
            12 => Ok(TokenError::InvalidInstruction),
            13 => Ok(TokenError::InvalidState),
            14 => Ok(TokenError::Overflow),
            15 => Ok(TokenError::AuthorityTypeNotSupported),
            16 => Ok(TokenError::MintCannotFreeze),
            17 => Ok(TokenError::AccountFrozen),
            18 => Ok(TokenError::MintDecimalsMismatch),
            19 => Ok(TokenError::NonNativeNotSupported),
            _ => Err(ProgramError::InvalidArgument),
        }
    }
}

impl ToStr for TokenError {
    fn to_str(&self) -> &'static str {
        match self {
            TokenError::NotRentExempt => "Error: Lamport balance below rent-exempt threshold",
            TokenError::InsufficientFunds => "Error: insufficient funds",
            TokenError::InvalidMint => "Error: Invalid Mint",
            TokenError::MintMismatch => "Error: Account not associated with this Mint",
            TokenError::OwnerMismatch => "Error: owner does not match",
            TokenError::FixedSupply => "Error: the total supply of this token is fixed",
            TokenError::AlreadyInUse => "Error: account or token already in use",
            TokenError::InvalidNumberOfProvidedSigners => {
                "Error: Invalid number of provided signers"
            }
            TokenError::InvalidNumberOfRequiredSigners => {
                "Error: Invalid number of required signers"
            }
            TokenError::UninitializedState => "Error: State is uninitialized",
            TokenError::NativeNotSupported => "Error: Instruction does not support native tokens",
            TokenError::NonNativeHasBalance => {
                "Error: Non-native account can only be closed if its balance is zero"
            }
            TokenError::InvalidInstruction => "Error: Invalid instruction",
            TokenError::InvalidState => "Error: Invalid account state for operation",
            TokenError::Overflow => "Error: Operation overflowed",
            TokenError::AuthorityTypeNotSupported => {
                "Error: Account does not support specified authority type"
            }
            TokenError::MintCannotFreeze => "Error: This token mint cannot freeze accounts",
            TokenError::AccountFrozen => "Error: Account is frozen",
            TokenError::MintDecimalsMismatch => "Error: decimals different from the Mint decimals",
            TokenError::NonNativeNotSupported => {
                "Error: Instruction does not support non-native tokens"
            }
        }
    }
}

#[cfg(test)]
mod test {
    use {super::*, strum::IntoEnumIterator};
    #[test]
    fn test_parse_error_from_primitive_exhaustive() {
        for variant in TokenError::iter() {
            let variant_u32 = variant as u32;
            assert_eq!(
                TokenError::from_repr(variant_u32 as usize).unwrap(),
                TokenError::try_from(variant_u32).unwrap()
            );
        }
    }
}
