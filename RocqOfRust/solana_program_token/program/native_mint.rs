//! The Mint that represents the native token
#![deprecated(
    since = "8.1.0",
    note = "Use spl_token_interface::native_mint instead and remove spl_token as a dependency"
)]
pub use spl_token_interface::native_mint::*;
