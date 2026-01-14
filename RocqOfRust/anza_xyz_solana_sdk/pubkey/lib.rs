//! Solana account addresses.
#![no_std]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![cfg_attr(feature = "frozen-abi", feature(min_specialization))]
#![allow(clippy::arithmetic_side_effects)]

// If target_os = "solana", then this panics so there are no dependencies.
// When target_os != "solana", this should be opt-in so users
// don't need the curve25519 dependency.
#[cfg(any(target_os = "solana", feature = "curve25519"))]
pub use solana_address::bytes_are_curve_point;
#[cfg(target_os = "solana")]
pub use solana_address::syscalls;
pub use solana_address::{
    address as pubkey,
    error::{AddressError as PubkeyError, ParseAddressError as ParsePubkeyError},
    Address as Pubkey, ADDRESS_BYTES as PUBKEY_BYTES, MAX_SEEDS, MAX_SEED_LEN,
};
#[cfg(all(feature = "rand", not(target_os = "solana")))]
pub use solana_address::{
    AddressHasher as PubkeyHasher, AddressHasherBuilder as PubkeyHasherBuilder,
};

/// New random `Pubkey` for tests and benchmarks.
#[cfg(all(feature = "rand", not(target_os = "solana")))]
pub fn new_rand() -> Pubkey {
    Pubkey::from(rand::random::<[u8; PUBKEY_BYTES]>())
}

/// Convenience macro to declare a static public key and functions to interact with it.
///
/// Input: a single literal base58 string representation of a program's ID.
///
/// # Example
///
/// ```
/// # // wrapper is used so that the macro invocation occurs in the item position
/// # // rather than in the statement position which isn't allowed.
/// use std::str::FromStr;
/// use solana_pubkey::{declare_id, Pubkey};
///
/// # mod item_wrapper {
/// #   use solana_pubkey::declare_id;
/// declare_id!("My11111111111111111111111111111111111111111");
/// # }
/// # use item_wrapper::id;
///
/// let my_id = Pubkey::from_str("My11111111111111111111111111111111111111111").unwrap();
/// assert_eq!(id(), my_id);
/// ```
#[macro_export]
macro_rules! declare_id {
    ($pubkey:expr) => {
        /// The const program ID.
        pub const ID: $crate::Pubkey = $crate::Pubkey::from_str_const($pubkey);

        /// Returns `true` if given pubkey is the program ID.
        // TODO make this const once `derive_const` makes it out of nightly
        // and we can `derive_const(PartialEq)` on `Pubkey`.
        pub fn check_id(id: &$crate::Pubkey) -> bool {
            id == &ID
        }

        /// Returns the program ID.
        pub const fn id() -> $crate::Pubkey {
            ID
        }

        #[cfg(test)]
        #[test]
        fn test_id() {
            assert!(check_id(&id()));
        }
    };
}

/// Same as [`declare_id`] except that it reports that this ID has been deprecated.
#[macro_export]
macro_rules! declare_deprecated_id {
    ($pubkey:expr) => {
        /// The const program ID.
        pub const ID: $crate::Pubkey = $crate::Pubkey::from_str_const($pubkey);

        /// Returns `true` if given pubkey is the program ID.
        // TODO make this const once `derive_const` makes it out of nightly
        // and we can `derive_const(PartialEq)` on `Pubkey`.
        #[deprecated()]
        pub fn check_id(id: &$crate::Pubkey) -> bool {
            id == &ID
        }

        /// Returns the program ID.
        #[deprecated()]
        pub const fn id() -> $crate::Pubkey {
            ID
        }

        #[cfg(test)]
        #[test]
        #[allow(deprecated)]
        fn test_id() {
            assert!(check_id(&id()));
        }
    };
}
