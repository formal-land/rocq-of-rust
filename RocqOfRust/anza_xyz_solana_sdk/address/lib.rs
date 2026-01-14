//! Address representation for Solana.
//!
//! An address is a sequence of 32 bytes, often shown as a base58 encoded string
//! (e.g. 14grJpemFaf88c8tiVb77W7TYg2W3ir6pfkKz3YjhhZ5).

#![no_std]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![cfg_attr(feature = "frozen-abi", feature(min_specialization))]
#![allow(clippy::arithmetic_side_effects)]

#[cfg(feature = "error")]
pub mod error;
#[cfg(feature = "rand")]
mod hasher;
#[cfg(any(feature = "curve25519", feature = "syscalls"))]
pub mod syscalls;

#[cfg(feature = "sha2")]
use crate::error::AddressError;
#[cfg(feature = "decode")]
use crate::error::ParseAddressError;
#[cfg(all(feature = "rand", not(target_os = "solana")))]
pub use crate::hasher::{AddressHasher, AddressHasherBuilder};

#[cfg(feature = "std")]
extern crate std;
#[cfg(feature = "dev-context-only-utils")]
use arbitrary::Arbitrary;
#[cfg(feature = "bytemuck")]
use bytemuck_derive::{Pod, Zeroable};
#[cfg(feature = "decode")]
use core::str::FromStr;
use core::{
    array,
    convert::TryFrom,
    hash::{Hash, Hasher},
};
#[cfg(feature = "serde")]
use serde_derive::{Deserialize, Serialize};
#[cfg(feature = "std")]
use std::vec::Vec;
#[cfg(feature = "borsh")]
use {
    borsh::{BorshDeserialize, BorshSchema, BorshSerialize},
    std::string::ToString,
};

/// Number of bytes in an address.
pub const ADDRESS_BYTES: usize = 32;
/// maximum length of derived `Address` seed
pub const MAX_SEED_LEN: usize = 32;
/// Maximum number of seeds
pub const MAX_SEEDS: usize = 16;
#[cfg(feature = "decode")]
/// Maximum string length of a base58 encoded address.
const MAX_BASE58_LEN: usize = 44;

#[cfg(feature = "sha2")]
const PDA_MARKER: &[u8; 21] = b"ProgramDerivedAddress";

/// The address of a [Solana account][acc].
///
/// Some account addresses are [ed25519] public keys, with corresponding secret
/// keys that are managed off-chain. Often, though, account addresses do not
/// have corresponding secret keys &mdash; as with [_program derived
/// addresses_][pdas] &mdash; or the secret key is not relevant to the operation
/// of a program, and may have even been disposed of. As running Solana programs
/// can not safely create or manage secret keys, the full [`Keypair`] is not
/// defined in `solana-program` but in `solana-sdk`.
///
/// [acc]: https://solana.com/docs/core/accounts
/// [ed25519]: https://ed25519.cr.yp.to/
/// [pdas]: https://solana.com/docs/core/cpi#program-derived-addresses
/// [`Keypair`]: https://docs.rs/solana-sdk/latest/solana_sdk/signer/keypair/struct.Keypair.html
#[repr(transparent)]
#[cfg_attr(feature = "frozen-abi", derive(solana_frozen_abi_macro::AbiExample))]
#[cfg_attr(
    feature = "borsh",
    derive(BorshSerialize, BorshDeserialize),
    borsh(crate = "borsh")
)]
#[cfg_attr(all(feature = "borsh", feature = "std"), derive(BorshSchema))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[cfg_attr(feature = "bytemuck", derive(Pod, Zeroable))]
#[derive(Clone, Copy, Default, Eq, Ord, PartialEq, PartialOrd)]
#[cfg_attr(feature = "dev-context-only-utils", derive(Arbitrary))]
pub struct Address(pub(crate) [u8; 32]);

#[cfg(feature = "sanitize")]
impl solana_sanitize::Sanitize for Address {}

#[cfg(feature = "decode")]
impl FromStr for Address {
    type Err = ParseAddressError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use five8::DecodeError;
        if s.len() > MAX_BASE58_LEN {
            return Err(ParseAddressError::WrongSize);
        }
        let mut bytes = [0; ADDRESS_BYTES];
        five8::decode_32(s, &mut bytes).map_err(|e| match e {
            DecodeError::InvalidChar(_) => ParseAddressError::Invalid,
            DecodeError::TooLong
            | DecodeError::TooShort
            | DecodeError::LargestTermTooHigh
            | DecodeError::OutputTooLong => ParseAddressError::WrongSize,
        })?;
        Ok(Address(bytes))
    }
}

/// Custom impl of Hash for Address.
///
/// This allows us to skip hashing the length of the address
/// which is always the same anyway.
impl Hash for Address {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write(self.as_array());
    }
}

impl From<&Address> for Address {
    #[inline]
    fn from(value: &Address) -> Self {
        *value
    }
}

impl From<[u8; 32]> for Address {
    #[inline]
    fn from(from: [u8; 32]) -> Self {
        Self(from)
    }
}

impl TryFrom<&[u8]> for Address {
    type Error = array::TryFromSliceError;

    #[inline]
    fn try_from(address: &[u8]) -> Result<Self, Self::Error> {
        <[u8; 32]>::try_from(address).map(Self::from)
    }
}

#[cfg(feature = "std")]
impl TryFrom<Vec<u8>> for Address {
    type Error = Vec<u8>;

    #[inline]
    fn try_from(address: Vec<u8>) -> Result<Self, Self::Error> {
        <[u8; 32]>::try_from(address).map(Self::from)
    }
}
#[cfg(feature = "decode")]
impl TryFrom<&str> for Address {
    type Error = ParseAddressError;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Address::from_str(s)
    }
}

// If target_os = "solana", then this panics so there are no dependencies.
// When target_os != "solana", this should be opt-in so users
// don't need the curve25519 dependency.
#[cfg(any(target_os = "solana", feature = "curve25519"))]
#[allow(clippy::used_underscore_binding)]
pub fn bytes_are_curve_point<T: AsRef<[u8]>>(_bytes: T) -> bool {
    #[cfg(not(target_os = "solana"))]
    {
        let Ok(compressed_edwards_y) =
            curve25519_dalek::edwards::CompressedEdwardsY::from_slice(_bytes.as_ref())
        else {
            return false;
        };
        compressed_edwards_y.decompress().is_some()
    }
    #[cfg(target_os = "solana")]
    unimplemented!();
}

impl Address {
    pub const fn new_from_array(address_array: [u8; 32]) -> Self {
        Self(address_array)
    }

    #[cfg(feature = "decode")]
    /// Decode a string into an `Address`, usable in a const context
    pub const fn from_str_const(s: &str) -> Self {
        let id_array = five8_const::decode_32_const(s);
        Address::new_from_array(id_array)
    }

    #[cfg(feature = "atomic")]
    /// Create an unique `Address` for tests and benchmarks.
    pub fn new_unique() -> Self {
        use solana_atomic_u64::AtomicU64;
        static I: AtomicU64 = AtomicU64::new(1);
        type T = u32;
        const COUNTER_BYTES: usize = core::mem::size_of::<T>();
        let mut b = [0u8; ADDRESS_BYTES];
        #[cfg(feature = "std")]
        let mut i = I.fetch_add(1) as T;
        #[cfg(not(feature = "std"))]
        let i = I.fetch_add(1) as T;
        // use big endian representation to ensure that recent unique addresses
        // are always greater than less recent unique addresses.
        b[0..COUNTER_BYTES].copy_from_slice(&i.to_be_bytes());
        // fill the rest of the address with pseudorandom numbers to make
        // data statistically similar to real addresses.
        #[cfg(feature = "std")]
        {
            let mut hash = std::hash::DefaultHasher::new();
            for slice in b[COUNTER_BYTES..].chunks_mut(COUNTER_BYTES) {
                hash.write_u32(i);
                i += 1;
                slice.copy_from_slice(&hash.finish().to_ne_bytes()[0..COUNTER_BYTES]);
            }
        }
        // if std is not available, just replicate last byte of the counter.
        // this is not as good as a proper hash, but at least it is uniform
        #[cfg(not(feature = "std"))]
        {
            for b in b[COUNTER_BYTES..].iter_mut() {
                *b = (i & 0xFF) as u8;
            }
        }
        Self::from(b)
    }

    // If target_os = "solana", then the solana_sha256_hasher crate will use
    // syscalls which bring no dependencies.
    // When target_os != "solana", this should be opt-in so users
    // don't need the sha2 dependency.
    #[cfg(feature = "sha2")]
    pub fn create_with_seed(
        base: &Address,
        seed: &str,
        owner: &Address,
    ) -> Result<Address, AddressError> {
        if seed.len() > MAX_SEED_LEN {
            return Err(AddressError::MaxSeedLengthExceeded);
        }

        let owner = owner.as_ref();
        if owner.len() >= PDA_MARKER.len() {
            let slice = &owner[owner.len() - PDA_MARKER.len()..];
            if slice == PDA_MARKER {
                return Err(AddressError::IllegalOwner);
            }
        }
        let hash = solana_sha256_hasher::hashv(&[base.as_ref(), seed.as_ref(), owner]);
        Ok(Address::from(hash.to_bytes()))
    }

    pub const fn to_bytes(self) -> [u8; 32] {
        self.0
    }

    /// Return a reference to the `Address`'s byte array.
    #[inline(always)]
    pub const fn as_array(&self) -> &[u8; 32] {
        &self.0
    }

    // If target_os = "solana", then this panics so there are no dependencies.
    // When target_os != "solana", this should be opt-in so users
    // don't need the curve25519 dependency.
    #[cfg(any(target_os = "solana", feature = "curve25519"))]
    pub fn is_on_curve(&self) -> bool {
        bytes_are_curve_point(self)
    }
}

impl AsRef<[u8]> for Address {
    fn as_ref(&self) -> &[u8] {
        &self.0[..]
    }
}

impl AsMut<[u8]> for Address {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0[..]
    }
}

#[cfg(feature = "decode")]
fn write_as_base58(f: &mut core::fmt::Formatter, p: &Address) -> core::fmt::Result {
    let mut out = [0u8; MAX_BASE58_LEN];
    let len = five8::encode_32(&p.0, &mut out) as usize;
    // any sequence of base58 chars is valid utf8
    let as_str = unsafe { core::str::from_utf8_unchecked(&out[..len]) };
    f.write_str(as_str)
}

#[cfg(feature = "decode")]
impl core::fmt::Debug for Address {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write_as_base58(f, self)
    }
}

#[cfg(feature = "decode")]
impl core::fmt::Display for Address {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write_as_base58(f, self)
    }
}

/// Convenience macro to define a static `Address` value.
///
/// Input: a single literal base58 string representation of an `Address`.
///
/// # Example
///
/// ```
/// use std::str::FromStr;
/// use solana_address::{address, Address};
///
/// static ID: Address = address!("My11111111111111111111111111111111111111111");
///
/// let my_id = Address::from_str("My11111111111111111111111111111111111111111").unwrap();
/// assert_eq!(ID, my_id);
/// ```
#[macro_export]
macro_rules! address {
    ($input:literal) => {
        $crate::Address::from_str_const($input)
    };
}

#[cfg(test)]
mod tests {
    use {super::*, core::str::from_utf8, std::string::String};

    fn encode_address(address: &[u8; 32]) -> String {
        let mut buffer = [0u8; 44];
        let count = five8::encode_32(address, &mut buffer);
        from_utf8(&buffer[..count as usize]).unwrap().to_string()
    }

    #[test]
    fn test_new_unique() {
        assert!(Address::new_unique() != Address::new_unique());
    }

    #[test]
    fn address_fromstr() {
        let address = Address::new_unique();
        let mut address_base58_str = encode_address(&address.0);

        assert_eq!(address_base58_str.parse::<Address>(), Ok(address));

        address_base58_str.push_str(&encode_address(&address.0));
        assert_eq!(
            address_base58_str.parse::<Address>(),
            Err(ParseAddressError::WrongSize)
        );

        address_base58_str.truncate(address_base58_str.len() / 2);
        assert_eq!(address_base58_str.parse::<Address>(), Ok(address));

        address_base58_str.truncate(address_base58_str.len() / 2);
        assert_eq!(
            address_base58_str.parse::<Address>(),
            Err(ParseAddressError::WrongSize)
        );

        let mut address_base58_str = encode_address(&address.0);
        assert_eq!(address_base58_str.parse::<Address>(), Ok(address));

        // throw some non-base58 stuff in there
        address_base58_str.replace_range(..1, "I");
        assert_eq!(
            address_base58_str.parse::<Address>(),
            Err(ParseAddressError::Invalid)
        );

        // too long input string
        // longest valid encoding
        let mut too_long = encode_address(&[255u8; ADDRESS_BYTES]);
        // and one to grow on
        too_long.push('1');
        assert_eq!(
            too_long.parse::<Address>(),
            Err(ParseAddressError::WrongSize)
        );
    }

    #[test]
    fn test_create_with_seed() {
        assert!(
            Address::create_with_seed(&Address::new_unique(), "☉", &Address::new_unique()).is_ok()
        );
        assert_eq!(
            Address::create_with_seed(
                &Address::new_unique(),
                from_utf8(&[127; MAX_SEED_LEN + 1]).unwrap(),
                &Address::new_unique()
            ),
            Err(AddressError::MaxSeedLengthExceeded)
        );
        assert!(Address::create_with_seed(
            &Address::new_unique(),
            "\
             \u{10FFFF}\u{10FFFF}\u{10FFFF}\u{10FFFF}\u{10FFFF}\u{10FFFF}\u{10FFFF}\u{10FFFF}\
             ",
            &Address::new_unique()
        )
        .is_ok());
        // utf-8 abuse ;)
        assert_eq!(
            Address::create_with_seed(
                &Address::new_unique(),
                "\
                 x\u{10FFFF}\u{10FFFF}\u{10FFFF}\u{10FFFF}\u{10FFFF}\u{10FFFF}\u{10FFFF}\u{10FFFF}\
                 ",
                &Address::new_unique()
            ),
            Err(AddressError::MaxSeedLengthExceeded)
        );

        assert!(Address::create_with_seed(
            &Address::new_unique(),
            from_utf8(&[0; MAX_SEED_LEN]).unwrap(),
            &Address::new_unique(),
        )
        .is_ok());

        assert!(
            Address::create_with_seed(&Address::new_unique(), "", &Address::new_unique(),).is_ok()
        );

        assert_eq!(
            Address::create_with_seed(
                &Address::default(),
                "limber chicken: 4/45",
                &Address::default(),
            ),
            Ok("9h1HyLCW5dZnBVap8C5egQ9Z6pHyjsh5MNy83iPqqRuq"
                .parse()
                .unwrap())
        );
    }

    #[test]
    fn test_create_program_address() {
        let exceeded_seed = &[127; MAX_SEED_LEN + 1];
        let max_seed = &[0; MAX_SEED_LEN];
        let exceeded_seeds: &[&[u8]] = &[
            &[1],
            &[2],
            &[3],
            &[4],
            &[5],
            &[6],
            &[7],
            &[8],
            &[9],
            &[10],
            &[11],
            &[12],
            &[13],
            &[14],
            &[15],
            &[16],
            &[17],
        ];
        let max_seeds: &[&[u8]] = &[
            &[1],
            &[2],
            &[3],
            &[4],
            &[5],
            &[6],
            &[7],
            &[8],
            &[9],
            &[10],
            &[11],
            &[12],
            &[13],
            &[14],
            &[15],
            &[16],
        ];
        let program_id = Address::from_str("BPFLoaderUpgradeab1e11111111111111111111111").unwrap();
        let public_key = Address::from_str("SeedPubey1111111111111111111111111111111111").unwrap();

        assert_eq!(
            Address::create_program_address(&[exceeded_seed], &program_id),
            Err(AddressError::MaxSeedLengthExceeded)
        );
        assert_eq!(
            Address::create_program_address(&[b"short_seed", exceeded_seed], &program_id),
            Err(AddressError::MaxSeedLengthExceeded)
        );
        assert!(Address::create_program_address(&[max_seed], &program_id).is_ok());
        assert_eq!(
            Address::create_program_address(exceeded_seeds, &program_id),
            Err(AddressError::MaxSeedLengthExceeded)
        );
        assert!(Address::create_program_address(max_seeds, &program_id).is_ok());
        assert_eq!(
            Address::create_program_address(&[b"", &[1]], &program_id),
            Ok("BwqrghZA2htAcqq8dzP1WDAhTXYTYWj7CHxF5j7TDBAe"
                .parse()
                .unwrap())
        );
        assert_eq!(
            Address::create_program_address(&["☉".as_ref(), &[0]], &program_id),
            Ok("13yWmRpaTR4r5nAktwLqMpRNr28tnVUZw26rTvPSSB19"
                .parse()
                .unwrap())
        );
        assert_eq!(
            Address::create_program_address(&[b"Talking", b"Squirrels"], &program_id),
            Ok("2fnQrngrQT4SeLcdToJAD96phoEjNL2man2kfRLCASVk"
                .parse()
                .unwrap())
        );
        assert_eq!(
            Address::create_program_address(&[public_key.as_ref(), &[1]], &program_id),
            Ok("976ymqVnfE32QFe6NfGDctSvVa36LWnvYxhU6G2232YL"
                .parse()
                .unwrap())
        );
        assert_ne!(
            Address::create_program_address(&[b"Talking", b"Squirrels"], &program_id).unwrap(),
            Address::create_program_address(&[b"Talking"], &program_id).unwrap(),
        );
    }

    #[test]
    fn test_address_off_curve() {
        // try a bunch of random input, all successful generated program
        // addresses must land off the curve and be unique
        let mut addresses = std::vec![];
        for _ in 0..1_000 {
            let program_id = Address::new_unique();
            let bytes1 = rand::random::<[u8; 10]>();
            let bytes2 = rand::random::<[u8; 32]>();
            if let Ok(program_address) =
                Address::create_program_address(&[&bytes1, &bytes2], &program_id)
            {
                assert!(!program_address.is_on_curve());
                assert!(!addresses.contains(&program_address));
                addresses.push(program_address);
            }
        }
    }

    #[test]
    fn test_find_program_address() {
        for _ in 0..1_000 {
            let program_id = Address::new_unique();
            let (address, bump_seed) =
                Address::find_program_address(&[b"Lil'", b"Bits"], &program_id);
            assert_eq!(
                address,
                Address::create_program_address(&[b"Lil'", b"Bits", &[bump_seed]], &program_id)
                    .unwrap()
            );
        }
    }

    fn address_from_seed_by_marker(marker: &[u8]) -> Result<Address, AddressError> {
        let key = Address::new_unique();
        let owner = Address::default();

        let mut to_fake = owner.to_bytes().to_vec();
        to_fake.extend_from_slice(marker);

        let seed = from_utf8(&to_fake[..to_fake.len() - 32]).expect("not utf8");
        let base = &Address::try_from(&to_fake[to_fake.len() - 32..]).unwrap();

        Address::create_with_seed(&key, seed, base)
    }

    #[test]
    fn test_create_with_seed_rejects_illegal_owner() {
        assert_eq!(
            address_from_seed_by_marker(PDA_MARKER),
            Err(AddressError::IllegalOwner)
        );
        assert!(address_from_seed_by_marker(&PDA_MARKER[1..]).is_ok());
    }

    #[test]
    fn test_as_array() {
        let bytes = [1u8; 32];
        let key = Address::from(bytes);
        assert_eq!(key.as_array(), &bytes);
        assert_eq!(key.as_array(), &key.to_bytes());
        // Sanity check: ensure the pointer is the same.
        assert_eq!(key.as_array().as_ptr(), key.0.as_ptr());
    }

    #[test]
    fn test_address_macro() {
        const ADDRESS: Address =
            Address::from_str_const("9h1HyLCW5dZnBVap8C5egQ9Z6pHyjsh5MNy83iPqqRuq");
        assert_eq!(
            address!("9h1HyLCW5dZnBVap8C5egQ9Z6pHyjsh5MNy83iPqqRuq"),
            ADDRESS
        );
        assert_eq!(
            Address::from_str("9h1HyLCW5dZnBVap8C5egQ9Z6pHyjsh5MNy83iPqqRuq").unwrap(),
            ADDRESS
        );
    }
}
