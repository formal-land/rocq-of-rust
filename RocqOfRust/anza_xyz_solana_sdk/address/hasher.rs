use {
    crate::ADDRESS_BYTES,
    core::{
        cell::Cell,
        hash::{BuildHasher, Hasher},
        mem,
    },
    rand::{thread_rng, Rng},
};

/// A faster, but less collision resistant hasher for addresses.
///
/// Specialized hasher that uses a random 8 bytes subslice of the
/// address as the hash value. Should not be used when collisions
/// might be used to mount DOS attacks.
///
/// Using this results in about 4x faster lookups in a typical hashmap.
#[derive(Default)]
pub struct AddressHasher {
    offset: usize,
    state: u64,
}

impl Hasher for AddressHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.state
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        debug_assert_eq!(
            bytes.len(),
            ADDRESS_BYTES,
            "This hasher is intended to be used with addresses and nothing else"
        );
        // This slice/unwrap can never panic since offset is < ADDRESS_BYTES - mem::size_of::<u64>()
        let chunk: &[u8; mem::size_of::<u64>()] = bytes
            [self.offset..self.offset + mem::size_of::<u64>()]
            .try_into()
            .unwrap();
        self.state = u64::from_ne_bytes(*chunk);
    }
}

/// A builder for faster, but less collision resistant hasher for addresses.
///
/// Initializes `AddressHasher` instances that use an 8-byte
/// slice of the address as the hash value. Should not be used when
/// collisions might be used to mount DOS attacks.
///
/// Using this results in about 4x faster lookups in a typical hashmap.
#[derive(Clone)]
pub struct AddressHasherBuilder {
    offset: usize,
}

impl Default for AddressHasherBuilder {
    /// Default construct the AddressHasherBuilder.
    ///
    /// The position of the slice is determined initially
    /// through random draw and then by incrementing a thread-local
    /// This way each hashmap can be expected to use a slightly different
    /// slice. This is essentially the same mechanism as what is used by
    /// `RandomState`
    fn default() -> Self {
        std::thread_local!(static OFFSET: Cell<usize>  = {
            let mut rng = thread_rng();
            Cell::new(rng.gen_range(0..ADDRESS_BYTES - mem::size_of::<u64>()))
        });

        let offset = OFFSET.with(|offset| {
            let mut next_offset = offset.get() + 1;
            if next_offset > ADDRESS_BYTES - mem::size_of::<u64>() {
                next_offset = 0;
            }
            offset.set(next_offset);
            next_offset
        });
        AddressHasherBuilder { offset }
    }
}

impl BuildHasher for AddressHasherBuilder {
    type Hasher = AddressHasher;
    #[inline]
    fn build_hasher(&self) -> Self::Hasher {
        AddressHasher {
            offset: self.offset,
            state: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::AddressHasherBuilder,
        crate::Address,
        core::hash::{BuildHasher, Hasher},
    };
    #[test]
    fn test_address_hasher_builder() {
        let key = Address::new_unique();
        let builder = AddressHasherBuilder::default();
        let mut hasher1 = builder.build_hasher();
        let mut hasher2 = builder.build_hasher();
        hasher1.write(key.as_array());
        hasher2.write(key.as_array());
        assert_eq!(
            hasher1.finish(),
            hasher2.finish(),
            "Hashers made with same builder should be identical"
        );
        // Make sure that when we make new builders we get different slices
        // chosen for hashing
        let builder2 = AddressHasherBuilder::default();
        for _ in 0..64 {
            let mut hasher3 = builder2.build_hasher();
            hasher3.write(key.as_array());
            std::dbg!(hasher1.finish());
            std::dbg!(hasher3.finish());
            if hasher1.finish() != hasher3.finish() {
                return;
            }
        }
        panic!("Hashers built with different builder should be different due to random offset");
    }

    #[test]
    fn test_address_hasher() {
        let key1 = Address::new_unique();
        let key2 = Address::new_unique();
        let builder = AddressHasherBuilder::default();
        let mut hasher1 = builder.build_hasher();
        let mut hasher2 = builder.build_hasher();
        hasher1.write(key1.as_array());
        hasher2.write(key2.as_array());
        assert_ne!(hasher1.finish(), hasher2.finish());
    }
}
