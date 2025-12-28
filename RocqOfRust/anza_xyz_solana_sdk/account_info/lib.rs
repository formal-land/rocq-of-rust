//! Account information.
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
use {
    solana_program_error::ProgramError,
    solana_program_memory::sol_memset,
    solana_pubkey::Pubkey,
    std::{
        cell::{Ref, RefCell, RefMut},
        fmt,
        rc::Rc,
        slice::from_raw_parts_mut,
    },
};
pub mod debug_account_data;

/// Maximum number of bytes a program may add to an account during a single realloc
pub const MAX_PERMITTED_DATA_INCREASE: usize = 1_024 * 10;

/// Account information
#[derive(Clone)]
#[repr(C)]
pub struct AccountInfo<'a> {
    /// Public key of the account
    pub key: &'a Pubkey,
    /// The lamports in the account.  Modifiable by programs.
    pub lamports: Rc<RefCell<&'a mut u64>>,
    /// The data held in this account.  Modifiable by programs.
    pub data: Rc<RefCell<&'a mut [u8]>>,
    /// Program that owns this account
    pub owner: &'a Pubkey,
    /// Formerly, the epoch at which this account will next owe rent. A field
    /// must remain because the runtime depends on the exact layout of this
    /// struct.
    #[deprecated(
        since = "3.0.0",
        note = "Do not use this field, it will not exist in ABIv2"
    )]
    pub _unused: u64,
    /// Was the transaction signed by this account's public key?
    pub is_signer: bool,
    /// Is the account writable?
    pub is_writable: bool,
    /// This account's data contains a loaded program (and is now read-only)
    pub executable: bool,
}

impl fmt::Debug for AccountInfo<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_struct("AccountInfo");

        f.field("key", &self.key)
            .field("owner", &self.owner)
            .field("is_signer", &self.is_signer)
            .field("is_writable", &self.is_writable)
            .field("executable", &self.executable)
            .field("lamports", &self.lamports())
            .field("data.len", &self.data_len());
        debug_account_data::debug_account_data(&self.data.borrow(), &mut f);

        f.finish_non_exhaustive()
    }
}

impl<'a> AccountInfo<'a> {
    pub fn signer_key(&self) -> Option<&Pubkey> {
        if self.is_signer {
            Some(self.key)
        } else {
            None
        }
    }

    pub fn unsigned_key(&self) -> &Pubkey {
        self.key
    }

    pub fn lamports(&self) -> u64 {
        **self.lamports.borrow()
    }

    pub fn try_lamports(&self) -> Result<u64, ProgramError> {
        Ok(**self.try_borrow_lamports()?)
    }

    /// Return the account's original data length when it was serialized for the
    /// current program invocation.
    ///
    /// # Safety
    ///
    /// This method assumes that the original data length was serialized as a u32
    /// integer in the 4 bytes immediately preceding the serialized account key.
    pub unsafe fn original_data_len(&self) -> usize {
        let key_ptr = self.key as *const _ as *const u8;
        let original_data_len_ptr = key_ptr.offset(-4) as *const u32;
        *original_data_len_ptr as usize
    }

    pub fn data_len(&self) -> usize {
        self.data.borrow().len()
    }

    pub fn try_data_len(&self) -> Result<usize, ProgramError> {
        Ok(self.try_borrow_data()?.len())
    }

    pub fn data_is_empty(&self) -> bool {
        self.data.borrow().is_empty()
    }

    pub fn try_data_is_empty(&self) -> Result<bool, ProgramError> {
        Ok(self.try_borrow_data()?.is_empty())
    }

    pub fn try_borrow_lamports(&self) -> Result<Ref<'_, &mut u64>, ProgramError> {
        self.lamports
            .try_borrow()
            .map_err(|_| ProgramError::AccountBorrowFailed)
    }

    pub fn try_borrow_mut_lamports(&self) -> Result<RefMut<'_, &'a mut u64>, ProgramError> {
        self.lamports
            .try_borrow_mut()
            .map_err(|_| ProgramError::AccountBorrowFailed)
    }

    pub fn try_borrow_data(&self) -> Result<Ref<'_, &mut [u8]>, ProgramError> {
        self.data
            .try_borrow()
            .map_err(|_| ProgramError::AccountBorrowFailed)
    }

    pub fn try_borrow_mut_data(&self) -> Result<RefMut<'_, &'a mut [u8]>, ProgramError> {
        self.data
            .try_borrow_mut()
            .map_err(|_| ProgramError::AccountBorrowFailed)
    }

    /// Resize the account's data: Either truncating or zero extending.
    ///
    /// Note:  Account data can be increased within a single call by up to
    /// `solana_program::entrypoint::MAX_PERMITTED_DATA_INCREASE` bytes.
    ///
    /// # Safety
    ///
    /// This method makes assumptions about the layout and location of memory
    /// referenced by `AccountInfo` fields. It should only be called for
    /// instances of `AccountInfo` that were created by the runtime and received
    /// in the `process_instruction` entrypoint of a program.
    pub fn resize(&self, new_len: usize) -> Result<(), ProgramError> {
        let mut data = self.try_borrow_mut_data()?;
        let old_len = data.len();

        // Return early if length hasn't changed
        if new_len == old_len {
            return Ok(());
        }

        // Return early if the length increase from the original serialized data
        // length is too large and would result in an out of bounds allocation.
        let original_data_len = unsafe { self.original_data_len() };
        if new_len.saturating_sub(original_data_len) > MAX_PERMITTED_DATA_INCREASE {
            return Err(ProgramError::InvalidRealloc);
        }

        // realloc
        unsafe {
            let data_ptr = data.as_mut_ptr();

            // First set new length in the serialized data
            *(data_ptr.offset(-8) as *mut u64) = new_len as u64;

            // Then recreate the local slice with the new length
            *data = from_raw_parts_mut(data_ptr, new_len)
        }

        let len_increase = new_len.saturating_sub(old_len);
        if len_increase > 0 {
            unsafe { sol_memset(&mut data[old_len..], 0, len_increase) };
        }

        Ok(())
    }

    #[allow(invalid_reference_casting)]
    pub fn assign(&self, new_owner: &Pubkey) {
        // Set the non-mut owner field
        unsafe {
            std::ptr::write_volatile(
                self.owner as *const Pubkey as *mut [u8; 32],
                new_owner.to_bytes(),
            );
        }
    }

    pub fn new(
        key: &'a Pubkey,
        is_signer: bool,
        is_writable: bool,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        owner: &'a Pubkey,
        executable: bool,
    ) -> Self {
        #[allow(deprecated)]
        Self {
            key,
            is_signer,
            is_writable,
            lamports: Rc::new(RefCell::new(lamports)),
            data: Rc::new(RefCell::new(data)),
            owner,
            executable,
            _unused: 0,
        }
    }

    #[cfg(feature = "bincode")]
    pub fn deserialize_data<T: serde::de::DeserializeOwned>(&self) -> Result<T, bincode::Error> {
        bincode::deserialize(&self.data.borrow())
    }

    #[cfg(feature = "bincode")]
    pub fn serialize_data<T: serde::Serialize>(&self, state: &T) -> Result<(), bincode::Error> {
        if bincode::serialized_size(state)? > self.data_len() as u64 {
            return Err(Box::new(bincode::ErrorKind::SizeLimit));
        }
        bincode::serialize_into(&mut self.data.borrow_mut()[..], state)
    }
}

/// Constructs an `AccountInfo` from self, used in conversion implementations.
pub trait IntoAccountInfo<'a> {
    fn into_account_info(self) -> AccountInfo<'a>;
}
impl<'a, T: IntoAccountInfo<'a>> From<T> for AccountInfo<'a> {
    fn from(src: T) -> Self {
        src.into_account_info()
    }
}

/// Provides information required to construct an `AccountInfo`, used in
/// conversion implementations.
pub trait Account {
    fn get(&mut self) -> (&mut u64, &mut [u8], &Pubkey, bool);
}

/// Convert (&'a Pubkey, &'a mut T) where T: Account into an `AccountInfo`
impl<'a, T: Account> IntoAccountInfo<'a> for (&'a Pubkey, &'a mut T) {
    fn into_account_info(self) -> AccountInfo<'a> {
        let (key, account) = self;
        let (lamports, data, owner, executable) = account.get();
        AccountInfo::new(key, false, false, lamports, data, owner, executable)
    }
}

/// Convert (&'a Pubkey, bool, &'a mut T)  where T: Account into an
/// `AccountInfo`.
impl<'a, T: Account> IntoAccountInfo<'a> for (&'a Pubkey, bool, &'a mut T) {
    fn into_account_info(self) -> AccountInfo<'a> {
        let (key, is_signer, account) = self;
        let (lamports, data, owner, executable) = account.get();
        AccountInfo::new(key, is_signer, false, lamports, data, owner, executable)
    }
}

/// Convert &'a mut (Pubkey, T) where T: Account into an `AccountInfo`.
impl<'a, T: Account> IntoAccountInfo<'a> for &'a mut (Pubkey, T) {
    fn into_account_info(self) -> AccountInfo<'a> {
        let (ref key, account) = self;
        let (lamports, data, owner, executable) = account.get();
        AccountInfo::new(key, false, false, lamports, data, owner, executable)
    }
}

/// Convenience function for accessing the next item in an [`AccountInfo`]
/// iterator.
///
/// This is simply a wrapper around [`Iterator::next`] that returns a
/// [`ProgramError`] instead of an option.
///
/// # Errors
///
/// Returns [`ProgramError::NotEnoughAccountKeys`] if there are no more items in
/// the iterator.
///
/// # Examples
///
/// ```
/// use solana_program_error::ProgramResult;
/// use solana_account_info::{AccountInfo, next_account_info};
/// use solana_pubkey::Pubkey;
/// # use solana_program_error::ProgramError;
///
/// pub fn process_instruction(
///     program_id: &Pubkey,
///     accounts: &[AccountInfo],
///     instruction_data: &[u8],
/// ) -> ProgramResult {
///     let accounts_iter = &mut accounts.iter();
///     let signer = next_account_info(accounts_iter)?;
///     let payer = next_account_info(accounts_iter)?;
///
///     // do stuff ...
///
///     Ok(())
/// }
/// # let p = Pubkey::new_unique();
/// # let l = &mut 0;
/// # let d = &mut [0u8];
/// # let a = AccountInfo::new(&p, false, false, l, d, &p, false);
/// # let accounts = &[a.clone(), a];
/// # process_instruction(
/// #    &Pubkey::new_unique(),
/// #    accounts,
/// #    &[],
/// # )?;
/// # Ok::<(), ProgramError>(())
/// ```
pub fn next_account_info<'a, 'b, I: Iterator<Item = &'a AccountInfo<'b>>>(
    iter: &mut I,
) -> Result<I::Item, ProgramError> {
    iter.next().ok_or(ProgramError::NotEnoughAccountKeys)
}

/// Convenience function for accessing multiple next items in an [`AccountInfo`]
/// iterator.
///
/// Returns a slice containing the next `count` [`AccountInfo`]s.
///
/// # Errors
///
/// Returns [`ProgramError::NotEnoughAccountKeys`] if there are not enough items
/// in the iterator to satisfy the request.
///
/// # Examples
///
/// ```
/// use solana_program_error::ProgramResult;
/// use solana_account_info::{AccountInfo, next_account_info, next_account_infos};
/// use solana_pubkey::Pubkey;
/// # use solana_program_error::ProgramError;
///
/// pub fn process_instruction(
///     program_id: &Pubkey,
///     accounts: &[AccountInfo],
///     instruction_data: &[u8],
/// ) -> ProgramResult {
///     let accounts_iter = &mut accounts.iter();
///     let signer = next_account_info(accounts_iter)?;
///     let payer = next_account_info(accounts_iter)?;
///     let outputs = next_account_infos(accounts_iter, 3)?;
///
///     // do stuff ...
///
///     Ok(())
/// }
/// # let p = Pubkey::new_unique();
/// # let l = &mut 0;
/// # let d = &mut [0u8];
/// # let a = AccountInfo::new(&p, false, false, l, d, &p, false);
/// # let accounts = &[a.clone(), a.clone(), a.clone(), a.clone(), a];
/// # process_instruction(
/// #    &Pubkey::new_unique(),
/// #    accounts,
/// #    &[],
/// # )?;
/// # Ok::<(), ProgramError>(())
/// ```
pub fn next_account_infos<'a, 'b: 'a>(
    iter: &mut std::slice::Iter<'a, AccountInfo<'b>>,
    count: usize,
) -> Result<&'a [AccountInfo<'b>], ProgramError> {
    let accounts = iter.as_slice();
    if accounts.len() < count {
        return Err(ProgramError::NotEnoughAccountKeys);
    }
    let (accounts, remaining) = accounts.split_at(count);
    *iter = remaining.iter();
    Ok(accounts)
}

impl<'a> AsRef<AccountInfo<'a>> for AccountInfo<'a> {
    fn as_ref(&self) -> &AccountInfo<'a> {
        self
    }
}

#[doc(hidden)]
#[allow(clippy::arithmetic_side_effects)]
pub fn check_type_assumptions() {
    use std::mem::offset_of;

    let key = Pubkey::new_from_array([10; 32]);
    let mut lamports = 31;
    let mut data = vec![1, 2, 3, 4, 5];
    let owner = Pubkey::new_from_array([22; 32]);
    let account_info = AccountInfo::new(&key, true, false, &mut lamports, &mut data, &owner, true);
    let account_info_addr = &account_info as *const _ as u64;

    // key
    assert_eq!(offset_of!(AccountInfo, key), 0);
    let key_ptr = (account_info_addr) as *const &Pubkey;
    unsafe {
        assert_eq!(**key_ptr, key);
    }

    // lamports
    assert_eq!(offset_of!(AccountInfo, lamports), 8);
    let lamports_ptr = (account_info_addr + 8) as *const Rc<RefCell<&mut u64>>;
    unsafe {
        assert_eq!(**(*lamports_ptr).as_ptr(), 31);
    }

    // data
    assert_eq!(offset_of!(AccountInfo, data), 16);
    let data_ptr = (account_info_addr + 16) as *const Rc<RefCell<&mut [u8]>>;
    unsafe {
        assert_eq!((&(*(*data_ptr).as_ptr()))[..], data[..]);
    }

    // owner
    assert_eq!(offset_of!(AccountInfo, owner), 24);
    let owner_ptr = (account_info_addr + 24) as *const &Pubkey;
    unsafe {
        assert_eq!(**owner_ptr, owner);
    }

    // previously rent_epoch
    #[allow(deprecated)]
    {
        assert_eq!(offset_of!(AccountInfo, _unused), 32);
        let unused_ptr = (account_info_addr + 32) as *const u64;
        unsafe {
            assert_eq!(*unused_ptr, 0);
        }
    }

    // is_signer
    assert_eq!(offset_of!(AccountInfo, is_signer), 40);
    let is_signer_ptr = (account_info_addr + 40) as *const bool;
    unsafe {
        assert!(*is_signer_ptr);
    }

    // is_writable
    assert_eq!(offset_of!(AccountInfo, is_writable), 41);
    let is_writable_ptr = (account_info_addr + 41) as *const bool;
    unsafe {
        assert!(!*is_writable_ptr);
    }

    // executable
    assert_eq!(offset_of!(AccountInfo, executable), 42);
    let executable_ptr = (account_info_addr + 42) as *const bool;
    unsafe {
        assert!(*executable_ptr);
    }
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::debug_account_data::{Hex, MAX_DEBUG_ACCOUNT_DATA},
    };

    #[test]
    fn test_next_account_infos() {
        let k1 = Pubkey::new_unique();
        let k2 = Pubkey::new_unique();
        let k3 = Pubkey::new_unique();
        let k4 = Pubkey::new_unique();
        let k5 = Pubkey::new_unique();
        let l1 = &mut 0;
        let l2 = &mut 0;
        let l3 = &mut 0;
        let l4 = &mut 0;
        let l5 = &mut 0;
        let d1 = &mut [0u8];
        let d2 = &mut [0u8];
        let d3 = &mut [0u8];
        let d4 = &mut [0u8];
        let d5 = &mut [0u8];

        let infos = &[
            AccountInfo::new(&k1, false, false, l1, d1, &k1, false),
            AccountInfo::new(&k2, false, false, l2, d2, &k2, false),
            AccountInfo::new(&k3, false, false, l3, d3, &k3, false),
            AccountInfo::new(&k4, false, false, l4, d4, &k4, false),
            AccountInfo::new(&k5, false, false, l5, d5, &k5, false),
        ];
        let infos_iter = &mut infos.iter();
        let info1 = next_account_info(infos_iter).unwrap();
        let info2_3_4 = next_account_infos(infos_iter, 3).unwrap();
        let info5 = next_account_info(infos_iter).unwrap();

        assert_eq!(k1, *info1.key);
        assert_eq!(k2, *info2_3_4[0].key);
        assert_eq!(k3, *info2_3_4[1].key);
        assert_eq!(k4, *info2_3_4[2].key);
        assert_eq!(k5, *info5.key);
    }

    #[test]
    fn test_account_info_as_ref() {
        let k = Pubkey::new_unique();
        let l = &mut 0;
        let d = &mut [0u8];
        let info = AccountInfo::new(&k, false, false, l, d, &k, false);
        assert_eq!(info.key, info.as_ref().key);
    }

    #[test]
    fn test_account_info_debug_data() {
        let key = Pubkey::new_unique();
        let mut lamports = 42;
        let mut data = vec![5; 80];
        let data_str = format!("{:?}", Hex(&data[..MAX_DEBUG_ACCOUNT_DATA]));
        let info = AccountInfo::new(&key, false, false, &mut lamports, &mut data, &key, false);
        assert_eq!(
            format!("{info:?}"),
            format!(
                "AccountInfo {{ \
                key: {}, \
                owner: {}, \
                is_signer: {}, \
                is_writable: {}, \
                executable: {}, \
                lamports: {}, \
                data.len: {}, \
                data: {}, .. }}",
                key,
                key,
                false,
                false,
                false,
                lamports,
                data.len(),
                data_str,
            )
        );

        let mut data = vec![5; 40];
        let data_str = format!("{:?}", Hex(&data));
        let info = AccountInfo::new(&key, false, false, &mut lamports, &mut data, &key, false);
        assert_eq!(
            format!("{info:?}"),
            format!(
                "AccountInfo {{ \
                key: {}, \
                owner: {}, \
                is_signer: {}, \
                is_writable: {}, \
                executable: {}, \
                lamports: {}, \
                data.len: {}, \
                data: {}, .. }}",
                key,
                key,
                false,
                false,
                false,
                lamports,
                data.len(),
                data_str,
            )
        );

        let mut data = vec![];
        let info = AccountInfo::new(&key, false, false, &mut lamports, &mut data, &key, false);
        assert_eq!(
            format!("{info:?}"),
            format!(
                "AccountInfo {{ \
                key: {}, \
                owner: {}, \
                is_signer: {}, \
                is_writable: {}, \
                executable: {}, \
                lamports: {}, \
                data.len: {}, .. }}",
                key,
                key,
                false,
                false,
                false,
                lamports,
                data.len(),
            )
        );
    }

    #[test]
    fn test_layout_assumptions() {
        super::check_type_assumptions();
    }
}
