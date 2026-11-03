//! The interfaces a contract shell uses: its storage and `require_auth`.

use crate::val::{Address, Durability, Val};

/// Why the facade refused an operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// A storage key holds a muxed address, or `require_auth` names one.
    MuxedAddress,
    /// A stored value has no [`Val`] form, or a key or value given is no
    /// value the facade models (an `Other` holding XDR the facade does not
    /// read, such as an executable tag).
    Undecodable,
    /// The address has not authorized the call.
    Unauthorized,
}

/// A contract's own storage: a map from a durability and a key to a value.
///
/// Every method refuses a key that holds a muxed address
/// ([`Val::storable`]) with [`Refusal::MuxedAddress`] and changes nothing.
pub trait Storage {
    fn get(&self, d: Durability, key: &Val) -> Result<Option<Val>, Refusal>;
    fn has(&self, d: Durability, key: &Val) -> Result<bool, Refusal>;
    fn set(&mut self, d: Durability, key: &Val, val: &Val) -> Result<(), Refusal>;
    /// Removes the key's value; removing an absent key changes nothing.
    fn remove(&mut self, d: Durability, key: &Val) -> Result<(), Refusal>;
}

/// Authorization of the current call.
pub trait Auth {
    /// Requires `address` to have authorized the current call with its
    /// arguments. On the host a refusal aborts the call, which the host then
    /// rolls back, so the real implementation returns only `Ok` or
    /// [`Refusal::MuxedAddress`].
    fn require_auth(&mut self, address: &Address) -> Result<(), Refusal>;
}
