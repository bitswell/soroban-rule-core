//! Soroban values as plain data.

use alloc::vec::Vec;

/// An address, following `ScAddress`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Address {
    /// A Stellar account, by its ed25519 public key.
    Account([u8; 32]),
    /// A contract, by its id.
    Contract([u8; 32]),
    /// A muxed account: an account key and a 64-bit id.
    MuxedAccount { id: u64, key: [u8; 32] },
}

impl Address {
    /// Whether the address is a muxed account, which no storage key may hold.
    #[must_use]
    pub fn is_muxed(&self) -> bool {
        matches!(self, Address::MuxedAccount { .. })
    }
}

/// A value a contract passes to the host or receives from it, following
/// `ScVal`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Val {
    Void,
    Bool(bool),
    U32(u32),
    U64(u64),
    I128(i128),
    Bytes(Vec<u8>),
    String(Vec<u8>),
    Symbol(Vec<u8>),
    Address(Address),
    Vec(Vec<Val>),
    /// A map's entries, in the host's key order.
    Map(Vec<(Val, Val)>),
    /// A value of any other type (`i32`, `i64`, `u128`, `u256`, `i256`, a time
    /// point, a duration or an error), as its full `ScVal` XDR. The real
    /// implementation refuses any other XDR here.
    Other(Vec<u8>),
}

impl Val {
    /// Whether the value may be a storage key: no muxed address occurs in it.
    #[must_use]
    pub fn storable(&self) -> bool {
        match self {
            Val::Address(a) => !a.is_muxed(),
            Val::Vec(items) => items.iter().all(Val::storable),
            Val::Map(entries) => entries.iter().all(|(k, v)| k.storable() && v.storable()),
            _ => true,
        }
    }
}

/// Where a contract keeps a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Durability {
    Persistent,
    Temporary,
    /// The contract instance's own storage.
    Instance,
}
