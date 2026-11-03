//! A plain implementation of the interfaces, for testing a shell without a
//! host.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use crate::host::{Auth, Refusal, Storage};
use crate::val::{Address, Durability, Val};

/// Storage as a map, and `require_auth` against a list of addresses that
/// have authorized everything.
#[derive(Clone, Debug, Default)]
pub struct PlainHost {
    storage: BTreeMap<(Durability, Val), Val>,
    authorized: Vec<Address>,
    /// Every address `require_auth` was called with, in order.
    pub required: Vec<Address>,
}

impl PlainHost {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Makes every later `require_auth` of `address` succeed.
    pub fn authorize(&mut self, address: Address) {
        self.authorized.push(address);
    }
}

fn storable(key: &Val) -> Result<(), Refusal> {
    if key.storable() {
        Ok(())
    } else {
        Err(Refusal::MuxedAddress)
    }
}

impl Storage for PlainHost {
    fn get(&self, d: Durability, key: &Val) -> Result<Option<Val>, Refusal> {
        storable(key)?;
        Ok(self.storage.get(&(d, key.clone())).cloned())
    }

    fn has(&self, d: Durability, key: &Val) -> Result<bool, Refusal> {
        storable(key)?;
        Ok(self.storage.contains_key(&(d, key.clone())))
    }

    fn set(&mut self, d: Durability, key: &Val, val: &Val) -> Result<(), Refusal> {
        storable(key)?;
        self.storage.insert((d, key.clone()), val.clone());
        Ok(())
    }

    fn remove(&mut self, d: Durability, key: &Val) -> Result<(), Refusal> {
        storable(key)?;
        self.storage.remove(&(d, key.clone()));
        Ok(())
    }
}

impl Auth for PlainHost {
    fn require_auth(&mut self, address: &Address) -> Result<(), Refusal> {
        if address.is_muxed() {
            return Err(Refusal::MuxedAddress);
        }
        self.required.push(address.clone());
        if self.authorized.contains(address) {
            Ok(())
        } else {
            Err(Refusal::Unauthorized)
        }
    }
}
