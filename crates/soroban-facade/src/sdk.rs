//! The real implementation, over soroban-sdk. It is the only code in the
//! repository that calls the SDK.
//!
//! Values cross between the facade and the SDK as XDR: a facade value is
//! encoded with [`xdr::encode`] and the host deserializes it
//! (`FromXdr`), and a host value is serialized by the host (`ToXdr`) and
//! read with [`xdr::decode`]. The host traps on XDR it cannot represent as a
//! value, as it does for any contract: a symbol with a character outside
//! `[a-zA-Z0-9_]` or over 32 bytes, or a map whose keys are not in the
//! host's order.

use alloc::vec;
use alloc::vec::Vec;

use soroban_sdk::xdr::{FromXdr, ToXdr};
use soroban_sdk::{Address as SdkAddress, Bytes, Env, Val as SdkVal};

use crate::context::{AuthContext, auth_contexts};
use crate::host::{Auth, Refusal, Storage};
use crate::val::{Address, Durability, Val};
use crate::xdr;

/// The facade's interfaces on a contract's [`Env`].
pub struct SdkHost<'a> {
    env: &'a Env,
}

impl<'a> SdkHost<'a> {
    #[must_use]
    pub fn new(env: &'a Env) -> Self {
        Self { env }
    }

    /// The host value for `v`.
    #[must_use]
    pub fn to_sdk(&self, v: &Val) -> Option<SdkVal> {
        let b = Bytes::from_slice(self.env, &xdr::encode(v));
        SdkVal::from_xdr(self.env, &b).ok()
    }

    /// The facade value for a host value, or `None` for a value it has no
    /// form for.
    #[must_use]
    pub fn from_sdk(&self, v: SdkVal) -> Option<Val> {
        let b = v.to_xdr(self.env);
        let mut buf = vec![0u8; b.len() as usize];
        b.copy_into_slice(&mut buf);
        xdr::decode(&buf)
    }

    /// The host address for `a`, or `None` for a muxed account, which is no
    /// `Address` on the host.
    #[must_use]
    pub fn address(&self, a: &Address) -> Option<SdkAddress> {
        if a.is_muxed() {
            return None;
        }
        let b = Bytes::from_slice(self.env, &xdr::encode(&Val::Address(a.clone())));
        SdkAddress::from_xdr(self.env, &b).ok()
    }

    /// `__check_auth`'s contexts, given as the host passes them: all of them,
    /// or `None` when any one cannot be read.
    #[must_use]
    pub fn auth_contexts(&self, contexts: SdkVal) -> Option<Vec<AuthContext>> {
        auth_contexts(&self.from_sdk(contexts)?)
    }

    fn key(&self, key: &Val) -> Result<SdkVal, Refusal> {
        if !key.storable() {
            return Err(Refusal::MuxedAddress);
        }
        self.to_sdk(key).ok_or(Refusal::Undecodable)
    }
}

impl Storage for SdkHost<'_> {
    fn get(&self, d: Durability, key: &Val) -> Result<Option<Val>, Refusal> {
        let k = self.key(key)?;
        let storage = self.env.storage();
        let v: Option<SdkVal> = match d {
            Durability::Persistent => storage.persistent().get(&k),
            Durability::Temporary => storage.temporary().get(&k),
            Durability::Instance => storage.instance().get(&k),
        };
        match v {
            Some(v) => self.from_sdk(v).map(Some).ok_or(Refusal::Undecodable),
            None => Ok(None),
        }
    }

    fn has(&self, d: Durability, key: &Val) -> Result<bool, Refusal> {
        let k = self.key(key)?;
        let storage = self.env.storage();
        Ok(match d {
            Durability::Persistent => storage.persistent().has(&k),
            Durability::Temporary => storage.temporary().has(&k),
            Durability::Instance => storage.instance().has(&k),
        })
    }

    fn set(&mut self, d: Durability, key: &Val, val: &Val) -> Result<(), Refusal> {
        let k = self.key(key)?;
        let v = self.to_sdk(val).ok_or(Refusal::Undecodable)?;
        let storage = self.env.storage();
        match d {
            Durability::Persistent => storage.persistent().set(&k, &v),
            Durability::Temporary => storage.temporary().set(&k, &v),
            Durability::Instance => storage.instance().set(&k, &v),
        }
        Ok(())
    }

    fn remove(&mut self, d: Durability, key: &Val) -> Result<(), Refusal> {
        let k = self.key(key)?;
        let storage = self.env.storage();
        match d {
            Durability::Persistent => storage.persistent().remove(&k),
            Durability::Temporary => storage.temporary().remove(&k),
            Durability::Instance => storage.instance().remove(&k),
        }
        Ok(())
    }
}

impl Auth for SdkHost<'_> {
    fn require_auth(&mut self, address: &Address) -> Result<(), Refusal> {
        let a = self.address(address).ok_or(Refusal::MuxedAddress)?;
        a.require_auth();
        Ok(())
    }
}
