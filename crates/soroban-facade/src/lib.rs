//! A small part of the Soroban SDK as plain data and simple interfaces, for
//! contract shells that use `rule-eval`.
//!
//! - [`Val`] and [`Address`] are Soroban values as plain data: `void`,
//!   `bool`, `u32`, `u64`, `i128`, bytes, strings, symbols, addresses
//!   (accounts, contracts and muxed accounts), vectors, maps, and `Other`
//!   for a value of any other type, as its XDR. [`xdr`] writes and reads
//!   their `ScVal` XDR.
//! - [`Storage`] is a contract's storage by [`Durability`]: get, has, set
//!   and remove. A key holding a muxed address is refused.
//! - [`Auth`] is `require_auth`.
//! - [`AuthContext`] is one context `__check_auth` receives;
//!   [`auth_contexts`] reads them from the value the host passes, refusing
//!   the whole batch when one cannot be read, and [`to_rule_eval`] is what
//!   `rule-eval` reads of a context.
//!
//! [`PlainHost`] implements the interfaces as plain data, for tests. With
//! the `sdk` feature, `SdkHost` implements them over soroban-sdk 27; it is
//! the only code in the repository that touches the SDK.
//!
//! The Lean models of what these stand for are in
//! `formal/RuleCore/Soroban/`: [`xdr::encode`] is `Val.xdr`,
//! [`val_to_rule_eval`] is `Val.toChain` and [`to_rule_eval`] is
//! `AuthFn.toChain`. The conformance vectors in
//! `conformance/vectors/soroban` check this crate against them, and the
//! host harness in `conformance/host` checks both against
//! `soroban-env-host`.
#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

mod context;
mod host;
mod plain;
#[cfg(feature = "sdk")]
mod sdk;
mod val;
pub mod xdr;

pub use context::{
    AuthContext, auth_contexts, contexts_to_rule_eval, to_rule_eval, val_to_rule_eval,
};
pub use host::{Auth, Refusal, Storage};
pub use plain::PlainHost;
#[cfg(feature = "sdk")]
pub use sdk::SdkHost;
pub use val::{Address, Durability, Val};
