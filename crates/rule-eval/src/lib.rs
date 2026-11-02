//! Rule-set evaluator for Soroban authorization contexts.
//!
//! A [`Rule`] names one contract, a list of function names, a list of
//! conditions on the arguments of the call it matches, a list of
//! [`Signer`]s and a threshold. An authorization carries the signers it
//! authenticated, one list for every context it covers. A rule allows a
//! [`Context`] under those signers when the call matches, every condition
//! holds, and at least `threshold` distinct signers of the rule are
//! authenticated. A rule set (a slice of rules) allows a context when some
//! rule allows it, and allows a batch, every context of a Soroban
//! authorization tree, when it allows each context. No rule allows a contract
//! creation.
//!
//! The readable Lean model this crate implements:
//!
//! ```lean
//! structure Rule (Ctx Sig : Type) where
//!   scope : Ctx → Bool          -- contract and function match
//!   conds : List (Ctx → Bool)   -- conditions on this call's arguments
//!   signers : List Sig          -- the signers that count towards the threshold
//!   threshold : Nat             -- how many distinct signers must be authenticated
//!
//! def Rule.present (r : Rule Ctx Sig) (auth : List Sig) : List Sig :=
//!   r.signers.eraseDups.filter (· ∈ auth)
//!
//! def Rule.signed (r : Rule Ctx Sig) (auth : List Sig) : Bool :=
//!   decide (r.threshold ≤ (r.present auth).length)
//!
//! def Rule.allows (r : Rule Ctx Sig) (c : Ctx) (auth : List Sig) : Bool :=
//!   r.scope c && r.conds.all (· c) && r.signed auth
//!
//! def RuleSet (Ctx Sig : Type) := List (Rule Ctx Sig)
//!
//! def RuleSet.allows (rs : RuleSet Ctx Sig) (c : Ctx) (auth : List Sig) : Bool :=
//!   rs.any (·.allows c auth)
//!
//! def RuleSet.allowsAll (rs : RuleSet Ctx Sig) (cs : List Ctx) (auth : List Sig) : Bool :=
//!   cs.all (rs.allows · auth)
//! ```
//!
//! [`allows`] and [`allows_all`] evaluate a rule set. [`drop_rule`],
//! [`add_cond`], [`remove_functions`], [`remove_signers`] and
//! [`raise_threshold`] are the attenuation steps: each returns a new rule set
//! that allows no context, under any authenticated signers, that the original
//! does not.
//!
//! [`check_spend`] is the spending-cap check: given what a capped rule has
//! spent in its window ([`SpendRecord`]), the cap, the current ledger and the
//! amount of a new spend, it returns the record after the spend or a
//! [`CapError`].
//!
//! Identifiers and byte payloads compare exactly (same length, same bytes).
//! Values of different [`Val`] constructors are never equal, and signers of
//! different [`Signer`] constructors are never equal. The evaluator
//! normalizes nothing.
//!
//! The code is written in a restricted Rust subset so Charon and Aeneas can
//! translate it to Lean as total functions:
//!
//! - plain structs and enums; no traits, trait objects, closures, iterator
//!   adaptors or derived impls; enums compare by explicit `match` and byte
//!   strings through one loop ([`bytes_eq`]);
//! - each loop is a single `while i < s.len()` over one slice, with an early
//!   `return` where it decides;
//! - slice indexing `s[i]` happens only under `i < s.len()`, and indices taken
//!   from rules go through `get`; the counter step `i += 1` runs under
//!   `i < s.len()`, so it cannot overflow, and the signer count grows by at
//!   most one per step of its loop, so it stays at most `i`;
//! - indices and thresholds are `u32` widened with `as usize`, lossless on
//!   every target with at least 32-bit pointers (asserted at compile time
//!   below);
//! - no parameter or local variable is named after a module of the crate
//!   (`attenuate`, `bytes`, `cap`, `context`, `rule`, `rule_set`, `signer`,
//!   `val`): the translation puts each module's items in a Lean namespace of
//!   that name, which a binding of the same name would shadow.
//!
//! The only panic left is allocation failure in `Vec::push`, which the
//! attenuation steps and [`check_spend`] call to build their result;
//! [`allows`] and [`allows_all`] do not allocate.
#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

mod attenuate;
mod bytes;
mod cap;
mod context;
mod rule;
mod rule_set;
mod signer;
mod val;

pub use attenuate::{
    AttenuationError, add_cond, drop_rule, raise_threshold, remove_functions, remove_signers,
};
pub use bytes::{bytes_eq, bytes_in};
pub use cap::{
    CapError, CapParams, MAX_HISTORY_ENTRIES, SpendEntry, SpendRecord, check_spend, empty_record,
    params_valid,
};
pub use context::Context;
pub use rule::{Cond, Rule, cond_holds, rule_allows};
pub use rule_set::{allows, allows_all};
pub use signer::{Signer, signer_eq, signer_in, signers_met};
pub use val::{Val, val_eq};

const _: () = assert!(usize::BITS >= 32);
