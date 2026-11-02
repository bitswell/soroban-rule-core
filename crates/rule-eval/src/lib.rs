//! Rule-set evaluator for Soroban authorization contexts.
//!
//! A [`Rule`] names one contract, a list of function names and a list of
//! conditions on the arguments of the call it matches. A rule set (a slice of
//! rules) allows a [`Context`] when some rule allows it, and allows a batch,
//! every context of a Soroban authorization tree, when it allows each context.
//! No rule allows a contract creation.
//!
//! The readable Lean model this crate implements:
//!
//! ```lean
//! structure Rule (Ctx : Type) where
//!   scope : Ctx → Bool          -- contract and function match
//!   conds : List (Ctx → Bool)   -- conditions on this call's arguments
//!
//! def Rule.allows (r : Rule Ctx) (c : Ctx) : Bool :=
//!   r.scope c && r.conds.all (· c)
//!
//! def RuleSet (Ctx : Type) := List (Rule Ctx)
//!
//! def RuleSet.allows (rs : RuleSet Ctx) (c : Ctx) : Bool :=
//!   rs.any (·.allows c)
//!
//! def RuleSet.allowsAll (rs : RuleSet Ctx) (cs : List Ctx) : Bool :=
//!   cs.all rs.allows
//! ```
//!
//! [`allows`] and [`allows_all`] evaluate a rule set. [`drop_rule`],
//! [`add_cond`] and [`remove_functions`] are the attenuation steps: each
//! returns a new rule set that allows no context the original does not.
//!
//! Identifiers and byte payloads compare exactly (same length, same bytes).
//! Values of different [`Val`] constructors are never equal. The evaluator
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
//!   `i < s.len()`, so it cannot overflow;
//! - indices are `u32` widened with `as usize`, lossless on every target with
//!   at least 32-bit pointers (asserted at compile time below);
//! - no parameter or local variable is named after a module of the crate
//!   (`attenuate`, `bytes`, `context`, `rule`, `rule_set`, `val`): the
//!   translation puts each module's items in a Lean namespace of that name,
//!   which a binding of the same name would shadow.
//!
//! The only panic left is allocation failure in `Vec::push`, which the
//! attenuation steps call to build their result; [`allows`] and
//! [`allows_all`] do not allocate.
#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

mod attenuate;
mod bytes;
mod context;
mod rule;
mod rule_set;
mod val;

pub use attenuate::{AttenuationError, add_cond, drop_rule, remove_functions};
pub use bytes::{bytes_eq, bytes_in};
pub use context::Context;
pub use rule::{Cond, Rule, cond_holds, rule_allows};
pub use rule_set::{allows, allows_all};
pub use val::{Val, val_eq};

const _: () = assert!(usize::BITS >= 32);
