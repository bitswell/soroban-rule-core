//! Rule-set evaluator for Soroban authorization contexts.
//!
//! A [`Rule`] names one contract, the [`Functions`] it matches there (a list,
//! or every function except a list), a list of conditions on the arguments
//! of the call it matches, a list of [`Signer`]s, a threshold and,
//! optionally, a spending [`Cap`], a last ledger and a generation. An
//! authorization carries the signers it authenticated, one list for every
//! context it covers. A rule allows a [`Context`] under those signers when the
//! call matches, every condition holds, and at least `threshold` distinct
//! signers of the rule are authenticated. A rule set (a slice of rules) allows
//! a context when some rule allows it, and allows a batch, every context of a
//! Soroban authorization tree, when it allows each context. No rule allows a
//! contract creation.
//!
//! The readable Lean model this crate implements:
//!
//! ```lean
//! structure RuleCap (Ctx : Type) where
//!   params : Cap.Params         -- at most `limit` within `period` ledgers
//!   amount : Ctx → Option Int   -- the amount a context spends, if it names one
//!
//! structure Rule (Ctx Sig : Type) where
//!   scope : Ctx → Bool          -- contract and function match
//!   conds : List (Ctx → Bool)   -- conditions on this call's arguments
//!   signers : List Sig          -- the signers that count towards the threshold
//!   threshold : Nat             -- how many distinct signers must be authenticated
//!   cap : Option (RuleCap Ctx) := none  -- the rule's spending cap, if it has one
//!   validUntil : Option Nat := none     -- the last ledger it authorizes in, if any
//!   generation : Option Nat := none     -- the generation it was issued under, if any
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
//! [`allows`] and [`allows_all`] evaluate a rule set, without caps, time or
//! generation. [`authorize`] is the stateful check: an authorization names
//! one rule per context, as OpenZeppelin's smart account does, each chosen
//! rule must be unexpired at the current ledger, belong to the current
//! generation when it carries one, and allow its context, every
//! authenticated signer must be a signer of some chosen rule, and the
//! context's amount is charged to the record of each chosen rule with a cap;
//! it returns the records after every charge or a [`Refusal`] that changes
//! nothing. Every batch it accepts, [`allows_all`] allows.
//!
//! [`drop_rule`], [`add_cond`], [`remove_functions`], [`restrict_functions`],
//! [`remove_signers`], [`raise_threshold`], [`add_cap`], [`lower_cap_limit`],
//! [`lengthen_cap_period`] and [`lower_valid_until`] are the attenuation
//! steps: each returns a new rule set that allows no context, under any
//! authenticated signers, that the original does not, and accepts no run of
//! authorizations from empty records that the original does not accept from
//! its own, with each rule index renumbered past a dropped rule. No step
//! changes a rule's generation.
//!
//! [`check_spend`] is the spending-cap check: given what a capped rule has
//! spent in its window ([`SpendRecord`]), the cap, the current ledger and the
//! amount of a new spend, it returns the record after the spend or a
//! [`CapError`]. [`authorize`] calls it for every charge.
//!
//! [`spend`], [`delegate`] and [`refill`] keep budgets on the delegation
//! tree, a slice of [`Node`]s: a spend charges the spender and every ancestor
//! up to its root, or refuses with a [`BudgetError`] that changes nothing and
//! names the first node that would be overdrawn; a delegation appends a child
//! with any allowance; a refill raises one node's allowance.
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
//!   from rules or from an authorization's choices go through `get` or
//!   `get_mut`; the counter step `i += 1` runs under
//!   `i < s.len()`, so it cannot overflow, and the signer count grows by at
//!   most one per step of its loop, so it stays at most `i`;
//! - indices and thresholds are `u32` widened with `as usize`, lossless on
//!   every target with at least 32-bit pointers (asserted at compile time
//!   below);
//! - no parameter or local variable is named after a module of the crate
//!   (`attenuate`, `authorize`, `budget`, `bytes`, `cap`, `context`, `rule`,
//!   `rule_set`, `signer`, `val`): the translation puts each module's items in a Lean
//!   namespace of that name, which a binding of the same name would shadow.
//!
//! The only panic left is allocation failure in `Vec::push`, which the
//! attenuation steps, [`check_spend`], [`authorize`] and the budget operations
//! call to build their result; [`allows`] and [`allows_all`] do not allocate.
#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

mod attenuate;
mod authorize;
mod budget;
mod bytes;
mod cap;
mod context;
mod rule;
mod rule_set;
mod signer;
mod val;

pub use attenuate::{
    AttenuationError, add_cap, add_cond, drop_rule, lengthen_cap_period, lower_cap_limit,
    lower_valid_until, raise_threshold, remove_functions, remove_signers, restrict_functions,
};
pub use authorize::{Refusal, authorize};
pub use budget::{BudgetError, MAX_NODES, Node, delegate, refill, spend, tree_valid};
pub use bytes::{bytes_eq, bytes_in, bytes_starts_with};
pub use cap::{
    CapError, CapParams, MAX_HISTORY_ENTRIES, SpendEntry, SpendRecord, check_spend, empty_record,
    params_valid,
};
pub use context::Context;
pub use rule::{Cap, Cond, Functions, Rule, cap_valid, cond_holds, functions_match, rule_allows};
pub use rule_set::{allows, allows_all};
pub use signer::{Signer, signer_eq, signer_in, signers_met};
pub use val::{Val, val_eq, val_in};

const _: () = assert!(usize::BITS >= 32);
