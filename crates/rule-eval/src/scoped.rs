//! Scoped documents: grants the owner issues under the admin document.
//!
//! A scoped document has the admin document's form and no recovery
//! configuration. It is lowered like the admin document, with two
//! differences: it is refused when any of its rules applies to a contract it
//! may not reach, and each rule it lowers to carries the generation it was
//! issued under. The contracts it may not reach are the account itself, by
//! a self-admin scope or by its address, and every contract of the excluded
//! set, which [`excluded`] takes from the admin document: the account, its
//! recovery controller, and the adapter and pool of its zero-knowledge
//! factor.

use alloc::vec::Vec;

use crate::bytes::{bytes_copy, bytes_eq, bytes_in};
use crate::document::{Doc, DocRule, Scope};
use crate::lowering::lower_rules;
use crate::rule::Rule;

/// Why a scoped document was refused.
pub enum ScopeError {
    /// The document has a recovery configuration.
    RecoveryConfigured,
    /// A rule applies to the account or to a contract of the excluded set.
    ExcludedScope,
}

/// The excluded set of the admin document `admin` on `account`: the account,
/// then, when `admin` has a recovery configuration, its controller and,
/// when that has a zero-knowledge factor, the factor's adapter and pool.
#[must_use]
pub fn excluded(admin: &Doc, account: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    out.push(bytes_copy(account));
    if let Some(rc) = &admin.recovery {
        out.push(bytes_copy(&rc.controller));
        if let Some(z) = &rc.zk {
            out.push(bytes_copy(&z.adapter));
            out.push(bytes_copy(&z.pool));
        }
    }
    out
}

/// Whether scope `s` applies to `account` or to a contract of `excluded`.
fn scope_excluded(s: &Scope, account: &[u8], excluded: &[Vec<u8>]) -> bool {
    match s {
        Scope::SelfAdmin => true,
        Scope::Contract(a) => bytes_eq(a, account) || bytes_in(a, excluded),
    }
}

/// Whether some rule of `rules` applies to `account` or to a contract of
/// `excluded`.
fn any_excluded(rules: &[DocRule], account: &[u8], excluded: &[Vec<u8>]) -> bool {
    let mut i = 0;
    while i < rules.len() {
        if scope_excluded(&rules[i].scope, account, excluded) {
            return true;
        }
        i += 1;
    }
    false
}

/// The rules the scoped document `d` lowers to on `account`, under the
/// excluded set `excluded` and the current generation `generation`: one per
/// document rule, in order, each carrying `generation`.
///
/// # Errors
///
/// - [`ScopeError::RecoveryConfigured`] if `d` has a recovery configuration;
/// - [`ScopeError::ExcludedScope`] if a rule of `d` has a self-admin scope,
///   or a contract scope on `account` or on a contract of `excluded`.
pub fn lower_scoped(
    d: &Doc,
    account: &[u8],
    excluded: &[Vec<u8>],
    generation: u64,
) -> Result<Vec<Rule>, ScopeError> {
    match &d.recovery {
        Some(_) => Err(ScopeError::RecoveryConfigured),
        None => {
            if any_excluded(&d.rules, account, excluded) {
                return Err(ScopeError::ExcludedScope);
            }
            Ok(lower_rules(&d.rules, &d.signers, account, Some(generation)))
        }
    }
}
