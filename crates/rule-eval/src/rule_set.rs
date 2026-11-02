//! Rule sets: slices of rules.

use crate::context::Context;
use crate::rule::{Rule, rule_allows};
use crate::signer::Signer;

/// Whether some rule in `rules` allows `ctx` under the authorization's
/// `authenticated` signers.
#[must_use]
pub fn allows(rules: &[Rule], ctx: &Context, authenticated: &[Signer]) -> bool {
    let mut i = 0;
    while i < rules.len() {
        if rule_allows(&rules[i], ctx, authenticated) {
            return true;
        }
        i += 1;
    }
    false
}

/// Whether `rules` allows every context in `contexts` under the
/// authorization's `authenticated` signers. A Soroban authorization tree is
/// checked by passing every context in the tree, with the signers that
/// authenticated the whole tree, so one disallowed nested call denies the
/// whole tree.
#[must_use]
pub fn allows_all(rules: &[Rule], contexts: &[Context], authenticated: &[Signer]) -> bool {
    let mut i = 0;
    while i < contexts.len() {
        if !allows(rules, &contexts[i], authenticated) {
            return false;
        }
        i += 1;
    }
    true
}
