//! Rule sets: slices of rules.

use crate::context::Context;
use crate::rule::{Rule, rule_allows};

/// Whether some rule in `rules` allows `ctx`.
#[must_use]
pub fn allows(rules: &[Rule], ctx: &Context) -> bool {
    let mut i = 0;
    while i < rules.len() {
        if rule_allows(&rules[i], ctx) {
            return true;
        }
        i += 1;
    }
    false
}

/// Whether `rules` allows every context in `contexts`. A Soroban
/// authorization tree is checked by passing every context in the tree, so one
/// disallowed nested call denies the whole tree.
#[must_use]
pub fn allows_all(rules: &[Rule], contexts: &[Context]) -> bool {
    let mut i = 0;
    while i < contexts.len() {
        if !allows(rules, &contexts[i]) {
            return false;
        }
        i += 1;
    }
    true
}
