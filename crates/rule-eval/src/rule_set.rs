//! Rule sets: slices of rules.

use crate::context::{Context, entry_root};
use crate::rule::{Rule, rule_allows, rule_allows_in};
use crate::signer::Signer;

/// Whether some rule in `rules` allows `ctx` under the authorization's
/// `authenticated` signers. Root constraints, caps, time and generation are
/// ignored: this is only local-context screening.
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

/// Local-context screening for every context; ignores root constraints,
/// caps, choices, time, generation and signer coverage. Use [`allows_batch`]
/// for root-aware screening and [`check_auth`](crate::check_auth) for the full
/// decision. Empty batches pass this screening.
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

/// Root-aware screening of one authorization entry. Each context needs some
/// rule whose local conditions and exact root constraint both hold. The root
/// is always this batch's first context; other entries cannot supply it.
/// Empty batches pass. Caps, choices, time, generation and signer coverage
/// remain the responsibility of [`check_auth`](crate::check_auth).
#[must_use]
pub fn allows_batch(rules: &[Rule], contexts: &[Context], authenticated: &[Signer]) -> bool {
    let mut i = 0;
    while i < contexts.len() {
        if !allows_in(rules, entry_root(contexts), &contexts[i], authenticated) {
            return false;
        }
        i += 1;
    }
    true
}

/// Root-aware screening of one context, with an explicit entry root.
fn allows_in(
    rules: &[Rule],
    root: Option<&Context>,
    ctx: &Context,
    authenticated: &[Signer],
) -> bool {
    let mut i = 0;
    while i < rules.len() {
        if rule_allows_in(&rules[i], root, ctx, authenticated) {
            return true;
        }
        i += 1;
    }
    false
}
