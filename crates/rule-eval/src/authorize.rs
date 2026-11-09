//! Authorization: each context checked against the rule chosen for it, and
//! the caps of the chosen rules charged.
//!
//! An authorization names, for each context of its batch, the index of the
//! rule that authorizes it: `choices[i]` is the rule for `contexts[i]`. This
//! follows OpenZeppelin's smart account, whose `AuthPayload` carries one
//! context rule id per authorization context, aligned by index and bound into
//! the signed digest. Each capped rule keeps a [`SpendRecord`]: `records[j]`
//! is the record of `rules[j]`, and a rule without a cap keeps its record
//! unchanged.
//!
//! [`check_auth`] works in three passes, as OpenZeppelin's `do_check_auth`
//! (`packages/accounts/src/smart_account/storage.rs` of `stellar-accounts` at
//! the revision Perch pins) validates every context against its rule, then
//! checks the authenticated signers, before it enforces any policy:
//!
//! 1. in context order, every chosen rule exists, has not expired (its
//!    `valid_until`, when it has one, is not before `now`: OpenZeppelin
//!    refuses `valid_until < e.ledger().sequence()`), was issued under the
//!    current `generation` when it carries one, and allows its context under
//!    the authenticated signers ([`rule_allows_in`]);
//! 2. every authenticated signer is a signer of some chosen rule, as
//!    OpenZeppelin refuses a signer that belongs to no selected rule with
//!    `UnauthorizedSigner`;
//! 3. in context order, for every chosen rule with a cap, the context's
//!    argument at the cap's `amount_arg` is an `I128`, and it is charged to
//!    that rule's record with [`check_spend`]. Two contexts charging one rule
//!    are charged one after the other, the second against the record the
//!    first left.
//!
//! It is pure: the shell loads the records before the call and stores what
//! `check_auth` returns. A refusal returns no records, so the stored ones stay
//! as they were, the charges of earlier contexts in the batch included.
//! [`allows`](crate::allows) and [`allows_all`](crate::allows_all) are the
//! local screening view: they also ignore root constraints. Every accepted
//! batch passes [`allows_batch`](crate::allows_batch), which checks the
//! current entry's root as well as local conditions, but does not enforce
//! caps, choices, time, generation or signer coverage.

use alloc::vec::Vec;

use crate::cap::{CapError, SpendRecord, check_spend, record_copy};
use crate::context::{Context, entry_root};
use crate::rule::{Cap, Rule, rule_allows_in};
use crate::signer::{Signer, signer_in};
use crate::val::Val;

/// Why an authorization was refused.
pub enum Refusal {
    /// `choices` does not hold exactly one rule index per context.
    ChoicesMismatch,
    /// `records` does not hold exactly one record per rule.
    RecordsMismatch,
    /// A chosen index is not below the number of rules.
    NoSuchRule,
    /// A chosen rule's last ledger is before the current one.
    Expired,
    /// A chosen rule was issued under a generation other than the current
    /// one.
    StaleGeneration,
    /// A chosen rule does not allow its context under the authenticated
    /// signers.
    NotAllowed,
    /// An authenticated signer is a signer of no chosen rule.
    UnauthorizedSigner,
    /// A chosen rule has a cap and its context has no `I128` argument at the
    /// cap's `amount_arg`.
    NoAmount,
    /// A chosen rule's cap refused the spend.
    Cap(CapError),
}

/// The amount `ctx` spends under `limits`: its argument at `amount_arg`, when
/// that argument exists and is an `I128`.
fn spend_amount(limits: &Cap, ctx: &Context) -> Option<i128> {
    match ctx {
        Context::Call { args, .. } => match args.get(limits.amount_arg as usize) {
            Some(Val::I128(v)) => Some(*v),
            _ => None,
        },
        Context::Create { .. } => None,
    }
}

/// Whether `r` has expired at ledger `now`: it has a last ledger, and `now`
/// is after it.
fn expired(r: &Rule, now: u32) -> bool {
    match r.valid_until {
        Some(last) => last < now,
        None => false,
    }
}

/// Whether `r` was issued under a generation other than `generation`.
fn stale(r: &Rule, generation: u64) -> bool {
    match r.generation {
        Some(issued) => issued != generation,
        None => false,
    }
}

/// The first pass: whether the rule chosen for each context exists, is
/// current at ledger `now` and in `generation`, and allows the context, or
/// the refusal for the first context that fails.
fn check_choices(
    rules: &[Rule],
    contexts: &[Context],
    choices: &[u32],
    authenticated: &[Signer],
    now: u32,
    generation: u64,
) -> Result<(), Refusal> {
    let mut i = 0;
    while i < contexts.len() {
        let index = match choices.get(i) {
            Some(index) => *index as usize,
            None => return Err(Refusal::ChoicesMismatch),
        };
        match rules.get(index) {
            Some(r) => {
                if expired(r, now) {
                    return Err(Refusal::Expired);
                }
                if stale(r, generation) {
                    return Err(Refusal::StaleGeneration);
                }
                if !rule_allows_in(r, entry_root(contexts), &contexts[i], authenticated) {
                    return Err(Refusal::NotAllowed);
                }
            }
            None => return Err(Refusal::NoSuchRule),
        }
        i += 1;
    }
    Ok(())
}

/// Whether `s` is a signer of some rule of `rules` that `choices` names.
fn signer_chosen(s: &Signer, rules: &[Rule], choices: &[u32]) -> bool {
    let mut i = 0;
    while i < choices.len() {
        if let Some(r) = rules.get(choices[i] as usize)
            && signer_in(s, &r.signers)
        {
            return true;
        }
        i += 1;
    }
    false
}

/// The second pass: whether every authenticated signer is a signer of some
/// chosen rule.
fn signers_chosen(authenticated: &[Signer], rules: &[Rule], choices: &[u32]) -> bool {
    let mut i = 0;
    while i < authenticated.len() {
        if !signer_chosen(&authenticated[i], rules, choices) {
            return false;
        }
        i += 1;
    }
    true
}

/// A fresh copy of `records`, keeping order.
fn records_copy(records: &[SpendRecord]) -> Vec<SpendRecord> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < records.len() {
        out.push(record_copy(&records[i]));
        i += 1;
    }
    out
}

/// The third pass: the records after charging, in context order, each
/// context whose chosen rule has a cap, or the refusal for the first charge
/// that fails.
fn charge_all(
    rules: &[Rule],
    records: &[SpendRecord],
    contexts: &[Context],
    choices: &[u32],
    now: u32,
) -> Result<Vec<SpendRecord>, Refusal> {
    let mut out = records_copy(records);
    let mut i = 0;
    while i < contexts.len() {
        let index = match choices.get(i) {
            Some(index) => *index as usize,
            None => return Err(Refusal::ChoicesMismatch),
        };
        match rules.get(index) {
            Some(Rule {
                cap: Some(limits), ..
            }) => {
                let amount = match spend_amount(limits, &contexts[i]) {
                    Some(amount) => amount,
                    None => return Err(Refusal::NoAmount),
                };
                match out.get_mut(index) {
                    Some(record) => {
                        match check_spend(record, limits.limit, limits.period, now, amount) {
                            Ok(next) => *record = next,
                            Err(e) => return Err(Refusal::Cap(e)),
                        }
                    }
                    None => return Err(Refusal::RecordsMismatch),
                }
            }
            Some(_) => {}
            None => return Err(Refusal::NoSuchRule),
        }
        i += 1;
    }
    Ok(out)
}

/// The records after an authorization at ledger `now`, with `generation` the
/// current generation, of `contexts`, each by the rule of `rules` that
/// `choices` names for it, under the authenticated signers `authenticated`;
/// or why it is refused.
///
/// # Errors
///
/// - [`Refusal::ChoicesMismatch`] if `choices` and `contexts` differ in
///   length;
/// - [`Refusal::RecordsMismatch`] if `records` and `rules` differ in length;
/// - [`Refusal::NoSuchRule`], [`Refusal::Expired`],
///   [`Refusal::StaleGeneration`] or [`Refusal::NotAllowed`] if, for the first
///   context whose chosen rule fails, the index is out of range, the rule's
///   last ledger is before `now`, the rule carries a generation other than
///   `generation`, or the rule does not allow the context;
/// - [`Refusal::UnauthorizedSigner`] if an authenticated signer is a signer
///   of no chosen rule;
/// - otherwise, in context order, [`Refusal::NoAmount`] if a capped rule's
///   context has no `I128` amount at the cap's `amount_arg`, and
///   [`Refusal::Cap`] if [`check_spend`] refuses the charge.
pub fn check_auth(
    rules: &[Rule],
    records: &[SpendRecord],
    contexts: &[Context],
    choices: &[u32],
    authenticated: &[Signer],
    now: u32,
    generation: u64,
) -> Result<Vec<SpendRecord>, Refusal> {
    if choices.len() != contexts.len() {
        return Err(Refusal::ChoicesMismatch);
    }
    if records.len() != rules.len() {
        return Err(Refusal::RecordsMismatch);
    }
    match check_choices(rules, contexts, choices, authenticated, now, generation) {
        Ok(()) => {
            if !signers_chosen(authenticated, rules, choices) {
                return Err(Refusal::UnauthorizedSigner);
            }
            charge_all(rules, records, contexts, choices, now)
        }
        Err(e) => Err(e),
    }
}
