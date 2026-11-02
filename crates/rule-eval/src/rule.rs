//! Rules and their conditions.

use alloc::vec::Vec;

use crate::bytes::{bytes_copy, bytes_eq, bytes_in, bytes_list_copy};
use crate::context::Context;
use crate::signer::{Signer, signers_copy, signers_met};
use crate::val::{Val, val_copy, val_eq};

/// A condition on the arguments of the call its rule matches. Argument
/// indices count from zero. A missing argument, or an argument of another
/// constructor, makes the condition false.
pub enum Cond {
    /// The argument at this index exists and equals this value.
    ArgEq(u32, Val),
    /// The argument at this index exists, is `I128(v)`, and `v` is at most
    /// this bound.
    ArgI128AtMost(u32, i128),
}

/// A spending cap on the calls a rule allows: at most `limit` spent within
/// `period` consecutive ledgers, each call spending its argument at index
/// `amount_arg`. A cap may be added to a rule only when [`cap_valid`] holds.
pub struct Cap {
    pub limit: i128,
    pub period: u32,
    /// The index of the argument that holds the amount a call spends, an
    /// `I128`.
    pub amount_arg: u32,
}

/// A rule: calls to `contract` whose function is in `functions` and whose
/// arguments satisfy every condition in `conds`, authorized by at least
/// `threshold` distinct signers of `signers`, and spending within `cap` when
/// the rule has one.
pub struct Rule {
    pub contract: Vec<u8>,
    pub functions: Vec<Vec<u8>>,
    pub conds: Vec<Cond>,
    /// The signers whose authentication counts towards `threshold`.
    pub signers: Vec<Signer>,
    /// How many distinct signers of `signers` must be among the
    /// authorization's authenticated signers. 0 puts no requirement on them.
    pub threshold: u32,
    /// The rule's spending cap, if it has one. [`rule_allows`] does not read
    /// it; [`authorize`](crate::authorize) charges it.
    pub cap: Option<Cap>,
}

/// Whether `limits` may be added to a rule: a positive limit and a nonzero
/// period, as [`params_valid`](crate::params_valid) requires of a cap's
/// parameters.
#[must_use]
pub fn cap_valid(limits: &Cap) -> bool {
    limits.limit > 0 && limits.period > 0
}

/// Whether `cond` holds on the arguments `args`.
#[must_use]
pub fn cond_holds(cond: &Cond, args: &[Val]) -> bool {
    match cond {
        Cond::ArgEq(index, expected) => match args.get(*index as usize) {
            Some(v) => val_eq(v, expected),
            None => false,
        },
        Cond::ArgI128AtMost(index, bound) => match args.get(*index as usize) {
            Some(Val::I128(v)) => *v <= *bound,
            _ => false,
        },
    }
}

/// Whether every condition in `conds` holds on `args`.
fn conds_hold(conds: &[Cond], args: &[Val]) -> bool {
    let mut i = 0;
    while i < conds.len() {
        if !cond_holds(&conds[i], args) {
            return false;
        }
        i += 1;
    }
    true
}

/// Whether `r` allows `ctx` under the authorization's `authenticated`
/// signers: it is a call to the rule's contract, its function is in the
/// rule's list, every condition holds on its arguments, and at least the
/// rule's threshold of its distinct signers are authenticated. No rule allows
/// a creation.
#[must_use]
pub fn rule_allows(r: &Rule, ctx: &Context, authenticated: &[Signer]) -> bool {
    match ctx {
        Context::Call {
            contract,
            function,
            args,
        } => {
            bytes_eq(contract, &r.contract)
                && bytes_in(function, &r.functions)
                && conds_hold(&r.conds, args)
                && signers_met(&r.signers, r.threshold, authenticated)
        }
        Context::Create { .. } => false,
    }
}

/// A fresh copy of `cond`.
pub(crate) fn cond_copy(cond: &Cond) -> Cond {
    match cond {
        Cond::ArgEq(index, v) => Cond::ArgEq(*index, val_copy(v)),
        Cond::ArgI128AtMost(index, bound) => Cond::ArgI128AtMost(*index, *bound),
    }
}

/// A fresh copy of `conds`, keeping order.
pub(crate) fn conds_copy(conds: &[Cond]) -> Vec<Cond> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < conds.len() {
        out.push(cond_copy(&conds[i]));
        i += 1;
    }
    out
}

/// A fresh copy of `limits`.
pub(crate) fn cap_copy(limits: &Cap) -> Cap {
    Cap {
        limit: limits.limit,
        period: limits.period,
        amount_arg: limits.amount_arg,
    }
}

/// A fresh copy of a rule's cap.
pub(crate) fn cap_option_copy(limits: &Option<Cap>) -> Option<Cap> {
    if let Some(c) = limits {
        return Some(cap_copy(c));
    }
    None
}

/// A fresh copy of `r`.
pub(crate) fn rule_copy(r: &Rule) -> Rule {
    Rule {
        contract: bytes_copy(&r.contract),
        functions: bytes_list_copy(&r.functions),
        conds: conds_copy(&r.conds),
        signers: signers_copy(&r.signers),
        threshold: r.threshold,
        cap: cap_option_copy(&r.cap),
    }
}
