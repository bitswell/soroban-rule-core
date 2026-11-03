//! Rules and their conditions.

use alloc::vec::Vec;

use crate::bytes::{bytes_copy, bytes_eq, bytes_in, bytes_list_copy, bytes_starts_with};
use crate::context::Context;
use crate::signer::{Signer, signers_copy, signers_met};
use crate::val::{Val, val_copy, val_eq, val_in, vals_copy};

/// The functions a rule matches on its contract.
pub enum Functions {
    /// Every function except the ones listed. The wildcard, every function
    /// on the contract, lists none; removing functions from a wildcard lists
    /// them here.
    AnyExcept(Vec<Vec<u8>>),
    /// Only the functions listed.
    Only(Vec<Vec<u8>>),
}

/// A condition on the arguments of the call its rule matches. Argument
/// indices count from zero. A missing argument, or an argument of another
/// constructor, makes the condition false.
pub enum Cond {
    /// The argument at this index exists and equals this value.
    ArgEq(u32, Val),
    /// The argument at this index exists, is `I128(v)`, and `v` is at most
    /// this bound.
    ArgI128AtMost(u32, i128),
    /// The argument at this index exists and equals one of these values, each
    /// compared as [`Cond::ArgEq`] compares.
    ArgIn(u32, Vec<Val>),
    /// The argument at this index exists, is `String(s)`, and the first bytes
    /// of `s` are exactly these.
    ArgStrPrefix(u32, Vec<u8>),
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
/// the rule has one. [`authorize`](crate::authorize) also refuses the rule
/// after its `valid_until` ledger and outside its `generation`.
pub struct Rule {
    pub contract: Vec<u8>,
    pub functions: Functions,
    pub conds: Vec<Cond>,
    /// The signers whose authentication counts towards `threshold`.
    pub signers: Vec<Signer>,
    /// How many distinct signers of `signers` must be among the
    /// authorization's authenticated signers. 0 puts no requirement on them.
    pub threshold: u32,
    /// The rule's spending cap, if it has one. [`rule_allows`] does not read
    /// it; [`authorize`](crate::authorize) charges it.
    pub cap: Option<Cap>,
    /// The last ledger the rule authorizes in, if it has one. [`rule_allows`]
    /// does not read it; [`authorize`](crate::authorize) refuses the rule at
    /// any later ledger.
    pub valid_until: Option<u32>,
    /// The generation the rule was issued under, if it has one.
    /// [`rule_allows`] does not read it; [`authorize`](crate::authorize)
    /// refuses the rule when the current generation is another.
    pub generation: Option<u64>,
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
        Cond::ArgIn(index, values) => match args.get(*index as usize) {
            Some(v) => val_in(v, values),
            None => false,
        },
        Cond::ArgStrPrefix(index, prefix) => match args.get(*index as usize) {
            Some(Val::String(s)) => bytes_starts_with(s, prefix),
            _ => false,
        },
    }
}

/// Whether `functions` matches the function named `function`.
#[must_use]
pub fn functions_match(functions: &Functions, function: &[u8]) -> bool {
    match functions {
        Functions::AnyExcept(removed) => !bytes_in(function, removed),
        Functions::Only(listed) => bytes_in(function, listed),
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
/// signers: it is a call to the rule's contract, the rule's functions match
/// its function, every condition holds on its arguments, and at least the
/// rule's threshold of its distinct signers are authenticated. No rule allows
/// a creation. The rule's expiry and generation are not read: this is the
/// view without time or generation that [`authorize`](crate::authorize)
/// refines.
#[must_use]
pub fn rule_allows(r: &Rule, ctx: &Context, authenticated: &[Signer]) -> bool {
    match ctx {
        Context::Call {
            contract,
            function,
            args,
        } => {
            bytes_eq(contract, &r.contract)
                && functions_match(&r.functions, function)
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
        Cond::ArgIn(index, values) => Cond::ArgIn(*index, vals_copy(values)),
        Cond::ArgStrPrefix(index, prefix) => Cond::ArgStrPrefix(*index, bytes_copy(prefix)),
    }
}

/// A fresh copy of `functions`.
pub(crate) fn functions_copy(functions: &Functions) -> Functions {
    match functions {
        Functions::AnyExcept(removed) => Functions::AnyExcept(bytes_list_copy(removed)),
        Functions::Only(listed) => Functions::Only(bytes_list_copy(listed)),
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
        functions: functions_copy(&r.functions),
        conds: conds_copy(&r.conds),
        signers: signers_copy(&r.signers),
        threshold: r.threshold,
        cap: cap_option_copy(&r.cap),
        valid_until: r.valid_until,
        generation: r.generation,
    }
}
