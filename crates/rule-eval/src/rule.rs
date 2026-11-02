//! Rules and their conditions.

use alloc::vec::Vec;

use crate::bytes::{bytes_copy, bytes_eq, bytes_in, bytes_list_copy};
use crate::context::Context;
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

/// A rule: calls to `contract` whose function is in `functions` and whose
/// arguments satisfy every condition in `conds`.
pub struct Rule {
    pub contract: Vec<u8>,
    pub functions: Vec<Vec<u8>>,
    pub conds: Vec<Cond>,
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

/// Whether `rule` allows `context`: it is a call to the rule's contract, its
/// function is in the rule's list, and every condition holds on its
/// arguments. No rule allows a creation.
#[must_use]
pub fn rule_allows(rule: &Rule, context: &Context) -> bool {
    match context {
        Context::Call {
            contract,
            function,
            args,
        } => {
            bytes_eq(contract, &rule.contract)
                && bytes_in(function, &rule.functions)
                && conds_hold(&rule.conds, args)
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

/// A fresh copy of `rule`.
pub(crate) fn rule_copy(rule: &Rule) -> Rule {
    Rule {
        contract: bytes_copy(&rule.contract),
        functions: bytes_list_copy(&rule.functions),
        conds: conds_copy(&rule.conds),
    }
}
