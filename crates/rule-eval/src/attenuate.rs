//! Attenuation: the steps a holder may take to narrow a rule set.
//!
//! Each step reads a rule set and returns a new one, or
//! [`AttenuationError::NoSuchRule`] when its rule index is out of range. The
//! new rule set allows no context the original does not. Nothing else is an
//! attenuation step.

use alloc::vec::Vec;

use crate::bytes::{bytes_copy, bytes_list_without};
use crate::rule::{Cond, Rule, cond_copy, conds_copy, rule_copy};

/// Why an attenuation step was refused.
pub enum AttenuationError {
    /// The rule index is not below the rule set's length.
    NoSuchRule,
}

/// `rules` without the rule at `index`.
///
/// # Errors
///
/// [`AttenuationError::NoSuchRule`] if `index` is out of range.
pub fn drop_rule(rules: &[Rule], index: u32) -> Result<Vec<Rule>, AttenuationError> {
    let index = index as usize;
    if index >= rules.len() {
        return Err(AttenuationError::NoSuchRule);
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        if i != index {
            out.push(rule_copy(&rules[i]));
        }
        i += 1;
    }
    Ok(out)
}

/// `rules` with `cond` appended to the conditions of the rule at `index`.
///
/// # Errors
///
/// [`AttenuationError::NoSuchRule`] if `index` is out of range.
pub fn add_cond(rules: &[Rule], index: u32, cond: &Cond) -> Result<Vec<Rule>, AttenuationError> {
    let index = index as usize;
    if index >= rules.len() {
        return Err(AttenuationError::NoSuchRule);
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        let mut rule = rule_copy(&rules[i]);
        if i == index {
            rule.conds.push(cond_copy(cond));
        }
        out.push(rule);
        i += 1;
    }
    Ok(out)
}

/// `rules` with every function in `functions` removed from the function list
/// of the rule at `index`.
///
/// # Errors
///
/// [`AttenuationError::NoSuchRule`] if `index` is out of range.
pub fn remove_functions(
    rules: &[Rule],
    index: u32,
    functions: &[Vec<u8>],
) -> Result<Vec<Rule>, AttenuationError> {
    let index = index as usize;
    if index >= rules.len() {
        return Err(AttenuationError::NoSuchRule);
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        if i == index {
            out.push(rule_without_functions(&rules[i], functions));
        } else {
            out.push(rule_copy(&rules[i]));
        }
        i += 1;
    }
    Ok(out)
}

/// A copy of `rule` without the functions in `functions`.
fn rule_without_functions(rule: &Rule, functions: &[Vec<u8>]) -> Rule {
    Rule {
        contract: bytes_copy(&rule.contract),
        functions: bytes_list_without(&rule.functions, functions),
        conds: conds_copy(&rule.conds),
    }
}
