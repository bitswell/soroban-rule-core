//! Attenuation: the steps a holder may take to narrow a rule set.
//!
//! Each step reads a rule set and returns a new one, or
//! [`AttenuationError::NoSuchRule`] when its rule index is out of range;
//! [`raise_threshold`] also refuses to lower a threshold. The new rule set
//! allows no context, under any authenticated signers, that the original does
//! not. Nothing else is an attenuation step.

use alloc::vec::Vec;

use crate::bytes::{bytes_copy, bytes_list_copy, bytes_list_without};
use crate::rule::{Cond, Rule, cond_copy, conds_copy, rule_copy};
use crate::signer::{Signer, signers_copy, signers_without};

/// Why an attenuation step was refused.
pub enum AttenuationError {
    /// The rule index is not below the rule set's length.
    NoSuchRule,
    /// The new threshold is below the rule's current threshold.
    ThresholdLowered,
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
        let mut r = rule_copy(&rules[i]);
        if i == index {
            r.conds.push(cond_copy(cond));
        }
        out.push(r);
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

/// A copy of `r` without the functions in `functions`.
fn rule_without_functions(r: &Rule, functions: &[Vec<u8>]) -> Rule {
    Rule {
        contract: bytes_copy(&r.contract),
        functions: bytes_list_without(&r.functions, functions),
        conds: conds_copy(&r.conds),
        signers: signers_copy(&r.signers),
        threshold: r.threshold,
    }
}

/// `rules` with every signer in `signers` removed from the signer list of the
/// rule at `index`. The rule's threshold is unchanged.
///
/// # Errors
///
/// [`AttenuationError::NoSuchRule`] if `index` is out of range.
pub fn remove_signers(
    rules: &[Rule],
    index: u32,
    signers: &[Signer],
) -> Result<Vec<Rule>, AttenuationError> {
    let index = index as usize;
    if index >= rules.len() {
        return Err(AttenuationError::NoSuchRule);
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        if i == index {
            out.push(rule_without_signers(&rules[i], signers));
        } else {
            out.push(rule_copy(&rules[i]));
        }
        i += 1;
    }
    Ok(out)
}

/// A copy of `r` without the signers in `signers`.
fn rule_without_signers(r: &Rule, signers: &[Signer]) -> Rule {
    Rule {
        contract: bytes_copy(&r.contract),
        functions: bytes_list_copy(&r.functions),
        conds: conds_copy(&r.conds),
        signers: signers_without(&r.signers, signers),
        threshold: r.threshold,
    }
}

/// `rules` with the threshold of the rule at `index` set to `threshold`.
///
/// # Errors
///
/// [`AttenuationError::NoSuchRule`] if `index` is out of range, and
/// [`AttenuationError::ThresholdLowered`] if `threshold` is below the rule's
/// current threshold.
pub fn raise_threshold(
    rules: &[Rule],
    index: u32,
    threshold: u32,
) -> Result<Vec<Rule>, AttenuationError> {
    let index = index as usize;
    match rules.get(index) {
        Some(r) => {
            if threshold < r.threshold {
                return Err(AttenuationError::ThresholdLowered);
            }
        }
        None => return Err(AttenuationError::NoSuchRule),
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        let mut r = rule_copy(&rules[i]);
        if i == index {
            r.threshold = threshold;
        }
        out.push(r);
        i += 1;
    }
    Ok(out)
}
