//! Attenuation: the steps a holder may take to narrow a rule set.
//!
//! Each step reads a rule set and returns a new one, or
//! [`AttenuationError::NoSuchRule`] when its rule index is out of range;
//! [`raise_threshold`] also refuses to lower a threshold, the three cap steps
//! refuse what would widen or invalidate a cap, and [`lower_valid_until`]
//! refuses to extend a rule's validity. No step changes a rule's
//! generation. The new rule set allows
//! no context, under any authenticated signers, that the original does not,
//! and accepts no run of authorizations that the original does not (see
//! [`authorize`](crate::authorize)). Nothing else is an attenuation step.

use alloc::vec::Vec;

use crate::bytes::{
    bytes_copy, bytes_list_copy, bytes_list_extend, bytes_list_within, bytes_list_without,
};
use crate::rule::{
    Cap, Cond, Functions, Rule, auth_root_copy, cap_copy, cap_option_copy, cap_valid, cond_copy,
    conds_copy, functions_copy, rule_copy,
};
use crate::signer::{Signer, signers_copy, signers_without};

/// Why an attenuation step was refused.
pub enum AttenuationError {
    /// The rule index is not below the rule set's length.
    NoSuchRule,
    /// The new threshold is below the rule's current threshold.
    ThresholdLowered,
    /// The rule already has a cap.
    CapPresent,
    /// The rule has no cap.
    NoCap,
    /// The cap would not be valid: its limit is not positive or its period
    /// is 0.
    InvalidCap,
    /// The new limit is above the rule's current limit.
    LimitRaised,
    /// The new period is below the rule's current period.
    PeriodShortened,
    /// The new last ledger is after the rule's current one.
    ValidUntilRaised,
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

/// `rules` with every function in `functions` removed from the functions of
/// the rule at `index`. A list loses the functions; a wildcard,
/// [`Functions::AnyExcept`], adds them to the functions it excludes.
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

/// `current` without the functions in `functions`.
fn functions_without(current: &Functions, functions: &[Vec<u8>]) -> Functions {
    match current {
        Functions::AnyExcept(removed) => {
            Functions::AnyExcept(bytes_list_extend(bytes_list_copy(removed), functions))
        }
        Functions::Only(listed) => Functions::Only(bytes_list_without(listed, functions)),
    }
}

/// A copy of `r` without the functions in `functions`.
fn rule_without_functions(r: &Rule, functions: &[Vec<u8>]) -> Rule {
    Rule {
        contract: bytes_copy(&r.contract),
        functions: functions_without(&r.functions, functions),
        conds: conds_copy(&r.conds),
        signers: signers_copy(&r.signers),
        threshold: r.threshold,
        cap: cap_option_copy(&r.cap),
        valid_until: r.valid_until,
        generation: r.generation,
        auth_root: auth_root_copy(&r.auth_root),
    }
}

/// `rules` with the functions of the rule at `index` restricted to those in
/// `functions`: a wildcard becomes the list of `functions` it does not
/// exclude, and a list keeps the functions that are also in `functions`.
///
/// # Errors
///
/// [`AttenuationError::NoSuchRule`] if `index` is out of range.
pub fn restrict_functions(
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
            out.push(rule_within_functions(&rules[i], functions));
        } else {
            out.push(rule_copy(&rules[i]));
        }
        i += 1;
    }
    Ok(out)
}

/// `current` restricted to the functions in `functions`.
fn functions_within(current: &Functions, functions: &[Vec<u8>]) -> Functions {
    match current {
        Functions::AnyExcept(removed) => Functions::Only(bytes_list_without(functions, removed)),
        Functions::Only(listed) => Functions::Only(bytes_list_within(listed, functions)),
    }
}

/// A copy of `r` with its functions restricted to those in `functions`.
fn rule_within_functions(r: &Rule, functions: &[Vec<u8>]) -> Rule {
    Rule {
        contract: bytes_copy(&r.contract),
        functions: functions_within(&r.functions, functions),
        conds: conds_copy(&r.conds),
        signers: signers_copy(&r.signers),
        threshold: r.threshold,
        cap: cap_option_copy(&r.cap),
        valid_until: r.valid_until,
        generation: r.generation,
        auth_root: auth_root_copy(&r.auth_root),
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
        functions: functions_copy(&r.functions),
        conds: conds_copy(&r.conds),
        signers: signers_without(&r.signers, signers),
        threshold: r.threshold,
        cap: cap_option_copy(&r.cap),
        valid_until: r.valid_until,
        generation: r.generation,
        auth_root: auth_root_copy(&r.auth_root),
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

/// `rules` with the cap `new_cap` added to the rule at `index`.
///
/// # Errors
///
/// [`AttenuationError::NoSuchRule`] if `index` is out of range,
/// [`AttenuationError::CapPresent`] if the rule already has a cap, and
/// [`AttenuationError::InvalidCap`] if `new_cap` is not valid
/// ([`cap_valid`]).
pub fn add_cap(rules: &[Rule], index: u32, new_cap: &Cap) -> Result<Vec<Rule>, AttenuationError> {
    let index = index as usize;
    match rules.get(index) {
        Some(Rule { cap: None, .. }) => {}
        Some(_) => return Err(AttenuationError::CapPresent),
        None => return Err(AttenuationError::NoSuchRule),
    }
    if !cap_valid(new_cap) {
        return Err(AttenuationError::InvalidCap);
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        let mut r = rule_copy(&rules[i]);
        if i == index {
            r.cap = Some(cap_copy(new_cap));
        }
        out.push(r);
        i += 1;
    }
    Ok(out)
}

/// `rules` with the limit of the cap of the rule at `index` set to `limit`.
///
/// # Errors
///
/// [`AttenuationError::NoSuchRule`] if `index` is out of range,
/// [`AttenuationError::NoCap`] if the rule has no cap,
/// [`AttenuationError::LimitRaised`] if `limit` is above the cap's current
/// limit, and [`AttenuationError::InvalidCap`] if `limit` is not positive.
pub fn lower_cap_limit(
    rules: &[Rule],
    index: u32,
    limit: i128,
) -> Result<Vec<Rule>, AttenuationError> {
    let index = index as usize;
    match rules.get(index) {
        Some(r) => match &r.cap {
            Some(c) => {
                if limit > c.limit {
                    return Err(AttenuationError::LimitRaised);
                }
                if limit <= 0 {
                    return Err(AttenuationError::InvalidCap);
                }
            }
            None => return Err(AttenuationError::NoCap),
        },
        None => return Err(AttenuationError::NoSuchRule),
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        let mut r = rule_copy(&rules[i]);
        if i == index
            && let Some(c) = &mut r.cap
        {
            c.limit = limit;
        }
        out.push(r);
        i += 1;
    }
    Ok(out)
}

/// `rules` with the period of the cap of the rule at `index` set to `period`.
///
/// # Errors
///
/// [`AttenuationError::NoSuchRule`] if `index` is out of range,
/// [`AttenuationError::NoCap`] if the rule has no cap, and
/// [`AttenuationError::PeriodShortened`] if `period` is below the cap's
/// current period.
pub fn lengthen_cap_period(
    rules: &[Rule],
    index: u32,
    period: u32,
) -> Result<Vec<Rule>, AttenuationError> {
    let index = index as usize;
    match rules.get(index) {
        Some(r) => match &r.cap {
            Some(c) => {
                if period < c.period {
                    return Err(AttenuationError::PeriodShortened);
                }
            }
            None => return Err(AttenuationError::NoCap),
        },
        None => return Err(AttenuationError::NoSuchRule),
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        let mut r = rule_copy(&rules[i]);
        if i == index
            && let Some(c) = &mut r.cap
        {
            c.period = period;
        }
        out.push(r);
        i += 1;
    }
    Ok(out)
}

/// Whether setting the last ledger of `r` to `valid_until` would move it
/// later: `r` has a last ledger and `valid_until` is after it.
fn extends_validity(r: &Rule, valid_until: u32) -> bool {
    match r.valid_until {
        Some(current) => valid_until > current,
        None => false,
    }
}

/// `rules` with the last ledger of the rule at `index` set to `valid_until`:
/// added to a rule without one, or moved earlier.
///
/// # Errors
///
/// [`AttenuationError::NoSuchRule`] if `index` is out of range, and
/// [`AttenuationError::ValidUntilRaised`] if the rule has a last ledger and
/// `valid_until` is after it.
pub fn lower_valid_until(
    rules: &[Rule],
    index: u32,
    valid_until: u32,
) -> Result<Vec<Rule>, AttenuationError> {
    let index = index as usize;
    match rules.get(index) {
        Some(r) => {
            if extends_validity(r, valid_until) {
                return Err(AttenuationError::ValidUntilRaised);
            }
        }
        None => return Err(AttenuationError::NoSuchRule),
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        let mut r = rule_copy(&rules[i]);
        if i == index {
            r.valid_until = Some(valid_until);
        }
        out.push(r);
        i += 1;
    }
    Ok(out)
}
