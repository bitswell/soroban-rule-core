//! Checks `rule-eval` against the conformance vectors.
//!
//! A vector (see `conformance/README.md`) holds a rule set, a batch of
//! contexts, the signers the batch's authorization authenticated, attenuation
//! step lists, and the results the Lean model computes for them. [`check`]
//! decodes a vector into `rule-eval`'s types, evaluates it with `rule-eval`,
//! and reports the first result that differs. [`caps`] checks the cap traces,
//! [`authorize`] the authorization traces, [`budget`] the budget traces and
//! [`documents`] the document traces. [`soroban`] decodes the Soroban vectors
//! and checks `soroban-facade` against the value and context vectors and the
//! storage traces.

use std::fs;
use std::path::{Path, PathBuf};

use rule_eval::{
    AttenuationError, Cap, Cond, Context, Functions, Rule, Signer, Val, add_cap, add_cond, allows,
    allows_all, drop_rule, lengthen_cap_period, lower_cap_limit, lower_valid_until,
    raise_threshold, remove_functions, remove_signers, restrict_functions, signer_eq, val_eq,
};
use serde::Deserialize;

pub mod authorize;
pub mod budget;
pub mod caps;
pub mod documents;
pub mod soroban;

/// The vector format version this runner reads.
pub const FORMAT: u32 = 4;

/// One vector file.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Vector {
    pub format: u32,
    pub name: String,
    pub description: String,
    pub rules: Vec<JsonRule>,
    pub batch: Vec<JsonContext>,
    pub authenticated: Vec<JsonSigner>,
    pub expected: Verdicts,
    pub attenuations: Vec<AttenuationCase>,
}

/// A rule set's verdict on each context of the batch, and on the whole batch.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Verdicts {
    pub allows: Vec<bool>,
    pub allows_all: bool,
}

/// Steps applied in order to the vector's rule set, and their result.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AttenuationCase {
    pub steps: Vec<JsonStep>,
    pub expected: Outcome,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum Outcome {
    /// Every step was taken: the resulting rule set and its verdicts on the
    /// vector's batch.
    Ok {
        rules: Vec<JsonRule>,
        allows: Vec<bool>,
        allows_all: bool,
    },
    /// A step was refused.
    Error(JsonError),
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
#[serde(rename_all = "snake_case")]
pub enum JsonError {
    NoSuchRule,
    ThresholdLowered,
    CapPresent,
    NoCap,
    InvalidCap,
    LimitRaised,
    PeriodShortened,
    ValidUntilRaised,
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct JsonRule {
    pub contract: String,
    pub functions: JsonFunctions,
    pub conds: Vec<JsonCond>,
    pub signers: Vec<JsonSigner>,
    pub threshold: u32,
    /// The rule's cap, or `null` when it has none.
    pub cap: Option<JsonCap>,
    /// The rule's last ledger, or `null` when it has none.
    pub valid_until: Option<u32>,
    /// The generation the rule was issued under, a decimal `u64`, or `null`.
    pub generation: Option<String>,
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonFunctions {
    Only(Vec<String>),
    AnyExcept(Vec<String>),
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct JsonCap {
    pub limit: String,
    pub period: u32,
    pub amount_arg: u32,
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonSigner {
    Delegated { address: String },
    External { verifier: String, key: String },
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonContext {
    Call {
        contract: String,
        function: String,
        args: Vec<JsonVal>,
    },
    Create {
        wasm_hash: String,
    },
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonCond {
    ArgEq {
        index: u32,
        value: JsonVal,
    },
    #[serde(rename = "arg_i128_at_most")]
    ArgI128AtMost {
        index: u32,
        bound: String,
    },
    ArgIn {
        index: u32,
        values: Vec<JsonVal>,
    },
    ArgStrPrefix {
        index: u32,
        prefix: String,
    },
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonVal {
    I128(String),
    U64(String),
    Bool(bool),
    Bytes(String),
    Address(String),
    Symbol(String),
    String(String),
    Other(String),
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonStep {
    DropRule {
        index: u32,
    },
    AddCond {
        index: u32,
        cond: JsonCond,
    },
    RemoveFunctions {
        index: u32,
        functions: Vec<String>,
    },
    RestrictFunctions {
        index: u32,
        functions: Vec<String>,
    },
    RemoveSigners {
        index: u32,
        signers: Vec<JsonSigner>,
    },
    RaiseThreshold {
        index: u32,
        threshold: u32,
    },
    AddCap {
        index: u32,
        cap: JsonCap,
    },
    LowerCapLimit {
        index: u32,
        limit: String,
    },
    LengthenCapPeriod {
        index: u32,
        period: u32,
    },
    LowerValidUntil {
        index: u32,
        valid_until: u32,
    },
}

/// An attenuation step in `rule-eval`'s types.
pub enum Step {
    DropRule(u32),
    AddCond(u32, Cond),
    RemoveFunctions(u32, Vec<Vec<u8>>),
    RestrictFunctions(u32, Vec<Vec<u8>>),
    RemoveSigners(u32, Vec<Signer>),
    RaiseThreshold(u32, u32),
    AddCap(u32, Cap),
    LowerCapLimit(u32, i128),
    LengthenCapPeriod(u32, u32),
    LowerValidUntil(u32, u32),
}

// ---------------------------------------------------------------------------
// Loading.

/// Every `*.json` file in `dir`, parsed, in file-name order. A vector's
/// `name` must be its file name without `.json`.
///
/// # Errors
///
/// A message naming the file that cannot be read or parsed.
pub fn load_dir(dir: &Path) -> Result<Vec<(PathBuf, Vector)>, String> {
    let entries = fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let mut paths = Vec::new();
    for entry in entries {
        let path = entry.map_err(|e| format!("{}: {e}", dir.display()))?.path();
        if path.extension().is_some_and(|x| x == "json") {
            paths.push(path);
        }
    }
    paths.sort();
    let mut out = Vec::new();
    for path in paths {
        let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let vector: Vector =
            serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
        if path.file_stem().and_then(|s| s.to_str()) != Some(vector.name.as_str()) {
            return Err(format!(
                "{}: name {:?} differs from the file name",
                path.display(),
                vector.name
            ));
        }
        out.push((path, vector));
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Decoding.

/// Lowercase hexadecimal, two digits per byte.
///
/// # Errors
///
/// If `s` has odd length or a character other than `0-9a-f`.
pub fn decode_hex(s: &str) -> Result<Vec<u8>, String> {
    fn digit(c: u8) -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            _ => None,
        }
    }
    let raw = s.as_bytes();
    if !raw.len().is_multiple_of(2) {
        return Err(format!("odd-length hex {s:?}"));
    }
    raw.chunks(2)
        .map(|pair| match (digit(pair[0]), digit(pair[1])) {
            (Some(hi), Some(lo)) => Ok(hi * 16 + lo),
            _ => Err(format!("not lowercase hex: {s:?}")),
        })
        .collect()
}

/// A decimal integer: an optional `-` and at least one digit, nothing else.
pub(crate) fn decode_decimal<T: std::str::FromStr>(s: &str) -> Result<T, String> {
    let digits = s.strip_prefix('-').unwrap_or(s);
    if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
        return Err(format!("not a decimal integer: {s:?}"));
    }
    s.parse().map_err(|_| format!("out of range: {s:?}"))
}

/// # Errors
///
/// If a payload is not lowercase hex or an integer is malformed or out of
/// range.
pub fn decode_val(v: &JsonVal) -> Result<Val, String> {
    Ok(match v {
        JsonVal::I128(x) => Val::I128(decode_decimal(x)?),
        JsonVal::U64(x) => Val::U64(decode_decimal(x)?),
        JsonVal::Bool(x) => Val::Bool(*x),
        JsonVal::Bytes(x) => Val::Bytes(decode_hex(x)?),
        JsonVal::Address(x) => Val::Address(decode_hex(x)?),
        JsonVal::Symbol(x) => Val::Symbol(decode_hex(x)?),
        JsonVal::String(x) => Val::String(decode_hex(x)?),
        JsonVal::Other(x) => Val::Other(decode_hex(x)?),
    })
}

/// # Errors
///
/// As [`decode_val`].
pub fn decode_context(c: &JsonContext) -> Result<Context, String> {
    Ok(match c {
        JsonContext::Call {
            contract,
            function,
            args,
        } => Context::Call {
            contract: decode_hex(contract)?,
            function: decode_hex(function)?,
            args: args.iter().map(decode_val).collect::<Result<_, _>>()?,
        },
        JsonContext::Create { wasm_hash } => Context::Create {
            wasm_hash: decode_hex(wasm_hash)?,
        },
    })
}

/// # Errors
///
/// As [`decode_val`].
pub fn decode_cond(c: &JsonCond) -> Result<Cond, String> {
    Ok(match c {
        JsonCond::ArgEq { index, value } => Cond::ArgEq(*index, decode_val(value)?),
        JsonCond::ArgI128AtMost { index, bound } => {
            Cond::ArgI128AtMost(*index, decode_decimal(bound)?)
        }
        JsonCond::ArgIn { index, values } => Cond::ArgIn(
            *index,
            values.iter().map(decode_val).collect::<Result<_, _>>()?,
        ),
        JsonCond::ArgStrPrefix { index, prefix } => Cond::ArgStrPrefix(*index, decode_hex(prefix)?),
    })
}

/// # Errors
///
/// If a function name is not lowercase hex.
pub fn decode_functions(f: &JsonFunctions) -> Result<Functions, String> {
    Ok(match f {
        JsonFunctions::Only(listed) => Functions::Only(decode_hex_list(listed)?),
        JsonFunctions::AnyExcept(removed) => Functions::AnyExcept(decode_hex_list(removed)?),
    })
}

/// # Errors
///
/// If a byte string is not lowercase hex.
pub fn decode_signer(s: &JsonSigner) -> Result<Signer, String> {
    Ok(match s {
        JsonSigner::Delegated { address } => Signer::Delegated(decode_hex(address)?),
        JsonSigner::External { verifier, key } => {
            Signer::External(decode_hex(verifier)?, decode_hex(key)?)
        }
    })
}

/// # Errors
///
/// As [`decode_signer`].
pub fn decode_signers(list: &[JsonSigner]) -> Result<Vec<Signer>, String> {
    list.iter().map(decode_signer).collect()
}

/// # Errors
///
/// If the limit is not a decimal `i128`.
pub fn decode_cap(c: &JsonCap) -> Result<Cap, String> {
    Ok(Cap {
        limit: decode_decimal(&c.limit)?,
        period: c.period,
        amount_arg: c.amount_arg,
    })
}

/// # Errors
///
/// As [`decode_val`] and [`decode_cap`].
pub fn decode_rules(rules: &[JsonRule]) -> Result<Vec<Rule>, String> {
    rules
        .iter()
        .map(|r| {
            Ok(Rule {
                contract: decode_hex(&r.contract)?,
                functions: decode_functions(&r.functions)?,
                conds: r.conds.iter().map(decode_cond).collect::<Result<_, _>>()?,
                signers: decode_signers(&r.signers)?,
                threshold: r.threshold,
                cap: r.cap.as_ref().map(decode_cap).transpose()?,
                valid_until: r.valid_until,
                generation: r.generation.as_deref().map(decode_decimal).transpose()?,
            })
        })
        .collect()
}

fn decode_hex_list(list: &[String]) -> Result<Vec<Vec<u8>>, String> {
    list.iter().map(|s| decode_hex(s)).collect()
}

/// # Errors
///
/// As [`decode_val`].
pub fn decode_step(s: &JsonStep) -> Result<Step, String> {
    Ok(match s {
        JsonStep::DropRule { index } => Step::DropRule(*index),
        JsonStep::AddCond { index, cond } => Step::AddCond(*index, decode_cond(cond)?),
        JsonStep::RemoveFunctions { index, functions } => {
            Step::RemoveFunctions(*index, decode_hex_list(functions)?)
        }
        JsonStep::RestrictFunctions { index, functions } => {
            Step::RestrictFunctions(*index, decode_hex_list(functions)?)
        }
        JsonStep::RemoveSigners { index, signers } => {
            Step::RemoveSigners(*index, decode_signers(signers)?)
        }
        JsonStep::RaiseThreshold { index, threshold } => Step::RaiseThreshold(*index, *threshold),
        JsonStep::AddCap { index, cap } => Step::AddCap(*index, decode_cap(cap)?),
        JsonStep::LowerCapLimit { index, limit } => {
            Step::LowerCapLimit(*index, decode_decimal(limit)?)
        }
        JsonStep::LengthenCapPeriod { index, period } => Step::LengthenCapPeriod(*index, *period),
        JsonStep::LowerValidUntil { index, valid_until } => {
            Step::LowerValidUntil(*index, *valid_until)
        }
    })
}

// ---------------------------------------------------------------------------
// Checking.

/// Apply `steps` to `rules` in order with `rule-eval`, stopping at the first
/// refused step.
///
/// # Errors
///
/// The error of the first refused step.
pub fn attenuate_all(rules: Vec<Rule>, steps: &[Step]) -> Result<Vec<Rule>, AttenuationError> {
    let mut current = rules;
    for step in steps {
        current = match step {
            Step::DropRule(i) => drop_rule(&current, *i)?,
            Step::AddCond(i, cond) => add_cond(&current, *i, cond)?,
            Step::RemoveFunctions(i, fs) => remove_functions(&current, *i, fs)?,
            Step::RestrictFunctions(i, fs) => restrict_functions(&current, *i, fs)?,
            Step::RemoveSigners(i, ss) => remove_signers(&current, *i, ss)?,
            Step::RaiseThreshold(i, k) => raise_threshold(&current, *i, *k)?,
            Step::AddCap(i, c) => add_cap(&current, *i, c)?,
            Step::LowerCapLimit(i, limit) => lower_cap_limit(&current, *i, *limit)?,
            Step::LengthenCapPeriod(i, period) => lengthen_cap_period(&current, *i, *period)?,
            Step::LowerValidUntil(i, last) => lower_valid_until(&current, *i, *last)?,
        };
    }
    Ok(current)
}

fn cond_eq(p: &Cond, q: &Cond) -> bool {
    match (p, q) {
        (Cond::ArgEq(i, v), Cond::ArgEq(j, w)) => i == j && val_eq(v, w),
        (Cond::ArgI128AtMost(i, n), Cond::ArgI128AtMost(j, m)) => i == j && n == m,
        (Cond::ArgIn(i, vs), Cond::ArgIn(j, ws)) => {
            i == j && vs.len() == ws.len() && vs.iter().zip(ws).all(|(v, w)| val_eq(v, w))
        }
        (Cond::ArgStrPrefix(i, p), Cond::ArgStrPrefix(j, q)) => i == j && p == q,
        _ => false,
    }
}

fn functions_eq(p: &Functions, q: &Functions) -> bool {
    match (p, q) {
        (Functions::Only(x), Functions::Only(y))
        | (Functions::AnyExcept(x), Functions::AnyExcept(y)) => x == y,
        _ => false,
    }
}

fn cap_eq(p: Option<&Cap>, q: Option<&Cap>) -> bool {
    match (p, q) {
        (None, None) => true,
        (Some(p), Some(q)) => {
            p.limit == q.limit && p.period == q.period && p.amount_arg == q.amount_arg
        }
        _ => false,
    }
}

/// The name `conformance/README.md` gives a refusal of an attenuation step.
#[must_use]
pub fn error_of(e: &AttenuationError) -> JsonError {
    match e {
        AttenuationError::NoSuchRule => JsonError::NoSuchRule,
        AttenuationError::ThresholdLowered => JsonError::ThresholdLowered,
        AttenuationError::CapPresent => JsonError::CapPresent,
        AttenuationError::NoCap => JsonError::NoCap,
        AttenuationError::InvalidCap => JsonError::InvalidCap,
        AttenuationError::LimitRaised => JsonError::LimitRaised,
        AttenuationError::PeriodShortened => JsonError::PeriodShortened,
        AttenuationError::ValidUntilRaised => JsonError::ValidUntilRaised,
    }
}

/// Structural equality: same contract, same functions (the same kind, the
/// same names in the same order), same conditions in the same order, same
/// signers in the same order, same threshold, same cap, same last ledger, same
/// generation.
#[must_use]
pub fn rules_eq(xs: &[Rule], ys: &[Rule]) -> bool {
    xs.len() == ys.len()
        && xs.iter().zip(ys).all(|(x, y)| {
            x.contract == y.contract
                && functions_eq(&x.functions, &y.functions)
                && x.conds.len() == y.conds.len()
                && x.conds.iter().zip(&y.conds).all(|(p, q)| cond_eq(p, q))
                && x.signers.len() == y.signers.len()
                && x.signers
                    .iter()
                    .zip(&y.signers)
                    .all(|(p, q)| signer_eq(p, q))
                && x.threshold == y.threshold
                && cap_eq(x.cap.as_ref(), y.cap.as_ref())
                && x.valid_until == y.valid_until
                && x.generation == y.generation
        })
}

fn check_verdicts(
    what: &str,
    rules: &[Rule],
    batch: &[Context],
    authenticated: &[Signer],
    expected_allows: &[bool],
    expected_allows_all: bool,
) -> Result<(), String> {
    if expected_allows.len() != batch.len() {
        return Err(format!(
            "{what}: {} expected verdicts for {} contexts",
            expected_allows.len(),
            batch.len()
        ));
    }
    for (k, (context, &expected)) in batch.iter().zip(expected_allows).enumerate() {
        let got = allows(rules, context, authenticated);
        if got != expected {
            return Err(format!(
                "{what}: allows(batch[{k}]) is {got}, expected {expected}"
            ));
        }
    }
    let got = allows_all(rules, batch, authenticated);
    if got != expected_allows_all {
        return Err(format!(
            "{what}: allows_all is {got}, expected {expected_allows_all}"
        ));
    }
    Ok(())
}

/// Evaluate `vector` with `rule-eval` and compare every result with the
/// vector's expected one.
///
/// # Errors
///
/// A message describing the first malformed field or differing result.
pub fn check(vector: &Vector) -> Result<(), String> {
    if vector.format != FORMAT {
        return Err(format!(
            "format {} (this runner reads {FORMAT})",
            vector.format
        ));
    }
    let rules = decode_rules(&vector.rules)?;
    let batch = vector
        .batch
        .iter()
        .map(decode_context)
        .collect::<Result<Vec<_>, _>>()?;
    let authenticated = decode_signers(&vector.authenticated)?;
    check_verdicts(
        "rules",
        &rules,
        &batch,
        &authenticated,
        &vector.expected.allows,
        vector.expected.allows_all,
    )?;
    for (k, case) in vector.attenuations.iter().enumerate() {
        let what = format!("attenuations[{k}]");
        let steps = case
            .steps
            .iter()
            .map(decode_step)
            .collect::<Result<Vec<_>, _>>()?;
        let got = attenuate_all(decode_rules(&vector.rules)?, &steps);
        match (got, &case.expected) {
            (
                Ok(got),
                Outcome::Ok {
                    rules: expected,
                    allows,
                    allows_all,
                },
            ) => {
                if !rules_eq(&got, &decode_rules(expected)?) {
                    return Err(format!("{what}: the resulting rule set differs"));
                }
                check_verdicts(&what, &got, &batch, &authenticated, allows, *allows_all)?;
            }
            (Err(e), Outcome::Error(want)) => {
                if error_of(&e) != *want {
                    return Err(format!(
                        "{what}: a step was refused with {:?}, expected {want:?}",
                        error_of(&e)
                    ));
                }
            }
            (Ok(_), Outcome::Error(_)) => {
                return Err(format!("{what}: the steps were taken, expected a refusal"));
            }
            (Err(e), Outcome::Ok { .. }) => {
                return Err(format!(
                    "{what}: a step was refused with {:?}, expected a result",
                    error_of(&e)
                ));
            }
        }
    }
    Ok(())
}
