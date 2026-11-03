//! Checks `rule-eval`'s `authorize` against the authorization traces.
//!
//! An authorization trace (see `conformance/README.md`) holds a rule set, the
//! records it starts from, and authorizations, each with the outcome the Lean
//! model computes for it on the records the authorizations before it left.
//! [`check`] runs the authorizations through [`authorize`], keeping the
//! records unchanged after a refusal, and reports the first outcome that
//! differs.

use std::fs;
use std::path::{Path, PathBuf};

use rule_eval::{CapError, Refusal, SpendRecord, authorize};
use serde::Deserialize;

use crate::caps::{JsonRecord, decode_record};
use crate::{
    JsonContext, JsonRule, JsonSigner, decode_context, decode_decimal, decode_rules, decode_signers,
};

/// The authorization trace format version this runner reads.
pub const FORMAT: u32 = 2;

/// One authorization trace file.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Trace {
    pub format: u32,
    pub name: String,
    pub description: String,
    pub rules: Vec<JsonRule>,
    pub start: Vec<JsonRecord>,
    pub authorizations: Vec<JsonAuthorization>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonAuthorization {
    pub batch: Vec<JsonContext>,
    pub choices: Vec<u32>,
    pub authenticated: Vec<JsonSigner>,
    pub now: u32,
    /// The current generation, a decimal `u64`.
    pub generation: String,
    pub expected: Outcome,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum Outcome {
    /// The authorization was accepted: the records after it, one per rule.
    Ok(Vec<JsonRecord>),
    /// The authorization was refused, and the records stay as they were.
    Error(JsonRefusal),
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
#[serde(rename_all = "snake_case")]
pub enum JsonRefusal {
    ChoicesMismatch,
    RecordsMismatch,
    NoSuchRule,
    Expired,
    StaleGeneration,
    NotAllowed,
    UnauthorizedSigner,
    NoAmount,
    CapNegativeAmount,
    CapLedgerBeforeNewest,
    CapOverflow,
    CapLimitExceeded,
    CapHistoryFull,
}

/// Every `*.json` authorization trace in `dir`, sorted by path, each checked
/// to carry its file's name.
///
/// # Errors
///
/// A file that cannot be read or parsed, or whose name differs from its file
/// name.
pub fn load_dir(dir: &Path) -> Result<Vec<(PathBuf, Trace)>, String> {
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
        let trace: Trace =
            serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
        if path.file_stem().and_then(|s| s.to_str()) != Some(trace.name.as_str()) {
            return Err(format!(
                "{}: name {:?} differs from the file name",
                path.display(),
                trace.name
            ));
        }
        out.push((path, trace));
    }
    Ok(out)
}

/// The name `conformance/README.md` gives a refusal of `authorize`.
#[must_use]
pub fn refusal_of(r: &Refusal) -> JsonRefusal {
    match r {
        Refusal::ChoicesMismatch => JsonRefusal::ChoicesMismatch,
        Refusal::RecordsMismatch => JsonRefusal::RecordsMismatch,
        Refusal::NoSuchRule => JsonRefusal::NoSuchRule,
        Refusal::Expired => JsonRefusal::Expired,
        Refusal::StaleGeneration => JsonRefusal::StaleGeneration,
        Refusal::NotAllowed => JsonRefusal::NotAllowed,
        Refusal::UnauthorizedSigner => JsonRefusal::UnauthorizedSigner,
        Refusal::NoAmount => JsonRefusal::NoAmount,
        Refusal::Cap(CapError::NegativeAmount) => JsonRefusal::CapNegativeAmount,
        Refusal::Cap(CapError::LedgerBeforeNewest) => JsonRefusal::CapLedgerBeforeNewest,
        Refusal::Cap(CapError::Overflow) => JsonRefusal::CapOverflow,
        Refusal::Cap(CapError::LimitExceeded) => JsonRefusal::CapLimitExceeded,
        Refusal::Cap(CapError::HistoryFull) => JsonRefusal::CapHistoryFull,
    }
}

/// The entries and total of each record, for comparison.
type Parts = Vec<(Vec<(u32, i128)>, i128)>;

fn parts(records: &[SpendRecord]) -> Parts {
    records
        .iter()
        .map(|r| {
            (
                r.history.iter().map(|e| (e.ledger, e.amount)).collect(),
                r.total,
            )
        })
        .collect()
}

fn decode_records(records: &[JsonRecord]) -> Result<Vec<SpendRecord>, String> {
    records.iter().map(decode_record).collect()
}

/// Runs `trace` through `rule-eval`.
///
/// # Errors
///
/// A field that does not decode, or the first result `rule-eval` computes
/// differently from the trace.
pub fn check(trace: &Trace) -> Result<(), String> {
    if trace.format != FORMAT {
        return Err(format!(
            "format {} where this runner reads {FORMAT}",
            trace.format
        ));
    }
    let rules = decode_rules(&trace.rules)?;
    let mut records = decode_records(&trace.start)?;
    for (i, a) in trace.authorizations.iter().enumerate() {
        let batch = a
            .batch
            .iter()
            .map(decode_context)
            .collect::<Result<Vec<_>, _>>()?;
        let authenticated = decode_signers(&a.authenticated)?;
        let generation: u64 = decode_decimal(&a.generation)?;
        let got = authorize(
            &rules,
            &records,
            &batch,
            &a.choices,
            &authenticated,
            a.now,
            generation,
        );
        match (got, &a.expected) {
            (Ok(out), Outcome::Ok(want)) => {
                let want = decode_records(want)?;
                if parts(&out) != parts(&want) {
                    return Err(format!(
                        "authorization {i}: records {:?} where the trace has {:?}",
                        parts(&out),
                        parts(&want)
                    ));
                }
                records = out;
            }
            (Err(e), Outcome::Error(want)) => {
                if refusal_of(&e) != *want {
                    return Err(format!(
                        "authorization {i}: refused with {:?} where the trace has {want:?}",
                        refusal_of(&e)
                    ));
                }
            }
            (Ok(out), Outcome::Error(want)) => {
                return Err(format!(
                    "authorization {i}: accepted with {:?} where the trace refuses with {want:?}",
                    parts(&out)
                ));
            }
            (Err(e), Outcome::Ok(_)) => {
                return Err(format!(
                    "authorization {i}: refused with {:?} where the trace accepts",
                    refusal_of(&e)
                ));
            }
        }
    }
    Ok(())
}
