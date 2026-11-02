//! Checks `rule-eval`'s spending-cap check against the cap traces.
//!
//! A cap trace (see `conformance/README.md`) holds a cap, a starting record,
//! and calls, each with the outcome the Lean model computes for it on the
//! record the calls before it left. [`check`] runs the calls through
//! [`check_spend`], keeping the record unchanged after a refusal, and reports
//! the first outcome that differs.

use std::fs;
use std::path::{Path, PathBuf};

use rule_eval::{CapError, CapParams, SpendEntry, SpendRecord, check_spend, params_valid};
use serde::Deserialize;

use crate::decode_decimal;

/// The cap trace format version this runner reads.
pub const FORMAT: u32 = 1;

/// One cap trace file.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Trace {
    pub format: u32,
    pub name: String,
    pub description: String,
    pub limit: String,
    pub period: u32,
    pub params_valid: bool,
    pub start: JsonRecord,
    pub calls: Vec<JsonCall>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonRecord {
    pub history: Vec<JsonEntry>,
    pub total: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonEntry {
    pub ledger: u32,
    pub amount: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonCall {
    pub now: u32,
    pub amount: String,
    pub expected: Outcome,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum Outcome {
    /// The spend was accepted: the record after it.
    Ok(JsonRecord),
    /// The spend was refused, and the record stays as it was.
    Error(JsonCapError),
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
#[serde(rename_all = "snake_case")]
pub enum JsonCapError {
    NegativeAmount,
    LedgerBeforeNewest,
    Overflow,
    LimitExceeded,
    HistoryFull,
}

/// Every `*.json` cap trace in `dir`, sorted by path, each checked to carry
/// its file's name.
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

/// `r` as a `rule-eval` record.
///
/// # Errors
///
/// An amount or total that is not a decimal `i128`.
pub fn decode_record(r: &JsonRecord) -> Result<SpendRecord, String> {
    let mut history = Vec::new();
    for e in &r.history {
        history.push(SpendEntry {
            ledger: e.ledger,
            amount: decode_decimal(&e.amount)?,
        });
    }
    Ok(SpendRecord {
        history,
        total: decode_decimal(&r.total)?,
    })
}

fn error_of(e: &CapError) -> JsonCapError {
    match e {
        CapError::NegativeAmount => JsonCapError::NegativeAmount,
        CapError::LedgerBeforeNewest => JsonCapError::LedgerBeforeNewest,
        CapError::Overflow => JsonCapError::Overflow,
        CapError::LimitExceeded => JsonCapError::LimitExceeded,
        CapError::HistoryFull => JsonCapError::HistoryFull,
    }
}

/// The entries and total of `r`, for comparison.
fn parts(r: &SpendRecord) -> (Vec<(u32, i128)>, i128) {
    (
        r.history.iter().map(|e| (e.ledger, e.amount)).collect(),
        r.total,
    )
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
    let limit: i128 = decode_decimal(&trace.limit)?;
    let params = CapParams {
        limit,
        period: trace.period,
    };
    if params_valid(&params) != trace.params_valid {
        return Err(format!(
            "params_valid is {} where the trace has {}",
            params_valid(&params),
            trace.params_valid
        ));
    }
    let mut record = decode_record(&trace.start)?;
    for (i, call) in trace.calls.iter().enumerate() {
        let amount: i128 = decode_decimal(&call.amount)?;
        let got = check_spend(&record, limit, trace.period, call.now, amount);
        match (got, &call.expected) {
            (Ok(out), Outcome::Ok(want)) => {
                let want = decode_record(want)?;
                if parts(&out) != parts(&want) {
                    return Err(format!(
                        "call {i}: record {:?} where the trace has {:?}",
                        parts(&out),
                        parts(&want)
                    ));
                }
                record = out;
            }
            (Err(e), Outcome::Error(want)) => {
                if error_of(&e) != *want {
                    return Err(format!(
                        "call {i}: refused with {:?} where the trace has {want:?}",
                        error_of(&e)
                    ));
                }
            }
            (Ok(out), Outcome::Error(want)) => {
                return Err(format!(
                    "call {i}: accepted with {:?} where the trace refuses with {want:?}",
                    parts(&out)
                ));
            }
            (Err(e), Outcome::Ok(_)) => {
                return Err(format!(
                    "call {i}: refused with {:?} where the trace accepts",
                    error_of(&e)
                ));
            }
        }
    }
    Ok(())
}
