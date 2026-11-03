//! `rule-eval`'s cap check against every trace in `conformance/vectors/caps`,
//! or in the `caps` directory under the one the `CONFORMANCE_VECTORS`
//! environment variable names.

use std::collections::BTreeSet;
use std::path::PathBuf;

use rule_eval_conformance::caps::{JsonCapError, Outcome, Trace, check, load_dir};

fn dir() -> PathBuf {
    rule_eval_conformance::vectors_dir().join("caps")
}

fn traces() -> Vec<(PathBuf, Trace)> {
    load_dir(&dir()).unwrap_or_else(|e| panic!("{e}"))
}

#[test]
fn rule_eval_agrees_with_every_cap_trace() {
    let traces = traces();
    assert!(!traces.is_empty(), "no cap traces found");
    let failures: Vec<String> = traces
        .iter()
        .filter_map(|(path, t)| check(t).err().map(|e| format!("{}: {e}", path.display())))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The traces keep exercising each outcome and edge: removing the last trace
/// that covers one fails this test.
#[test]
fn cap_traces_cover_every_outcome() {
    let mut seen = BTreeSet::new();
    for (_, t) in traces() {
        seen.insert(if t.params_valid {
            "valid params"
        } else {
            "invalid params"
        });
        if !t.start.history.is_empty() {
            seen.insert("non-empty start");
        }
        if t.period == u32::MAX {
            seen.insert("period u32::MAX");
        }
        for c in &t.calls {
            if c.now == 0 {
                seen.insert("ledger 0");
            }
            if c.now == u32::MAX {
                seen.insert("ledger u32::MAX");
            }
            if c.amount == "0" {
                seen.insert("zero amount");
            }
            seen.insert(match &c.expected {
                Outcome::Ok(_) => "accepted",
                Outcome::Error(JsonCapError::NegativeAmount) => "negative_amount",
                Outcome::Error(JsonCapError::LedgerBeforeNewest) => "ledger_before_newest",
                Outcome::Error(JsonCapError::Overflow) => "overflow",
                Outcome::Error(JsonCapError::LimitExceeded) => "limit_exceeded",
                Outcome::Error(JsonCapError::HistoryFull) => "history_full",
            });
        }
    }
    let want = [
        "valid params",
        "invalid params",
        "non-empty start",
        "period u32::MAX",
        "ledger 0",
        "ledger u32::MAX",
        "zero amount",
        "accepted",
        "negative_amount",
        "ledger_before_newest",
        "overflow",
        "limit_exceeded",
        "history_full",
    ];
    let missing: Vec<&str> = want.into_iter().filter(|k| !seen.contains(k)).collect();
    assert!(missing.is_empty(), "no cap trace covers: {missing:?}");
}

/// The runner reports a trace whose outcomes `rule-eval` does not reproduce,
/// so a passing run is not vacuous.
#[test]
fn a_wrong_cap_expectation_is_reported() {
    let text = std::fs::read_to_string(dir().join("cap-window-slides.json")).unwrap();

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    if let Outcome::Ok(r) = &mut t.calls[0].expected {
        r.total.push('1');
    }
    assert!(check(&t).is_err(), "a changed total passed");

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    t.calls[3].expected = Outcome::Error(JsonCapError::HistoryFull);
    assert!(check(&t).is_err(), "a changed refusal passed");

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    t.params_valid = !t.params_valid;
    assert!(check(&t).is_err(), "a changed params_valid passed");

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    t.calls[0].expected = Outcome::Error(JsonCapError::LimitExceeded);
    assert!(
        check(&t).is_err(),
        "an accepted call recorded as refused passed"
    );
}
