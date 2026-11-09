//! `rule-eval`'s `check_auth` against every trace in
//! `conformance/vectors/authorize`, or in the `authorize` directory under the
//! one the `CONFORMANCE_VECTORS` environment variable names.

use std::collections::BTreeSet;
use std::path::PathBuf;

use rule_eval_conformance::authorize::{JsonRefusal, Outcome, Trace, check, load_dir};
use rule_eval_conformance::caps::JsonRecord;

fn dir() -> PathBuf {
    rule_eval_conformance::vectors_dir().join("authorize")
}

fn traces() -> Vec<(PathBuf, Trace)> {
    load_dir(&dir()).unwrap_or_else(|e| panic!("{e}"))
}

#[test]
fn rule_eval_agrees_with_every_authorization_trace() {
    let traces = traces();
    assert!(!traces.is_empty(), "no authorization traces found");
    let failures: Vec<String> = traces
        .iter()
        .filter_map(|(path, t)| check(t).err().map(|e| format!("{}: {e}", path.display())))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Whether some record of `after` lost an entry `before` held: eviction.
fn evicted(before: &[JsonRecord], after: &[JsonRecord]) -> bool {
    before.iter().zip(after).any(|(b, a)| {
        b.history.iter().any(|e| {
            !a.history
                .iter()
                .any(|x| x.ledger == e.ledger && x.amount == e.amount)
        })
    })
}

/// The traces keep exercising each outcome and edge: removing the last trace
/// that covers one fails this test.
#[test]
fn authorization_traces_cover_every_outcome() {
    let mut seen = BTreeSet::new();
    for (_, t) in traces() {
        if t.start.len() != t.rules.len() {
            seen.insert("start records mismatch");
        }
        for r in &t.rules {
            seen.insert(if r.cap.is_some() {
                "capped rule"
            } else {
                "uncapped rule"
            });
        }
        let mut records: Vec<JsonRecord> = t
            .start
            .iter()
            .map(|r| serde_json::from_value(record_value(r)).unwrap())
            .collect();
        for a in &t.authorizations {
            if a.batch.is_empty() {
                seen.insert("empty batch");
            }
            if a.batch.len() > 1 {
                seen.insert("several contexts");
            }
            let repeated = (0..a.choices.len()).any(|k| a.choices[..k].contains(&a.choices[k]));
            match &a.expected {
                Outcome::Ok(after) => {
                    seen.insert("accepted");
                    let charges_twice = repeated
                        && a.choices.iter().enumerate().any(|(k, &j)| {
                            a.choices[..k].contains(&j)
                                && t.rules.get(j as usize).is_some_and(|r| r.cap.is_some())
                        });
                    if charges_twice {
                        seen.insert("one rule charged twice in a batch");
                    }
                    if evicted(&records, after) {
                        seen.insert("eviction");
                    }
                    records = after
                        .iter()
                        .map(|r| serde_json::from_value(record_value(r)).unwrap())
                        .collect();
                }
                Outcome::Error(e) => {
                    seen.insert(match e {
                        JsonRefusal::ChoicesMismatch => "choices_mismatch",
                        JsonRefusal::RecordsMismatch => "records_mismatch",
                        JsonRefusal::NoSuchRule => "no_such_rule",
                        JsonRefusal::Expired => "expired",
                        JsonRefusal::StaleGeneration => "stale_generation",
                        JsonRefusal::NotAllowed => "not_allowed",
                        JsonRefusal::UnauthorizedSigner => "unauthorized_signer",
                        JsonRefusal::NoAmount => "no_amount",
                        JsonRefusal::CapNegativeAmount => "cap_negative_amount",
                        JsonRefusal::CapLedgerBeforeNewest => "cap_ledger_before_newest",
                        JsonRefusal::CapOverflow => "cap_overflow",
                        JsonRefusal::CapLimitExceeded => "cap_limit_exceeded",
                        JsonRefusal::CapHistoryFull => "cap_history_full",
                    });
                }
            }
        }
    }
    let want = [
        "start records mismatch",
        "capped rule",
        "uncapped rule",
        "empty batch",
        "several contexts",
        "accepted",
        "one rule charged twice in a batch",
        "eviction",
        "choices_mismatch",
        "records_mismatch",
        "no_such_rule",
        "expired",
        "stale_generation",
        "not_allowed",
        "unauthorized_signer",
        "no_amount",
        "cap_negative_amount",
        "cap_ledger_before_newest",
        "cap_overflow",
        "cap_limit_exceeded",
        "cap_history_full",
    ];
    let missing: Vec<&str> = want.into_iter().filter(|k| !seen.contains(k)).collect();
    assert!(
        missing.is_empty(),
        "no authorization trace covers: {missing:?}"
    );
}

/// A record as JSON, to copy it.
fn record_value(r: &JsonRecord) -> serde_json::Value {
    serde_json::json!({
        "history": r.history.iter().map(|e| serde_json::json!({
            "ledger": e.ledger,
            "amount": e.amount,
        })).collect::<Vec<_>>(),
        "total": r.total,
    })
}

/// The runner reports a trace whose outcomes `rule-eval` does not reproduce,
/// so a passing run is not vacuous.
#[test]
fn a_wrong_authorization_expectation_is_reported() {
    let text = std::fs::read_to_string(dir().join("authorize-batch-same-rule.json")).unwrap();

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    if let Outcome::Ok(records) = &mut t.authorizations[0].expected {
        records[0].total.push('1');
    }
    assert!(check(&t).is_err(), "a changed total passed");

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    t.authorizations[0].expected = Outcome::Error(JsonRefusal::NotAllowed);
    assert!(
        check(&t).is_err(),
        "an accepted authorization recorded as refused passed"
    );

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    let last = t.authorizations.len() - 1;
    t.authorizations[last].expected = Outcome::Error(JsonRefusal::CapHistoryFull);
    assert!(check(&t).is_err(), "a changed refusal passed");
}
