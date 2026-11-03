//! `rule-eval`'s lowering and `authorize` against every trace in
//! `conformance/vectors/documents`, or in the `documents` directory under the
//! one the `CONFORMANCE_VECTORS` environment variable names.

use std::collections::BTreeSet;
use std::path::PathBuf;

use rule_eval_conformance::documents::{
    JsonPred, JsonPrincipals, JsonScope, JsonScopeError, Lowered, Trace, Verdict, check, load_dir,
};

fn dir() -> PathBuf {
    rule_eval_conformance::vectors_dir().join("documents")
}

fn traces() -> Vec<(PathBuf, Trace)> {
    load_dir(&dir()).unwrap_or_else(|e| panic!("{e}"))
}

#[test]
fn rule_eval_agrees_with_every_document_trace() {
    let traces = traces();
    assert!(!traces.is_empty(), "no document traces found");
    let failures: Vec<String> = traces
        .iter()
        .filter_map(|(path, t)| check(t).err().map(|e| format!("{}: {e}", path.display())))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The traces keep exercising each construct and outcome: removing the last
/// trace that covers one fails this test.
#[test]
fn document_traces_cover_every_construct_and_outcome() {
    let mut seen = BTreeSet::new();
    for (_, t) in traces() {
        seen.insert(if t.scoped.is_some() {
            "scoped document"
        } else {
            "admin document"
        });
        if t.document.recovery.is_some() {
            seen.insert("recovery configured");
        }
        for r in &t.document.rules {
            seen.insert(match r.scope {
                JsonScope::SelfAdmin => "self-admin scope",
                JsonScope::Contract(_) => "contract scope",
            });
            seen.insert(match r.principals {
                JsonPrincipals::All(_) => "all principals",
                JsonPrincipals::Threshold { .. } => "threshold principals",
            });
            if r.functions.is_none() {
                seen.insert("no function list");
            }
            if r.cap.is_some() {
                seen.insert("cap");
            }
            if r.not_after_ledger.is_some() {
                seen.insert("not-after ledger");
            }
            for c in r.args.iter().flatten() {
                seen.insert(match c.pred {
                    JsonPred::IsSelf => "is-self",
                    JsonPred::AddressEq(_) => "address-eq",
                    JsonPred::StringIn(_) => "string-in",
                    JsonPred::StringPrefix(_) => "string-prefix",
                    JsonPred::U32Eq(_) => "u32-eq",
                });
            }
        }
        match t.lowered {
            Lowered::Ok(_) => {}
            Lowered::Error(JsonScopeError::RecoveryConfigured) => {
                seen.insert("recovery_configured");
            }
            Lowered::Error(JsonScopeError::ExcludedScope) => {
                seen.insert("excluded_scope");
            }
        }
        for a in &t.authorizations {
            seen.insert(match a.expected {
                Verdict::Ok(_) => "accepted",
                Verdict::Refused => "refused",
            });
        }
    }
    let want = [
        "admin document",
        "scoped document",
        "recovery configured",
        "self-admin scope",
        "contract scope",
        "all principals",
        "threshold principals",
        "no function list",
        "cap",
        "not-after ledger",
        "is-self",
        "address-eq",
        "string-in",
        "string-prefix",
        "u32-eq",
        "recovery_configured",
        "excluded_scope",
        "accepted",
        "refused",
    ];
    let missing: Vec<&str> = want.into_iter().filter(|k| !seen.contains(k)).collect();
    assert!(missing.is_empty(), "no document trace covers: {missing:?}");
}

/// The runner reports a trace whose results `rule-eval` does not reproduce, so
/// a passing run is not vacuous.
#[test]
fn a_wrong_document_expectation_is_reported() {
    let text = std::fs::read_to_string(dir().join("document-capped-approve.json")).unwrap();

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    t.authorizations[1].expected = Verdict::Ok(Vec::new());
    assert!(
        check(&t).is_err(),
        "a refused authorization recorded as accepted passed"
    );

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    t.authorizations[0].expected = Verdict::Refused;
    assert!(
        check(&t).is_err(),
        "an accepted authorization recorded as refused passed"
    );

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    if let Lowered::Ok(rules) = &mut t.lowered {
        rules[1].threshold += 1;
    }
    assert!(check(&t).is_err(), "a changed lowered rule passed");

    let text = std::fs::read_to_string(dir().join("document-scoped-pool.json")).unwrap();
    let mut t: Trace = serde_json::from_str(&text).unwrap();
    t.lowered = Lowered::Error(JsonScopeError::RecoveryConfigured);
    assert!(check(&t).is_err(), "a changed refusal passed");
}
