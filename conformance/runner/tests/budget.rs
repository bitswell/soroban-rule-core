//! `rule-eval`'s budget operations against every trace in
//! `conformance/vectors/budget`, or in the `budget` directory under the one the
//! `CONFORMANCE_VECTORS` environment variable names.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use rule_eval_conformance::budget::{JsonBudgetError, JsonOp, Outcome, Trace, check, load_dir};

fn dir() -> PathBuf {
    std::env::var_os("CONFORMANCE_VECTORS")
        .map_or_else(
            || Path::new(env!("CARGO_MANIFEST_DIR")).join("../vectors"),
            PathBuf::from,
        )
        .join("budget")
}

fn traces() -> Vec<(PathBuf, Trace)> {
    load_dir(&dir()).unwrap_or_else(|e| panic!("{e}"))
}

#[test]
fn rule_eval_agrees_with_every_budget_trace() {
    let traces = traces();
    assert!(!traces.is_empty(), "no budget traces found");
    let failures: Vec<String> = traces
        .iter()
        .filter_map(|(path, t)| check(t).err().map(|e| format!("{}: {e}", path.display())))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The traces keep exercising each outcome and edge: removing the last trace
/// that covers one fails this test. `TreeFull` needs a tree of `u32::MAX`
/// nodes and is not covered.
#[test]
fn budget_traces_cover_every_outcome() {
    let mut seen = BTreeSet::new();
    for (_, t) in traces() {
        seen.insert(if t.valid {
            "well-formed start"
        } else {
            "malformed start"
        });
        if t.start.is_empty() {
            seen.insert("empty tree");
        }
        if t.start.iter().filter(|n| n.parent.is_none()).count() > 1 {
            seen.insert("several roots");
        }
        for op in &t.ops {
            let kind = match op {
                JsonOp::Spend { .. } => "spend",
                JsonOp::Delegate { .. } => "delegate",
                JsonOp::Refill { .. } => "refill",
            };
            let outcome = match op.expected() {
                Outcome::Ok(_) => "ok",
                Outcome::Error(JsonBudgetError::Malformed) => "malformed",
                Outcome::Error(JsonBudgetError::NoSuchNode(_)) => "no_such_node",
                Outcome::Error(JsonBudgetError::NegativeAmount) => "negative_amount",
                Outcome::Error(JsonBudgetError::Overdrawn(_)) => "overdrawn",
                Outcome::Error(JsonBudgetError::Overflow) => "overflow",
                Outcome::Error(JsonBudgetError::TreeFull) => "tree_full",
            };
            seen.insert(match (kind, outcome) {
                ("spend", "ok") => "spend ok",
                ("spend", "malformed") => "spend malformed",
                ("spend", "no_such_node") => "spend no_such_node",
                ("spend", "negative_amount") => "spend negative_amount",
                ("spend", "overdrawn") => "spend overdrawn",
                ("delegate", "ok") => "delegate ok",
                ("delegate", "malformed") => "delegate malformed",
                ("delegate", "no_such_node") => "delegate no_such_node",
                ("delegate", "negative_amount") => "delegate negative_amount",
                ("refill", "ok") => "refill ok",
                ("refill", "malformed") => "refill malformed",
                ("refill", "no_such_node") => "refill no_such_node",
                ("refill", "negative_amount") => "refill negative_amount",
                ("refill", "overflow") => "refill overflow",
                _ => "other",
            });
            if let (JsonOp::Spend { node, .. }, Outcome::Error(JsonBudgetError::Overdrawn(j))) =
                (op, op.expected())
            {
                seen.insert(if node == j {
                    "overdrawn at the spender"
                } else {
                    "overdrawn at an ancestor"
                });
            }
        }
    }
    let want = [
        "well-formed start",
        "malformed start",
        "empty tree",
        "several roots",
        "spend ok",
        "spend malformed",
        "spend no_such_node",
        "spend negative_amount",
        "spend overdrawn",
        "overdrawn at the spender",
        "overdrawn at an ancestor",
        "delegate ok",
        "delegate malformed",
        "delegate no_such_node",
        "delegate negative_amount",
        "refill ok",
        "refill malformed",
        "refill no_such_node",
        "refill negative_amount",
        "refill overflow",
    ];
    let missing: Vec<&str> = want.into_iter().filter(|k| !seen.contains(k)).collect();
    assert!(missing.is_empty(), "no budget trace covers: {missing:?}");
}

/// The runner reports a trace whose outcomes `rule-eval` does not reproduce,
/// so a passing run is not vacuous.
#[test]
fn a_wrong_budget_expectation_is_reported() {
    let text = std::fs::read_to_string(dir().join("budget-oversubscribed-siblings.json")).unwrap();

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    if let Outcome::Ok(tree) = t.ops[0].expected_mut() {
        tree[0].spent.push('1');
    }
    assert!(check(&t).is_err(), "a changed spent amount passed");

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    *t.ops[1].expected_mut() = Outcome::Error(JsonBudgetError::Overdrawn(2));
    assert!(check(&t).is_err(), "a refusal naming another node passed");

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    t.valid = !t.valid;
    assert!(check(&t).is_err(), "a changed valid passed");

    let mut t: Trace = serde_json::from_str(&text).unwrap();
    *t.ops[0].expected_mut() = Outcome::Error(JsonBudgetError::Overdrawn(1));
    assert!(
        check(&t).is_err(),
        "an accepted spend recorded as refused passed"
    );
}
