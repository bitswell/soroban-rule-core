//! Checks `rule-eval`'s budget operations against the budget traces.
//!
//! A budget trace (see `conformance/README.md`) holds a starting tree and
//! operations, each a spend, a delegation or a refill with the outcome the
//! Lean model computes for it on the tree the operations before it left.
//! [`check`] runs the operations through [`spend`], [`delegate`] and
//! [`refill`], keeping the tree unchanged after a refusal, and reports the
//! first outcome that differs.

use std::fs;
use std::path::{Path, PathBuf};

use rule_eval::{BudgetError, Node, delegate, refill, spend, tree_valid};
use serde::Deserialize;

use crate::decode_decimal;

/// The budget trace format version this runner reads.
pub const FORMAT: u32 = 1;

/// One budget trace file.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Trace {
    pub format: u32,
    pub name: String,
    pub description: String,
    pub start: Vec<JsonNode>,
    pub valid: bool,
    pub ops: Vec<JsonOp>,
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct JsonNode {
    pub parent: Option<u32>,
    pub allowance: String,
    pub spent: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, tag = "op", rename_all = "snake_case")]
pub enum JsonOp {
    Spend {
        node: u32,
        amount: String,
        expected: Outcome,
    },
    Delegate {
        parent: u32,
        allowance: String,
        expected: Outcome,
    },
    Refill {
        node: u32,
        amount: String,
        expected: Outcome,
    },
}

impl JsonOp {
    #[must_use]
    pub fn expected(&self) -> &Outcome {
        match self {
            JsonOp::Spend { expected, .. }
            | JsonOp::Delegate { expected, .. }
            | JsonOp::Refill { expected, .. } => expected,
        }
    }

    pub fn expected_mut(&mut self) -> &mut Outcome {
        match self {
            JsonOp::Spend { expected, .. }
            | JsonOp::Delegate { expected, .. }
            | JsonOp::Refill { expected, .. } => expected,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum Outcome {
    /// The operation succeeded: the tree after it.
    Ok(Vec<JsonNode>),
    /// The operation was refused, and the tree stays as it was.
    Error(JsonBudgetError),
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
#[serde(rename_all = "snake_case")]
pub enum JsonBudgetError {
    Malformed,
    NoSuchNode(u32),
    NegativeAmount,
    Overdrawn(u32),
    Overflow,
    TreeFull,
}

/// Every `*.json` budget trace in `dir`, sorted by path, each checked to carry
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

/// `t` as a `rule-eval` tree.
///
/// # Errors
///
/// An allowance or spent amount that is not a decimal `i128`.
pub fn decode_tree(t: &[JsonNode]) -> Result<Vec<Node>, String> {
    let mut out = Vec::new();
    for n in t {
        out.push(Node {
            parent: n.parent,
            allowance: decode_decimal(&n.allowance)?,
            spent: decode_decimal(&n.spent)?,
        });
    }
    Ok(out)
}

fn error_of(e: &BudgetError) -> JsonBudgetError {
    match e {
        BudgetError::Malformed => JsonBudgetError::Malformed,
        BudgetError::NoSuchNode(i) => JsonBudgetError::NoSuchNode(*i),
        BudgetError::NegativeAmount => JsonBudgetError::NegativeAmount,
        BudgetError::Overdrawn(i) => JsonBudgetError::Overdrawn(*i),
        BudgetError::Overflow => JsonBudgetError::Overflow,
        BudgetError::TreeFull => JsonBudgetError::TreeFull,
    }
}

/// The fields of every node of `t`, for comparison.
fn parts(t: &[Node]) -> Vec<(Option<u32>, i128, i128)> {
    t.iter().map(|n| (n.parent, n.allowance, n.spent)).collect()
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
    let mut tree = decode_tree(&trace.start)?;
    if tree_valid(&tree) != trace.valid {
        return Err(format!(
            "tree_valid is {} where the trace has {}",
            tree_valid(&tree),
            trace.valid
        ));
    }
    for (i, op) in trace.ops.iter().enumerate() {
        let got = match op {
            JsonOp::Spend { node, amount, .. } => spend(&tree, *node, decode_decimal(amount)?),
            JsonOp::Delegate {
                parent, allowance, ..
            } => delegate(&tree, *parent, decode_decimal(allowance)?),
            JsonOp::Refill { node, amount, .. } => refill(&tree, *node, decode_decimal(amount)?),
        };
        match (got, op.expected()) {
            (Ok(out), Outcome::Ok(want)) => {
                let want = decode_tree(want)?;
                if parts(&out) != parts(&want) {
                    return Err(format!(
                        "op {i}: tree {:?} where the trace has {:?}",
                        parts(&out),
                        parts(&want)
                    ));
                }
                tree = out;
            }
            (Err(e), Outcome::Error(want)) => {
                if error_of(&e) != *want {
                    return Err(format!(
                        "op {i}: refused with {:?} where the trace has {want:?}",
                        error_of(&e)
                    ));
                }
            }
            (Ok(out), Outcome::Error(want)) => {
                return Err(format!(
                    "op {i}: accepted with {:?} where the trace refuses with {want:?}",
                    parts(&out)
                ));
            }
            (Err(e), Outcome::Ok(_)) => {
                return Err(format!(
                    "op {i}: refused with {:?} where the trace accepts",
                    error_of(&e)
                ));
            }
        }
    }
    Ok(())
}
