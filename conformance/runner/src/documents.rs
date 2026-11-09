//! Checks `rule-eval`'s lowering and `check_auth` against the document traces.
//!
//! A document trace (see `conformance/README.md`) holds a document, the
//! account it belongs to, optionally the admin document it is issued under as
//! a scoped document and the generation, the rules the Lean model lowers it to
//! (or the scoped lowering's refusal), and authorizations, each with the
//! verdict the document's meaning gives on the records the authorizations
//! before it left. [`check`] lowers the document with [`lower`] or
//! [`lower_scoped`] under the set [`excluded`] takes from the admin document,
//! compares the rules, runs the authorizations through [`check_auth`] and
//! reports the first difference.

use std::fs;
use std::path::{Path, PathBuf};

use rule_eval::{
    ArgConstraint, Doc, DocCap, DocRule, Pred, Principals, Recovery, Scope, ScopeError, SignerDecl,
    SpendRecord, ZkFactor, check_auth, empty_record, excluded, lower, lower_scoped,
};
use serde::Deserialize;

use crate::caps::{JsonRecord, decode_record};
use crate::{
    JsonContext, JsonRule, JsonSigner, decode_context, decode_decimal, decode_hex, decode_rules,
    decode_signer, decode_signers, rules_eq,
};

/// The document trace format version this runner reads.
pub const FORMAT: u32 = 1;

/// One document trace file.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Trace {
    pub format: u32,
    pub name: String,
    pub description: String,
    pub document: JsonDoc,
    pub account: String,
    /// For a scoped document: the admin document and the generation it is
    /// issued in; `null` for an admin document.
    pub scoped: Option<JsonScoped>,
    pub lowered: Lowered,
    pub authorizations: Vec<JsonAuthorization>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonScoped {
    pub admin: JsonDoc,
    /// The generation, a decimal `u64`.
    pub generation: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum Lowered {
    /// The rules the document lowers to.
    Ok(Vec<JsonRule>),
    /// The scoped lowering's refusal.
    Error(JsonScopeError),
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
#[serde(rename_all = "snake_case")]
pub enum JsonScopeError {
    RecoveryConfigured,
    ExcludedScope,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonDoc {
    pub signers: Vec<JsonDecl>,
    pub rules: Vec<JsonDocRule>,
    pub recovery: Option<JsonRecovery>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonDecl {
    pub id: String,
    pub signer: JsonSigner,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonDocRule {
    pub scope: JsonScope,
    pub principals: JsonPrincipals,
    pub functions: Option<Vec<String>>,
    pub args: Option<Vec<JsonArg>>,
    pub not_after_ledger: Option<u32>,
    pub cap: Option<JsonDocCap>,
    pub auth_root: Option<crate::JsonAuthRoot>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonScope {
    Contract(String),
    SelfAdmin,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonPrincipals {
    All(Vec<String>),
    Threshold { ids: Vec<String>, m: u32 },
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonArg {
    pub index: u32,
    pub pred: JsonPred,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonPred {
    IsSelf,
    AddressEq(String),
    StringIn(Vec<String>),
    StringPrefix(String),
    U32Eq(u32),
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonDocCap {
    pub limit: String,
    pub period_ledgers: u32,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonRecovery {
    pub controller: String,
    pub zk: Option<JsonZk>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonZk {
    pub adapter: String,
    pub pool: String,
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
    pub expected: Verdict,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum Verdict {
    /// The document accepts the authorization: the records after it, one per
    /// installed rule.
    Ok(Vec<JsonRecord>),
    /// The document refuses it, and the records stay as they were.
    Refused,
}

/// Every `*.json` document trace in `dir`, sorted by path, each checked to
/// carry its file's name.
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

fn decode_hex_list(list: &[String]) -> Result<Vec<Vec<u8>>, String> {
    list.iter().map(|s| decode_hex(s)).collect()
}

fn decode_pred(p: &JsonPred) -> Result<Pred, String> {
    Ok(match p {
        JsonPred::IsSelf => Pred::IsSelf,
        JsonPred::AddressEq(a) => Pred::AddressEq(decode_hex(a)?),
        JsonPred::StringIn(values) => Pred::StringIn(decode_hex_list(values)?),
        JsonPred::StringPrefix(pre) => Pred::StringPrefix(decode_hex(pre)?),
        JsonPred::U32Eq(v) => Pred::U32Eq(*v),
    })
}

fn decode_doc_rule(r: &JsonDocRule) -> Result<DocRule, String> {
    Ok(DocRule {
        auth_root: r
            .auth_root
            .as_ref()
            .map(crate::decode_auth_root)
            .transpose()?,
        scope: match &r.scope {
            JsonScope::Contract(a) => Scope::Contract(decode_hex(a)?),
            JsonScope::SelfAdmin => Scope::SelfAdmin,
        },
        principals: match &r.principals {
            JsonPrincipals::All(ids) => Principals::All(decode_hex_list(ids)?),
            JsonPrincipals::Threshold { ids, m } => {
                Principals::Threshold(decode_hex_list(ids)?, *m)
            }
        },
        functions: r.functions.as_deref().map(decode_hex_list).transpose()?,
        args: r
            .args
            .as_ref()
            .map(|cs| {
                cs.iter()
                    .map(|c| {
                        Ok(ArgConstraint {
                            index: c.index,
                            pred: decode_pred(&c.pred)?,
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()
            })
            .transpose()?,
        not_after_ledger: r.not_after_ledger,
        cap: r
            .cap
            .as_ref()
            .map(|k| {
                Ok::<_, String>(DocCap {
                    limit: decode_decimal(&k.limit)?,
                    period_ledgers: k.period_ledgers,
                })
            })
            .transpose()?,
    })
}

/// The document a trace's JSON describes.
///
/// # Errors
///
/// A byte string that is not lowercase hex, or a limit that is not a decimal
/// `i128`.
pub fn decode_doc(d: &JsonDoc) -> Result<Doc, String> {
    Ok(Doc {
        signers: d
            .signers
            .iter()
            .map(|s| {
                Ok(SignerDecl {
                    id: decode_hex(&s.id)?,
                    signer: decode_signer(&s.signer)?,
                })
            })
            .collect::<Result<_, String>>()?,
        rules: d
            .rules
            .iter()
            .map(decode_doc_rule)
            .collect::<Result<_, _>>()?,
        recovery: d
            .recovery
            .as_ref()
            .map(|rc| {
                Ok::<_, String>(Recovery {
                    controller: decode_hex(&rc.controller)?,
                    zk: rc
                        .zk
                        .as_ref()
                        .map(|z| {
                            Ok::<_, String>(ZkFactor {
                                adapter: decode_hex(&z.adapter)?,
                                pool: decode_hex(&z.pool)?,
                            })
                        })
                        .transpose()?,
                })
            })
            .transpose()?,
    })
}

/// The name `conformance/README.md` gives a refusal of `lower_scoped`.
#[must_use]
pub fn scope_error_of(e: &ScopeError) -> JsonScopeError {
    match e {
        ScopeError::RecoveryConfigured => JsonScopeError::RecoveryConfigured,
        ScopeError::ExcludedScope => JsonScopeError::ExcludedScope,
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
    let d = decode_doc(&trace.document)?;
    let account = decode_hex(&trace.account)?;
    let got = match &trace.scoped {
        None => Ok(lower(&d, &account)),
        Some(scoped) => {
            let admin = decode_doc(&scoped.admin)?;
            let generation: u64 = decode_decimal(&scoped.generation)?;
            lower_scoped(&d, &account, &excluded(&admin, &account), generation)
        }
    };
    let rules = match (got, &trace.lowered) {
        (Ok(rules), Lowered::Ok(want)) => {
            if !rules_eq(&rules, &decode_rules(want)?) {
                return Err("the lowered rules differ".into());
            }
            rules
        }
        (Err(e), Lowered::Error(want)) => {
            if scope_error_of(&e) != *want {
                return Err(format!(
                    "refused with {:?} where the trace has {want:?}",
                    scope_error_of(&e)
                ));
            }
            if !trace.authorizations.is_empty() {
                return Err("a refused document has authorizations".into());
            }
            return Ok(());
        }
        (Ok(_), Lowered::Error(want)) => {
            return Err(format!("lowered where the trace refuses with {want:?}"));
        }
        (Err(e), Lowered::Ok(_)) => {
            return Err(format!(
                "refused with {:?} where the trace lowers",
                scope_error_of(&e)
            ));
        }
    };
    let mut records: Vec<SpendRecord> = rules.iter().map(|_| empty_record()).collect();
    for (i, a) in trace.authorizations.iter().enumerate() {
        let batch = a
            .batch
            .iter()
            .map(decode_context)
            .collect::<Result<Vec<_>, _>>()?;
        let authenticated = decode_signers(&a.authenticated)?;
        let generation: u64 = decode_decimal(&a.generation)?;
        let got = check_auth(
            &rules,
            &records,
            &batch,
            &a.choices,
            &authenticated,
            a.now,
            generation,
        );
        match (got, &a.expected) {
            (Ok(out), Verdict::Ok(want)) => {
                let want = want
                    .iter()
                    .map(decode_record)
                    .collect::<Result<Vec<_>, _>>()?;
                if parts(&out) != parts(&want) {
                    return Err(format!(
                        "authorization {i}: records {:?} where the trace has {:?}",
                        parts(&out),
                        parts(&want)
                    ));
                }
                records = out;
            }
            (Err(_), Verdict::Refused) => {}
            (Ok(out), Verdict::Refused) => {
                return Err(format!(
                    "authorization {i}: accepted with {:?} where the document refuses",
                    parts(&out)
                ));
            }
            (Err(_), Verdict::Ok(_)) => {
                return Err(format!(
                    "authorization {i}: refused where the document accepts"
                ));
            }
        }
    }
    Ok(())
}
