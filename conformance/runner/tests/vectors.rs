//! `rule-eval` against every vector in `conformance/vectors`, or in the
//! directory the `CONFORMANCE_VECTORS` environment variable names.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use rule_eval_conformance::{
    JsonCond, JsonContext, JsonError, JsonRule, JsonSigner, JsonStep, JsonVal, Outcome, Vector,
    check, decode_hex, load_dir,
};

/// `conformance/vectors`, or the directory `CONFORMANCE_VECTORS` names.
fn dir() -> PathBuf {
    std::env::var_os("CONFORMANCE_VECTORS").map_or_else(
        || Path::new(env!("CARGO_MANIFEST_DIR")).join("../vectors"),
        PathBuf::from,
    )
}

fn vectors() -> Vec<(PathBuf, Vector)> {
    load_dir(&dir()).unwrap_or_else(|e| panic!("{e}"))
}

#[test]
fn rule_eval_agrees_with_every_vector() {
    let vectors = vectors();
    assert!(!vectors.is_empty(), "no vectors found");
    let failures: Vec<String> = vectors
        .iter()
        .filter_map(|(path, v)| check(v).err().map(|e| format!("{}: {e}", path.display())))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn note_cond(seen: &mut BTreeSet<&'static str>, c: &JsonCond) {
    match c {
        JsonCond::ArgEq { index, .. } => {
            seen.insert("cond arg_eq");
            if *index == u32::MAX {
                seen.insert("arg index u32::MAX");
            }
        }
        JsonCond::ArgI128AtMost { .. } => {
            seen.insert("cond arg_i128_at_most");
        }
    }
}

fn note_signers(seen: &mut BTreeSet<&'static str>, signers: &[JsonSigner]) {
    for (k, x) in signers.iter().enumerate() {
        seen.insert(match x {
            JsonSigner::Delegated { .. } => "signer delegated",
            JsonSigner::External { .. } => "signer external",
        });
        if signers[..k].iter().any(|y| same_signer(x, y)) {
            seen.insert("repeated signer");
        }
    }
}

fn same_signer(x: &JsonSigner, y: &JsonSigner) -> bool {
    match (x, y) {
        (JsonSigner::Delegated { address: a }, JsonSigner::Delegated { address: b }) => a == b,
        (
            JsonSigner::External {
                verifier: v,
                key: k,
            },
            JsonSigner::External {
                verifier: w,
                key: l,
            },
        ) => v == w && k == l,
        _ => false,
    }
}

/// The number of distinct signers a rule lists.
fn distinct_signers(r: &JsonRule) -> usize {
    (0..r.signers.len())
        .filter(|&k| !r.signers[..k].iter().any(|y| same_signer(&r.signers[k], y)))
        .count()
}

fn note_rule(seen: &mut BTreeSet<&'static str>, r: &JsonRule) {
    if r.functions.is_empty() {
        seen.insert("empty function list");
    }
    seen.insert(if r.cap.is_some() {
        "rule with a cap"
    } else {
        "rule without a cap"
    });
    for c in &r.conds {
        note_cond(seen, c);
    }
    note_signers(seen, &r.signers);
    let n = distinct_signers(r);
    let t = r.threshold as usize;
    seen.insert(if t == 0 {
        "threshold 0"
    } else if t == 1 {
        "threshold 1"
    } else if t < n {
        "threshold between 1 and the number of signers"
    } else if t == n {
        "threshold all signers"
    } else {
        "threshold above the number of signers"
    });
}

/// The vectors keep exercising each kind of input and result: removing the
/// last vector that covers one fails this test.
#[test]
fn vectors_cover_every_kind() {
    let mut seen = BTreeSet::new();
    for (_, v) in vectors() {
        if v.batch.is_empty() {
            seen.insert("empty batch");
        }
        if v.rules.is_empty() {
            seen.insert("empty rule set");
        }
        if v.rules.len() > 1 {
            seen.insert("several rules");
        }
        for r in &v.rules {
            note_rule(&mut seen, r);
        }
        seen.insert(if v.authenticated.is_empty() {
            "no authenticated signer"
        } else {
            "authenticated signers"
        });
        note_signers(&mut seen, &v.authenticated);
        for (c, &allowed) in v.batch.iter().zip(&v.expected.allows) {
            seen.insert(if allowed { "allowed" } else { "refused" });
            match c {
                JsonContext::Create { .. } => {
                    seen.insert("create");
                }
                JsonContext::Call { args, .. } => {
                    for a in args {
                        seen.insert(match a {
                            JsonVal::I128(_) => "val i128",
                            JsonVal::U64(_) => "val u64",
                            JsonVal::Bool(_) => "val bool",
                            JsonVal::Bytes(_) => "val bytes",
                            JsonVal::Address(_) => "val address",
                            JsonVal::Symbol(_) => "val symbol",
                            JsonVal::Other(_) => "val other",
                        });
                    }
                }
            }
        }
        if v.expected.allows.contains(&true) && v.expected.allows.contains(&false) {
            seen.insert("mixed batch");
        }
        for a in &v.attenuations {
            for s in &a.steps {
                match s {
                    JsonStep::DropRule { .. } => seen.insert("step drop_rule"),
                    JsonStep::AddCond { cond, .. } => {
                        note_cond(&mut seen, cond);
                        seen.insert("step add_cond")
                    }
                    JsonStep::RemoveFunctions { .. } => seen.insert("step remove_functions"),
                    JsonStep::RemoveSigners { signers, .. } => {
                        note_signers(&mut seen, signers);
                        seen.insert("step remove_signers")
                    }
                    JsonStep::RaiseThreshold { .. } => seen.insert("step raise_threshold"),
                    JsonStep::AddCap { .. } => seen.insert("step add_cap"),
                    JsonStep::LowerCapLimit { .. } => seen.insert("step lower_cap_limit"),
                    JsonStep::LengthenCapPeriod { .. } => seen.insert("step lengthen_cap_period"),
                };
                let index = match s {
                    JsonStep::DropRule { index }
                    | JsonStep::AddCond { index, .. }
                    | JsonStep::RemoveFunctions { index, .. }
                    | JsonStep::RemoveSigners { index, .. }
                    | JsonStep::RaiseThreshold { index, .. }
                    | JsonStep::AddCap { index, .. }
                    | JsonStep::LowerCapLimit { index, .. }
                    | JsonStep::LengthenCapPeriod { index, .. } => *index,
                };
                if index == u32::MAX {
                    seen.insert("rule index u32::MAX");
                }
            }
            if a.steps.len() > 1 {
                seen.insert("step chain");
            }
            if let Outcome::Ok { rules, .. } = &a.expected {
                for r in rules {
                    note_rule(&mut seen, r);
                }
            }
            seen.insert(match &a.expected {
                Outcome::Ok { .. } => "outcome ok",
                Outcome::Error(JsonError::NoSuchRule) => "outcome no_such_rule",
                Outcome::Error(JsonError::ThresholdLowered) => "outcome threshold_lowered",
                Outcome::Error(JsonError::CapPresent) => "outcome cap_present",
                Outcome::Error(JsonError::NoCap) => "outcome no_cap",
                Outcome::Error(JsonError::InvalidCap) => "outcome invalid_cap",
                Outcome::Error(JsonError::LimitRaised) => "outcome limit_raised",
                Outcome::Error(JsonError::PeriodShortened) => "outcome period_shortened",
            });
        }
    }
    let want = [
        "allowed",
        "refused",
        "mixed batch",
        "empty batch",
        "empty rule set",
        "several rules",
        "empty function list",
        "rule with a cap",
        "rule without a cap",
        "create",
        "val i128",
        "val u64",
        "val bool",
        "val bytes",
        "val address",
        "val symbol",
        "val other",
        "cond arg_eq",
        "cond arg_i128_at_most",
        "arg index u32::MAX",
        "signer delegated",
        "signer external",
        "repeated signer",
        "threshold 0",
        "threshold 1",
        "threshold between 1 and the number of signers",
        "threshold all signers",
        "threshold above the number of signers",
        "no authenticated signer",
        "authenticated signers",
        "step drop_rule",
        "step add_cond",
        "step remove_functions",
        "step remove_signers",
        "step raise_threshold",
        "step add_cap",
        "step lower_cap_limit",
        "step lengthen_cap_period",
        "step chain",
        "rule index u32::MAX",
        "outcome ok",
        "outcome no_such_rule",
        "outcome threshold_lowered",
        "outcome cap_present",
        "outcome no_cap",
        "outcome invalid_cap",
        "outcome limit_raised",
        "outcome period_shortened",
    ];
    let missing: Vec<&str> = want.into_iter().filter(|k| !seen.contains(k)).collect();
    assert!(missing.is_empty(), "no vector covers: {missing:?}");
}

/// The runner reports a vector whose expected results `rule-eval` does not
/// reproduce, so a passing run is not vacuous.
#[test]
fn a_wrong_expectation_is_reported() {
    let vectors = vectors();
    let (_, original) = vectors
        .iter()
        .find(|(_, v)| !v.batch.is_empty())
        .expect("a vector with a non-empty batch");
    let text = vector_text(original);

    let mut v: Vector = serde_json::from_str(&text).unwrap();
    v.expected.allows[0] = !v.expected.allows[0];
    assert!(check(&v).is_err(), "a flipped context verdict passed");

    let mut v: Vector = serde_json::from_str(&text).unwrap();
    v.expected.allows_all = !v.expected.allows_all;
    assert!(check(&v).is_err(), "a flipped batch verdict passed");

    let (_, attenuating) = vectors
        .iter()
        .find(|(_, v)| {
            v.attenuations
                .iter()
                .any(|a| matches!(&a.expected, Outcome::Ok { rules, .. } if !rules.is_empty()))
        })
        .expect("a vector with a non-empty attenuation result");
    let text = vector_text(attenuating);
    let mut v: Vector = serde_json::from_str(&text).unwrap();
    for a in &mut v.attenuations {
        if let Outcome::Ok { rules, .. } = &mut a.expected
            && let Some(r) = rules.first_mut()
        {
            r.contract.push_str("00");
            break;
        }
    }
    assert!(check(&v).is_err(), "a changed attenuation result passed");

    let (_, capped) = vectors
        .iter()
        .find(|(_, v)| v.rules.iter().any(|r| r.cap.is_some()))
        .expect("a vector with a capped rule");
    let text = vector_text(capped);
    let mut v: Vector = serde_json::from_str(&text).unwrap();
    for a in &mut v.attenuations {
        if let Outcome::Ok { rules, .. } = &mut a.expected
            && let Some(c) = rules.iter_mut().find_map(|r| r.cap.as_mut())
        {
            c.period += 1;
            break;
        }
    }
    assert!(
        check(&v).is_err(),
        "a changed cap in an attenuation result passed"
    );
}

#[test]
fn hex_is_lowercase_and_even() {
    assert_eq!(decode_hex("").unwrap(), Vec::<u8>::new());
    assert_eq!(decode_hex("00ff7a").unwrap(), vec![0x00, 0xff, 0x7a]);
    assert!(decode_hex("0").is_err());
    assert!(decode_hex("FF").is_err());
    assert!(decode_hex("0g").is_err());
}

/// The text of `v`'s file, to parse a fresh copy to modify.
fn vector_text(v: &Vector) -> String {
    std::fs::read_to_string(dir().join(format!("{}.json", v.name))).unwrap()
}
