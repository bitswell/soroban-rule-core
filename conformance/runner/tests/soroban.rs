//! `soroban-facade`'s plain code against the Soroban value and context
//! vectors and storage traces in `conformance/vectors/soroban`, or under the
//! directory the `CONFORMANCE_VECTORS` environment variable names.

use std::collections::BTreeSet;
use std::path::PathBuf;

use rule_eval_conformance::soroban::{
    ContextVector, JsonValue, Observed, OpKind, StorageTrace, ValueVector, check_context,
    check_storage, check_values, load_dir, vectors_dir,
};

fn values() -> Vec<(PathBuf, ValueVector)> {
    load_dir(&vectors_dir("values")).unwrap_or_else(|e| panic!("{e}"))
}

fn contexts() -> Vec<(PathBuf, ContextVector)> {
    load_dir(&vectors_dir("contexts")).unwrap_or_else(|e| panic!("{e}"))
}

fn storage() -> Vec<(PathBuf, StorageTrace)> {
    load_dir(&vectors_dir("storage")).unwrap_or_else(|e| panic!("{e}"))
}

fn failures<T>(vs: &[(PathBuf, T)], check: impl Fn(&T) -> Result<(), String>) -> Vec<String> {
    vs.iter()
        .filter_map(|(path, v)| check(v).err().map(|e| format!("{}: {e}", path.display())))
        .collect()
}

#[test]
fn the_facade_writes_and_reads_every_value_as_the_model_does() {
    let vs = values();
    assert!(!vs.is_empty(), "no value vectors found");
    let failed = failures(&vs, check_values);
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

#[test]
fn the_facade_reads_every_context_vector_as_the_model_does() {
    let vs = contexts();
    assert!(!vs.is_empty(), "no context vectors found");
    let failed = failures(&vs, check_context);
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

#[test]
fn plain_storage_agrees_with_every_storage_trace() {
    let ts = storage();
    assert!(!ts.is_empty(), "no storage traces found");
    let failed = failures(&ts, check_storage);
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

fn kind(v: &JsonValue, seen: &mut BTreeSet<&'static str>) {
    let name = match v {
        JsonValue::Void(()) => "void",
        JsonValue::Bool(_) => "bool",
        JsonValue::U32(_) => "u32",
        JsonValue::U64(_) => "u64",
        JsonValue::I128(_) => "i128",
        JsonValue::Bytes(_) => "bytes",
        JsonValue::String(_) => "string",
        JsonValue::Symbol(_) => "symbol",
        JsonValue::Address(_) => "address",
        JsonValue::Vec(items) => {
            for x in items {
                kind(x, seen);
            }
            "vec"
        }
        JsonValue::Map(entries) => {
            for (k, x) in entries {
                kind(k, seen);
                kind(x, seen);
            }
            "map"
        }
        JsonValue::Other(_) => "other",
    };
    seen.insert(name);
}

/// The vectors keep covering every constructor, refused and read contexts,
/// unstorable keys, and every storage operation and outcome.
#[test]
fn the_soroban_vectors_cover_every_kind() {
    let mut seen = BTreeSet::new();
    for (_, v) in values() {
        for case in &v.values {
            kind(&case.value, &mut seen);
            if !case.storable {
                seen.insert("unstorable");
            }
        }
    }
    for (_, v) in contexts() {
        seen.insert(if v.expected.is_some() {
            "read"
        } else {
            "refused context"
        });
    }
    for (_, t) in storage() {
        for op in &t.ops {
            seen.insert(match op.op {
                OpKind::Get => "get",
                OpKind::Has => "has",
                OpKind::Set => "set",
                OpKind::Remove => "remove",
            });
            seen.insert(match &op.expected {
                Observed::Value(Some(_)) => "read a value",
                Observed::Value(None) => "read nothing",
                Observed::Present(true) => "present",
                Observed::Present(false) => "absent",
                Observed::Done => "done",
                Observed::Refused => "refused key",
            });
        }
    }
    for want in [
        "void",
        "bool",
        "u32",
        "u64",
        "i128",
        "bytes",
        "string",
        "symbol",
        "address",
        "vec",
        "map",
        "other",
        "unstorable",
        "read",
        "refused context",
        "get",
        "has",
        "set",
        "remove",
        "read a value",
        "read nothing",
        "present",
        "absent",
        "done",
        "refused key",
    ] {
        assert!(seen.contains(want), "no Soroban vector covers {want}");
    }
}

#[test]
fn a_wrong_soroban_expectation_is_reported() {
    let (_, mut v) = values().into_iter().next().expect("a value vector");
    v.values[0].storable = !v.values[0].storable;
    assert!(check_values(&v).is_err());

    let (_, mut c) = contexts()
        .into_iter()
        .find(|(_, c)| c.expected.is_some())
        .expect("a context vector that reads");
    c.expected = None;
    assert!(check_context(&c).is_err());

    let (_, mut t) = storage()
        .into_iter()
        .find(|(_, t)| {
            t.ops
                .iter()
                .any(|op| matches!(op.expected, Observed::Present(_)))
        })
        .expect("a storage trace with has");
    let op = t
        .ops
        .iter_mut()
        .find(|op| matches!(op.expected, Observed::Present(_)))
        .expect("a has");
    if let Observed::Present(p) = &mut op.expected {
        *p = !*p;
    }
    assert!(check_storage(&t).is_err());
}
