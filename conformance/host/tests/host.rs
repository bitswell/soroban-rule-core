//! The Soroban vectors in `conformance/vectors/soroban`, or under the
//! directory the `CONFORMANCE_VECTORS` environment variable names, replayed on
//! the host this crate pins.

use std::path::PathBuf;

use rule_eval_conformance::soroban::{
    HostTrace, JsonEvent, StorageTrace, ValueVector, load_dir, vectors_dir,
};
use soroban_host_p27 as harness;

fn failures<T>(vs: &[(PathBuf, T)], check: impl Fn(&T) -> Result<(), String>) -> Vec<String> {
    vs.iter()
        .filter_map(|(path, v)| check(v).err().map(|e| format!("{}: {e}", path.display())))
        .collect()
}

fn host_traces() -> Vec<(PathBuf, HostTrace)> {
    load_dir(&vectors_dir("host")).unwrap_or_else(|e| panic!("{e}"))
}

/// The ledger testutils gives a fresh environment is at the pinned protocol.
/// The SDK deprecates reading the protocol version from contracts; a test
/// reads it to name the protocol the vectors ran at.
#[test]
#[allow(deprecated)]
fn the_host_runs_the_pinned_protocol() {
    assert_eq!(harness::env().ledger().protocol_version(), 27);
}

#[test]
fn every_value_crosses_the_host_unchanged() {
    let vs: Vec<(PathBuf, ValueVector)> =
        load_dir(&vectors_dir("values")).unwrap_or_else(|e| panic!("{e}"));
    assert!(!vs.is_empty(), "no value vectors found");
    let failed = failures(&vs, harness::check_values);
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

#[test]
fn storage_on_the_host_agrees_with_every_storage_trace() {
    let ts: Vec<(PathBuf, StorageTrace)> =
        load_dir(&vectors_dir("storage")).unwrap_or_else(|e| panic!("{e}"));
    assert!(!ts.is_empty(), "no storage traces found");
    let failed = failures(&ts, harness::check_storage);
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

#[test]
fn the_host_agrees_with_every_host_trace() {
    let ts = host_traces();
    assert!(!ts.is_empty(), "no host traces found");
    let failed = failures(&ts, harness::check_host);
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

/// The harness reports a changed outcome, a missing event, a changed
/// payload, a changed read and a changed slot.
#[test]
fn a_wrong_host_expectation_is_reported() {
    let trace = |name: &str| {
        host_traces()
            .into_iter()
            .find(|(path, _)| path.file_stem().is_some_and(|s| s == name))
            .unwrap_or_else(|| panic!("no host trace {name}"))
            .1
    };

    let mut t = trace("host-exact-tree");
    t.txs[0].expected.ok = false;
    assert!(harness::check_host(&t).is_err(), "a changed outcome");

    let mut t = trace("host-exact-tree");
    t.txs[0].expected.events.pop();
    assert!(harness::check_host(&t).is_err(), "a missing event");

    let mut t = trace("host-exact-tree");
    let Some(JsonEvent::CheckAuth(check)) = t.txs[0].expected.events.first_mut() else {
        panic!("host-exact-tree starts with __check_auth")
    };
    check.preimage.nonce = "2".into();
    assert!(harness::check_host(&t).is_err(), "a changed payload");

    let mut t = trace("host-reentrant-instance");
    let Some(JsonEvent::Read { value, .. }) = t.txs[0].expected.events.get_mut(1) else {
        panic!("host-reentrant-instance reads in __check_auth")
    };
    *value = None;
    assert!(harness::check_host(&t).is_err(), "a changed read");

    let mut t = trace("host-rollback-caught");
    t.txs[0].expected.store[0].value = None;
    assert!(harness::check_host(&t).is_err(), "a changed slot");
}
