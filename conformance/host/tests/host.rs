//! The Soroban vectors in `conformance/vectors/soroban`, or under the
//! directory the `CONFORMANCE_VECTORS` environment variable names, replayed on
//! the host this crate pins.

use std::path::PathBuf;

use rule_eval_conformance::soroban::{
    ContextVector, HostTrace, JsonEvent, StorageTrace, ValueVector, load_dir, vectors_dir,
};

fn failures<T>(vs: &[(PathBuf, T)], check: impl Fn(&T) -> Result<(), String>) -> Vec<String> {
    vs.iter()
        .filter_map(|(path, v)| check(v).err().map(|e| format!("{}: {e}", path.display())))
        .collect()
}

fn host_traces() -> Vec<(PathBuf, HostTrace)> {
    load_dir(&vectors_dir("host")).unwrap_or_else(|e| panic!("{e}"))
}

/// The ledger testutils gives a fresh environment is at the protocol the
/// entry's name gives (`soroban-host-p29` runs protocol 29). The SDK
/// deprecates reading the protocol version from contracts; a test reads it to
/// name the protocol the vectors ran at.
#[test]
#[allow(deprecated)]
fn the_host_runs_the_pinned_protocol() {
    let protocol: u32 = env!("CARGO_PKG_NAME")
        .strip_prefix("soroban-host-p")
        .and_then(|p| p.parse().ok())
        .expect("an entry is named soroban-host-p<protocol>");
    assert_eq!(harness::env().ledger().protocol_version(), protocol);
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
fn the_sdk_reads_every_context_vector_as_the_model_does() {
    let vs: Vec<(PathBuf, ContextVector)> =
        load_dir(&vectors_dir("contexts")).unwrap_or_else(|e| panic!("{e}"));
    assert!(!vs.is_empty(), "no context vectors found");
    let failed = failures(&vs, harness::check_contexts);
    assert!(failed.is_empty(), "{}", failed.join("\n"));

    let (_, mut v) = vs
        .into_iter()
        .find(|(path, _)| {
            path.file_stem()
                .is_some_and(|s| s == "contexts-create-external-ref")
        })
        .expect("a context vector of external references");
    v.expected = None;
    assert!(
        harness::check_contexts(&v).is_err(),
        "a refusal the SDK does not make is reported"
    );
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

/// soroban-env-host's own authorization tests, transcribed into host traces
/// (`conformance/vectors/soroban/seed/host`).
#[test]
fn the_host_agrees_with_every_seed_trace() {
    let ts: Vec<(PathBuf, HostTrace)> =
        load_dir(&vectors_dir("seed/host")).unwrap_or_else(|e| panic!("{e}"));
    assert!(!ts.is_empty(), "no seed host traces found");
    let failed = failures(&ts, harness::check_host);
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

/// soroban-env-host's own storage tests, transcribed into storage traces
/// (`conformance/vectors/soroban/seed/storage`).
#[test]
fn storage_on_the_host_agrees_with_every_seed_storage_trace() {
    let ts: Vec<(PathBuf, StorageTrace)> =
        load_dir(&vectors_dir("seed/storage")).unwrap_or_else(|e| panic!("{e}"));
    assert!(!ts.is_empty(), "no seed storage traces found");
    let failed = failures(&ts, harness::check_storage);
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

/// An executable tag (CAP-85) is no value the facade models, so its real
/// implementation refuses one as a key or a value before the host sees it:
/// the host takes the tag's XDR, but would let a contract put such a key only
/// in persistent storage and only with a Wasm hash, and never remove it.
#[cfg(feature = "facade")]
#[test]
fn the_facade_refuses_an_executable_tag() {
    use soroban_facade::{Durability, Refusal, SdkHost, Storage, Val, xdr};
    use soroban_sdk::xdr::FromXdr;

    let env = harness::env();
    // SCV_EXECUTABLE_TAG, then the string "v1".
    let tag = Val::Other(vec![0, 0, 0, 22, 0, 0, 0, 2, b'v', b'1', 0, 0]);
    let bytes = soroban_sdk::Bytes::from_slice(&env, &xdr::encode(&tag));
    assert!(
        soroban_sdk::Val::from_xdr(&env, &bytes).is_ok(),
        "the host takes an executable tag's XDR"
    );
    assert_eq!(xdr::decode(&xdr::encode(&tag)), None);

    let mut host = SdkHost::new(&env);
    assert!(host.to_sdk(&tag).is_none());
    let hash = Val::Bytes(vec![1; 32]);
    for d in [
        Durability::Persistent,
        Durability::Temporary,
        Durability::Instance,
    ] {
        assert_eq!(host.set(d, &tag, &hash), Err(Refusal::Undecodable));
        assert_eq!(host.remove(d, &tag), Err(Refusal::Undecodable));
        assert_eq!(host.get(d, &tag), Err(Refusal::Undecodable));
        assert_eq!(host.has(d, &tag), Err(Refusal::Undecodable));
    }
    assert_eq!(
        host.set(Durability::Persistent, &Val::Symbol(b"k".to_vec()), &tag),
        Err(Refusal::Undecodable)
    );
}
