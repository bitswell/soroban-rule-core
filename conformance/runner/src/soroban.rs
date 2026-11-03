//! The Soroban vectors: value and context vectors, storage traces and host
//! traces (`conformance/vectors/soroban`), decoded into `soroban-facade`'s
//! types.
//!
//! [`check_values`], [`check_context`] and [`check_storage`] check the
//! facade's plain code against the Lean models: its XDR, its reading of
//! `__check_auth`'s contexts, its conversion to `rule-eval`'s contexts and its
//! plain storage. Host traces need a host; `conformance/host` replays them on
//! `soroban-env-host`.

use std::fs;
use std::path::{Path, PathBuf};

use rule_eval::{Context, val_eq};
use serde::Deserialize;
use serde::de::DeserializeOwned;
use soroban_facade::{
    Address, AuthContext, Durability, PlainHost, Refusal, Storage, Val, auth_contexts,
    contexts_to_rule_eval, val_to_rule_eval, xdr,
};

use crate::{
    JsonContext, JsonRule, JsonSigner, JsonVal, decode_context, decode_decimal, decode_hex,
};

/// The Soroban vector format version this runner reads.
pub const FORMAT: u32 = 1;

// ---------------------------------------------------------------------------
// Values and contexts.

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonAddress {
    Account(String),
    Contract(String),
    MuxedAccount { id: String, key: String },
}

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonValue {
    Void(()),
    Bool(bool),
    U32(u32),
    U64(String),
    I128(String),
    Bytes(String),
    String(String),
    Symbol(String),
    Address(JsonAddress),
    Vec(Vec<JsonValue>),
    Map(Vec<(JsonValue, JsonValue)>),
    Other(String),
}

#[derive(Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum JsonDurability {
    Persistent,
    Temporary,
    Instance,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonAuthContext {
    Contract {
        contract: JsonAddress,
        fn_name: String,
        args: Vec<JsonValue>,
    },
    CreateContract {
        wasm_hash: String,
        salt: String,
        constructor_args: Vec<JsonValue>,
    },
}

/// One value vector file.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ValueVector {
    pub format: u32,
    pub name: String,
    pub description: String,
    pub values: Vec<ValueCase>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ValueCase {
    pub value: JsonValue,
    /// The value's `ScVal` XDR.
    pub xdr: String,
    /// What `rule-eval` reads of the value.
    pub rule_eval: JsonVal,
    /// Whether the value may be a storage key.
    pub storable: bool,
}

/// One context vector file.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContextVector {
    pub format: u32,
    pub name: String,
    pub description: String,
    /// The value `__check_auth` would receive as its contexts.
    pub value: JsonValue,
    pub xdr: String,
    /// The contexts read from it, or `null` when one cannot be read.
    pub expected: Option<ContextsRead>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContextsRead {
    pub contexts: Vec<JsonAuthContext>,
    pub rule_eval: Vec<JsonContext>,
}

fn array32(s: &str) -> Result<[u8; 32], String> {
    decode_hex(s)?
        .try_into()
        .map_err(|_| format!("not 32 bytes: {s:?}"))
}

/// # Errors
///
/// If a key or id is not 32 bytes of lowercase hex, or an id is malformed.
pub fn decode_address(a: &JsonAddress) -> Result<Address, String> {
    Ok(match a {
        JsonAddress::Account(k) => Address::Account(array32(k)?),
        JsonAddress::Contract(i) => Address::Contract(array32(i)?),
        JsonAddress::MuxedAccount { id, key } => Address::MuxedAccount {
            id: decode_decimal(id)?,
            key: array32(key)?,
        },
    })
}

/// # Errors
///
/// If a payload is not lowercase hex or an integer is malformed or out of
/// range.
pub fn decode_value(v: &JsonValue) -> Result<Val, String> {
    Ok(match v {
        JsonValue::Void(()) => Val::Void,
        JsonValue::Bool(b) => Val::Bool(*b),
        JsonValue::U32(n) => Val::U32(*n),
        JsonValue::U64(n) => Val::U64(decode_decimal(n)?),
        JsonValue::I128(n) => Val::I128(decode_decimal(n)?),
        JsonValue::Bytes(b) => Val::Bytes(decode_hex(b)?),
        JsonValue::String(b) => Val::String(decode_hex(b)?),
        JsonValue::Symbol(b) => Val::Symbol(decode_hex(b)?),
        JsonValue::Address(a) => Val::Address(decode_address(a)?),
        JsonValue::Vec(items) => Val::Vec(decode_values(items)?),
        JsonValue::Map(entries) => Val::Map(
            entries
                .iter()
                .map(|(k, v)| Ok((decode_value(k)?, decode_value(v)?)))
                .collect::<Result<_, String>>()?,
        ),
        JsonValue::Other(x) => Val::Other(decode_hex(x)?),
    })
}

/// # Errors
///
/// As [`decode_value`].
pub fn decode_values(vs: &[JsonValue]) -> Result<Vec<Val>, String> {
    vs.iter().map(decode_value).collect()
}

#[must_use]
pub fn decode_durability(d: JsonDurability) -> Durability {
    match d {
        JsonDurability::Persistent => Durability::Persistent,
        JsonDurability::Temporary => Durability::Temporary,
        JsonDurability::Instance => Durability::Instance,
    }
}

/// # Errors
///
/// As [`decode_value`], or if a hash or salt is not 32 bytes.
pub fn decode_auth_context(c: &JsonAuthContext) -> Result<AuthContext, String> {
    Ok(match c {
        JsonAuthContext::Contract {
            contract,
            fn_name,
            args,
        } => AuthContext::Contract {
            contract: decode_address(contract)?,
            fn_name: decode_hex(fn_name)?,
            args: decode_values(args)?,
        },
        JsonAuthContext::CreateContract {
            wasm_hash,
            salt,
            constructor_args,
        } => AuthContext::CreateContract {
            wasm_hash: array32(wasm_hash)?,
            salt: array32(salt)?,
            constructor_args: decode_values(constructor_args)?,
        },
    })
}

/// # Errors
///
/// As [`decode_auth_context`].
pub fn decode_auth_contexts(cs: &[JsonAuthContext]) -> Result<Vec<AuthContext>, String> {
    cs.iter().map(decode_auth_context).collect()
}

/// Whether two `rule-eval` contexts are the same: same constructor and equal
/// fields, values compared as `rule-eval` compares them.
#[must_use]
pub fn context_eq(a: &Context, b: &Context) -> bool {
    match (a, b) {
        (
            Context::Call {
                contract: c1,
                function: f1,
                args: a1,
            },
            Context::Call {
                contract: c2,
                function: f2,
                args: a2,
            },
        ) => {
            c1 == c2
                && f1 == f2
                && a1.len() == a2.len()
                && a1.iter().zip(a2).all(|(x, y)| val_eq(x, y))
        }
        (Context::Create { wasm_hash: h1 }, Context::Create { wasm_hash: h2 }) => h1 == h2,
        _ => false,
    }
}

/// Whether two lists of `rule-eval` contexts are the same, in order.
#[must_use]
pub fn contexts_eq(a: &[Context], b: &[Context]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| context_eq(x, y))
}

/// # Errors
///
/// As [`decode_context`].
pub fn decode_rule_eval_contexts(cs: &[JsonContext]) -> Result<Vec<Context>, String> {
    cs.iter().map(decode_context).collect()
}

/// Checks every value of a value vector: the facade writes the XDR the model
/// computes and reads it back, converts the value as the model does for
/// `rule-eval`, and agrees on whether it may be a storage key.
///
/// # Errors
///
/// A description of the first value that differs.
pub fn check_values(v: &ValueVector) -> Result<(), String> {
    if v.format != FORMAT {
        return Err(format!(
            "format {} where the runner reads {FORMAT}",
            v.format
        ));
    }
    for (i, case) in v.values.iter().enumerate() {
        let value = decode_value(&case.value)?;
        let want = decode_hex(&case.xdr)?;
        let got = xdr::encode(&value);
        if got != want {
            return Err(format!(
                "value {i} ({value:?}): XDR {got:02x?}, expected {want:02x?}"
            ));
        }
        match xdr::decode(&want) {
            Some(back) if back == value => {}
            other => return Err(format!("value {i}: XDR reads back as {other:?}")),
        }
        if !val_eq(
            &val_to_rule_eval(&value),
            &crate::decode_val(&case.rule_eval)?,
        ) {
            return Err(format!(
                "value {i} ({value:?}): rule-eval reads it differently"
            ));
        }
        if value.storable() != case.storable {
            return Err(format!(
                "value {i} ({value:?}): storable is {}",
                value.storable()
            ));
        }
    }
    Ok(())
}

/// Checks a context vector: the facade reads the same contexts from the
/// value as the model, or refuses the same value, writes each context back
/// as the same value, and converts them as the model does for `rule-eval`.
///
/// # Errors
///
/// A description of the first difference.
pub fn check_context(v: &ContextVector) -> Result<(), String> {
    if v.format != FORMAT {
        return Err(format!(
            "format {} where the runner reads {FORMAT}",
            v.format
        ));
    }
    let value = decode_value(&v.value)?;
    if xdr::encode(&value) != decode_hex(&v.xdr)? {
        return Err("the value's XDR differs".into());
    }
    let read = auth_contexts(&value);
    match (&v.expected, read) {
        (None, None) => Ok(()),
        (None, Some(cs)) => Err(format!("read {cs:?} where the model reads nothing")),
        (Some(_), None) => Err("read nothing where the model reads contexts".into()),
        (Some(want), Some(got)) => {
            let want_contexts = decode_auth_contexts(&want.contexts)?;
            if got != want_contexts {
                return Err(format!("read {got:?}, expected {want_contexts:?}"));
            }
            if let Val::Vec(items) = &value {
                for (c, item) in got.iter().zip(items) {
                    if c.to_val() != *item {
                        return Err(format!("{c:?} writes back as {:?}", c.to_val()));
                    }
                }
            }
            if !contexts_eq(
                &contexts_to_rule_eval(&got),
                &decode_rule_eval_contexts(&want.rule_eval)?,
            ) {
                return Err("rule-eval reads the contexts differently".into());
            }
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// Storage traces.

/// One storage trace file.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StorageTrace {
    pub format: u32,
    pub name: String,
    pub description: String,
    pub contract: JsonAddress,
    pub ops: Vec<StorageOp>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StorageOp {
    pub op: OpKind,
    pub durability: JsonDurability,
    pub key: JsonValue,
    /// The value `set` writes.
    #[serde(default)]
    pub val: Option<JsonValue>,
    pub expected: Observed,
}

#[derive(Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum OpKind {
    Get,
    Has,
    Set,
    Remove,
}

/// What an operation returned.
#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum Observed {
    /// What `get` read, `null` for nothing.
    Value(Option<JsonValue>),
    /// What `has` found.
    Present(bool),
    /// `set` or `remove` done.
    Done,
    /// The key holds a muxed address.
    Refused,
}

/// One storage operation on `s`, and what it returned.
///
/// # Errors
///
/// As [`decode_value`], or if `set` has no value.
pub fn apply_op<S: Storage>(
    s: &mut S,
    op: &StorageOp,
) -> Result<Result<Observation, Refusal>, String> {
    let d = decode_durability(op.durability);
    let key = decode_value(&op.key)?;
    Ok(match op.op {
        OpKind::Get => s.get(d, &key).map(Observation::Value),
        OpKind::Has => s.has(d, &key).map(Observation::Present),
        OpKind::Set => {
            let val = decode_value(op.val.as_ref().ok_or("set without a value")?)?;
            s.set(d, &key, &val).map(|()| Observation::Done)
        }
        OpKind::Remove => s.remove(d, &key).map(|()| Observation::Done),
    })
}

/// What an operation returned, decoded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Observation {
    Value(Option<Val>),
    Present(bool),
    Done,
}

/// Whether an operation's result is what the trace expects.
///
/// # Errors
///
/// As [`decode_value`].
pub fn observed_matches(
    got: &Result<Observation, Refusal>,
    want: &Observed,
) -> Result<bool, String> {
    Ok(match (got, want) {
        (Ok(Observation::Value(v)), Observed::Value(w)) => {
            *v == w.as_ref().map(decode_value).transpose()?
        }
        (Ok(Observation::Present(p)), Observed::Present(q)) => p == q,
        (Ok(Observation::Done), Observed::Done)
        | (Err(Refusal::MuxedAddress), Observed::Refused) => true,
        _ => false,
    })
}

/// Runs a storage trace on [`PlainHost`] and compares every result.
///
/// # Errors
///
/// A description of the first operation whose result differs.
pub fn check_storage(t: &StorageTrace) -> Result<(), String> {
    if t.format != FORMAT {
        return Err(format!(
            "format {} where the runner reads {FORMAT}",
            t.format
        ));
    }
    let mut host = PlainHost::new();
    for (i, op) in t.ops.iter().enumerate() {
        let got = apply_op(&mut host, op)?;
        if !observed_matches(&got, &op.expected)? {
            return Err(format!(
                "op {i} ({:?}): got {got:?}, expected {:?}",
                op.op, op.expected
            ));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Host traces.

/// One host trace file.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HostTrace {
    pub format: u32,
    pub name: String,
    pub description: String,
    /// Every contract the trace calls, signs as or delegates to.
    pub contracts: Vec<JsonAddress>,
    pub accounts: Vec<JsonAccount>,
    pub txs: Vec<JsonTx>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonAccount {
    pub address: JsonAddress,
    pub check_auth: Vec<JsonAccountStep>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonTx {
    pub ledger: u32,
    pub entries: Vec<JsonEntry>,
    pub call: JsonCall,
    pub expected: JsonTxExpected,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonTxExpected {
    pub ok: bool,
    pub events: Vec<JsonEvent>,
    pub store: Vec<JsonSlotValue>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonSlotValue {
    pub contract: JsonAddress,
    pub durability: JsonDurability,
    pub key: JsonValue,
    pub value: Option<JsonValue>,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields)]
pub struct JsonInvocation {
    pub context: JsonAuthContext,
    pub subs: Vec<JsonInvocation>,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields)]
pub struct JsonDelegate {
    pub address: JsonAddress,
    pub signature: JsonValue,
    pub nested: Vec<JsonDelegate>,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonCredentials {
    Address,
    AddressV2,
    WithDelegates(Vec<JsonDelegate>),
}

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields)]
pub struct JsonEntry {
    pub address: JsonAddress,
    pub nonce: String,
    pub expiration: u32,
    pub signature: JsonValue,
    pub credentials: JsonCredentials,
    pub root: JsonInvocation,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields)]
pub struct JsonPreimage {
    /// The signer's address, when the credentials bind it.
    pub address: Option<JsonAddress>,
    pub nonce: String,
    pub expiration: u32,
    pub invocation: JsonInvocation,
}

#[derive(Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum JsonFailKind {
    Error,
    Trap,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields)]
pub struct JsonCall {
    pub contract: JsonAddress,
    pub fn_name: String,
    pub args: Vec<JsonValue>,
    pub body: Vec<JsonStep>,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields)]
pub struct JsonSlot {
    pub durability: JsonDurability,
    pub key: JsonValue,
}

#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields)]
pub struct JsonPut {
    pub durability: JsonDurability,
    pub key: JsonValue,
    pub val: JsonValue,
}

/// A step of a contract call.
#[derive(Deserialize, Clone, Debug)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonStep {
    Get(JsonSlot),
    Has(JsonSlot),
    Put(JsonPut),
    Remove(JsonSlot),
    RequireAuth(JsonAddress),
    Call { callee: JsonCall, catches: bool },
    Fail(JsonFailKind),
}

/// A step of an account's `__check_auth`.
#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonAccountStep {
    Get(JsonSlot),
    Put(JsonPut),
    Remove(JsonSlot),
    CheckRules {
        rules: Vec<JsonRule>,
        authenticated: Vec<JsonSigner>,
    },
    Delegate(JsonAddress),
    Fail(JsonFailKind),
}

#[derive(Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum JsonVia {
    Invoker,
    Entry,
}

/// What a `__check_auth` call received.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsonCheckAuth {
    pub account: JsonAddress,
    pub preimage: JsonPreimage,
    pub signature: JsonValue,
    pub contexts: Vec<JsonAuthContext>,
    /// The contexts as the value the host passes them in.
    pub contexts_value: JsonValue,
    /// The contexts as `rule-eval` reads them.
    pub rule_eval_contexts: Vec<JsonContext>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum JsonEvent {
    CheckAuth(Box<JsonCheckAuth>),
    Read {
        contract: JsonAddress,
        durability: JsonDurability,
        key: JsonValue,
        value: Option<JsonValue>,
    },
    Found {
        contract: JsonAddress,
        durability: JsonDurability,
        key: JsonValue,
        present: bool,
    },
    Authorized {
        address: JsonAddress,
        context: JsonAuthContext,
        via: JsonVia,
    },
}

// ---------------------------------------------------------------------------
// Loading.

/// A name a vector file must carry: its file name without `.json`.
pub trait Named {
    fn name(&self) -> &str;
}

impl Named for ValueVector {
    fn name(&self) -> &str {
        &self.name
    }
}

impl Named for ContextVector {
    fn name(&self) -> &str {
        &self.name
    }
}

impl Named for StorageTrace {
    fn name(&self) -> &str {
        &self.name
    }
}

impl Named for HostTrace {
    fn name(&self) -> &str {
        &self.name
    }
}

/// Every `.json` file in `dir`, in file-name order, each decoded.
///
/// # Errors
///
/// If the directory cannot be read, a file is not valid JSON of the type, or
/// a vector's name differs from its file name.
pub fn load_dir<T: DeserializeOwned + Named>(dir: &Path) -> Result<Vec<(PathBuf, T)>, String> {
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
        let v: T = serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
        if path.file_stem().and_then(|s| s.to_str()) != Some(v.name()) {
            return Err(format!(
                "{}: name {:?} differs from the file name",
                path.display(),
                v.name()
            ));
        }
        out.push((path, v));
    }
    Ok(out)
}

/// The directory of the Soroban vectors of one kind: `soroban/<kind>` under
/// the directory `CONFORMANCE_VECTORS` names, or under `conformance/vectors`.
#[must_use]
pub fn vectors_dir(kind: &str) -> PathBuf {
    std::env::var_os("CONFORMANCE_VECTORS")
        .map_or_else(
            || Path::new(env!("CARGO_MANIFEST_DIR")).join("../vectors"),
            PathBuf::from,
        )
        .join("soroban")
        .join(kind)
}
