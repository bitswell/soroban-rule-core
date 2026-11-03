//! Replays the Soroban vectors of `conformance/vectors/soroban` on
//! `soroban-env-host`, through soroban-sdk's testutils, with enforcing
//! authorization (`set_auths`).
//!
//! Every contract a host trace names is registered as a native contract
//! ([`Dispatcher`]) that runs what the trace says: before each call the
//! harness hands the callee the body the trace gives that call, and the
//! callee runs its steps on the host; `__check_auth` records what it receives
//! and runs the account's program. Each transaction's entries are installed
//! with `set_auths`, its top call is invoked with `try_invoke_contract`, and
//! the harness compares, with the model's:
//!
//! - whether the transaction succeeded (refusals are compared as refusals,
//!   whatever error the host reports);
//! - every event, in order: each `__check_auth` call's account, payload
//!   (SHA-256 of the model's preimage, built with `stellar-xdr` and the
//!   ledger's network id), signature and contexts (as the host's value, as
//!   `soroban-facade` reads them and as `rule-eval` reads those), each read,
//!   each presence check and each `require_auth` that held;
//! - every slot's value after the transaction.
//!
//! With the `facade` feature, storage, `require_auth` and the reading of
//! `__check_auth`'s contexts go through `soroban-facade`'s real
//! implementation ([`soroban_facade::SdkHost`]); without it, through the SDK
//! directly, with the facade's plain reading of the contexts.
//!
//! The same source builds against each host version a crate in this
//! directory pins.

use std::cell::RefCell;
use std::rc::Rc;

use rule_eval_conformance::soroban::{
    ContextVector, HostTrace, JsonAccountStep, JsonAddress, JsonCall, JsonCredentials,
    JsonDelegate, JsonEntry, JsonEvent, JsonFailKind, JsonInvocation, JsonPreimage, JsonSlot,
    JsonStep, JsonTx, StorageTrace, ValueVector, contexts_eq, decode_address, decode_auth_context,
    decode_auth_contexts, decode_durability, decode_rule_eval_contexts, decode_value,
    decode_values,
};
use rule_eval_conformance::{decode_hex, decode_rules, decode_signers};
use sha2::{Digest, Sha256};
use soroban_facade::{Address, AuthContext, Durability, Val, contexts_to_rule_eval, xdr};
use soroban_sdk::testutils::{ContractFunctionSet, EnvTestConfig, Ledger as _};
use soroban_sdk::xdr::{
    Hash, HashIdPreimage, HashIdPreimageSorobanAuthorization,
    HashIdPreimageSorobanAuthorizationWithAddress, InvokeContractArgs, Limits, ReadXdr, ScAddress,
    ScSymbol, ScVal, SorobanAddressCredentials, SorobanAddressCredentialsWithDelegates,
    SorobanAuthorizationEntry, SorobanAuthorizedFunction, SorobanAuthorizedInvocation,
    SorobanCredentials, SorobanDelegateSignature, StringM, WriteXdr,
};
use soroban_sdk::{Address as SdkAddress, BytesN, Env, Error, Symbol, TryFromVal, Val as SdkVal};

/// A fresh testutils environment that writes no test snapshot and records
/// no diagnostic events.
///
/// Diagnostic events are no part of what the harness compares. With them on
/// (testutils' default), a native contract's storage call refused because its
/// key holds a muxed address leaves the host's shadow budget spent while the
/// refusal is recorded, and the next invocation hook (testutils' record of
/// the authorizations) panics with `Error(Budget, ExceededLimit)`, on
/// soroban-env-host 29.0.1 and 30.0.0 alike.
///
/// # Panics
///
/// If the host refuses the diagnostic level.
#[must_use]
pub fn env() -> Env {
    let env = Env::new_with_config(EnvTestConfig {
        capture_snapshot_at_drop: false,
    });
    env.host()
        .set_diagnostic_level(soroban_env_host::DiagnosticLevel::None)
        .expect("the host takes a diagnostic level");
    env
}

// ---------------------------------------------------------------------------
// Values across the host boundary.

/// The `stellar-xdr` value of a facade value.
///
/// # Panics
///
/// If the facade's XDR of `v` is not a valid `ScVal`.
#[must_use]
pub fn scval(v: &Val) -> ScVal {
    ScVal::from_xdr(xdr::encode(v), Limits::none()).expect("the facade writes valid ScVal XDR")
}

/// The facade value of a `stellar-xdr` value.
///
/// # Panics
///
/// If the facade cannot read the value's XDR.
#[must_use]
pub fn facade_val(v: &ScVal) -> Val {
    let bytes = v.to_xdr(Limits::none()).expect("ScVal writes");
    xdr::decode(&bytes).expect("the facade reads every value the host gives")
}

/// The host value of a facade value.
///
/// # Panics
///
/// If the host cannot represent the value.
#[must_use]
pub fn to_host(env: &Env, v: &Val) -> SdkVal {
    SdkVal::try_from_val(env, &scval(v)).expect("the host represents the value")
}

/// The facade value of a host value.
///
/// # Panics
///
/// If the host value has no `ScVal` or the facade cannot read it.
#[must_use]
pub fn from_host(env: &Env, v: &SdkVal) -> Val {
    facade_val(&ScVal::try_from_val(env, v).expect("the host value has an ScVal"))
}

/// The `stellar-xdr` address of a facade address.
///
/// # Panics
///
/// If the facade's XDR of the address is not a valid `ScAddress`.
#[must_use]
pub fn scaddress(a: &Address) -> ScAddress {
    ScAddress::from_xdr(xdr::address_xdr(a), Limits::none()).expect("valid ScAddress XDR")
}

/// The host address of a facade address.
///
/// # Panics
///
/// If the address is a muxed account.
#[must_use]
pub fn sdk_address(env: &Env, a: &Address) -> SdkAddress {
    SdkAddress::try_from_val(env, &scaddress(a)).expect("an account or contract address")
}

fn scsymbol(b: &[u8]) -> ScSymbol {
    ScSymbol(StringM::try_from(b.to_vec()).expect("a symbol of at most 32 bytes"))
}

fn symbol(env: &Env, b: &[u8]) -> Symbol {
    Symbol::new(env, std::str::from_utf8(b).expect("an ASCII symbol"))
}

// ---------------------------------------------------------------------------
// Storage, require_auth and contexts: through the facade, or through the SDK.

#[cfg(feature = "facade")]
mod backend {
    use soroban_facade::{Address, Auth, AuthContext, Durability, SdkHost, Storage, Val};
    use soroban_sdk::{Env, Val as SdkVal};

    pub fn get(env: &Env, d: Durability, key: &Val) -> Option<Option<Val>> {
        SdkHost::new(env).get(d, key).ok()
    }

    pub fn has(env: &Env, d: Durability, key: &Val) -> Option<bool> {
        SdkHost::new(env).has(d, key).ok()
    }

    pub fn set(env: &Env, d: Durability, key: &Val, val: &Val) -> Option<()> {
        SdkHost::new(env).set(d, key, val).ok()
    }

    pub fn remove(env: &Env, d: Durability, key: &Val) -> Option<()> {
        SdkHost::new(env).remove(d, key).ok()
    }

    pub fn require_auth(env: &Env, a: &Address) -> Option<()> {
        SdkHost::new(env).require_auth(a).ok()
    }

    pub fn contexts(env: &Env, v: SdkVal) -> Option<Vec<AuthContext>> {
        SdkHost::new(env).auth_contexts(v)
    }
}

#[cfg(not(feature = "facade"))]
mod backend {
    use soroban_facade::{Address, AuthContext, Durability, Val, auth_contexts};
    use soroban_sdk::{Env, Val as SdkVal};

    use super::{from_host, sdk_address, to_host};

    // A key holding a muxed address makes the host trap in persistent and
    // temporary storage, which the harness sees as the call failing.

    pub fn get(env: &Env, d: Durability, key: &Val) -> Option<Option<Val>> {
        let k = to_host(env, key);
        let s = env.storage();
        let v: Option<SdkVal> = match d {
            Durability::Persistent => s.persistent().get(&k),
            Durability::Temporary => s.temporary().get(&k),
            Durability::Instance => s.instance().get(&k),
        };
        Some(v.map(|v| from_host(env, &v)))
    }

    pub fn has(env: &Env, d: Durability, key: &Val) -> Option<bool> {
        let k = to_host(env, key);
        let s = env.storage();
        Some(match d {
            Durability::Persistent => s.persistent().has(&k),
            Durability::Temporary => s.temporary().has(&k),
            Durability::Instance => s.instance().has(&k),
        })
    }

    pub fn set(env: &Env, d: Durability, key: &Val, val: &Val) -> Option<()> {
        let (k, v) = (to_host(env, key), to_host(env, val));
        let s = env.storage();
        match d {
            Durability::Persistent => s.persistent().set(&k, &v),
            Durability::Temporary => s.temporary().set(&k, &v),
            Durability::Instance => s.instance().set(&k, &v),
        }
        Some(())
    }

    pub fn remove(env: &Env, d: Durability, key: &Val) -> Option<()> {
        let k = to_host(env, key);
        let s = env.storage();
        match d {
            Durability::Persistent => s.persistent().remove(&k),
            Durability::Temporary => s.temporary().remove(&k),
            Durability::Instance => s.instance().remove(&k),
        }
        Some(())
    }

    pub fn require_auth(env: &Env, a: &Address) -> Option<()> {
        sdk_address(env, a).require_auth();
        Some(())
    }

    pub fn contexts(env: &Env, v: SdkVal) -> Option<Vec<AuthContext>> {
        auth_contexts(&from_host(env, &v))
    }
}

// ---------------------------------------------------------------------------
// The contracts.

/// What the harness saw run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    CheckAuth {
        account: Address,
        payload: [u8; 32],
        signature: Val,
        /// The contexts, as the host passed them.
        contexts_value: Val,
        /// The contexts as the facade reads them.
        contexts: Option<Vec<AuthContext>>,
    },
    Read {
        contract: Address,
        durability: Durability,
        key: Val,
        value: Option<Val>,
    },
    Found {
        contract: Address,
        durability: Durability,
        key: Val,
        present: bool,
    },
    Authorized {
        address: Address,
        context: AuthContext,
    },
}

/// What the contracts of a trace share: the call about to start, with the
/// body the trace gives it, the accounts' programs and what ran.
#[derive(Default)]
pub struct State {
    pending: Option<(AuthContext, Vec<JsonStep>)>,
    accounts: Vec<(Address, Vec<JsonAccountStep>)>,
    events: Vec<Event>,
}

/// A native contract that runs what the trace says.
pub struct Dispatcher {
    state: Rc<RefCell<State>>,
}

fn contract_error() -> SdkVal {
    Error::from_contract_error(1).into()
}

fn slot(s: &JsonSlot) -> (Durability, Val) {
    (
        decode_durability(s.durability),
        decode_value(&s.key).expect("a key"),
    )
}

impl Dispatcher {
    fn log(&self, e: Event) {
        self.state.borrow_mut().events.push(e);
    }

    /// Runs a call's body. A failing step returns a contract error or traps,
    /// so the host fails the call and rolls it back.
    fn run(&self, env: &Env, me: &Address, context: &AuthContext, body: &[JsonStep]) -> SdkVal {
        for step in body {
            match step {
                JsonStep::Get(s) => {
                    let (d, key) = slot(s);
                    let Some(value) = backend::get(env, d, &key) else {
                        return contract_error();
                    };
                    self.log(Event::Read {
                        contract: me.clone(),
                        durability: d,
                        key,
                        value,
                    });
                }
                JsonStep::Has(s) => {
                    let (d, key) = slot(s);
                    let Some(present) = backend::has(env, d, &key) else {
                        return contract_error();
                    };
                    self.log(Event::Found {
                        contract: me.clone(),
                        durability: d,
                        key,
                        present,
                    });
                }
                JsonStep::Put(p) => {
                    let d = decode_durability(p.durability);
                    let key = decode_value(&p.key).expect("a key");
                    let val = decode_value(&p.val).expect("a value");
                    if backend::set(env, d, &key, &val).is_none() {
                        return contract_error();
                    }
                }
                JsonStep::Remove(s) => {
                    let (d, key) = slot(s);
                    if backend::remove(env, d, &key).is_none() {
                        return contract_error();
                    }
                }
                JsonStep::RequireAuth(a) => {
                    let address = decode_address(a).expect("an address");
                    // A refusal traps inside the SDK and does not return.
                    if backend::require_auth(env, &address).is_none() {
                        return contract_error();
                    }
                    self.log(Event::Authorized {
                        address,
                        context: context.clone(),
                    });
                }
                JsonStep::Call { callee, catches } => {
                    if !invoke(env, &self.state, callee) && !catches {
                        return contract_error();
                    }
                }
                JsonStep::Fail(JsonFailKind::Error) => return contract_error(),
                JsonStep::Fail(JsonFailKind::Trap) => panic!("the trace's call traps"),
            }
        }
        SdkVal::VOID.into()
    }

    /// `__check_auth`: records its arguments, then runs the account's program.
    fn check_auth(&self, env: &Env, me: &Address, args: &[SdkVal]) -> SdkVal {
        let [payload, signature, contexts] = args else {
            panic!("__check_auth takes three arguments")
        };
        let payload = BytesN::<32>::try_from_val(env, payload).expect("a 32-byte payload");
        let read = backend::contexts(env, *contexts);
        self.log(Event::CheckAuth {
            account: me.clone(),
            payload: payload.to_array(),
            signature: from_host(env, signature),
            contexts_value: from_host(env, contexts),
            contexts: read.clone(),
        });
        let program = self
            .state
            .borrow()
            .accounts
            .iter()
            .find(|(a, _)| a == me)
            .map(|(_, p)| p.clone())
            .unwrap_or_default();
        for step in &program {
            match step {
                JsonAccountStep::Get(s) => {
                    let (d, key) = slot(s);
                    let Some(value) = backend::get(env, d, &key) else {
                        return contract_error();
                    };
                    self.log(Event::Read {
                        contract: me.clone(),
                        durability: d,
                        key,
                        value,
                    });
                }
                JsonAccountStep::Put(p) => {
                    let d = decode_durability(p.durability);
                    let key = decode_value(&p.key).expect("a key");
                    let val = decode_value(&p.val).expect("a value");
                    if backend::set(env, d, &key, &val).is_none() {
                        return contract_error();
                    }
                }
                JsonAccountStep::Remove(s) => {
                    let (d, key) = slot(s);
                    if backend::remove(env, d, &key).is_none() {
                        return contract_error();
                    }
                }
                JsonAccountStep::CheckRules {
                    rules,
                    authenticated,
                } => {
                    let rules = decode_rules(rules).expect("rules");
                    let authenticated = decode_signers(authenticated).expect("signers");
                    let Some(cs) = &read else {
                        return contract_error();
                    };
                    if !rule_eval::allows_all(&rules, &contexts_to_rule_eval(cs), &authenticated) {
                        return contract_error();
                    }
                }
                JsonAccountStep::Delegate(a) => {
                    let a = decode_address(a).expect("an address");
                    // A refusal traps inside the SDK and does not return.
                    env.custom_account().delegate_auth(&sdk_address(env, &a));
                }
                JsonAccountStep::Fail(JsonFailKind::Error) => return contract_error(),
                JsonAccountStep::Fail(JsonFailKind::Trap) => {
                    panic!("the trace's __check_auth traps")
                }
            }
        }
        SdkVal::VOID.into()
    }
}

impl ContractFunctionSet for Dispatcher {
    fn call(&self, func: &str, env: Env, args: &[SdkVal]) -> Option<SdkVal> {
        let me = match from_host(&env, &env.current_contract_address().to_val()) {
            Val::Address(a) => a,
            other => panic!("the current contract is {other:?}"),
        };
        match func {
            "__constructor" => Some(SdkVal::VOID.into()),
            "__check_auth" => Some(self.check_auth(&env, &me, args)),
            _ => {
                let context = AuthContext::Contract {
                    contract: me.clone(),
                    fn_name: func.as_bytes().to_vec(),
                    args: args.iter().map(|a| from_host(&env, a)).collect(),
                };
                let (expected, body) = self
                    .state
                    .borrow_mut()
                    .pending
                    .take()
                    .unwrap_or_else(|| panic!("the trace starts no call {context:?}"));
                assert_eq!(context, expected, "the host started another call");
                Some(self.run(&env, &me, &context, &body))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Signed entries.

fn invocation(i: &JsonInvocation) -> SorobanAuthorizedInvocation {
    let AuthContext::Contract {
        contract,
        fn_name,
        args,
    } = decode_auth_context(&i.context).expect("a context")
    else {
        panic!("host traces sign contract calls only")
    };
    SorobanAuthorizedInvocation {
        function: SorobanAuthorizedFunction::ContractFn(InvokeContractArgs {
            contract_address: scaddress(&contract),
            function_name: scsymbol(&fn_name),
            args: args
                .iter()
                .map(scval)
                .collect::<Vec<_>>()
                .try_into()
                .expect("arguments"),
        }),
        sub_invocations: i
            .subs
            .iter()
            .map(invocation)
            .collect::<Vec<_>>()
            .try_into()
            .expect("sub-invocations"),
    }
}

fn delegate(d: &JsonDelegate) -> SorobanDelegateSignature {
    SorobanDelegateSignature {
        address: scaddress(&decode_address(&d.address).expect("an address")),
        signature: scval(&decode_value(&d.signature).expect("a signature")),
        nested_delegates: d
            .nested
            .iter()
            .map(delegate)
            .collect::<Vec<_>>()
            .try_into()
            .expect("delegates"),
    }
}

fn entry(e: &JsonEntry) -> SorobanAuthorizationEntry {
    let address_credentials = SorobanAddressCredentials {
        address: scaddress(&decode_address(&e.address).expect("an address")),
        nonce: e.nonce.parse().expect("an i64 nonce"),
        signature_expiration_ledger: e.expiration,
        signature: scval(&decode_value(&e.signature).expect("a signature")),
    };
    let credentials = match &e.credentials {
        JsonCredentials::Address => SorobanCredentials::Address(address_credentials),
        JsonCredentials::AddressV2 => SorobanCredentials::AddressV2(address_credentials),
        JsonCredentials::WithDelegates(ds) => {
            SorobanCredentials::AddressWithDelegates(SorobanAddressCredentialsWithDelegates {
                address_credentials,
                delegates: ds
                    .iter()
                    .map(delegate)
                    .collect::<Vec<_>>()
                    .try_into()
                    .expect("delegates"),
            })
        }
    };
    SorobanAuthorizationEntry {
        credentials,
        root_invocation: invocation(&e.root),
    }
}

/// The signature payload of a preimage: SHA-256 of its `HashIdPreimage` XDR.
fn payload(network_id: [u8; 32], p: &JsonPreimage) -> [u8; 32] {
    let nonce = p.nonce.parse().expect("an i64 nonce");
    let invocation = invocation(&p.invocation);
    let pre = match &p.address {
        None => HashIdPreimage::SorobanAuthorization(HashIdPreimageSorobanAuthorization {
            network_id: Hash(network_id),
            nonce,
            signature_expiration_ledger: p.expiration,
            invocation,
        }),
        Some(a) => HashIdPreimage::SorobanAuthorizationWithAddress(
            HashIdPreimageSorobanAuthorizationWithAddress {
                network_id: Hash(network_id),
                address: scaddress(&decode_address(a).expect("an address")),
                nonce,
                signature_expiration_ledger: p.expiration,
                invocation,
            },
        ),
    };
    Sha256::digest(pre.to_xdr(Limits::none()).expect("the preimage writes")).into()
}

// ---------------------------------------------------------------------------
// Replaying.

/// Invokes a call of the trace, catching its failure, with its body pending
/// for the callee. The host refuses a call of a contract already on the call
/// stack before the callee runs, so the body is dropped afterwards whether
/// the callee took it or not. Returns whether the call succeeded.
fn invoke(env: &Env, state: &Rc<RefCell<State>>, c: &JsonCall) -> bool {
    let contract = decode_address(&c.contract).expect("an address");
    let fn_name = decode_hex(&c.fn_name).expect("a function name");
    let args = decode_values(&c.args).expect("arguments");
    let mut host_args = soroban_sdk::Vec::<SdkVal>::new(env);
    for a in &args {
        host_args.push_back(to_host(env, a));
    }
    state.borrow_mut().pending = Some((
        AuthContext::Contract {
            contract: contract.clone(),
            fn_name: fn_name.clone(),
            args,
        },
        c.body.clone(),
    ));
    let r = env.try_invoke_contract::<SdkVal, Error>(
        &sdk_address(env, &contract),
        &symbol(env, &fn_name),
        host_args,
    );
    state.borrow_mut().pending = None;
    matches!(r, Ok(Ok(_)))
}

/// A host with every contract of `contracts` registered, sharing `state`.
fn host(contracts: &[JsonAddress], state: &Rc<RefCell<State>>) -> Env {
    let env = env();
    for c in contracts {
        let a = decode_address(c).expect("an address");
        env.register_at(
            &sdk_address(&env, &a),
            Dispatcher {
                state: state.clone(),
            },
            (),
        );
    }
    env
}

/// Runs one transaction: its entries with `set_auths`, then its top call.
/// Returns whether it succeeded and what ran.
fn run_tx(env: &Env, state: &Rc<RefCell<State>>, tx: &JsonTx) -> (bool, Vec<Event>) {
    state.borrow_mut().events.clear();
    env.ledger().set_sequence_number(tx.ledger);
    env.set_auths(&tx.entries.iter().map(entry).collect::<Vec<_>>());
    let ok = invoke(env, state, &tx.call);
    (ok, state.borrow().events.clone())
}

fn check_event(env: &Env, got: &Event, want: &JsonEvent) -> Result<(), String> {
    let same = match (got, want) {
        (
            Event::CheckAuth {
                account,
                payload: p,
                signature,
                contexts_value,
                contexts,
            },
            JsonEvent::CheckAuth(want),
        ) => {
            let want_contexts = decode_auth_contexts(&want.contexts)?;
            *account == decode_address(&want.account)?
                && *p == payload(env.ledger().network_id().to_array(), &want.preimage)
                && *signature == decode_value(&want.signature)?
                && *contexts_value == decode_value(&want.contexts_value)?
                && contexts.as_ref() == Some(&want_contexts)
                && contexts_eq(
                    &contexts_to_rule_eval(&want_contexts),
                    &decode_rule_eval_contexts(&want.rule_eval_contexts)?,
                )
        }
        (
            Event::Read {
                contract,
                durability,
                key,
                value,
            },
            JsonEvent::Read {
                contract: c,
                durability: d,
                key: k,
                value: v,
            },
        ) => {
            *contract == decode_address(c)?
                && *durability == decode_durability(*d)
                && *key == decode_value(k)?
                && *value == v.as_ref().map(decode_value).transpose()?
        }
        (
            Event::Found {
                contract,
                durability,
                key,
                present,
            },
            JsonEvent::Found {
                contract: c,
                durability: d,
                key: k,
                present: p,
            },
        ) => {
            *contract == decode_address(c)?
                && *durability == decode_durability(*d)
                && *key == decode_value(k)?
                && present == p
        }
        (
            Event::Authorized { address, context },
            JsonEvent::Authorized {
                address: a,
                context: c,
                ..
            },
        ) => *address == decode_address(a)? && *context == decode_auth_context(c)?,
        _ => false,
    };
    if same {
        Ok(())
    } else {
        Err(format!("saw {got:?}"))
    }
}

/// Replays a host trace and compares every transaction with the model's
/// outcome, events and storage.
///
/// # Errors
///
/// A description of the first difference.
pub fn check_host(t: &HostTrace) -> Result<(), String> {
    let state = Rc::new(RefCell::new(State::default()));
    for a in &t.accounts {
        state
            .borrow_mut()
            .accounts
            .push((decode_address(&a.address)?, a.check_auth.clone()));
    }
    let env = host(&t.contracts, &state);
    for (i, tx) in t.txs.iter().enumerate() {
        let (ok, events) = run_tx(&env, &state, tx);
        if ok != tx.expected.ok {
            return Err(format!(
                "tx {i}: ok is {ok}, the model says {}; events {events:?}",
                tx.expected.ok
            ));
        }
        if events.len() != tx.expected.events.len() {
            return Err(format!(
                "tx {i}: {} events, the model has {}: {events:?}",
                events.len(),
                tx.expected.events.len()
            ));
        }
        for (j, (got, want)) in events.iter().zip(&tx.expected.events).enumerate() {
            check_event(&env, got, want).map_err(|e| format!("tx {i}, event {j}: {e}"))?;
        }
        for s in &tx.expected.store {
            let contract = decode_address(&s.contract)?;
            let d = decode_durability(s.durability);
            let key = decode_value(&s.key)?;
            let want = s.value.as_ref().map(decode_value).transpose()?;
            let got = if key.storable() {
                env.as_contract(&sdk_address(&env, &contract), || {
                    backend::get(&env, d, &key)
                })
                .ok_or("an unreadable slot")?
            } else {
                None
            };
            if got != want {
                return Err(format!(
                    "tx {i}: {contract:?} {d:?} {key:?} holds {got:?}, the model says {want:?}"
                ));
            }
        }
    }
    Ok(())
}

/// Replays a storage trace on the host, each operation a transaction of its
/// own on the trace's contract, and compares each result with the model's.
///
/// # Errors
///
/// A description of the first operation whose result differs.
pub fn check_storage(t: &StorageTrace) -> Result<(), String> {
    use rule_eval_conformance::soroban::{JsonPut, Observed, OpKind};
    let state = Rc::new(RefCell::new(State::default()));
    let env = host(std::slice::from_ref(&t.contract), &state);
    for (i, op) in t.ops.iter().enumerate() {
        let s = JsonSlot {
            durability: op.durability,
            key: op.key.clone(),
        };
        let step = match op.op {
            OpKind::Get => JsonStep::Get(s),
            OpKind::Has => JsonStep::Has(s),
            OpKind::Remove => JsonStep::Remove(s),
            OpKind::Set => JsonStep::Put(JsonPut {
                durability: op.durability,
                key: op.key.clone(),
                val: op.val.clone().ok_or("set without a value")?,
            }),
        };
        let tx = JsonTx {
            ledger: 100,
            entries: Vec::new(),
            call: JsonCall {
                contract: t.contract.clone(),
                fn_name: "6f70".into(),
                args: vec![rule_eval_conformance::soroban::JsonValue::U32(
                    u32::try_from(i).map_err(|_| "too many ops")?,
                )],
                body: vec![step],
            },
            expected: rule_eval_conformance::soroban::JsonTxExpected {
                ok: true,
                events: Vec::new(),
                store: Vec::new(),
            },
        };
        let (ok, events) = run_tx(&env, &state, &tx);
        let same = match (&op.expected, ok, events.as_slice()) {
            (Observed::Refused, false, []) => true,
            (Observed::Done, true, []) => true,
            (Observed::Value(v), true, [Event::Read { value, .. }]) => {
                *value == v.as_ref().map(decode_value).transpose()?
            }
            (Observed::Present(p), true, [Event::Found { present, .. }]) => present == p,
            _ => false,
        };
        if !same {
            return Err(format!(
                "op {i} ({:?}): ok {ok}, saw {events:?}, the model says {:?}",
                op.op, op.expected
            ));
        }
    }
    Ok(())
}

/// Checks that every value of a value vector crosses the host unchanged: its
/// model XDR is the `ScVal` `stellar-xdr` reads and writes back, the host
/// takes it and gives the same value back, and the facade's value for it is
/// the vector's.
///
/// # Errors
///
/// A description of the first value that differs.
pub fn check_values(v: &ValueVector) -> Result<(), String> {
    let env = env();
    for (i, case) in v.values.iter().enumerate() {
        let bytes = decode_hex(&case.xdr)?;
        let sc = ScVal::from_xdr(&bytes, Limits::none())
            .map_err(|e| format!("value {i}: stellar-xdr does not read the model's XDR: {e}"))?;
        if sc.to_xdr(Limits::none()).map_err(|e| e.to_string())? != bytes {
            return Err(format!("value {i}: stellar-xdr writes {sc:?} differently"));
        }
        let host_val = SdkVal::try_from_val(&env, &sc)
            .map_err(|e| format!("value {i}: the host does not take {sc:?}: {e:?}"))?;
        let back = ScVal::try_from_val(&env, &host_val).map_err(|e| format!("value {i}: {e:?}"))?;
        if back != sc {
            return Err(format!("value {i}: the host gives {back:?} for {sc:?}"));
        }
        if facade_val(&back) != decode_value(&case.value)? {
            return Err(format!("value {i}: the facade reads {back:?} differently"));
        }
    }
    Ok(())
}

/// Checks a context vector against the SDK's `auth::Context`, the type a
/// shell's `__check_auth` takes its contexts as: the host takes the vector's
/// XDR as a value, the SDK reads it as a vector of contexts exactly when the
/// model reads it, and the SDK writes what it read back as the same XDR.
///
/// # Errors
///
/// On the first difference.
pub fn check_contexts(v: &ContextVector) -> Result<(), String> {
    use soroban_sdk::auth::Context;
    use soroban_sdk::{IntoVal, Vec as SdkVec};

    let env = env();
    let bytes = decode_hex(&v.xdr)?;
    let sc = ScVal::from_xdr(&bytes, Limits::none())
        .map_err(|e| format!("stellar-xdr does not read the model's XDR: {e}"))?;
    // The SDK's vector checks its elements' types only when they are read,
    // so each element is read as a context here. Reading a context whose
    // fields do not fit traps, as it does in a contract, where the trap
    // refuses the authorization; here the trap is a panic, read as a refusal.
    let read = SdkVal::try_from_val(&env, &sc)
        .ok()
        .and_then(|host_val| SdkVec::<SdkVal>::try_from_val(&env, &host_val).ok())
        .and_then(|items| {
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut cs = SdkVec::<Context>::new(&env);
                for item in items.iter() {
                    cs.push_back(Context::try_from_val(&env, &item).ok()?);
                }
                Some(cs)
            }))
            .ok()
            .flatten()
        });
    match (read, &v.expected) {
        (None, None) => Ok(()),
        (Some(_), None) => Err("the SDK reads contexts the model refuses".into()),
        (None, Some(_)) => Err("the SDK refuses contexts the model reads".into()),
        (Some(cs), Some(_)) => {
            let back: SdkVal = cs.into_val(&env);
            let back = ScVal::try_from_val(&env, &back).map_err(|e| format!("{e:?}"))?;
            if back.to_xdr(Limits::none()).map_err(|e| e.to_string())? == bytes {
                Ok(())
            } else {
                Err(format!("the SDK writes the contexts as {back:?}"))
            }
        }
    }
}
