//! Authorization contexts: what `__check_auth` receives, and what `rule-eval`
//! reads of it.

use alloc::vec::Vec;

use crate::val::{Address, Val};
use crate::xdr;

/// One context `__check_auth` receives, following SDK 29's `auth::Context`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthContext {
    /// A call of `fn_name` on `contract` with `args`.
    Contract {
        contract: Address,
        fn_name: Vec<u8>,
        args: Vec<Val>,
    },
    /// A creation running `executable`, with `salt` and the constructor
    /// arguments, none for a creation without a constructor call.
    CreateContract {
        executable: Executable,
        salt: [u8; 32],
        constructor_args: Vec<Val>,
    },
}

/// What a created contract runs, following SDK 29's `ContractExecutable`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Executable {
    /// Uploaded Wasm, by its hash.
    Wasm([u8; 32]),
    /// The Wasm hash `owner` keeps in its persistent storage under the
    /// executable tag with the string `tag` (CAP-85).
    ExternalRef { owner: Address, tag: Vec<u8> },
}

impl Executable {
    /// Reads an executable from its `contracttype` encoding: `Wasm` and the
    /// hash, or `ExternalRef` and a map of the owner and the tag.
    #[must_use]
    pub fn from_val(v: &Val) -> Option<Executable> {
        let Val::Vec(items) = v else { return None };
        let [name, body] = items.as_slice() else {
            return None;
        };
        if is_sym(name, "Wasm") {
            bytes32(body).map(Executable::Wasm)
        } else if is_sym(name, "ExternalRef") {
            match fields(body, ["owner", "tag"])? {
                [Val::Address(owner), Val::String(tag)] => Some(Executable::ExternalRef {
                    owner: owner.clone(),
                    tag: tag.clone(),
                }),
                _ => None,
            }
        } else {
            None
        }
    }

    /// The executable's `contracttype` encoding.
    #[must_use]
    pub fn to_val(&self) -> Val {
        match self {
            Executable::Wasm(h) => Val::Vec(alloc::vec![sym("Wasm"), Val::Bytes(h.to_vec())]),
            Executable::ExternalRef { owner, tag } => Val::Vec(alloc::vec![
                sym("ExternalRef"),
                Val::Map(alloc::vec![
                    (sym("owner"), Val::Address(owner.clone())),
                    (sym("tag"), Val::String(tag.clone())),
                ]),
            ]),
        }
    }

    /// What identifies the executable to `rule-eval`: the Wasm hash, or the
    /// `ScVal` XDR of an external reference, which is longer than any hash.
    #[must_use]
    pub fn id(&self) -> Vec<u8> {
        match self {
            Executable::Wasm(h) => h.to_vec(),
            Executable::ExternalRef { .. } => xdr::encode(&self.to_val()),
        }
    }
}

fn sym(s: &str) -> Val {
    Val::Symbol(s.as_bytes().to_vec())
}

fn is_sym(v: &Val, s: &str) -> bool {
    matches!(v, Val::Symbol(b) if b.as_slice() == s.as_bytes())
}

fn bytes32(v: &Val) -> Option<[u8; 32]> {
    match v {
        Val::Bytes(b) => b.as_slice().try_into().ok(),
        _ => None,
    }
}

/// The entries of a map with exactly the symbol keys `keys`, in that order.
fn fields<'a, const N: usize>(v: &'a Val, keys: [&str; N]) -> Option<[&'a Val; N]> {
    let Val::Map(entries) = v else { return None };
    if entries.len() != N {
        return None;
    }
    let mut out = [&Val::Void; N];
    for (i, key) in keys.iter().enumerate() {
        let (k, val) = &entries[i];
        if !is_sym(k, key) {
            return None;
        }
        out[i] = val;
    }
    Some(out)
}

impl AuthContext {
    /// Reads one context from its `contracttype` encoding, the form the host
    /// passes it in: a variant name and a map of fields.
    #[must_use]
    pub fn from_val(v: &Val) -> Option<AuthContext> {
        let Val::Vec(items) = v else { return None };
        let [name, body] = items.as_slice() else {
            return None;
        };
        if is_sym(name, "Contract") {
            let [args, contract, fn_name] = fields(body, ["args", "contract", "fn_name"])?;
            match (args, contract, fn_name) {
                (Val::Vec(args), Val::Address(contract), Val::Symbol(fn_name)) => {
                    Some(AuthContext::Contract {
                        contract: contract.clone(),
                        fn_name: fn_name.clone(),
                        args: args.clone(),
                    })
                }
                _ => None,
            }
        } else if is_sym(name, "CreateContractHostFn") {
            let [executable, salt] = fields(body, ["executable", "salt"])?;
            Some(AuthContext::CreateContract {
                executable: Executable::from_val(executable)?,
                salt: bytes32(salt)?,
                constructor_args: Vec::new(),
            })
        } else if is_sym(name, "CreateContractWithCtorHostFn") {
            let [args, executable, salt] =
                fields(body, ["constructor_args", "executable", "salt"])?;
            let Val::Vec(args) = args else { return None };
            Some(AuthContext::CreateContract {
                executable: Executable::from_val(executable)?,
                salt: bytes32(salt)?,
                constructor_args: args.clone(),
            })
        } else {
            None
        }
    }

    /// The context's `contracttype` encoding, as the host passes it.
    #[must_use]
    pub fn to_val(&self) -> Val {
        match self {
            AuthContext::Contract {
                contract,
                fn_name,
                args,
            } => Val::Vec(alloc::vec![
                sym("Contract"),
                Val::Map(alloc::vec![
                    (sym("args"), Val::Vec(args.clone())),
                    (sym("contract"), Val::Address(contract.clone())),
                    (sym("fn_name"), Val::Symbol(fn_name.clone())),
                ]),
            ]),
            AuthContext::CreateContract {
                executable,
                salt,
                constructor_args,
            } => {
                let executable = executable.to_val();
                let salt = Val::Bytes(salt.to_vec());
                if constructor_args.is_empty() {
                    Val::Vec(alloc::vec![
                        sym("CreateContractHostFn"),
                        Val::Map(alloc::vec![
                            (sym("executable"), executable),
                            (sym("salt"), salt)
                        ]),
                    ])
                } else {
                    Val::Vec(alloc::vec![
                        sym("CreateContractWithCtorHostFn"),
                        Val::Map(alloc::vec![
                            (sym("constructor_args"), Val::Vec(constructor_args.clone())),
                            (sym("executable"), executable),
                            (sym("salt"), salt),
                        ]),
                    ])
                }
            }
        }
    }
}

/// Reads `__check_auth`'s contexts, given as one value (a vector of
/// contexts): all of them, or `None` when any one cannot be read, so that a
/// shell refuses the whole batch.
#[must_use]
pub fn auth_contexts(v: &Val) -> Option<Vec<AuthContext>> {
    let Val::Vec(items) = v else { return None };
    items.iter().map(AuthContext::from_val).collect()
}

/// A value as `rule-eval` reads it: `i128`, `u64`, `bool`, bytes, strings and
/// symbols as themselves, an address as its `ScAddress` XDR, and every other
/// value as `Other` of its full `ScVal` XDR.
#[must_use]
pub fn val_to_rule_eval(v: &Val) -> rule_eval::Val {
    match v {
        Val::I128(n) => rule_eval::Val::I128(*n),
        Val::U64(n) => rule_eval::Val::U64(*n),
        Val::Bool(b) => rule_eval::Val::Bool(*b),
        Val::Bytes(b) => rule_eval::Val::Bytes(b.clone()),
        Val::String(b) => rule_eval::Val::String(b.clone()),
        Val::Symbol(b) => rule_eval::Val::Symbol(b.clone()),
        Val::Address(a) => rule_eval::Val::Address(xdr::address_xdr(a)),
        _ => rule_eval::Val::Other(xdr::encode(v)),
    }
}

/// A context as `rule-eval` reads it: a call of the contract's `ScAddress`
/// XDR, or a creation, which no rule allows, of the executable's
/// [`Executable::id`].
#[must_use]
pub fn to_rule_eval(c: &AuthContext) -> rule_eval::Context {
    match c {
        AuthContext::Contract {
            contract,
            fn_name,
            args,
        } => rule_eval::Context::Call {
            contract: xdr::address_xdr(contract),
            function: fn_name.clone(),
            args: args.iter().map(val_to_rule_eval).collect(),
        },
        AuthContext::CreateContract { executable, .. } => rule_eval::Context::Create {
            wasm_hash: executable.id(),
        },
    }
}

/// Every context as `rule-eval` reads it, in order.
#[must_use]
pub fn contexts_to_rule_eval(cs: &[AuthContext]) -> Vec<rule_eval::Context> {
    cs.iter().map(to_rule_eval).collect()
}
