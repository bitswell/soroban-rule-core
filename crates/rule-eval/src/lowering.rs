//! The lowering of a document's rules to the evaluator's [`Rule`]s.
//!
//! Each document rule becomes one rule, as Perch's `perch_compile::compile`
//! lowers it (`crates/perch-compile/src/lib.rs`) and its smart account
//! installs it on OpenZeppelin's (`crates/perch-smart-account/src/rules.rs`):
//!
//! - the scope's contract, or the account's own address for a self-admin
//!   scope;
//! - the functions listed, or every function when the rule lists none;
//! - one condition per argument predicate, in order;
//! - the signers declared under the principals' ids, in order, with a
//!   threshold of all of them for `All` and of `m` for `Threshold(_, m)`;
//! - a last ledger one before `not_after_ledger`, since OpenZeppelin's
//!   `valid_until` is the last ledger a rule authorizes in.
//!
//! A capped rule authorizes only what OpenZeppelin's spending-limit policy
//! meters: a `transfer` whose argument 2 is an `i128`. Its functions are
//! `transfer` when the document's cover it and none otherwise, it gets the
//! condition that argument 2 is an `i128` (`ArgI128AtMost(2, i128::MAX)`),
//! and its cap reads the amount from argument 2.
//!
//! A document with a recovery configuration also gets the recovery rule,
//! after its own rules: the account's `apply_doc`, with no conditions, no
//! signers and threshold 0. On chain the recovery controller checks that
//! rule's calls against its own state; the lowered rule allows every call it
//! can allow, and more.

use alloc::vec::Vec;

use crate::bytes::{bytes_copy, bytes_eq, bytes_in, bytes_list_copy};
use crate::document::{ArgConstraint, Doc, DocCap, DocRule, Pred, Principals, Scope, SignerDecl};
use crate::rule::{Cap, Cond, Functions, Rule};
use crate::signer::{Signer, signer_copy};
use crate::val::Val;

/// The longest string Perch's `string-in` compares: a value longer than this
/// never matches an argument on chain.
pub const MAX_STRING_LEN: usize = 256;

/// The argument OpenZeppelin's spending-limit policy reads a transfer's
/// amount from.
pub const AMOUNT_ARG: u32 = 2;

/// The function name `transfer`.
pub(crate) fn transfer() -> Vec<u8> {
    bytes_copy(b"transfer")
}

/// The function name `apply_doc`.
pub(crate) fn apply_doc() -> Vec<u8> {
    bytes_copy(b"apply_doc")
}

/// The `ScVal` XDR of the `u32` value `v`: the discriminant `SCV_U32`, which
/// is 3, then the value, each as four big-endian bytes. A shell gives a `u32`
/// argument to `rule-eval` as `Val::Other` of exactly these bytes.
#[must_use]
pub fn u32_xdr(v: u32) -> Vec<u8> {
    bytes_copy(&[
        0,
        0,
        0,
        3,
        (v / 16_777_216) as u8,
        (v / 65_536 % 256) as u8,
        (v / 256 % 256) as u8,
        (v % 256) as u8,
    ])
}

/// The signer declared under `id`: the first declaration with that id.
fn resolve(id: &[u8], signers: &[SignerDecl]) -> Option<Signer> {
    let mut i = 0;
    while i < signers.len() {
        if bytes_eq(&signers[i].id, id) {
            return Some(signer_copy(&signers[i].signer));
        }
        i += 1;
    }
    None
}

/// The signers declared under `ids`, in order. An id no signer is declared
/// under names none.
fn named(ids: &[Vec<u8>], signers: &[SignerDecl]) -> Vec<Signer> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < ids.len() {
        if let Some(s) = resolve(&ids[i], signers) {
            out.push(s);
        }
        i += 1;
    }
    out
}

/// The ids `p` names.
fn principal_ids(p: &Principals) -> &[Vec<u8>] {
    match p {
        Principals::All(ids) | Principals::Threshold(ids, _) => ids,
    }
}

/// The threshold `p` asks of the `count` signers it names: all of them for
/// `All`, and `m` for `Threshold(_, m)`. A count that does not fit a `u32`
/// gives `u32::MAX`.
fn threshold_of(p: &Principals, count: usize) -> u32 {
    match p {
        Principals::All(_) => {
            if count > u32::MAX as usize {
                return u32::MAX;
            }
            count as u32
        }
        Principals::Threshold(_, m) => *m,
    }
}

/// The contract a rule of scope `s` applies to.
fn contract_of(s: &Scope, account: &[u8]) -> Vec<u8> {
    match s {
        Scope::Contract(a) => bytes_copy(a),
        Scope::SelfAdmin => bytes_copy(account),
    }
}

/// Whether a rule's functions cover `transfer`.
fn covers_transfer(functions: &Option<Vec<Vec<u8>>>) -> bool {
    match functions {
        Some(fs) => bytes_in(&transfer(), fs),
        None => true,
    }
}

/// The functions a capped rule lowers to: `transfer` when the rule's
/// functions cover it, and none otherwise.
fn capped_functions(functions: &Option<Vec<Vec<u8>>>) -> Functions {
    let mut only = Vec::new();
    if covers_transfer(functions) {
        only.push(transfer());
    }
    Functions::Only(only)
}

/// The functions a rule without a cap lowers to: its functions, or the
/// wildcard when it lists none.
fn listed_functions(functions: &Option<Vec<Vec<u8>>>) -> Functions {
    match functions {
        Some(fs) => Functions::Only(bytes_list_copy(fs)),
        None => Functions::AnyExcept(Vec::new()),
    }
}

/// The functions a rule lowers to.
fn lower_functions(functions: &Option<Vec<Vec<u8>>>, cap: &Option<DocCap>) -> Functions {
    match cap {
        Some(_) => capped_functions(functions),
        None => listed_functions(functions),
    }
}

/// The values of `values` of at most [`MAX_STRING_LEN`] bytes, as strings,
/// in order.
fn strings_within(values: &[Vec<u8>]) -> Vec<Val> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < values.len() {
        if values[i].len() <= MAX_STRING_LEN {
            out.push(Val::String(bytes_copy(&values[i])));
        }
        i += 1;
    }
    out
}

/// The condition predicate `pred` on argument `index` lowers to.
fn lower_pred(index: u32, pred: &Pred, account: &[u8]) -> Cond {
    match pred {
        Pred::IsSelf => Cond::ArgEq(index, Val::Address(bytes_copy(account))),
        Pred::AddressEq(a) => Cond::ArgEq(index, Val::Address(bytes_copy(a))),
        Pred::StringIn(values) => Cond::ArgIn(index, strings_within(values)),
        Pred::StringPrefix(p) => Cond::ArgStrPrefix(index, bytes_copy(p)),
        Pred::U32Eq(v) => Cond::ArgEq(index, Val::Other(u32_xdr(*v))),
    }
}

/// The conditions `args` lower to, in order.
fn lower_args(args: &[ArgConstraint], account: &[u8]) -> Vec<Cond> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < args.len() {
        out.push(lower_pred(args[i].index, &args[i].pred, account));
        i += 1;
    }
    out
}

/// `conds` followed by the condition that argument [`AMOUNT_ARG`] is an
/// `i128`, which every `i128` is at most `i128::MAX` of.
fn with_amount(conds: Vec<Cond>) -> Vec<Cond> {
    let mut out = conds;
    out.push(Cond::ArgI128AtMost(AMOUNT_ARG, i128::MAX));
    out
}

/// A rule's conditions: its argument predicates, then, for a capped rule,
/// that argument [`AMOUNT_ARG`] is an `i128`.
fn lower_conds(
    args: &Option<Vec<ArgConstraint>>,
    cap: &Option<DocCap>,
    account: &[u8],
) -> Vec<Cond> {
    let out = match args {
        Some(cs) => lower_args(cs, account),
        None => Vec::new(),
    };
    match cap {
        Some(_) => with_amount(out),
        None => out,
    }
}

/// A rule's cap, reading the amount from argument [`AMOUNT_ARG`].
fn lower_cap(cap: &Option<DocCap>) -> Option<Cap> {
    if let Some(c) = cap {
        return Some(Cap {
            limit: c.limit,
            period: c.period_ledgers,
            amount_arg: AMOUNT_ARG,
        });
    }
    None
}

/// The last ledger a rule that stops authorizing at `not_after_ledger`
/// authorizes in.
fn last_ledger(not_after_ledger: Option<u32>) -> Option<u32> {
    if let Some(x) = not_after_ledger {
        return Some(x.saturating_sub(1));
    }
    None
}

/// The rule the document rule `r` lowers to, on `account`, carrying
/// `generation`.
fn lower_rule(
    r: &DocRule,
    signers: &[SignerDecl],
    account: &[u8],
    generation: Option<u64>,
) -> Rule {
    let rule_signers = named(principal_ids(&r.principals), signers);
    let threshold = threshold_of(&r.principals, rule_signers.len());
    Rule {
        contract: contract_of(&r.scope, account),
        functions: lower_functions(&r.functions, &r.cap),
        conds: lower_conds(&r.args, &r.cap, account),
        signers: rule_signers,
        threshold,
        cap: lower_cap(&r.cap),
        valid_until: last_ledger(r.not_after_ledger),
        generation,
    }
}

/// The rules the document rules `rules` lower to, in order, each carrying
/// `generation`.
pub(crate) fn lower_rules(
    rules: &[DocRule],
    signers: &[SignerDecl],
    account: &[u8],
    generation: Option<u64>,
) -> Vec<Rule> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        out.push(lower_rule(&rules[i], signers, account, generation));
        i += 1;
    }
    out
}

/// The recovery rule on `account`: its `apply_doc`, with no conditions, no
/// signers and threshold 0.
#[must_use]
pub fn recovery_rule(account: &[u8]) -> Rule {
    Rule {
        contract: bytes_copy(account),
        functions: Functions::Only(bytes_list_copy(&[apply_doc()])),
        conds: Vec::new(),
        signers: Vec::new(),
        threshold: 0,
        cap: None,
        valid_until: None,
        generation: None,
    }
}

/// `rules` followed by the recovery rule on `account`.
fn with_recovery(rules: Vec<Rule>, account: &[u8]) -> Vec<Rule> {
    let mut out = rules;
    out.push(recovery_rule(account));
    out
}

/// The rules the admin document `d` lowers to on `account`: one per document
/// rule, in order, then the recovery rule when `d` has a recovery
/// configuration. No rule carries a generation.
#[must_use]
pub fn lower(d: &Doc, account: &[u8]) -> Vec<Rule> {
    let out = lower_rules(&d.rules, &d.signers, account, None);
    match &d.recovery {
        Some(_) => with_recovery(out, account),
        None => out,
    }
}
