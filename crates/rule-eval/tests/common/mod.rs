//! Builders, small universes and a reference reading of the semantics shared
//! by the integration tests.
#![allow(dead_code)]

use rule_eval::{Cap, Cond, Context, Functions, Rule, Signer, Val};

pub fn b(s: &str) -> Vec<u8> {
    s.as_bytes().to_vec()
}

pub fn call(contract: &str, function: &str, args: Vec<Val>) -> Context {
    Context::Call {
        contract: b(contract),
        function: b(function),
        args,
    }
}

pub fn create(hash: &str) -> Context {
    Context::Create { wasm_hash: b(hash) }
}

/// A rule with no signer requirement.
pub fn rule(contract: &str, functions: &[&str], conds: Vec<Cond>) -> Rule {
    signed_rule(contract, functions, conds, Vec::new(), 0)
}

pub fn signed_rule(
    contract: &str,
    functions: &[&str],
    conds: Vec<Cond>,
    signers: Vec<Signer>,
    threshold: u32,
) -> Rule {
    Rule {
        contract: b(contract),
        functions: Functions::Only(functions.iter().map(|f| b(f)).collect()),
        conds,
        signers,
        threshold,
        cap: None,
        valid_until: None,
        generation: None,
    }
}

/// `r` matching every function of its contract except `except`.
pub fn wildcard(r: Rule, except: &[&str]) -> Rule {
    Rule {
        functions: Functions::AnyExcept(except.iter().map(|f| b(f)).collect()),
        ..r
    }
}

/// `r` with last ledger `last`.
pub fn valid_until(r: Rule, last: u32) -> Rule {
    Rule {
        valid_until: Some(last),
        ..r
    }
}

/// `r` issued under generation `g`.
pub fn issued(r: Rule, g: u64) -> Rule {
    Rule {
        generation: Some(g),
        ..r
    }
}

pub fn only(fs: &[&str]) -> Functions {
    Functions::Only(fs.iter().map(|f| b(f)).collect())
}

pub fn any_except(fs: &[&str]) -> Functions {
    Functions::AnyExcept(fs.iter().map(|f| b(f)).collect())
}

pub fn functions_eq(x: &Functions, y: &Functions) -> bool {
    match (x, y) {
        (Functions::AnyExcept(p), Functions::AnyExcept(q))
        | (Functions::Only(p), Functions::Only(q)) => p == q,
        _ => false,
    }
}

pub fn copy_functions(fs: &Functions) -> Functions {
    match fs {
        Functions::AnyExcept(p) => Functions::AnyExcept(p.clone()),
        Functions::Only(p) => Functions::Only(p.clone()),
    }
}

pub fn cap(limit: i128, period: u32, amount_arg: u32) -> Cap {
    Cap {
        limit,
        period,
        amount_arg,
    }
}

/// `r` with the cap `c`.
pub fn capped(r: Rule, c: Cap) -> Rule {
    Rule { cap: Some(c), ..r }
}

pub fn copy_cap(c: &Option<Cap>) -> Option<Cap> {
    c.as_ref().map(|c| cap(c.limit, c.period, c.amount_arg))
}

pub fn cap_eq(x: &Option<Cap>, y: &Option<Cap>) -> bool {
    match (x, y) {
        (None, None) => true,
        (Some(p), Some(q)) => {
            p.limit == q.limit && p.period == q.period && p.amount_arg == q.amount_arg
        }
        _ => false,
    }
}

pub fn delegated(address: &str) -> Signer {
    Signer::Delegated(b(address))
}

pub fn external(verifier: &str, key: &str) -> Signer {
    Signer::External(b(verifier), b(key))
}

/// Structural equality on rules, for checking what an attenuation step built.
pub fn rule_eq(x: &Rule, y: &Rule) -> bool {
    x.contract == y.contract
        && functions_eq(&x.functions, &y.functions)
        && x.conds.len() == y.conds.len()
        && x.conds.iter().zip(&y.conds).all(|(p, q)| cond_eq(p, q))
        && x.signers.len() == y.signers.len()
        && x.signers
            .iter()
            .zip(&y.signers)
            .all(|(p, q)| ref_signer_eq(p, q))
        && x.threshold == y.threshold
        && cap_eq(&x.cap, &y.cap)
        && x.valid_until == y.valid_until
        && x.generation == y.generation
}

pub fn rules_eq(xs: &[Rule], ys: &[Rule]) -> bool {
    xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| rule_eq(x, y))
}

pub fn cond_eq(p: &Cond, q: &Cond) -> bool {
    match (p, q) {
        (Cond::ArgEq(i, v), Cond::ArgEq(j, w)) => i == j && rule_eval::val_eq(v, w),
        (Cond::ArgI128AtMost(i, n), Cond::ArgI128AtMost(j, m)) => i == j && n == m,
        (Cond::ArgIn(i, vs), Cond::ArgIn(j, ws)) => {
            i == j
                && vs.len() == ws.len()
                && vs.iter().zip(ws).all(|(v, w)| rule_eval::val_eq(v, w))
        }
        (Cond::ArgStrPrefix(i, p), Cond::ArgStrPrefix(j, q)) => i == j && p == q,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Small universes. Values are built fresh from an index each time, since the
// evaluator's types implement no traits.

pub const SIGNERS: usize = 5;

/// The `k`-th signer of a universe holding both constructors, an external
/// signer whose verifier holds another signer's address bytes, and an address
/// that extends another.
pub fn signer(k: usize) -> Signer {
    match k {
        0 => delegated("a"),
        1 => delegated("b"),
        2 => external("v", "k"),
        3 => external("a", ""),
        4 => delegated("ab"),
        _ => unreachable!(),
    }
}

/// Every authenticated list over the signer universe: each subset, in order,
/// and each subset with its first signer repeated at the end.
pub fn authenticated_lists() -> Vec<Vec<Signer>> {
    let mut out = Vec::new();
    for mask in 0..(1usize << SIGNERS) {
        let members: Vec<usize> = (0..SIGNERS).filter(|k| mask & (1 << k) != 0).collect();
        out.push(members.iter().map(|&k| signer(k)).collect());
        if let Some(&first) = members.first() {
            let mut repeated: Vec<Signer> = members.iter().map(|&k| signer(k)).collect();
            repeated.push(signer(first));
            out.push(repeated);
        }
    }
    out
}

pub const CONTRACTS: [&str; 2] = ["c1", "c2"];
pub const FUNCTIONS: [&str; 2] = ["f", "g"];

pub const VALS: usize = 11;

/// The `k`-th value of a universe holding every constructor, two values of
/// one constructor, byte payloads equal across constructors, and a string that
/// extends another.
pub fn val(k: usize) -> Val {
    match k {
        0 => Val::I128(5),
        1 => Val::I128(9),
        2 => Val::U64(5),
        3 => Val::Bool(true),
        4 => Val::Bytes(b("c1")),
        5 => Val::Address(b("c1")),
        6 => Val::Symbol(b("c1")),
        7 => Val::Other(b("c1")),
        8 => Val::I128(-3),
        9 => Val::String(b("c1")),
        10 => Val::String(b("c12")),
        _ => unreachable!(),
    }
}

pub const CONDS: usize = 7;

/// How many conditions of the universe are combined in pairs.
pub const PAIRED_CONDS: usize = 5;

/// The `k`-th condition of a universe touching argument 0 and argument 1.
pub fn cond(k: usize) -> Cond {
    match k {
        0 => Cond::ArgEq(0, Val::I128(5)),
        1 => Cond::ArgI128AtMost(0, 7),
        2 => Cond::ArgEq(1, Val::Address(b("c1"))),
        3 => Cond::ArgEq(0, Val::Bytes(b("c1"))),
        4 => Cond::ArgI128AtMost(1, 0),
        5 => Cond::ArgIn(0, vec![Val::I128(9), Val::Symbol(b("c1"))]),
        6 => Cond::ArgStrPrefix(0, b("c1")),
        _ => unreachable!(),
    }
}

/// Argument lists: empty, one argument of each value, and two-argument lists.
pub fn args_universe() -> Vec<Vec<Val>> {
    let mut out = vec![Vec::new()];
    for k in 0..VALS {
        out.push(vec![val(k)]);
    }
    for k in 0..VALS {
        for l in [0, 5, 8] {
            out.push(vec![val(k), val(l)]);
        }
    }
    out
}

/// Every call to a universe contract (plus one unknown contract) and function
/// (plus one unknown function) with every argument list, and two creations.
pub fn contexts() -> Vec<Context> {
    let mut out = Vec::new();
    for contract in CONTRACTS.iter().chain(&["c3"]) {
        for function in FUNCTIONS.iter().chain(&["h"]) {
            for args in args_universe() {
                out.push(call(contract, function, args));
            }
        }
    }
    out.push(create("c1"));
    out.push(create(""));
    out
}

/// A rule described by small indices, so a test can build any number of
/// identical copies.
#[derive(Clone, Copy, Debug)]
pub struct RuleSpec {
    pub contract: usize,
    /// Bit `k` set: `FUNCTIONS[k]` is in the function list, or, for a
    /// wildcard, excluded from it.
    pub functions: u8,
    /// The rule matches every function except the ones `functions` names.
    pub wildcard: bool,
    /// Indices into the condition universe.
    pub conds: [Option<usize>; 2],
}

impl RuleSpec {
    pub fn build(self) -> Rule {
        let listed: Vec<Vec<u8>> = (0..FUNCTIONS.len())
            .filter(|k| self.functions & (1 << k) != 0)
            .map(|k| b(FUNCTIONS[k]))
            .collect();
        Rule {
            contract: b(CONTRACTS[self.contract]),
            functions: if self.wildcard {
                Functions::AnyExcept(listed)
            } else {
                Functions::Only(listed)
            },
            conds: self.conds.iter().flatten().map(|&k| cond(k)).collect(),
            signers: Vec::new(),
            threshold: 0,
            cap: None,
            valid_until: None,
            generation: None,
        }
    }
}

/// Every rule with a universe contract, any subset of the universe functions,
/// and no condition, one condition, or two of the first `PAIRED_CONDS`; and
/// every wildcard excluding any subset of the universe functions, with no
/// condition or one of the conditions after them.
pub fn rule_specs() -> Vec<RuleSpec> {
    let mut cond_choices = vec![[None, None]];
    for p in 0..CONDS {
        cond_choices.push([Some(p), None]);
    }
    for p in 0..PAIRED_CONDS {
        for q in p + 1..PAIRED_CONDS {
            cond_choices.push([Some(p), Some(q)]);
        }
    }
    let mut wildcard_conds = vec![[None, None]];
    for p in PAIRED_CONDS..CONDS {
        wildcard_conds.push([Some(p), None]);
    }
    let mut out = Vec::new();
    for contract in 0..CONTRACTS.len() {
        for functions in 0..(1u8 << FUNCTIONS.len()) {
            for conds in &cond_choices {
                out.push(RuleSpec {
                    contract,
                    functions,
                    wildcard: false,
                    conds: *conds,
                });
            }
            for conds in &wildcard_conds {
                out.push(RuleSpec {
                    contract,
                    functions,
                    wildcard: true,
                    conds: *conds,
                });
            }
        }
    }
    out
}

/// Every rule set of up to two rules from `rule_specs`.
pub fn rule_sets() -> Vec<Vec<RuleSpec>> {
    let specs = rule_specs();
    let mut out = vec![Vec::new()];
    for &x in &specs {
        out.push(vec![x]);
        for &y in &specs {
            out.push(vec![x, y]);
        }
    }
    out
}

pub fn build(specs: &[RuleSpec]) -> Vec<Rule> {
    specs.iter().map(|s| s.build()).collect()
}

/// Every function-name list a `remove_functions` step is tried with.
pub fn removal_lists() -> Vec<Vec<Vec<u8>>> {
    vec![
        Vec::new(),
        vec![b("f")],
        vec![b("g")],
        vec![b("f"), b("g")],
        vec![b("h")],
        vec![b("")],
    ]
}

// ---------------------------------------------------------------------------
// A reference reading of the semantics in ordinary Rust.

pub fn ref_val_eq(a: &Val, x: &Val) -> bool {
    match (a, x) {
        (Val::I128(p), Val::I128(q)) => p == q,
        (Val::U64(p), Val::U64(q)) => p == q,
        (Val::Bool(p), Val::Bool(q)) => p == q,
        (Val::Bytes(p), Val::Bytes(q))
        | (Val::Address(p), Val::Address(q))
        | (Val::Symbol(p), Val::Symbol(q))
        | (Val::String(p), Val::String(q))
        | (Val::Other(p), Val::Other(q)) => p == q,
        _ => false,
    }
}

pub fn ref_cond_holds(c: &Cond, args: &[Val]) -> bool {
    match c {
        Cond::ArgEq(i, v) => args.get(*i as usize).is_some_and(|a| ref_val_eq(a, v)),
        Cond::ArgI128AtMost(i, n) => matches!(args.get(*i as usize), Some(Val::I128(v)) if v <= n),
        Cond::ArgIn(i, vs) => args
            .get(*i as usize)
            .is_some_and(|a| vs.iter().any(|v| ref_val_eq(a, v))),
        Cond::ArgStrPrefix(i, p) => {
            matches!(args.get(*i as usize), Some(Val::String(s)) if s.starts_with(p))
        }
    }
}

pub fn ref_functions_match(fs: &Functions, function: &Vec<u8>) -> bool {
    match fs {
        Functions::AnyExcept(removed) => !removed.contains(function),
        Functions::Only(listed) => listed.contains(function),
    }
}

pub fn ref_signer_eq(a: &Signer, x: &Signer) -> bool {
    match (a, x) {
        (Signer::Delegated(p), Signer::Delegated(q)) => p == q,
        (Signer::External(v, k), Signer::External(w, l)) => v == w && k == l,
        _ => false,
    }
}

/// Whether at least `threshold` distinct signers of `signers` are among
/// `authenticated`.
pub fn ref_signers_met(signers: &[Signer], threshold: u32, authenticated: &[Signer]) -> bool {
    let mut distinct: Vec<&Signer> = Vec::new();
    for s in signers {
        if !distinct.iter().any(|d| ref_signer_eq(d, s)) {
            distinct.push(s);
        }
    }
    let present = distinct
        .iter()
        .filter(|d| authenticated.iter().any(|a| ref_signer_eq(a, d)))
        .count();
    present >= threshold as usize
}

pub fn ref_rule_allows(r: &Rule, c: &Context, authenticated: &[Signer]) -> bool {
    match c {
        Context::Call {
            contract,
            function,
            args,
        } => {
            *contract == r.contract
                && ref_functions_match(&r.functions, function)
                && r.conds.iter().all(|k| ref_cond_holds(k, args))
                && ref_signers_met(&r.signers, r.threshold, authenticated)
        }
        Context::Create { .. } => false,
    }
}

pub fn ref_allows(rs: &[Rule], c: &Context, authenticated: &[Signer]) -> bool {
    rs.iter().any(|r| ref_rule_allows(r, c, authenticated))
}

// ---------------------------------------------------------------------------
// Copies, built field by field.

pub fn copy_val(v: &Val) -> Val {
    match v {
        Val::I128(x) => Val::I128(*x),
        Val::U64(x) => Val::U64(*x),
        Val::Bool(x) => Val::Bool(*x),
        Val::Bytes(x) => Val::Bytes(x.clone()),
        Val::Address(x) => Val::Address(x.clone()),
        Val::Symbol(x) => Val::Symbol(x.clone()),
        Val::String(x) => Val::String(x.clone()),
        Val::Other(x) => Val::Other(x.clone()),
    }
}

pub fn copy_context(c: &Context) -> Context {
    match c {
        Context::Call {
            contract,
            function,
            args,
        } => Context::Call {
            contract: contract.clone(),
            function: function.clone(),
            args: args.iter().map(copy_val).collect(),
        },
        Context::Create { wasm_hash } => Context::Create {
            wasm_hash: wasm_hash.clone(),
        },
    }
}

pub fn copy_cond(c: &Cond) -> Cond {
    match c {
        Cond::ArgEq(i, v) => Cond::ArgEq(*i, copy_val(v)),
        Cond::ArgI128AtMost(i, n) => Cond::ArgI128AtMost(*i, *n),
        Cond::ArgIn(i, vs) => Cond::ArgIn(*i, vs.iter().map(copy_val).collect()),
        Cond::ArgStrPrefix(i, p) => Cond::ArgStrPrefix(*i, p.clone()),
    }
}

pub fn copy_signer(s: &Signer) -> Signer {
    match s {
        Signer::Delegated(x) => Signer::Delegated(x.clone()),
        Signer::External(v, k) => Signer::External(v.clone(), k.clone()),
    }
}

pub fn copy_rule(r: &Rule) -> Rule {
    Rule {
        contract: r.contract.clone(),
        functions: copy_functions(&r.functions),
        conds: r.conds.iter().map(copy_cond).collect(),
        signers: r.signers.iter().map(copy_signer).collect(),
        threshold: r.threshold,
        cap: copy_cap(&r.cap),
        valid_until: r.valid_until,
        generation: r.generation,
    }
}

// ---------------------------------------------------------------------------
// Reference readings of the attenuation steps, for an in-range index.

pub fn ref_drop_rule(rs: &[Rule], i: usize) -> Vec<Rule> {
    rs.iter()
        .enumerate()
        .filter(|(j, _)| *j != i)
        .map(|(_, r)| copy_rule(r))
        .collect()
}

pub fn ref_add_cond(rs: &[Rule], i: usize, c: &Cond) -> Vec<Rule> {
    let mut out: Vec<Rule> = rs.iter().map(copy_rule).collect();
    out[i].conds.push(copy_cond(c));
    out
}

pub fn ref_remove_functions(rs: &[Rule], i: usize, fs: &[Vec<u8>]) -> Vec<Rule> {
    let mut out: Vec<Rule> = rs.iter().map(copy_rule).collect();
    out[i].functions = match &out[i].functions {
        Functions::AnyExcept(removed) => {
            Functions::AnyExcept(removed.iter().chain(fs).cloned().collect())
        }
        Functions::Only(listed) => {
            Functions::Only(listed.iter().filter(|f| !fs.contains(f)).cloned().collect())
        }
    };
    out
}

pub fn ref_restrict_functions(rs: &[Rule], i: usize, fs: &[Vec<u8>]) -> Vec<Rule> {
    let mut out: Vec<Rule> = rs.iter().map(copy_rule).collect();
    out[i].functions = match &out[i].functions {
        Functions::AnyExcept(removed) => Functions::Only(
            fs.iter()
                .filter(|f| !removed.contains(f))
                .cloned()
                .collect(),
        ),
        Functions::Only(listed) => {
            Functions::Only(listed.iter().filter(|f| fs.contains(f)).cloned().collect())
        }
    };
    out
}

/// For a last ledger no later than the rule's own, if it has one.
pub fn ref_lower_valid_until(rs: &[Rule], i: usize, last: u32) -> Vec<Rule> {
    let mut out: Vec<Rule> = rs.iter().map(copy_rule).collect();
    out[i].valid_until = Some(last);
    out
}

pub fn ref_remove_signers(rs: &[Rule], i: usize, ss: &[Signer]) -> Vec<Rule> {
    let mut out: Vec<Rule> = rs.iter().map(copy_rule).collect();
    out[i]
        .signers
        .retain(|s| !ss.iter().any(|x| ref_signer_eq(x, s)));
    out
}

/// For a threshold at least the rule's own.
pub fn ref_raise_threshold(rs: &[Rule], i: usize, threshold: u32) -> Vec<Rule> {
    let mut out: Vec<Rule> = rs.iter().map(copy_rule).collect();
    out[i].threshold = threshold;
    out
}
