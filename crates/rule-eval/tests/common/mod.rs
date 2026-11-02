//! Builders, small universes and a reference reading of the semantics shared
//! by the integration tests.
#![allow(dead_code)]

use rule_eval::{Cond, Context, Rule, Val};

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

pub fn rule(contract: &str, functions: &[&str], conds: Vec<Cond>) -> Rule {
    Rule {
        contract: b(contract),
        functions: functions.iter().map(|f| b(f)).collect(),
        conds,
    }
}

/// Structural equality on rules, for checking what an attenuation step built.
pub fn rule_eq(x: &Rule, y: &Rule) -> bool {
    x.contract == y.contract
        && x.functions == y.functions
        && x.conds.len() == y.conds.len()
        && x.conds.iter().zip(&y.conds).all(|(p, q)| cond_eq(p, q))
}

pub fn rules_eq(xs: &[Rule], ys: &[Rule]) -> bool {
    xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| rule_eq(x, y))
}

pub fn cond_eq(p: &Cond, q: &Cond) -> bool {
    match (p, q) {
        (Cond::ArgEq(i, v), Cond::ArgEq(j, w)) => i == j && rule_eval::val_eq(v, w),
        (Cond::ArgI128AtMost(i, n), Cond::ArgI128AtMost(j, m)) => i == j && n == m,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Small universes. Values are built fresh from an index each time, since the
// evaluator's types implement no traits.

pub const CONTRACTS: [&str; 2] = ["c1", "c2"];
pub const FUNCTIONS: [&str; 2] = ["f", "g"];

pub const VALS: usize = 9;

/// The `k`-th value of a universe holding every constructor, two values of
/// one constructor, and byte payloads equal across constructors.
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
        _ => unreachable!(),
    }
}

pub const CONDS: usize = 5;

/// The `k`-th condition of a universe touching argument 0 and argument 1.
pub fn cond(k: usize) -> Cond {
    match k {
        0 => Cond::ArgEq(0, Val::I128(5)),
        1 => Cond::ArgI128AtMost(0, 7),
        2 => Cond::ArgEq(1, Val::Address(b("c1"))),
        3 => Cond::ArgEq(0, Val::Bytes(b("c1"))),
        4 => Cond::ArgI128AtMost(1, 0),
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
    /// Bit `k` set: `FUNCTIONS[k]` is in the function list.
    pub functions: u8,
    /// Indices into the condition universe.
    pub conds: [Option<usize>; 2],
}

impl RuleSpec {
    pub fn build(self) -> Rule {
        Rule {
            contract: b(CONTRACTS[self.contract]),
            functions: (0..FUNCTIONS.len())
                .filter(|k| self.functions & (1 << k) != 0)
                .map(|k| b(FUNCTIONS[k]))
                .collect(),
            conds: self.conds.iter().flatten().map(|&k| cond(k)).collect(),
        }
    }
}

/// Every rule with a universe contract, any subset of the universe functions,
/// and up to two conditions.
pub fn rule_specs() -> Vec<RuleSpec> {
    let mut cond_choices = vec![[None, None]];
    for p in 0..CONDS {
        cond_choices.push([Some(p), None]);
        for q in p + 1..CONDS {
            cond_choices.push([Some(p), Some(q)]);
        }
    }
    let mut out = Vec::new();
    for contract in 0..CONTRACTS.len() {
        for functions in 0..(1u8 << FUNCTIONS.len()) {
            for conds in &cond_choices {
                out.push(RuleSpec {
                    contract,
                    functions,
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
        | (Val::Other(p), Val::Other(q)) => p == q,
        _ => false,
    }
}

pub fn ref_cond_holds(c: &Cond, args: &[Val]) -> bool {
    match c {
        Cond::ArgEq(i, v) => args.get(*i as usize).is_some_and(|a| ref_val_eq(a, v)),
        Cond::ArgI128AtMost(i, n) => matches!(args.get(*i as usize), Some(Val::I128(v)) if v <= n),
    }
}

pub fn ref_rule_allows(r: &Rule, c: &Context) -> bool {
    match c {
        Context::Call {
            contract,
            function,
            args,
        } => {
            *contract == r.contract
                && r.functions.contains(function)
                && r.conds.iter().all(|k| ref_cond_holds(k, args))
        }
        Context::Create { .. } => false,
    }
}

pub fn ref_allows(rs: &[Rule], c: &Context) -> bool {
    rs.iter().any(|r| ref_rule_allows(r, c))
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
    }
}

pub fn copy_rule(r: &Rule) -> Rule {
    Rule {
        contract: r.contract.clone(),
        functions: r.functions.clone(),
        conds: r.conds.iter().map(copy_cond).collect(),
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
    out[i].functions.retain(|f| !fs.contains(f));
    out
}
