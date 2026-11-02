//! `allows`, `allows_all` and the condition and value semantics they rest on.

mod common;

use common::*;
use rule_eval::{
    Cond, Val, allows, allows_all, bytes_eq, bytes_in, cond_holds, rule_allows, val_eq,
};

#[test]
fn bytes_compare_exactly() {
    assert!(bytes_eq(b"", b""));
    assert!(bytes_eq(b"transfer", b"transfer"));
    assert!(!bytes_eq(b"transfer", b"transfe"));
    assert!(!bytes_eq(b"transfe", b"transfer"));
    assert!(!bytes_eq(b"transfer", b"Transfer"));
    assert!(!bytes_eq(b"", b"a"));
    assert!(!bytes_eq(b"ab", b"ba"));
}

#[test]
fn bytes_in_needs_an_exact_member() {
    let list = vec![b("transfer"), b("approve")];
    assert!(bytes_in(b"transfer", &list));
    assert!(bytes_in(b"approve", &list));
    assert!(!bytes_in(b"trans", &list));
    assert!(!bytes_in(b"transfer_from", &list));
    assert!(!bytes_in(b"", &list));
    assert!(!bytes_in(b"transfer", &[]));
}

#[test]
fn values_equal_only_with_the_same_constructor() {
    for k in 0..VALS {
        for l in 0..VALS {
            assert_eq!(val_eq(&val(k), &val(l)), k == l, "val {k} vs val {l}");
        }
    }
}

#[test]
fn every_constructor_equals_itself_and_compares_its_payload() {
    let pairs = [
        (
            Val::I128(i128::MIN),
            Val::I128(i128::MIN),
            Val::I128(i128::MAX),
        ),
        (Val::U64(0), Val::U64(0), Val::U64(u64::MAX)),
        (Val::Bool(false), Val::Bool(false), Val::Bool(true)),
        (Val::Bytes(b("ab")), Val::Bytes(b("ab")), Val::Bytes(b("a"))),
        (
            Val::Address(b("ab")),
            Val::Address(b("ab")),
            Val::Address(b("abc")),
        ),
        (
            Val::Symbol(b("ab")),
            Val::Symbol(b("ab")),
            Val::Symbol(b("aB")),
        ),
        (Val::Other(b("ab")), Val::Other(b("ab")), Val::Other(b(""))),
    ];
    for (x, same, other) in &pairs {
        assert!(val_eq(x, x));
        assert!(val_eq(x, same));
        assert!(!val_eq(x, other));
        assert!(!val_eq(other, x));
    }
}

#[test]
fn arg_eq_needs_the_argument_and_the_same_value() {
    let c = Cond::ArgEq(1, Val::Address(b("alice")));
    assert!(cond_holds(&c, &[Val::I128(0), Val::Address(b("alice"))]));
    assert!(!cond_holds(&c, &[Val::I128(0), Val::Address(b("bob"))]));
    assert!(!cond_holds(&c, &[Val::I128(0), Val::Address(b("alic"))]));
    // Same bytes under another constructor.
    assert!(!cond_holds(&c, &[Val::I128(0), Val::Bytes(b("alice"))]));
    assert!(!cond_holds(&c, &[Val::I128(0), Val::Symbol(b("alice"))]));
    assert!(!cond_holds(&c, &[Val::I128(0), Val::Other(b("alice"))]));
    // Missing argument.
    assert!(!cond_holds(&c, &[Val::Address(b("alice"))]));
    assert!(!cond_holds(&c, &[]));
}

#[test]
fn arg_eq_on_every_constructor() {
    for k in 0..VALS {
        let c = Cond::ArgEq(0, val(k));
        for l in 0..VALS {
            assert_eq!(cond_holds(&c, &[val(l)]), k == l);
        }
        assert!(!cond_holds(&c, &[]));
    }
}

#[test]
fn arg_i128_at_most_needs_an_i128_within_the_bound() {
    let c = Cond::ArgI128AtMost(0, 100);
    assert!(cond_holds(&c, &[Val::I128(100)]));
    assert!(cond_holds(&c, &[Val::I128(-5)]));
    assert!(cond_holds(&c, &[Val::I128(i128::MIN)]));
    assert!(!cond_holds(&c, &[Val::I128(101)]));
    assert!(!cond_holds(&c, &[Val::I128(i128::MAX)]));
    // Wrong constructor, even with a value within the bound.
    assert!(!cond_holds(&c, &[Val::U64(1)]));
    assert!(!cond_holds(&c, &[Val::Bool(false)]));
    assert!(!cond_holds(&c, &[Val::Bytes(Vec::new())]));
    assert!(!cond_holds(&c, &[Val::Other(Vec::new())]));
    // Missing argument.
    assert!(!cond_holds(&c, &[]));
    assert!(!cond_holds(&Cond::ArgI128AtMost(1, 100), &[Val::I128(0)]));
}

#[test]
fn out_of_range_condition_indices_are_false() {
    let args = [Val::I128(0)];
    assert!(!cond_holds(&Cond::ArgEq(u32::MAX, Val::I128(0)), &args));
    assert!(!cond_holds(
        &Cond::ArgI128AtMost(u32::MAX, i128::MAX),
        &args
    ));
}

#[test]
fn a_rule_matches_its_contract_and_functions_exactly() {
    let r = rule("token", &["transfer", "approve"], Vec::new());
    assert!(rule_allows(&r, &call("token", "transfer", Vec::new())));
    assert!(rule_allows(
        &r,
        &call("token", "approve", vec![Val::Bool(true)])
    ));
    assert!(!rule_allows(&r, &call("token", "burn", Vec::new())));
    assert!(!rule_allows(&r, &call("tokens", "transfer", Vec::new())));
    assert!(!rule_allows(&r, &call("toke", "transfer", Vec::new())));
    assert!(!rule_allows(&r, &call("token", "transfe", Vec::new())));
    assert!(!rule_allows(
        &r,
        &call("token", "transfer_from", Vec::new())
    ));
}

#[test]
fn a_rule_without_functions_allows_nothing() {
    let r = rule("token", &[], Vec::new());
    assert!(!rule_allows(&r, &call("token", "transfer", Vec::new())));
    assert!(!rule_allows(&r, &call("token", "", Vec::new())));
}

#[test]
fn a_rule_needs_every_condition() {
    let r = rule(
        "token",
        &["transfer"],
        vec![
            Cond::ArgEq(0, Val::Address(b("alice"))),
            Cond::ArgI128AtMost(2, 100),
        ],
    );
    let args = |from: &str, amount: i128| {
        vec![
            Val::Address(b(from)),
            Val::Address(b("bob")),
            Val::I128(amount),
        ]
    };
    assert!(rule_allows(
        &r,
        &call("token", "transfer", args("alice", 100))
    ));
    assert!(!rule_allows(
        &r,
        &call("token", "transfer", args("alice", 101))
    ));
    assert!(!rule_allows(
        &r,
        &call("token", "transfer", args("carol", 1))
    ));
}

#[test]
fn no_rule_allows_a_creation() {
    let rs = vec![
        rule("", &[""], Vec::new()),
        rule("c1", &["f", "g"], Vec::new()),
    ];
    for hash in ["", "c1", "f"] {
        let c = create(hash);
        for r in &rs {
            assert!(!rule_allows(r, &c));
        }
        assert!(!allows(&rs, &c));
    }
    for specs in rule_sets() {
        let rs = build(&specs);
        assert!(!allows(&rs, &create("c1")));
        assert!(!allows(&rs, &create("")));
    }
}

#[test]
fn a_cap_reads_only_the_call_its_rule_matches() {
    // Rule 0 caps argument 2 of token.transfer; rule 1 allows any
    // vault.deposit. A batch whose vault call has a large argument 2 is not
    // held to the token cap.
    let rs = vec![
        rule("token", &["transfer"], vec![Cond::ArgI128AtMost(2, 100)]),
        rule("vault", &["deposit"], Vec::new()),
    ];
    let small_transfer = || {
        call(
            "token",
            "transfer",
            vec![Val::Address(b("a")), Val::Address(b("b")), Val::I128(50)],
        )
    };
    let big_transfer = call(
        "token",
        "transfer",
        vec![Val::Address(b("a")), Val::Address(b("b")), Val::I128(500)],
    );
    let big_deposit = || {
        call(
            "vault",
            "deposit",
            vec![Val::Address(b("a")), Val::Address(b("b")), Val::I128(500)],
        )
    };

    assert!(allows(&rs, &big_deposit()));
    assert!(allows_all(&rs, &[small_transfer(), big_deposit()]));
    assert!(!allows(&rs, &big_transfer));
    assert!(!allows_all(&rs, &[big_transfer, big_deposit()]));
    // The cap's rule does not match the vault call, so the vault call is
    // allowed by its own rule only.
    assert!(!rule_allows(&rs[0], &big_deposit()));
}

#[test]
fn a_rule_set_allows_when_some_rule_does() {
    let rs = vec![
        rule("c1", &["f"], vec![Cond::ArgEq(0, Val::Bool(true))]),
        rule("c1", &["f"], vec![Cond::ArgEq(0, Val::Bool(false))]),
    ];
    assert!(allows(&rs, &call("c1", "f", vec![Val::Bool(true)])));
    assert!(allows(&rs, &call("c1", "f", vec![Val::Bool(false)])));
    assert!(!allows(&rs, &call("c1", "f", vec![Val::U64(0)])));
    assert!(!allows(&[], &call("c1", "f", Vec::new())));
}

#[test]
fn allows_all_on_empty_batches_and_empty_rule_sets() {
    assert!(allows_all(&[], &[]));
    assert!(allows_all(&[rule("c1", &["f"], Vec::new())], &[]));
    assert!(!allows_all(&[], &[call("c1", "f", Vec::new())]));
}

#[test]
fn allows_agrees_with_the_reference_reading() {
    let contexts = contexts();
    for specs in rule_sets() {
        let rs = build(&specs);
        for c in &contexts {
            assert_eq!(allows(&rs, c), ref_allows(&rs, c), "{specs:?}");
        }
    }
}

#[test]
fn allows_all_is_the_conjunction_of_allows() {
    // Every batch of up to two contexts from a twenty-context slice of the
    // universe, against every rule set of up to two rules.
    let small: Vec<_> = contexts().into_iter().step_by(17).collect();
    assert_eq!(small.len(), 20);
    let mut batches: Vec<Vec<rule_eval::Context>> = vec![Vec::new()];
    for x in &small {
        batches.push(vec![copy_context(x)]);
        for y in &small {
            batches.push(vec![copy_context(x), copy_context(y)]);
        }
    }
    let whole = contexts();
    for specs in rule_sets() {
        let rs = build(&specs);
        for batch in &batches {
            let each = batch.iter().all(|c| allows(&rs, c));
            assert_eq!(allows_all(&rs, batch), each, "{specs:?}");
        }
        let each = whole.iter().all(|c| allows(&rs, c));
        assert_eq!(allows_all(&rs, &whole), each, "{specs:?}");
    }
}
