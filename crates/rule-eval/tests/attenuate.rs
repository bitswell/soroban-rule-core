//! The attenuation steps: what each builds, its out-of-range error, and that
//! every step and every chain of steps only narrows.

mod common;

use common::*;
use rule_eval::{
    AttenuationError, Cond, Context, Rule, Val, add_cond, allows, allows_all, drop_rule,
    remove_functions,
};

fn sample() -> Vec<Rule> {
    vec![
        rule(
            "token",
            &["transfer", "approve"],
            vec![Cond::ArgI128AtMost(2, 100)],
        ),
        rule("vault", &["deposit"], Vec::new()),
        rule(
            "token",
            &["burn"],
            vec![Cond::ArgEq(0, Val::Address(b("alice")))],
        ),
    ]
}

fn is_no_such_rule(r: &Result<Vec<Rule>, AttenuationError>) -> bool {
    matches!(r, Err(AttenuationError::NoSuchRule))
}

#[test]
fn drop_rule_removes_exactly_that_rule() {
    let rs = sample();
    let out = drop_rule(&rs, 1).ok().unwrap();
    assert!(rules_eq(&out, &[copy_rule(&rs[0]), copy_rule(&rs[2])]));
    let out = drop_rule(&rs, 0).ok().unwrap();
    assert!(rules_eq(&out, &[copy_rule(&rs[1]), copy_rule(&rs[2])]));
    let out = drop_rule(&rs, 2).ok().unwrap();
    assert!(rules_eq(&out, &[copy_rule(&rs[0]), copy_rule(&rs[1])]));
    let one = vec![rule("c1", &["f"], Vec::new())];
    assert!(drop_rule(&one, 0).ok().unwrap().is_empty());
    // The input is unchanged.
    assert!(rules_eq(&rs, &sample()));
}

#[test]
fn add_cond_appends_to_that_rule_only() {
    let rs = sample();
    let c = Cond::ArgEq(1, Val::Address(b("bob")));
    let out = add_cond(&rs, 0, &c).ok().unwrap();
    let mut expected = sample();
    expected[0]
        .conds
        .push(Cond::ArgEq(1, Val::Address(b("bob"))));
    assert!(rules_eq(&out, &expected));
    assert_eq!(out[0].conds.len(), 2);
    assert!(cond_eq(&out[0].conds[0], &Cond::ArgI128AtMost(2, 100)));
    assert!(rules_eq(&rs, &sample()));
}

#[test]
fn remove_functions_removes_from_that_rule_only() {
    let rs = sample();
    let out = remove_functions(&rs, 0, &[b("approve"), b("burn")])
        .ok()
        .unwrap();
    let mut expected = sample();
    expected[0].functions = vec![b("transfer")];
    assert!(rules_eq(&out, &expected));
    // `burn` stays in rule 2: removal touches only the named rule.
    assert!(out[2].functions == vec![b("burn")]);
    assert!(rules_eq(&rs, &sample()));
}

#[test]
fn remove_functions_matches_names_exactly_and_removes_duplicates() {
    let rs = vec![rule(
        "c1",
        &["transfer", "transfer_from", "transfer"],
        Vec::new(),
    )];
    let out = remove_functions(&rs, 0, &[b("transfer")]).ok().unwrap();
    assert!(out[0].functions == vec![b("transfer_from")]);
    let out = remove_functions(&rs, 0, &[b("trans"), b("Transfer")])
        .ok()
        .unwrap();
    assert!(rules_eq(&out, &rs));
    let out = remove_functions(&rs, 0, &[]).ok().unwrap();
    assert!(rules_eq(&out, &rs));
    let out = remove_functions(&rs, 0, &[b("transfer"), b("transfer_from")])
        .ok()
        .unwrap();
    assert!(out[0].functions.is_empty());
    assert!(!allows(&out, &call("c1", "transfer", Vec::new())));
}

#[test]
fn out_of_range_indices_are_refused() {
    let rs = sample();
    let c = Cond::ArgI128AtMost(0, 0);
    for index in [3, 4, u32::MAX] {
        assert!(is_no_such_rule(&drop_rule(&rs, index)));
        assert!(is_no_such_rule(&add_cond(&rs, index, &c)));
        assert!(is_no_such_rule(&remove_functions(
            &rs,
            index,
            &[b("transfer")]
        )));
    }
    for index in [0, 1, u32::MAX] {
        assert!(is_no_such_rule(&drop_rule(&[], index)));
        assert!(is_no_such_rule(&add_cond(&[], index, &c)));
        assert!(is_no_such_rule(&remove_functions(&[], index, &[])));
    }
    assert!(rules_eq(&rs, &sample()));
}

#[test]
fn adding_a_cap_denies_what_it_excludes() {
    let rs = vec![rule("token", &["transfer"], Vec::new())];
    let send = |amount: i128| {
        call(
            "token",
            "transfer",
            vec![
                Val::Address(b("a")),
                Val::Address(b("b")),
                Val::I128(amount),
            ],
        )
    };
    assert!(allows(&rs, &send(1_000)));
    let capped = add_cond(&rs, 0, &Cond::ArgI128AtMost(2, 100)).ok().unwrap();
    assert!(allows(&capped, &send(100)));
    assert!(!allows(&capped, &send(1_000)));
}

/// Every attenuation step that applies to `rs`, with the reference reading of
/// its result.
fn steps(rs: &[Rule]) -> Vec<(String, Vec<Rule>, Vec<Rule>)> {
    let mut out = Vec::new();
    for i in 0..rs.len() {
        let index = u32::try_from(i).unwrap();
        out.push((
            format!("drop_rule {i}"),
            drop_rule(rs, index).ok().unwrap(),
            ref_drop_rule(rs, i),
        ));
        for k in 0..CONDS {
            let c = cond(k);
            out.push((
                format!("add_cond {i} cond {k}"),
                add_cond(rs, index, &c).ok().unwrap(),
                ref_add_cond(rs, i, &c),
            ));
        }
        for fs in removal_lists() {
            out.push((
                format!("remove_functions {i} {fs:?}"),
                remove_functions(rs, index, &fs).ok().unwrap(),
                ref_remove_functions(rs, i, &fs),
            ));
        }
    }
    out
}

fn narrower_on(narrow: &[Rule], wide: &[Rule], contexts: &[Context]) -> bool {
    contexts
        .iter()
        .all(|c| !allows(narrow, c) || allows(wide, c))
}

/// Every attenuation step on every rule set of up to two rules (each rule
/// with up to one condition) builds the reference result, and allows only
/// contexts the original allows.
#[test]
fn every_step_builds_its_result_and_only_narrows() {
    let contexts = contexts();
    let specs: Vec<RuleSpec> = rule_specs()
        .into_iter()
        .filter(|s| s.conds[1].is_none())
        .collect();
    let mut roots = vec![Vec::new()];
    for &x in &specs {
        roots.push(vec![x]);
        for &y in &specs {
            roots.push(vec![x, y]);
        }
    }
    let mut checked = 0usize;
    for root in &roots {
        let rs = build(root);
        for (name, got, expected) in steps(&rs) {
            assert!(rules_eq(&got, &expected), "{root:?} {name}");
            assert!(narrower_on(&got, &rs, &contexts), "{root:?} {name}");
            checked += 1;
        }
    }
    assert!(checked > 50_000);
}

/// Every chain of two steps from a single-rule root, and from a two-rule root
/// without conditions, allows only contexts the root allows, alone or across
/// a batch.
#[test]
fn every_two_step_chain_stays_inside_its_root() {
    let contexts = contexts();
    let batch: Vec<Context> = contexts.iter().step_by(11).map(copy_context).collect();
    let specs = rule_specs();
    let mut roots: Vec<Vec<RuleSpec>> = specs.iter().map(|&s| vec![s]).collect();
    let bare: Vec<RuleSpec> = specs.into_iter().filter(|s| s.conds[0].is_none()).collect();
    for &x in &bare {
        for &y in &bare {
            roots.push(vec![x, y]);
        }
    }
    for root in &roots {
        let rs = build(root);
        for (first, mid, _) in steps(&rs) {
            for (second, leaf, _) in steps(&mid) {
                assert!(
                    narrower_on(&leaf, &rs, &contexts),
                    "{root:?} {first}; {second}"
                );
                assert!(!allows_all(&leaf, &batch) || allows_all(&rs, &batch));
            }
        }
    }
}
