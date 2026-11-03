//! The attenuation steps: what each builds, its refusals, and that every step
//! and every chain of steps only narrows, under every authenticated signer
//! list.

mod common;

use common::*;
use rule_eval::{
    AttenuationError, Cond, Context, Rule, Signer, Val, add_cap, add_cond, allows, allows_all,
    drop_rule, lengthen_cap_period, lower_cap_limit, lower_valid_until, raise_threshold,
    remove_functions, remove_signers, restrict_functions,
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

fn is_threshold_lowered(r: &Result<Vec<Rule>, AttenuationError>) -> bool {
    matches!(r, Err(AttenuationError::ThresholdLowered))
}

/// A two-of-three rule next to a rule without signers.
fn signed_sample() -> Vec<Rule> {
    vec![
        signed_rule(
            "token",
            &["transfer"],
            Vec::new(),
            vec![
                delegated("a"),
                external("a", ""),
                delegated("b"),
                delegated("a"),
            ],
            2,
        ),
        rule("vault", &["deposit"], Vec::new()),
    ]
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
    expected[0].functions = only(&["transfer"]);
    assert!(rules_eq(&out, &expected));
    // `burn` stays in rule 2: removal touches only the named rule.
    assert!(functions_eq(&out[2].functions, &only(&["burn"])));
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
    assert!(functions_eq(&out[0].functions, &only(&["transfer_from"])));
    let out = remove_functions(&rs, 0, &[b("trans"), b("Transfer")])
        .ok()
        .unwrap();
    assert!(rules_eq(&out, &rs));
    let out = remove_functions(&rs, 0, &[]).ok().unwrap();
    assert!(rules_eq(&out, &rs));
    let out = remove_functions(&rs, 0, &[b("transfer"), b("transfer_from")])
        .ok()
        .unwrap();
    assert!(functions_eq(&out[0].functions, &only(&[])));
    assert!(!allows(&out, &call("c1", "transfer", Vec::new()), &[]));
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
        assert!(is_no_such_rule(&remove_signers(
            &rs,
            index,
            &[delegated("a")]
        )));
        // The index is checked first, whatever the threshold.
        assert!(is_no_such_rule(&raise_threshold(&rs, index, 0)));
        assert!(is_no_such_rule(&raise_threshold(&rs, index, u32::MAX)));
    }
    for index in [0, 1, u32::MAX] {
        assert!(is_no_such_rule(&drop_rule(&[], index)));
        assert!(is_no_such_rule(&add_cond(&[], index, &c)));
        assert!(is_no_such_rule(&remove_functions(&[], index, &[])));
        assert!(is_no_such_rule(&remove_signers(&[], index, &[])));
        assert!(is_no_such_rule(&raise_threshold(&[], index, 0)));
    }
    assert!(rules_eq(&rs, &sample()));
}

#[test]
fn remove_signers_removes_every_occurrence_from_that_rule_only() {
    let rs = signed_sample();
    let out = remove_signers(&rs, 0, &[delegated("a")]).ok().unwrap();
    let mut expected = signed_sample();
    expected[0].signers = vec![external("a", ""), delegated("b")];
    assert!(rules_eq(&out, &expected));
    // The threshold is kept, so the rule now needs both remaining signers.
    assert_eq!(out[0].threshold, 2);
    let send = call("token", "transfer", Vec::new());
    assert!(allows(&rs, &send, &[delegated("a"), delegated("b")]));
    assert!(!allows(&out, &send, &[delegated("a"), delegated("b")]));
    assert!(allows(&out, &send, &[external("a", ""), delegated("b")]));
    // Removal matches exactly: an external signer with equal bytes stays.
    let out = remove_signers(&rs, 0, &[delegated("ab"), external("b", "")])
        .ok()
        .unwrap();
    assert!(rules_eq(&out, &rs));
    let out = remove_signers(&rs, 0, &[]).ok().unwrap();
    assert!(rules_eq(&out, &rs));
    let out = remove_signers(&rs, 1, &[delegated("a")]).ok().unwrap();
    assert!(rules_eq(&out, &rs));
    assert!(rules_eq(&rs, &signed_sample()));
}

#[test]
fn raise_threshold_sets_that_rule_and_refuses_to_lower() {
    let rs = signed_sample();
    for k in [2, 3, 4, u32::MAX] {
        let out = raise_threshold(&rs, 0, k).ok().unwrap();
        let mut expected = signed_sample();
        expected[0].threshold = k;
        assert!(rules_eq(&out, &expected));
    }
    assert!(is_threshold_lowered(&raise_threshold(&rs, 0, 1)));
    assert!(is_threshold_lowered(&raise_threshold(&rs, 0, 0)));
    // Rule 1 has threshold 0: every threshold is a raise.
    let out = raise_threshold(&rs, 1, 0).ok().unwrap();
    assert!(rules_eq(&out, &rs));
    let out = raise_threshold(&rs, 1, 1).ok().unwrap();
    assert!(!allows(
        &out,
        &call("vault", "deposit", Vec::new()),
        &[delegated("a")]
    ));
    assert!(rules_eq(&rs, &signed_sample()));
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
    assert!(allows(&rs, &send(1_000), &[]));
    let capped = add_cond(&rs, 0, &Cond::ArgI128AtMost(2, 100)).ok().unwrap();
    assert!(allows(&capped, &send(100), &[]));
    assert!(!allows(&capped, &send(1_000), &[]));
}

/// Every signer list a `remove_signers` step is tried with.
fn signer_removal_lists() -> Vec<Vec<Signer>> {
    vec![
        Vec::new(),
        vec![signer(0)],
        vec![signer(3)],
        vec![signer(0), signer(2)],
        vec![signer(4), signer(1)],
    ]
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
        for fs in removal_lists() {
            out.push((
                format!("restrict_functions {i} {fs:?}"),
                restrict_functions(rs, index, &fs).ok().unwrap(),
                ref_restrict_functions(rs, i, &fs),
            ));
        }
        for (k, ss) in signer_removal_lists().iter().enumerate() {
            out.push((
                format!("remove_signers {i} list {k}"),
                remove_signers(rs, index, ss).ok().unwrap(),
                ref_remove_signers(rs, i, ss),
            ));
        }
        for last in [0, 5] {
            if rs[i].valid_until.is_none_or(|current| last <= current) {
                out.push((
                    format!("lower_valid_until {i} {last}"),
                    lower_valid_until(rs, index, last).ok().unwrap(),
                    ref_lower_valid_until(rs, i, last),
                ));
            }
        }
        for t in rs[i].threshold..rs[i].threshold + 2 {
            out.push((
                format!("raise_threshold {i} {t}"),
                raise_threshold(rs, index, t).ok().unwrap(),
                ref_raise_threshold(rs, i, t),
            ));
        }
    }
    out
}

/// Whether `narrow` allows, under each of `auths`, only contexts `wide`
/// allows under the same signers.
fn narrower_on(
    narrow: &[Rule],
    wide: &[Rule],
    contexts: &[Context],
    auths: &[Vec<Signer>],
) -> bool {
    auths.iter().all(|auth| {
        contexts
            .iter()
            .all(|c| !allows(narrow, c, auth) || allows(wide, c, auth))
    })
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
            assert!(
                narrower_on(&got, &rs, &contexts, &[Vec::new()]),
                "{root:?} {name}"
            );
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
                    narrower_on(&leaf, &rs, &contexts, &[Vec::new()]),
                    "{root:?} {first}; {second}"
                );
                assert!(!allows_all(&leaf, &batch, &[]) || allows_all(&rs, &batch, &[]));
            }
        }
    }
}

/// Rules with signers: every signer list of up to two signers over four
/// universe signers (repeats included), each threshold from 0 to 3, alone and
/// beside a rule without signers.
fn signed_roots() -> Vec<Vec<Rule>> {
    let mut lists: Vec<Vec<usize>> = vec![Vec::new()];
    for x in 0..4 {
        lists.push(vec![x]);
        for y in 0..4 {
            lists.push(vec![x, y]);
        }
    }
    let mut out = Vec::new();
    for list in &lists {
        for threshold in 0..=3 {
            let r = || {
                signed_rule(
                    "c1",
                    &["f", "g"],
                    Vec::new(),
                    list.iter().map(|&k| signer(k)).collect(),
                    threshold,
                )
            };
            out.push(vec![r()]);
            out.push(vec![rule("c1", &["g"], Vec::new()), r()]);
        }
    }
    out
}

/// Every step on every signed root builds the reference result and allows,
/// under every authenticated list, only what the root allows; every chain of
/// two steps from a single signed rule stays inside it.
#[test]
fn signer_steps_only_narrow_under_every_authenticated_list() {
    let auths = authenticated_lists();
    let contexts = [
        call("c1", "f", Vec::new()),
        call("c1", "g", Vec::new()),
        call("c2", "f", Vec::new()),
    ];
    let mut checked = 0usize;
    for rs in signed_roots() {
        for (name, got, expected) in steps(&rs) {
            assert!(rules_eq(&got, &expected), "{name}");
            assert!(narrower_on(&got, &rs, &contexts, &auths), "{name}");
            checked += 1;
            if rs.len() == 1 {
                for (second, leaf, _) in steps(&got) {
                    assert!(
                        narrower_on(&leaf, &rs, &contexts, &auths),
                        "{name}; {second}"
                    );
                }
            }
        }
    }
    assert!(checked > 4_000);
}

#[test]
fn remove_functions_on_a_wildcard_excludes_them() {
    let rs = vec![wildcard(rule("token", &[], Vec::new()), &["burn"])];
    let out = remove_functions(&rs, 0, &[b("approve"), b("burn")])
        .ok()
        .unwrap();
    assert!(functions_eq(
        &out[0].functions,
        &any_except(&["burn", "approve", "burn"])
    ));
    assert!(allows(&out, &call("token", "transfer", Vec::new()), &[]));
    assert!(allows(&out, &call("token", "anything", Vec::new()), &[]));
    assert!(!allows(&out, &call("token", "approve", Vec::new()), &[]));
    assert!(!allows(&out, &call("token", "burn", Vec::new()), &[]));
}

#[test]
fn restrict_functions_keeps_only_the_named_functions() {
    // A wildcard becomes the named functions it does not exclude.
    let rs = vec![wildcard(rule("token", &[], Vec::new()), &["burn"])];
    let out = restrict_functions(&rs, 0, &[b("transfer"), b("burn")])
        .ok()
        .unwrap();
    assert!(functions_eq(&out[0].functions, &only(&["transfer"])));
    // A list keeps the functions also named, in its own order.
    let rs = vec![rule("token", &["approve", "transfer", "burn"], Vec::new())];
    let out = restrict_functions(&rs, 0, &[b("burn"), b("approve"), b("mint")])
        .ok()
        .unwrap();
    assert!(functions_eq(&out[0].functions, &only(&["approve", "burn"])));
    // Names compare exactly.
    let out = restrict_functions(&rs, 0, &[b("Transfer"), b("trans")])
        .ok()
        .unwrap();
    assert!(functions_eq(&out[0].functions, &only(&[])));
    for index in [1, u32::MAX] {
        assert!(is_no_such_rule(&restrict_functions(&rs, index, &[])));
    }
}

#[test]
fn lower_valid_until_adds_or_lowers_and_refuses_to_raise() {
    let rs = vec![
        rule("token", &["transfer"], Vec::new()),
        valid_until(rule("vault", &["deposit"], Vec::new()), 10),
    ];
    let out = lower_valid_until(&rs, 0, 7).ok().unwrap();
    assert_eq!(out[0].valid_until, Some(7));
    assert_eq!(out[1].valid_until, Some(10));
    let out = lower_valid_until(&rs, 1, 10).ok().unwrap();
    assert_eq!(out[1].valid_until, Some(10));
    let out = lower_valid_until(&rs, 1, 0).ok().unwrap();
    assert_eq!(out[1].valid_until, Some(0));
    assert!(matches!(
        lower_valid_until(&rs, 1, 11),
        Err(AttenuationError::ValidUntilRaised)
    ));
    // The index is checked first.
    assert!(is_no_such_rule(&lower_valid_until(&rs, 2, u32::MAX)));
}

/// No step changes a rule's generation: each rule after a step carries the
/// generation of the rule it comes from.
#[test]
fn no_step_changes_a_generation() {
    let rs = vec![
        issued(
            capped(rule("token", &["transfer"], Vec::new()), cap(10, 5, 2)),
            7,
        ),
        rule("vault", &["deposit"], Vec::new()),
        issued(wildcard(rule("token", &[], Vec::new()), &[]), 8),
    ];
    let generations = |out: &[Rule]| out.iter().map(|r| r.generation).collect::<Vec<_>>();
    for i in 0..3u32 {
        let dropped = drop_rule(&rs, i).ok().unwrap();
        let mut expected = vec![Some(7), None, Some(8)];
        expected.remove(i as usize);
        assert_eq!(generations(&dropped), expected);
        for out in [
            add_cond(&rs, i, &Cond::ArgEq(0, Val::Bool(true)))
                .ok()
                .unwrap(),
            remove_functions(&rs, i, &[b("transfer")]).ok().unwrap(),
            restrict_functions(&rs, i, &[b("transfer")]).ok().unwrap(),
            remove_signers(&rs, i, &[delegated("a")]).ok().unwrap(),
            raise_threshold(&rs, i, 1).ok().unwrap(),
            lower_valid_until(&rs, i, 3).ok().unwrap(),
        ] {
            assert_eq!(generations(&out), vec![Some(7), None, Some(8)]);
        }
    }
    for out in [
        add_cap(&rs, 1, &cap(1, 1, 0)).ok().unwrap(),
        lower_cap_limit(&rs, 0, 1).ok().unwrap(),
        lengthen_cap_period(&rs, 0, 9).ok().unwrap(),
    ] {
        assert_eq!(generations(&out), vec![Some(7), None, Some(8)]);
    }
}
