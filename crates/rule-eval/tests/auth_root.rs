//! Exact authorization roots belong to each entry and to each restricted rule.
mod common;

use common::*;
use rule_eval::*;

fn root(contract: &str, function: &str) -> AuthRoot {
    AuthRoot {
        contract: b(contract),
        function: b(function),
    }
}

fn rules() -> Vec<Rule> {
    let game = signed_rule("game", &["guess"], vec![], vec![delegated("key")], 1);
    let mut transfer = capped(
        signed_rule("xlm", &["transfer"], vec![], vec![delegated("key")], 1),
        cap(10, 20, 2),
    );
    transfer.auth_root = Some(root("game", "guess"));
    vec![game, transfer]
}

fn guess() -> Context {
    call("game", "guess", vec![])
}
fn transfer(n: i128) -> Context {
    call(
        "xlm",
        "transfer",
        vec![Val::Address(b("me")), Val::Address(b("game")), Val::I128(n)],
    )
}
fn records(rs: &[Rule]) -> Vec<SpendRecord> {
    rs.iter().map(|_| empty_record()).collect()
}
fn auth() -> Vec<Signer> {
    vec![delegated("key")]
}
fn roots(rs: &[Rule]) -> Vec<Option<(Vec<u8>, Vec<u8>)>> {
    rs.iter()
        .map(|r| {
            r.auth_root
                .as_ref()
                .map(|x| (x.contract.clone(), x.function.clone()))
        })
        .collect()
}

#[test]
fn exact_root_wrong_contract_function_missing_and_creation() {
    let rs = rules();
    let requirement = &rs[1].auth_root;
    assert!(auth_root_matches(requirement, Some(&guess())));
    assert!(!auth_root_matches(
        requirement,
        Some(&call("other", "guess", vec![]))
    ));
    assert!(!auth_root_matches(
        requirement,
        Some(&call("game", "other", vec![]))
    ));
    assert!(!auth_root_matches(requirement, None));
    assert!(!auth_root_matches(requirement, Some(&create("wasm"))));
    assert!(auth_root_matches(&None, None));
    // Roots constrain only the pair, not its arguments.
    assert!(auth_root_matches(
        requirement,
        Some(&call("game", "guess", vec![Val::Bool(true)]))
    ));
}

#[test]
fn win_authenticates_without_charge_loss_charges_and_direct_transfer_is_refused() {
    let rs = rules();
    let recs = records(&rs);
    let win = check_auth(&rs, &recs, &[guess()], &[0], &auth(), 1, 0)
        .ok()
        .unwrap();
    assert_eq!(win[1].total, 0);
    assert!(win[1].history.is_empty());
    assert!(matches!(
        check_auth(&rs, &recs, &[guess()], &[0], &[], 1, 0),
        Err(Refusal::NotAllowed)
    ));
    let loss = check_auth(&rs, &win, &[guess(), transfer(4)], &[0, 1], &auth(), 2, 0)
        .ok()
        .unwrap();
    assert_eq!(loss[1].total, 4);
    assert!(allows_batch(&rs, &[guess(), transfer(4)], &auth()));
    assert!(!allows_batch(&rs, &[transfer(1)], &auth()));
    assert!(matches!(
        check_auth(&rs, &loss, &[transfer(1)], &[1], &auth(), 3, 0),
        Err(Refusal::NotAllowed)
    ));
    // A previously authenticated independent entry cannot supply a root.
    assert_eq!(loss[1].total, 4);
    // Legacy helpers are deliberately only local screening.
    assert!(rule_allows(&rs[1], &transfer(1), &auth()));
    assert!(allows(&rs, &transfer(1), &auth()));
    assert!(allows_all(&rs, &[transfer(1)], &auth()));
    assert!(!rule_allows_in(&rs[1], None, &transfer(1), &auth()));
}

#[test]
fn wrong_root_and_reordered_entry_refuse_even_with_an_independent_root_rule() {
    let mut rs = rules();
    rs.push(signed_rule(
        "other",
        &["guess"],
        vec![],
        vec![delegated("key")],
        1,
    ));
    rs.push(signed_rule(
        "game",
        &["other"],
        vec![],
        vec![delegated("key")],
        1,
    ));
    let recs = records(&rs);
    for (ctxs, choices) in [
        (
            vec![call("other", "guess", vec![]), transfer(1)],
            vec![2, 1],
        ),
        (vec![call("game", "other", vec![]), transfer(1)], vec![3, 1]),
        (vec![transfer(1), guess()], vec![1, 0]),
        (vec![create("wasm"), transfer(1)], vec![0, 1]),
    ] {
        assert!(!allows_batch(&rs, &ctxs, &auth()));
        assert!(matches!(
            check_auth(&rs, &recs, &ctxs, &choices, &auth(), 1, 0),
            Err(Refusal::NotAllowed)
        ));
    }
}

#[test]
fn root_check_remains_conjunctive_with_all_existing_checks() {
    let mut rs = rules();
    let recs = records(&rs);
    let ctxs = [guess(), transfer(1)];
    assert!(matches!(
        check_auth(&rs, &recs, &ctxs, &[0, 1], &[], 1, 0),
        Err(Refusal::NotAllowed)
    ));
    assert!(matches!(
        check_auth(&rs, &recs, &ctxs, &[0, 1], &[delegated("wrong")], 1, 0),
        Err(Refusal::NotAllowed)
    ));
    rs[1].conds.push(Cond::ArgEq(0, Val::Address(b("other"))));
    assert!(matches!(
        check_auth(&rs, &recs, &ctxs, &[0, 1], &auth(), 1, 0),
        Err(Refusal::NotAllowed)
    ));
    rs[1].conds.clear();
    rs[1].valid_until = Some(0);
    assert!(matches!(
        check_auth(&rs, &recs, &ctxs, &[0, 1], &auth(), 1, 0),
        Err(Refusal::Expired)
    ));
    rs[1].valid_until = None;
    rs[1].generation = Some(1);
    assert!(matches!(
        check_auth(&rs, &recs, &ctxs, &[0, 1], &auth(), 1, 0),
        Err(Refusal::StaleGeneration)
    ));
}

#[test]
fn aggregation_and_late_failure_return_no_charges() {
    let rs = rules();
    let recs = records(&rs);
    let first = check_auth(
        &rs,
        &recs,
        &[guess(), transfer(2), transfer(3)],
        &[0, 1, 1],
        &auth(),
        1,
        0,
    )
    .ok()
    .unwrap();
    assert_eq!(first[1].total, 5);
    assert!(matches!(
        check_auth(
            &rs,
            &first,
            &[guess(), transfer(4), transfer(2)],
            &[0, 1, 1],
            &auth(),
            2,
            0
        ),
        Err(Refusal::Cap(CapError::LimitExceeded))
    ));
    assert_eq!(first[1].total, 5);
    assert!(matches!(
        check_auth(
            &rs,
            &first,
            &[guess(), transfer(4), call("bad", "call", vec![])],
            &[0, 1, 1],
            &auth(),
            2,
            0
        ),
        Err(Refusal::NotAllowed)
    ));
    assert_eq!(first[1].total, 5);
    let final_records = check_auth(&rs, &first, &[guess(), transfer(5)], &[0, 1], &auth(), 3, 0)
        .ok()
        .unwrap();
    assert_eq!(final_records[1].total, 10);
}

#[test]
fn empty_and_mismatched_batches_keep_the_deliberate_existing_semantics() {
    let rs = rules();
    let recs = records(&rs);
    assert!(allows_batch(&rs, &[], &auth()));
    assert!(check_auth(&rs, &recs, &[], &[], &[], 1, 0).is_ok());
    assert!(matches!(
        check_auth(&rs, &recs, &[], &[], &auth(), 1, 0),
        Err(Refusal::UnauthorizedSigner)
    ));
    assert!(matches!(
        check_auth(&rs, &recs, &[guess()], &[], &auth(), 1, 0),
        Err(Refusal::ChoicesMismatch)
    ));
    assert!(matches!(
        check_auth(&rs, &[], &[], &[], &[], 1, 0),
        Err(Refusal::RecordsMismatch)
    ));
}

#[test]
fn every_attenuation_retains_surviving_roots_including_reindexing() {
    let rs = rules();
    for i in 0..2 {
        for out in [
            add_cond(&rs, i, &Cond::ArgEq(0, Val::Bool(true))),
            remove_functions(&rs, i, &[b("other")]),
            restrict_functions(&rs, i, &[b("guess"), b("transfer")]),
            remove_signers(&rs, i, &[delegated("other")]),
            raise_threshold(&rs, i, 2),
            lower_valid_until(&rs, i, 9),
        ] {
            assert_eq!(roots(&out.ok().unwrap()), roots(&rs));
        }
    }
    for out in [
        add_cap(&rs, 0, &cap(1, 1, 0)),
        lower_cap_limit(&rs, 1, 5),
        lengthen_cap_period(&rs, 1, 30),
    ] {
        assert_eq!(roots(&out.ok().unwrap()), roots(&rs));
    }
    let dropped = drop_rule(&rs, 0).ok().unwrap();
    assert_eq!(roots(&dropped), vec![Some((b("game"), b("guess")))]);
    assert!(!allows_batch(&dropped, &[transfer(1)], &auth()));
    // Reorder rules and choices together: roots and charging follow the rules.
    let mut reordered = rules();
    reordered.swap(0, 1);
    let out = check_auth(
        &reordered,
        &records(&reordered),
        &[guess(), transfer(3)],
        &[1, 0],
        &auth(),
        1,
        0,
    )
    .ok()
    .unwrap();
    assert_eq!(out[0].total, 3);
    assert_eq!(out[1].total, 0);
}

#[test]
fn lowering_retains_ordinary_roots_and_preserves_admin_recovery_eligibility() {
    let doc_rule = |scope| DocRule {
        scope,
        principals: Principals::All(vec![]),
        functions: Some(vec![b("transfer")]),
        args: None,
        not_after_ledger: None,
        cap: None,
        auth_root: Some(root("game", "guess")),
    };
    let d = Doc {
        signers: vec![],
        rules: vec![
            doc_rule(Scope::Contract(b("xlm"))),
            doc_rule(Scope::SelfAdmin),
        ],
        recovery: Some(Recovery {
            controller: b("controller"),
            zk: None,
        }),
    };
    let lowered = lower(&d, &b("account"));
    assert_eq!(
        roots(&lowered),
        vec![Some((b("game"), b("guess"))), None, None]
    );
    let scoped = Doc {
        signers: vec![],
        rules: vec![doc_rule(Scope::Contract(b("xlm")))],
        recovery: None,
    };
    let out = lower_scoped(&scoped, &b("account"), &[], 7).ok().unwrap();
    assert_eq!(roots(&out), vec![Some((b("game"), b("guess")))]);
    assert_eq!(out[0].generation, Some(7));
}

#[test]
fn changing_or_dropping_an_exact_root_is_not_certified_narrowing() {
    let expected = Some(root("game", "guess"));
    assert!(auth_root_narrows(&None, &None));
    assert!(auth_root_narrows(&expected, &None));
    assert!(auth_root_narrows(&Some(root("game", "guess")), &expected));
    assert!(!auth_root_narrows(&None, &expected));
    assert!(!auth_root_narrows(&Some(root("other", "guess")), &expected));
    assert!(!auth_root_narrows(&Some(root("game", "other")), &expected));
}
