//! The lowering of documents: what `lower`, `lower_scoped` and `excluded`
//! build, and, through `allows` and `check_auth`, the verdicts Perch's installed
//! rules give on the same calls (the probes of Perch's own harness, run on
//! OpenZeppelin's smart account in `soroban-env-host`).

mod common;

use common::*;
use rule_eval::{
    AMOUNT_ARG, ArgConstraint, Cond, Context, Doc, DocCap, DocRule, Functions, MAX_STRING_LEN,
    Pred, Principals, Recovery, Refusal, Rule, Scope, ScopeError, Signer, SignerDecl, Val,
    ZkFactor, allows, check_auth, empty_record, excluded, lower, lower_scoped, recovery_rule,
    u32_xdr,
};

const ACCOUNT: &str = "account";
const TOKEN: &str = "token";

fn ci() -> Signer {
    external("verifier", "ci-key")
}

fn ops() -> Signer {
    delegated("ops")
}

fn decls() -> Vec<SignerDecl> {
    vec![
        SignerDecl {
            id: b("ci"),
            signer: ci(),
        },
        SignerDecl {
            id: b("ops"),
            signer: ops(),
        },
    ]
}

/// A document rule on `TOKEN` that `ci` must sign.
fn doc_rule(functions: Option<&[&str]>) -> DocRule {
    DocRule {
        scope: Scope::Contract(b(TOKEN)),
        auth_root: None,
        principals: Principals::All(vec![b("ci")]),
        functions: functions.map(|fs| fs.iter().map(|f| b(f)).collect()),
        args: None,
        not_after_ledger: None,
        cap: None,
    }
}

fn doc(rules: Vec<DocRule>) -> Doc {
    Doc {
        signers: decls(),
        rules,
        recovery: None,
    }
}

fn with_args(r: DocRule, args: Vec<ArgConstraint>) -> DocRule {
    DocRule {
        args: Some(args),
        ..r
    }
}

fn capped_rule(r: DocRule) -> DocRule {
    DocRule {
        cap: Some(DocCap {
            limit: 10,
            period_ledgers: 1000,
        }),
        ..r
    }
}

fn arg(index: u32, pred: Pred) -> ArgConstraint {
    ArgConstraint { index, pred }
}

fn token_call(function: &str, args: Vec<Val>) -> Context {
    call(TOKEN, function, args)
}

fn transfer(amount: i128) -> Context {
    token_call(
        "transfer",
        vec![
            Val::Address(b("a")),
            Val::Address(b("b")),
            Val::I128(amount),
        ],
    )
}

/// Whether the rules accept `ctx`, chosen for rule 0, signed by `signers`,
/// at ledger `now`, from empty records.
fn accepted(rules: &[Rule], ctx: Context, signers: &[Signer], now: u32) -> bool {
    let records: Vec<_> = rules.iter().map(|_| empty_record()).collect();
    check_auth(rules, &records, &[ctx], &[0], signers, now, 0).is_ok()
}

fn refusal(rules: &[Rule], ctx: Context, signers: &[Signer], now: u32) -> Option<Refusal> {
    let records: Vec<_> = rules.iter().map(|_| empty_record()).collect();
    check_auth(rules, &records, &[ctx], &[0], signers, now, 0).err()
}

// ---------------------------------------------------------------------------
// What the lowering builds.

#[test]
fn a_rule_without_a_function_list_lowers_to_the_wildcard() {
    let rules = lower(&doc(vec![doc_rule(None)]), &b(ACCOUNT));
    assert_eq!(rules.len(), 1);
    assert!(functions_eq(&rules[0].functions, &any_except(&[])));
    assert_eq!(rules[0].contract, b(TOKEN));
    assert!(rules[0].conds.is_empty());
    assert!(rules[0].cap.is_none() && rules[0].valid_until.is_none());
    assert!(rules[0].generation.is_none());
}

#[test]
fn a_function_list_lowers_to_the_same_list() {
    let rules = lower(
        &doc(vec![doc_rule(Some(&["publish", "yank"]))]),
        &b(ACCOUNT),
    );
    assert!(functions_eq(
        &rules[0].functions,
        &only(&["publish", "yank"])
    ));
}

#[test]
fn a_self_admin_rule_lowers_to_the_account() {
    let r = DocRule {
        scope: Scope::SelfAdmin,
        ..doc_rule(None)
    };
    let rules = lower(&doc(vec![r]), &b(ACCOUNT));
    assert_eq!(rules[0].contract, b(ACCOUNT));
}

#[test]
fn principals_lower_to_their_signers_and_threshold() {
    let all = DocRule {
        principals: Principals::All(vec![b("ci"), b("ops")]),
        ..doc_rule(None)
    };
    let two_of = DocRule {
        principals: Principals::Threshold(vec![b("ops"), b("ci"), b("missing")], 1),
        ..doc_rule(None)
    };
    let rules = lower(&doc(vec![all, two_of]), &b(ACCOUNT));
    assert_eq!(rules[0].signers.len(), 2);
    assert!(ref_signer_eq(&rules[0].signers[0], &ci()));
    assert!(ref_signer_eq(&rules[0].signers[1], &ops()));
    assert_eq!(rules[0].threshold, 2);
    // An id no signer is declared under names none.
    assert_eq!(rules[1].signers.len(), 2);
    assert!(ref_signer_eq(&rules[1].signers[0], &ops()));
    assert_eq!(rules[1].threshold, 1);
}

#[test]
fn the_first_declaration_of_an_id_is_the_one_used() {
    let mut d = doc(vec![doc_rule(None)]);
    d.signers.push(SignerDecl {
        id: b("ci"),
        signer: delegated("other"),
    });
    let rules = lower(&d, &b(ACCOUNT));
    assert!(ref_signer_eq(&rules[0].signers[0], &ci()));
}

#[test]
fn not_after_ledger_lowers_to_the_ledger_before() {
    let r = DocRule {
        not_after_ledger: Some(600),
        ..doc_rule(Some(&["publish"]))
    };
    let rules = lower(&doc(vec![r]), &b(ACCOUNT));
    assert_eq!(rules[0].valid_until, Some(599));
}

#[test]
fn argument_predicates_lower_in_order() {
    let r = with_args(
        doc_rule(Some(&["f"])),
        vec![
            arg(0, Pred::IsSelf),
            arg(1, Pred::AddressEq(b("dest"))),
            arg(2, Pred::U32Eq(1000)),
            arg(3, Pred::StringPrefix(b("pkg_"))),
        ],
    );
    let rules = lower(&doc(vec![r]), &b(ACCOUNT));
    let want = [
        Cond::ArgEq(0, Val::Address(b(ACCOUNT))),
        Cond::ArgEq(1, Val::Address(b("dest"))),
        Cond::ArgEq(2, Val::Other(vec![0, 0, 0, 3, 0, 0, 3, 232])),
        Cond::ArgStrPrefix(3, b("pkg_")),
    ];
    assert_eq!(rules[0].conds.len(), want.len());
    for (c, w) in rules[0].conds.iter().zip(&want) {
        assert!(cond_eq(c, w));
    }
}

#[test]
fn u32_xdr_is_the_discriminant_then_the_value_big_endian() {
    assert_eq!(u32_xdr(0), vec![0, 0, 0, 3, 0, 0, 0, 0]);
    assert_eq!(u32_xdr(1000), vec![0, 0, 0, 3, 0, 0, 3, 232]);
    assert_eq!(
        u32_xdr(0x0102_0304),
        vec![0, 0, 0, 3, 0x01, 0x02, 0x03, 0x04]
    );
    assert_eq!(u32_xdr(u32::MAX), vec![0, 0, 0, 3, 255, 255, 255, 255]);
}

#[test]
fn string_in_drops_values_longer_than_256_bytes() {
    let long = vec![b'a'; MAX_STRING_LEN + 1];
    let edge = vec![b'e'; MAX_STRING_LEN];
    let r = with_args(
        doc_rule(Some(&["f"])),
        vec![arg(
            0,
            Pred::StringIn(vec![long.clone(), b("ok"), edge.clone()]),
        )],
    );
    let rules = lower(&doc(vec![r]), &b(ACCOUNT));
    assert!(cond_eq(
        &rules[0].conds[0],
        &Cond::ArgIn(0, vec![Val::String(b("ok")), Val::String(edge)])
    ));
}

#[test]
fn a_capped_rule_lowers_to_transfer_its_amount_and_its_cap() {
    let rules = lower(
        &doc(vec![
            capped_rule(doc_rule(Some(&["approve", "transfer"]))),
            capped_rule(doc_rule(None)),
            capped_rule(doc_rule(Some(&["approve"]))),
        ]),
        &b(ACCOUNT),
    );
    assert!(functions_eq(&rules[0].functions, &only(&["transfer"])));
    assert!(functions_eq(&rules[1].functions, &only(&["transfer"])));
    assert!(functions_eq(&rules[2].functions, &only(&[])));
    for r in &rules {
        assert_eq!(r.conds.len(), 1);
        assert!(cond_eq(
            &r.conds[0],
            &Cond::ArgI128AtMost(AMOUNT_ARG, i128::MAX)
        ));
        assert!(cap_eq(&r.cap, &Some(cap(10, 1000, AMOUNT_ARG))));
    }
}

#[test]
fn recovery_adds_the_recovery_rule_last() {
    let mut d = doc(vec![doc_rule(None)]);
    d.recovery = Some(Recovery {
        controller: b("controller"),
        zk: None,
    });
    let rules = lower(&d, &b(ACCOUNT));
    assert_eq!(rules.len(), 2);
    assert!(rule_eq(&rules[1], &recovery_rule(&b(ACCOUNT))));
    assert_eq!(rules[1].contract, b(ACCOUNT));
    assert!(functions_eq(&rules[1].functions, &only(&["apply_doc"])));
    assert!(rules[1].signers.is_empty() && rules[1].threshold == 0);
}

// ---------------------------------------------------------------------------
// The lowered rules on chain's calls: Perch's probes.

#[test]
fn a_capped_rule_listing_approve_authorizes_only_transfer() {
    let rules = lower(
        &doc(vec![capped_rule(doc_rule(Some(&["transfer", "approve"])))]),
        &b(ACCOUNT),
    );
    assert!(accepted(&rules, transfer(5), &[ci()], 500));
    let approve = token_call(
        "approve",
        vec![
            Val::Address(b("a")),
            Val::Address(b("s")),
            Val::I128(5),
            Val::Other(u32_xdr(1000)),
        ],
    );
    assert!(matches!(
        refusal(&rules, approve, &[ci()], 500),
        Some(Refusal::NotAllowed)
    ));
}

#[test]
fn a_capped_rule_without_functions_authorizes_only_transfer() {
    let rules = lower(&doc(vec![capped_rule(doc_rule(None))]), &b(ACCOUNT));
    assert!(accepted(&rules, transfer(5), &[ci()], 500));
    let burn = token_call("burn", vec![Val::Address(b("a")), Val::I128(5)]);
    assert!(!accepted(&rules, burn, &[ci()], 500));
}

#[test]
fn a_capped_transfer_needs_an_i128_amount() {
    let rules = lower(&doc(vec![capped_rule(doc_rule(None))]), &b(ACCOUNT));
    let no_amount = token_call(
        "transfer",
        vec![Val::Address(b("a")), Val::Address(b("b")), Val::U64(5)],
    );
    assert!(!allows(&rules, &no_amount, &[ci()]));
    assert!(matches!(
        refusal(&rules, no_amount, &[ci()], 500),
        Some(Refusal::NotAllowed)
    ));
}

#[test]
fn a_capped_rule_charges_up_to_its_limit() {
    let rules = lower(&doc(vec![capped_rule(doc_rule(None))]), &b(ACCOUNT));
    let records = vec![empty_record()];
    let after = check_auth(&rules, &records, &[transfer(10)], &[0], &[ci()], 500, 0)
        .ok()
        .unwrap();
    assert!(check_auth(&rules, &after, &[transfer(1)], &[0], &[ci()], 501, 0).is_err());
}

#[test]
fn an_extra_authenticated_signer_is_refused() {
    let rules = lower(&doc(vec![doc_rule(Some(&["transfer"]))]), &b(ACCOUNT));
    assert!(accepted(&rules, transfer(5), &[ci()], 500));
    assert!(matches!(
        refusal(
            &rules,
            transfer(5),
            &[ci(), external("verifier", "stranger")],
            500
        ),
        Some(Refusal::UnauthorizedSigner)
    ));
}

#[test]
fn not_after_ledger_600_authorizes_at_599_and_not_at_600() {
    let r = DocRule {
        not_after_ledger: Some(600),
        ..doc_rule(Some(&["publish"]))
    };
    let rules = lower(&doc(vec![r]), &b(ACCOUNT));
    let publish = || token_call("publish", vec![]);
    assert!(accepted(&rules, publish(), &[ci()], 599));
    assert!(matches!(
        refusal(&rules, publish(), &[ci()], 600),
        Some(Refusal::Expired)
    ));
}

#[test]
fn an_over_long_string_in_value_never_matches() {
    let long = vec![b'a'; 300];
    let r = with_args(
        doc_rule(Some(&["f"])),
        vec![arg(0, Pred::StringIn(vec![long.clone(), b("ok")]))],
    );
    let rules = lower(&doc(vec![r]), &b(ACCOUNT));
    assert!(accepted(
        &rules,
        token_call("f", vec![Val::String(b("ok"))]),
        &[ci()],
        500
    ));
    assert!(!accepted(
        &rules,
        token_call("f", vec![Val::String(long)]),
        &[ci()],
        500
    ));
}

#[test]
fn a_constraint_free_rule_allows_every_function() {
    let rules = lower(&doc(vec![doc_rule(None)]), &b(ACCOUNT));
    let anything = token_call("anything_at_all", vec![Val::Other(u32_xdr(42))]);
    assert!(accepted(&rules, anything, &[ci()], 500));
    assert!(!accepted(&rules, token_call("f", vec![]), &[], 500));
}

#[test]
fn string_prefix_reads_strings_not_symbols() {
    let r = with_args(
        doc_rule(Some(&["f"])),
        vec![arg(0, Pred::StringPrefix(b("pkg_")))],
    );
    let rules = lower(&doc(vec![r]), &b(ACCOUNT));
    let f = |v: Val| token_call("f", vec![v]);
    assert!(accepted(&rules, f(Val::String(b("pkg_a"))), &[ci()], 500));
    assert!(!accepted(&rules, f(Val::String(b("pk"))), &[ci()], 500));
    assert!(!accepted(&rules, f(Val::Symbol(b("pkg_a"))), &[ci()], 500));
}

#[test]
fn u32_eq_matches_the_u32_argument_and_nothing_else() {
    let r = with_args(doc_rule(Some(&["f"])), vec![arg(0, Pred::U32Eq(7))]);
    let rules = lower(&doc(vec![r]), &b(ACCOUNT));
    let f = |v: Val| token_call("f", vec![v]);
    assert!(allows(&rules, &f(Val::Other(u32_xdr(7))), &[ci()]));
    assert!(!allows(&rules, &f(Val::Other(u32_xdr(8))), &[ci()]));
    assert!(!allows(&rules, &f(Val::U64(7)), &[ci()]));
}

#[test]
fn the_recovery_rule_allows_any_apply_doc_on_the_account() {
    let mut d = doc(vec![]);
    d.recovery = Some(Recovery {
        controller: b("controller"),
        zk: None,
    });
    let rules = lower(&d, &b(ACCOUNT));
    let apply = call(ACCOUNT, "apply_doc", vec![Val::Bytes(b("target"))]);
    assert!(accepted(&rules, apply, &[], 500));
    assert!(!accepted(
        &rules,
        call(ACCOUNT, "execute", vec![]),
        &[],
        500
    ));
    assert!(!accepted(
        &rules,
        call(TOKEN, "apply_doc", vec![]),
        &[],
        500
    ));
}

// ---------------------------------------------------------------------------
// Scoped documents.

fn admin() -> Doc {
    let mut d = doc(vec![DocRule {
        scope: Scope::SelfAdmin,
        ..doc_rule(None)
    }]);
    d.recovery = Some(Recovery {
        controller: b("controller"),
        zk: Some(ZkFactor {
            adapter: b("adapter"),
            pool: b("pool"),
        }),
    });
    d
}

#[test]
fn the_excluded_set_is_the_account_and_the_recovery_contracts() {
    assert_eq!(
        excluded(&admin(), &b(ACCOUNT)),
        vec![b(ACCOUNT), b("controller"), b("adapter"), b("pool")]
    );
    let guardians_only = Doc {
        recovery: Some(Recovery {
            controller: b("controller"),
            zk: None,
        }),
        ..doc(vec![])
    };
    assert_eq!(
        excluded(&guardians_only, &b(ACCOUNT)),
        vec![b(ACCOUNT), b("controller")]
    );
    assert_eq!(excluded(&doc(vec![]), &b(ACCOUNT)), vec![b(ACCOUNT)]);
}

#[test]
fn a_scoped_document_is_stamped_with_the_generation() {
    let ex = excluded(&admin(), &b(ACCOUNT));
    let rules = lower_scoped(&doc(vec![doc_rule(None)]), &b(ACCOUNT), &ex, 7)
        .ok()
        .unwrap();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].generation, Some(7));
    let records = vec![empty_record()];
    let ok = check_auth(&rules, &records, &[transfer(1)], &[0], &[ci()], 500, 7);
    assert!(ok.is_ok());
    let stale = check_auth(&rules, &records, &[transfer(1)], &[0], &[ci()], 500, 8);
    assert!(matches!(stale, Err(Refusal::StaleGeneration)));
}

#[test]
fn a_scoped_document_naming_an_excluded_contract_is_refused() {
    let ex = excluded(&admin(), &b(ACCOUNT));
    for scope in [
        Scope::SelfAdmin,
        Scope::Contract(b(ACCOUNT)),
        Scope::Contract(b("controller")),
        Scope::Contract(b("adapter")),
        Scope::Contract(b("pool")),
    ] {
        let sd = doc(vec![
            doc_rule(None),
            DocRule {
                scope,
                ..doc_rule(None)
            },
        ]);
        assert!(matches!(
            lower_scoped(&sd, &b(ACCOUNT), &ex, 0),
            Err(ScopeError::ExcludedScope)
        ));
    }
}

#[test]
fn a_scoped_document_never_reaches_the_account_whatever_set_it_is_given() {
    let sd = doc(vec![DocRule {
        scope: Scope::Contract(b(ACCOUNT)),
        ..doc_rule(None)
    }]);
    assert!(matches!(
        lower_scoped(&sd, &b(ACCOUNT), &[], 0),
        Err(ScopeError::ExcludedScope)
    ));
}

#[test]
fn a_scoped_document_with_recovery_is_refused() {
    let mut sd = doc(vec![doc_rule(None)]);
    sd.recovery = Some(Recovery {
        controller: b("controller"),
        zk: None,
    });
    assert!(matches!(
        lower_scoped(&sd, &b(ACCOUNT), &[], 0),
        Err(ScopeError::RecoveryConfigured)
    ));
}

#[test]
fn scoped_rules_allow_nothing_on_the_excluded_set() {
    let ex = excluded(&admin(), &b(ACCOUNT));
    let rules = lower_scoped(&doc(vec![doc_rule(None)]), &b(ACCOUNT), &ex, 0)
        .ok()
        .unwrap();
    for contract in [ACCOUNT, "controller", "adapter", "pool"] {
        assert!(!allows(&rules, &call(contract, "f", vec![]), &[ci()]));
    }
    assert!(allows(&rules, &token_call("f", vec![]), &[ci()]));
}

#[test]
fn admin_rules_carry_no_generation_and_authorize_in_every_generation() {
    let rules = lower(&admin(), &b(ACCOUNT));
    assert!(rules.iter().all(|r| r.generation.is_none()));
    let records: Vec<_> = rules.iter().map(|_| empty_record()).collect();
    for generation in [0, 1, u64::MAX] {
        let admin_call = [call(ACCOUNT, "f", vec![])];
        assert!(check_auth(&rules, &records, &admin_call, &[0], &[ci()], 1, generation).is_ok());
        let apply = [call(ACCOUNT, "apply_doc", vec![])];
        assert!(check_auth(&rules, &records, &apply, &[1], &[], 1, generation).is_ok());
    }
}

#[test]
fn self_admin_wildcard_matches_any_function() {
    let rules = lower(&admin(), &b(ACCOUNT));
    assert!(functions_eq(
        &rules[0].functions,
        &Functions::AnyExcept(vec![])
    ));
}
