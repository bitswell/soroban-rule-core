//! The stateful check `authorize` and the cap steps: each refusal and its
//! precedence, charges accumulating across a batch, a refusal discarding a
//! batch's charges, windows rolling, soundness against `allows_all`, what each
//! cap step builds and refuses, and, over small universes, agreement with a
//! plain Rust reading, window safety and trace inclusion.

mod common;

use common::*;
use rule_eval::{
    AttenuationError, Cap, CapError, Context, Refusal, Rule, Signer, SpendEntry, SpendRecord, Val,
    add_cap, add_cond, allows, allows_all, authorize, cap_valid, check_spend, drop_rule,
    empty_record, lengthen_cap_period, lower_cap_limit, raise_threshold, remove_functions,
    remove_signers, rule_allows,
};

/// A record as its entries and total.
type Rec = (Vec<(u32, i128)>, i128);

fn rec_of(r: &SpendRecord) -> Rec {
    (
        r.history.iter().map(|e| (e.ledger, e.amount)).collect(),
        r.total,
    )
}

fn record_of(r: &Rec) -> SpendRecord {
    SpendRecord {
        history: r
            .0
            .iter()
            .map(|&(ledger, amount)| SpendEntry { ledger, amount })
            .collect(),
        total: r.1,
    }
}

fn empty(n: usize) -> Vec<SpendRecord> {
    (0..n).map(|_| empty_record()).collect()
}

fn cap_error_name(e: &CapError) -> &'static str {
    match e {
        CapError::NegativeAmount => "negative_amount",
        CapError::LedgerBeforeNewest => "ledger_before_newest",
        CapError::Overflow => "overflow",
        CapError::LimitExceeded => "limit_exceeded",
        CapError::HistoryFull => "history_full",
    }
}

fn refusal_name(r: &Refusal) -> String {
    match r {
        Refusal::ChoicesMismatch => "choices_mismatch".into(),
        Refusal::RecordsMismatch => "records_mismatch".into(),
        Refusal::NoSuchRule => "no_such_rule".into(),
        Refusal::NotAllowed => "not_allowed".into(),
        Refusal::NoAmount => "no_amount".into(),
        Refusal::Cap(e) => format!("cap {}", cap_error_name(e)),
    }
}

type Outcome = Result<Vec<Rec>, String>;

fn outcome(
    rules: &[Rule],
    records: &[SpendRecord],
    contexts: &[Context],
    choices: &[u32],
    auth: &[Signer],
    now: u32,
) -> Outcome {
    match authorize(rules, records, contexts, choices, auth, now) {
        Ok(out) => Ok(out.iter().map(rec_of).collect()),
        Err(e) => Err(refusal_name(&e)),
    }
}

/// A plain reading of `authorize`: the length checks, then every chosen rule
/// allowing its context, then each charge in context order against the
/// record the charges before it left.
fn reference(
    rules: &[Rule],
    records: &[SpendRecord],
    contexts: &[Context],
    choices: &[u32],
    auth: &[Signer],
    now: u32,
) -> Outcome {
    if choices.len() != contexts.len() {
        return Err("choices_mismatch".into());
    }
    if records.len() != rules.len() {
        return Err("records_mismatch".into());
    }
    for (ctx, &j) in contexts.iter().zip(choices) {
        match rules.get(j as usize) {
            None => return Err("no_such_rule".into()),
            Some(r) if !ref_rule_allows(r, ctx, auth) => return Err("not_allowed".into()),
            Some(_) => {}
        }
    }
    let mut out: Vec<Rec> = records.iter().map(rec_of).collect();
    for (ctx, &j) in contexts.iter().zip(choices) {
        let j = j as usize;
        let Some(c) = &rules[j].cap else { continue };
        let amount = match ctx {
            Context::Call { args, .. } => match args.get(c.amount_arg as usize) {
                Some(Val::I128(v)) => *v,
                _ => return Err("no_amount".into()),
            },
            Context::Create { .. } => return Err("no_amount".into()),
        };
        match check_spend(&record_of(&out[j]), c.limit, c.period, now, amount) {
            Ok(next) => out[j] = rec_of(&next),
            Err(e) => return Err(format!("cap {}", cap_error_name(&e))),
        }
    }
    Ok(out)
}

fn transfer(amount: i128) -> Context {
    call(
        "token",
        "transfer",
        vec![
            Val::Address(b("from")),
            Val::Address(b("to")),
            Val::I128(amount),
        ],
    )
}

/// A transfer rule capped at 100 per 10 ledgers next to an uncapped vault
/// rule that needs alice.
fn sample() -> Vec<Rule> {
    vec![
        capped(rule("token", &["transfer"], Vec::new()), cap(100, 10, 2)),
        signed_rule(
            "vault",
            &["deposit"],
            Vec::new(),
            vec![delegated("alice")],
            1,
        ),
    ]
}

#[test]
fn choices_and_records_must_match_their_lists() {
    let rs = sample();
    let batch = [transfer(1)];
    assert_eq!(
        outcome(&rs, &empty(2), &batch, &[], &[], 1),
        Err("choices_mismatch".into())
    );
    assert_eq!(
        outcome(&rs, &empty(2), &batch, &[0, 0], &[], 1),
        Err("choices_mismatch".into())
    );
    assert_eq!(
        outcome(&rs, &empty(1), &batch, &[0], &[], 1),
        Err("records_mismatch".into())
    );
    assert_eq!(
        outcome(&rs, &empty(3), &batch, &[0], &[], 1),
        Err("records_mismatch".into())
    );
    // The choice length is checked first.
    assert_eq!(
        outcome(&rs, &empty(3), &batch, &[], &[], 1),
        Err("choices_mismatch".into())
    );
}

#[test]
fn a_chosen_rule_must_exist_and_allow_its_context() {
    let rs = sample();
    let deposit = call("vault", "deposit", Vec::new());
    assert_eq!(
        outcome(&rs, &empty(2), &[transfer(1)], &[2], &[], 1),
        Err("no_such_rule".into())
    );
    assert_eq!(
        outcome(&rs, &empty(2), &[transfer(1)], &[u32::MAX], &[], 1),
        Err("no_such_rule".into())
    );
    // The vault rule exists but allows no transfer, and needs alice.
    assert_eq!(
        outcome(&rs, &empty(2), &[transfer(1)], &[1], &[], 1),
        Err("not_allowed".into())
    );
    assert_eq!(
        outcome(&rs, &empty(2), &[deposit], &[1], &[], 1),
        Err("not_allowed".into())
    );
    let deposit = call("vault", "deposit", Vec::new());
    assert!(outcome(&rs, &empty(2), &[deposit], &[1], &[delegated("alice")], 1).is_ok());
    // Some rule allows the transfer, but not the one chosen for it.
    assert!(allows(&rs, &transfer(1), &[]));
}

#[test]
fn every_choice_is_checked_before_any_charge() {
    let rs = sample();
    // The first context would exceed its cap; the second chooses a rule that
    // does not allow it. The choice is refused first.
    let batch = [transfer(101), call("vault", "deposit", Vec::new())];
    assert_eq!(
        outcome(&rs, &empty(2), &batch, &[0, 1], &[], 1),
        Err("not_allowed".into())
    );
    assert_eq!(
        outcome(&rs, &empty(2), &batch, &[0, 1], &[delegated("alice")], 1),
        Err("cap limit_exceeded".into())
    );
}

#[test]
fn a_capped_rule_needs_an_i128_amount() {
    let rs = vec![capped(
        rule("token", &["transfer"], Vec::new()),
        cap(100, 10, 2),
    )];
    let missing = call("token", "transfer", vec![Val::Address(b("from"))]);
    let wrong = call(
        "token",
        "transfer",
        vec![Val::Address(b("from")), Val::Address(b("to")), Val::U64(5)],
    );
    for ctx in [missing, wrong] {
        assert_eq!(
            outcome(&rs, &empty(1), &[ctx], &[0], &[], 1),
            Err("no_amount".into())
        );
    }
    // An uncapped rule reads no amount.
    let open = vec![rule("token", &["transfer"], Vec::new())];
    let missing = call("token", "transfer", Vec::new());
    assert_eq!(
        outcome(&open, &empty(1), &[missing], &[0], &[], 1),
        Ok(vec![(Vec::new(), 0)])
    );
}

#[test]
fn a_cap_refusal_is_passed_on() {
    let rs = sample();
    let auth = [delegated("alice")];
    assert_eq!(
        outcome(&rs, &empty(2), &[transfer(-1)], &[0], &auth, 1),
        Err("cap negative_amount".into())
    );
    assert_eq!(
        outcome(&rs, &empty(2), &[transfer(101)], &[0], &auth, 1),
        Err("cap limit_exceeded".into())
    );
    let records = vec![record_of(&(vec![(5, 10)], 10)), empty_record()];
    assert_eq!(
        outcome(&rs, &records, &[transfer(1)], &[0], &auth, 4),
        Err("cap ledger_before_newest".into())
    );
}

#[test]
fn two_contexts_charging_one_rule_accumulate() {
    let rs = sample();
    let batch = [transfer(60), transfer(40)];
    assert_eq!(
        outcome(&rs, &empty(2), &batch, &[0, 0], &[], 3),
        Ok(vec![(vec![(3, 60), (3, 40)], 100), (Vec::new(), 0)])
    );
    let batch = [transfer(60), transfer(41)];
    assert_eq!(
        outcome(&rs, &empty(2), &batch, &[0, 0], &[], 3),
        Err("cap limit_exceeded".into())
    );
}

#[test]
fn rules_with_their_own_caps_keep_their_own_records() {
    let rs = vec![
        capped(rule("token", &["transfer"], Vec::new()), cap(100, 10, 2)),
        capped(rule("token", &["transfer"], Vec::new()), cap(50, 10, 2)),
    ];
    let batch = [transfer(100), transfer(50)];
    assert_eq!(
        outcome(&rs, &empty(2), &batch, &[0, 1], &[], 1),
        Ok(vec![(vec![(1, 100)], 100), (vec![(1, 50)], 50)])
    );
}

#[test]
fn a_refused_authorization_discards_the_charges_before_it() {
    let rs = sample();
    let records = empty(2);
    let batch = [transfer(60), transfer(50)];
    assert_eq!(
        outcome(&rs, &records, &batch, &[0, 0], &[], 1),
        Err("cap limit_exceeded".into())
    );
    // The records passed in are unchanged, and the first charge alone passes.
    assert!(records.iter().all(|r| r.history.is_empty() && r.total == 0));
    assert_eq!(
        outcome(&rs, &records, &[transfer(60)], &[0], &[], 1),
        Ok(vec![(vec![(1, 60)], 60), (Vec::new(), 0)])
    );
}

#[test]
fn the_window_rolls() {
    let rs = vec![capped(
        rule("token", &["transfer"], Vec::new()),
        cap(100, 10, 2),
    )];
    let mut records = empty(1);
    for (now, amount, accepted) in [
        (1, 100, true),
        (5, 1, false),
        (10, 1, false),
        (11, 100, true),
        (20, 1, false),
        (21, 50, true),
        (22, 50, true),
        (22, 1, false),
    ] {
        match authorize(&rs, &records, &[transfer(amount)], &[0], &[], now) {
            Ok(out) => {
                assert!(accepted, "ledger {now} amount {amount}");
                records = out;
            }
            Err(e) => assert!(
                !accepted && matches!(e, Refusal::Cap(CapError::LimitExceeded)),
                "ledger {now} amount {amount}"
            ),
        }
    }
    assert_eq!(rec_of(&records[0]), (vec![(21, 50), (22, 50)], 100));
}

#[test]
fn an_empty_batch_is_authorized_and_changes_nothing() {
    let rs = sample();
    let records = vec![record_of(&(vec![(5, 10)], 10)), empty_record()];
    assert_eq!(
        outcome(&rs, &records, &[], &[], &[], 0),
        Ok(vec![(vec![(5, 10)], 10), (Vec::new(), 0)])
    );
}

// ---------------------------------------------------------------------------
// The cap steps.

fn is_err(r: &Result<Vec<Rule>, AttenuationError>, name: &str) -> bool {
    let got = match r {
        Ok(_) => "ok",
        Err(AttenuationError::NoSuchRule) => "no_such_rule",
        Err(AttenuationError::ThresholdLowered) => "threshold_lowered",
        Err(AttenuationError::CapPresent) => "cap_present",
        Err(AttenuationError::NoCap) => "no_cap",
        Err(AttenuationError::InvalidCap) => "invalid_cap",
        Err(AttenuationError::LimitRaised) => "limit_raised",
        Err(AttenuationError::PeriodShortened) => "period_shortened",
    };
    got == name
}

#[test]
fn caps_are_valid_with_a_positive_limit_and_a_nonzero_period() {
    assert!(cap_valid(&cap(1, 1, 0)));
    assert!(cap_valid(&cap(i128::MAX, u32::MAX, u32::MAX)));
    assert!(!cap_valid(&cap(0, 1, 0)));
    assert!(!cap_valid(&cap(-1, 1, 0)));
    assert!(!cap_valid(&cap(1, 0, 0)));
}

#[test]
fn add_cap_caps_that_rule_only_and_refuses_a_capped_rule_or_an_invalid_cap() {
    let rs = sample();
    let got = add_cap(&rs, 1, &cap(5, 3, 0)).ok().unwrap();
    let mut expected: Vec<Rule> = rs.iter().map(copy_rule).collect();
    expected[1].cap = Some(cap(5, 3, 0));
    assert!(rules_eq(&got, &expected));
    assert!(is_err(&add_cap(&rs, 0, &cap(5, 3, 0)), "cap_present"));
    assert!(is_err(&add_cap(&rs, 1, &cap(0, 3, 0)), "invalid_cap"));
    assert!(is_err(&add_cap(&rs, 1, &cap(5, 0, 0)), "invalid_cap"));
    assert!(is_err(&add_cap(&rs, 2, &cap(5, 3, 0)), "no_such_rule"));
    // The index is checked first, then the rule, then the cap.
    assert!(is_err(&add_cap(&rs, 2, &cap(0, 0, 0)), "no_such_rule"));
    assert!(is_err(&add_cap(&rs, 0, &cap(0, 0, 0)), "cap_present"));
}

#[test]
fn lower_cap_limit_lowers_that_limit_only() {
    let rs = sample();
    for limit in [100, 99, 1] {
        let got = lower_cap_limit(&rs, 0, limit).ok().unwrap();
        let mut expected: Vec<Rule> = rs.iter().map(copy_rule).collect();
        expected[0].cap = Some(cap(limit, 10, 2));
        assert!(rules_eq(&got, &expected), "limit {limit}");
    }
    assert!(is_err(&lower_cap_limit(&rs, 0, 101), "limit_raised"));
    assert!(is_err(&lower_cap_limit(&rs, 0, 0), "invalid_cap"));
    assert!(is_err(&lower_cap_limit(&rs, 0, -5), "invalid_cap"));
    assert!(is_err(&lower_cap_limit(&rs, 1, 5), "no_cap"));
    assert!(is_err(&lower_cap_limit(&rs, 2, 5), "no_such_rule"));
    assert!(is_err(&lower_cap_limit(&rs, u32::MAX, 5), "no_such_rule"));
}

#[test]
fn lengthen_cap_period_lengthens_that_period_only() {
    let rs = sample();
    for period in [10, 11, u32::MAX] {
        let got = lengthen_cap_period(&rs, 0, period).ok().unwrap();
        let mut expected: Vec<Rule> = rs.iter().map(copy_rule).collect();
        expected[0].cap = Some(cap(100, period, 2));
        assert!(rules_eq(&got, &expected), "period {period}");
    }
    assert!(is_err(&lengthen_cap_period(&rs, 0, 9), "period_shortened"));
    assert!(is_err(&lengthen_cap_period(&rs, 0, 0), "period_shortened"));
    assert!(is_err(&lengthen_cap_period(&rs, 1, 20), "no_cap"));
    assert!(is_err(&lengthen_cap_period(&rs, 2, 20), "no_such_rule"));
}

#[test]
fn the_other_steps_keep_each_rule_cap() {
    let rs = sample();
    let after: Vec<Vec<Rule>> = vec![
        drop_rule(&rs, 1).ok().unwrap(),
        add_cond(&rs, 0, &rule_eval::Cond::ArgI128AtMost(2, 5))
            .ok()
            .unwrap(),
        remove_functions(&rs, 0, &[b("approve")]).ok().unwrap(),
        remove_signers(&rs, 0, &[delegated("bob")]).ok().unwrap(),
        raise_threshold(&rs, 0, 0).ok().unwrap(),
    ];
    for got in &after {
        assert!(cap_eq(&got[0].cap, &Some(cap(100, 10, 2))));
    }
}

#[test]
fn cap_steps_leave_every_verdict_as_it_was() {
    let rs = sample();
    let contexts = contexts();
    let stepped = [
        add_cap(&rs, 1, &cap(5, 3, 0)).ok().unwrap(),
        lower_cap_limit(&rs, 0, 1).ok().unwrap(),
        lengthen_cap_period(&rs, 0, 1000).ok().unwrap(),
    ];
    for got in &stepped {
        for auth in authenticated_lists() {
            for c in contexts.iter().chain(&[transfer(5)]) {
                assert_eq!(allows(got, c, &auth), allows(&rs, c, &auth));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Small universes.

fn rule_universe() -> Vec<Rule> {
    vec![
        rule("token", &["transfer"], Vec::new()),
        capped(rule("token", &["transfer"], Vec::new()), cap(10, 5, 2)),
        capped(rule("token", &["transfer"], Vec::new()), cap(10, 5, 0)),
        capped(
            signed_rule(
                "token",
                &["transfer", "approve"],
                Vec::new(),
                vec![delegated("alice")],
                1,
            ),
            cap(7, 3, 2),
        ),
        signed_rule(
            "vault",
            &["deposit"],
            Vec::new(),
            vec![delegated("alice")],
            1,
        ),
    ]
}

fn context_universe() -> Vec<Context> {
    let mut out: Vec<Context> = [0, 3, 6, 11, -1].into_iter().map(transfer).collect();
    out.push(call(
        "token",
        "transfer",
        vec![Val::Address(b("from")), Val::Address(b("to")), Val::U64(3)],
    ));
    out.push(call(
        "token",
        "approve",
        vec![Val::I128(2), Val::Address(b("to")), Val::I128(4)],
    ));
    out.push(call("vault", "deposit", vec![Val::I128(1)]));
    out.push(create("token"));
    out
}

fn rule_set_universe() -> Vec<Vec<Rule>> {
    let n = rule_universe().len();
    let mut out = vec![Vec::new()];
    for x in 0..n {
        out.push(vec![copy_rule(&rule_universe()[x])]);
        for y in 0..n {
            out.push(vec![
                copy_rule(&rule_universe()[x]),
                copy_rule(&rule_universe()[y]),
            ]);
        }
    }
    out
}

fn batch_universe() -> Vec<(Vec<Context>, Vec<u32>)> {
    let ctxs = context_universe();
    let mut out = vec![(Vec::new(), Vec::new()), (Vec::new(), vec![0])];
    for x in &ctxs {
        for j in 0..3 {
            out.push((vec![copy_context(x)], vec![j]));
        }
        out.push((vec![copy_context(x)], Vec::new()));
    }
    for x in ctxs.iter().step_by(2) {
        for y in ctxs.iter().step_by(3) {
            for (j, k) in [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0)] {
                out.push((vec![copy_context(x), copy_context(y)], vec![j, k]));
            }
        }
    }
    out
}

/// `authorize` agrees with the plain reading on every rule set of up to two
/// rules from a universe of capped and uncapped rules, every batch of up to
/// two contexts with its choices, two authenticated lists and two ledgers,
/// from empty records and from records already holding a spend; and an
/// accepted authorization's batch is allowed by `allows_all`.
#[test]
fn authorize_agrees_with_the_reference_reading() {
    let auths = [Vec::new(), vec![delegated("alice")]];
    let mut checked = 0usize;
    let mut accepted = 0usize;
    for rs in rule_set_universe() {
        let starts = [
            empty(rs.len()),
            (0..rs.len())
                .map(|_| record_of(&(vec![(2, 5)], 5)))
                .collect::<Vec<_>>(),
        ];
        for records in &starts {
            for (batch, choices) in batch_universe() {
                for auth in &auths {
                    for now in [1, 7] {
                        let got = outcome(&rs, records, &batch, &choices, auth, now);
                        let expected = reference(&rs, records, &batch, &choices, auth, now);
                        assert_eq!(
                            got, expected,
                            "case {checked}: choices {choices:?} ledger {now}"
                        );
                        if got.is_ok() {
                            assert!(allows_all(&rs, &batch, auth));
                            for (c, &j) in batch.iter().zip(&choices) {
                                assert!(rule_allows(&rs[j as usize], c, auth));
                            }
                            accepted += 1;
                        }
                        checked += 1;
                    }
                }
            }
        }
    }
    assert_eq!(checked, 28_024);
    assert!(accepted > 2_000);
}

/// One authorization of a run: a batch, its choices and its ledger.
type Call = (Vec<Context>, Vec<u32>, u32);

fn call_pool() -> Vec<Call> {
    let mut out = Vec::new();
    for (now, a) in [(1, 6), (2, 5), (4, 4), (6, 6), (7, 3), (9, 10), (9, 1)] {
        out.push((vec![transfer(a)], vec![0], now));
        out.push((vec![transfer(a)], vec![1], now));
        out.push((vec![transfer(a), transfer(1)], vec![0, 1], now));
        out.push((vec![transfer(a), transfer(a)], vec![1, 1], now));
    }
    out
}

/// Every run of up to three authorizations from `pool`, applied from empty
/// records: the outcome of each authorization, the records after it (the same
/// after a refusal), and whether every one was accepted.
fn run(rs: &[Rule], calls: &[&Call]) -> (Vec<Outcome>, Vec<SpendRecord>, bool) {
    let mut records = empty(rs.len());
    let mut outcomes = Vec::new();
    let mut all = true;
    for (batch, choices, now) in calls {
        match authorize(rs, &records, batch, choices, &[], *now) {
            Ok(out) => {
                outcomes.push(Ok(out.iter().map(rec_of).collect()));
                records = out;
            }
            Err(e) => {
                outcomes.push(Err(refusal_name(&e)));
                all = false;
            }
        }
    }
    (outcomes, records, all)
}

fn sequences(pool: &[Call]) -> Vec<Vec<&Call>> {
    let mut out = vec![Vec::new()];
    for x in pool {
        out.push(vec![x]);
        for y in pool {
            out.push(vec![x, y]);
            for z in pool.iter().step_by(3) {
                out.push(vec![x, y, z]);
            }
        }
    }
    out
}

/// The accepted spends charged to rule `j` over a run, as (ledger, amount).
fn charged(rs: &[Rule], calls: &[&Call], j: usize) -> Vec<(u32, i128)> {
    let mut records = empty(rs.len());
    let mut out = Vec::new();
    for (batch, choices, now) in calls {
        if let Ok(next) = authorize(rs, &records, batch, choices, &[], *now) {
            records = next;
            for (c, &k) in batch.iter().zip(choices) {
                if k as usize == j
                    && let Context::Call { args, .. } = c
                    && let Some(Val::I128(v)) = args.get(2)
                {
                    out.push((*now, *v));
                }
            }
        }
    }
    out
}

/// Over every run of up to three authorizations from a pool of batches
/// charging one or two capped rules, each step agrees with the plain reading,
/// every window of `period` ledgers from ledger 1 on holds accepted spends of
/// at most the limit, and each stored record is the accepted spends in the
/// window at its last spend, with their sum as total.
#[test]
fn every_short_run_stays_within_every_window() {
    let rs = vec![
        capped(rule("token", &["transfer"], Vec::new()), cap(10, 5, 2)),
        capped(rule("token", &["transfer"], Vec::new()), cap(7, 3, 2)),
    ];
    let pool = call_pool();
    let mut checked = 0usize;
    for calls in sequences(&pool) {
        let mut records = empty(rs.len());
        for (batch, choices, now) in &calls {
            let got = outcome(&rs, &records, batch, choices, &[], *now);
            let expected = reference(&rs, &records, batch, choices, &[], *now);
            assert_eq!(got, expected);
            if let Ok(next) = authorize(&rs, &records, batch, choices, &[], *now) {
                records = next;
            }
        }
        for (j, r) in rs.iter().enumerate() {
            let c = r.cap.as_ref().unwrap();
            let spends = charged(&rs, &calls, j);
            for s in 1..12u32 {
                let sum: i128 = spends
                    .iter()
                    .filter(|(l, _)| s <= *l && *l < s + c.period)
                    .map(|(_, a)| a)
                    .sum();
                assert!(sum <= c.limit, "run {checked} rule {j} window {s}");
            }
            let stored = rec_of(&records[j]);
            assert_eq!(stored.1, stored.0.iter().map(|(_, a)| a).sum::<i128>());
            if let Some(&(last, _)) = spends.iter().rev().find(|(_, a)| *a > 0) {
                let window: Vec<(u32, i128)> = spends
                    .iter()
                    .filter(|(l, a)| *a > 0 && last.saturating_sub(c.period) < *l && *l <= last)
                    .copied()
                    .collect();
                assert_eq!(stored.0, window, "run {checked} rule {j}");
            }
        }
        checked += 1;
    }
    assert_eq!(checked, 8_653);
}

/// Whether every run from `pool` that `narrow` accepts in full from its empty
/// records, `wide` accepts in full from its own, with each choice `j`
/// renumbered to `f(j)`.
fn trace_included(narrow: &[Rule], wide: &[Rule], f: impl Fn(u32) -> u32, pool: &[Call]) -> bool {
    sequences(pool).iter().all(|calls| {
        if !run(narrow, calls).2 {
            return true;
        }
        let renumbered: Vec<Call> = calls
            .iter()
            .map(|(batch, choices, now)| {
                (
                    batch.iter().map(copy_context).collect(),
                    choices.iter().map(|&j| f(j)).collect(),
                    *now,
                )
            })
            .collect();
        let refs: Vec<&Call> = renumbered.iter().collect();
        run(wide, &refs).2
    })
}

/// Every cap step, and `drop_rule` with its renumbering, accepts only runs the
/// rule set before it accepts, each from its own empty records; so does a
/// chain of a cap step and a drop.
#[test]
fn every_step_is_trace_inclusion() {
    let root = vec![
        rule("token", &["transfer"], Vec::new()),
        capped(rule("token", &["transfer"], Vec::new()), cap(10, 5, 2)),
        capped(rule("token", &["transfer"], Vec::new()), cap(20, 2, 2)),
    ];
    let mut pool = call_pool();
    for (now, a) in [(1, 6), (3, 9), (8, 12)] {
        pool.push((vec![transfer(a)], vec![2], now));
        pool.push((vec![transfer(a), transfer(1)], vec![2, 1], now));
    }
    let id = |j: u32| j;
    let cases: Vec<(String, Vec<Rule>)> = vec![
        (
            "add_cap 0".into(),
            add_cap(&root, 0, &cap(5, 4, 2)).ok().unwrap(),
        ),
        (
            "lower_cap_limit 1".into(),
            lower_cap_limit(&root, 1, 6).ok().unwrap(),
        ),
        (
            "lower_cap_limit 2".into(),
            lower_cap_limit(&root, 2, 1).ok().unwrap(),
        ),
        (
            "lengthen_cap_period 1".into(),
            lengthen_cap_period(&root, 1, 9).ok().unwrap(),
        ),
        (
            "lengthen_cap_period 2".into(),
            lengthen_cap_period(&root, 2, 3).ok().unwrap(),
        ),
    ];
    for (name, narrow) in &cases {
        assert!(trace_included(narrow, &root, id, &pool), "{name}");
    }
    for i in 0..3u32 {
        let narrow = drop_rule(&root, i).ok().unwrap();
        let f = |j: u32| if j < i { j } else { j + 1 };
        assert!(trace_included(&narrow, &root, f, &pool), "drop_rule {i}");
    }
    // A chain: lower rule 1's limit, then drop rule 0.
    let lowered = lower_cap_limit(&root, 1, 4).ok().unwrap();
    let chain = drop_rule(&lowered, 0).ok().unwrap();
    assert!(trace_included(&chain, &root, |j| j + 1, &pool));
    // Raising a limit is not a step, and is not trace inclusion.
    let mut raised: Vec<Rule> = root.iter().map(copy_rule).collect();
    raised[1].cap = Some(cap(11, 5, 2));
    assert!(!trace_included(&raised, &root, id, &pool));
}

#[test]
fn caps_hold_across_contexts_that_choose_different_rules() {
    // Two rules allow the same transfer; each choice charges its own rule.
    let rs = vec![
        capped(rule("token", &["transfer"], Vec::new()), cap(10, 5, 2)),
        capped(rule("token", &["transfer"], Vec::new()), cap(10, 5, 2)),
    ];
    let first = authorize(&rs, &empty(2), &[transfer(10)], &[0], &[], 1)
        .ok()
        .unwrap();
    assert!(matches!(
        authorize(&rs, &first, &[transfer(1)], &[0], &[], 2),
        Err(Refusal::Cap(CapError::LimitExceeded))
    ));
    let second = authorize(&rs, &first, &[transfer(10)], &[1], &[], 2)
        .ok()
        .unwrap();
    assert_eq!(rec_of(&second[0]), (vec![(1, 10)], 10));
    assert_eq!(rec_of(&second[1]), (vec![(2, 10)], 10));
}

#[test]
fn a_rule_without_a_cap_keeps_its_record() {
    let rs = sample();
    let records = vec![empty_record(), record_of(&(vec![(3, 7)], 7))];
    let deposit = call("vault", "deposit", Vec::new());
    let out = authorize(&rs, &records, &[deposit], &[1], &[delegated("alice")], 9)
        .ok()
        .unwrap();
    assert_eq!(rec_of(&out[1]), (vec![(3, 7)], 7));
}

#[test]
fn a_cap_reads_only_its_own_amount_argument() {
    let rs = vec![capped(
        rule("token", &["approve"], Vec::new()),
        cap(10, 5, 0),
    )];
    let c = call(
        "token",
        "approve",
        vec![Val::I128(4), Val::Address(b("to")), Val::I128(1000)],
    );
    assert_eq!(
        outcome(&rs, &empty(1), &[c], &[0], &[], 1),
        Ok(vec![(vec![(1, 4)], 4)])
    );
    let unused: Cap = cap(1, 1, 0);
    assert!(cap_valid(&unused));
}
