mod common;
use common::*;
use rule_eval::{Refusal, authorize};

#[test]
fn selected_rules_authentication_caps_atomic_refusal_and_lifetime() {
    let compiled = compiled();
    let rules = compiled.rules();
    let mut ledger = records();
    let auth = [signer(1)];
    assert!(matches!(
        authorize(rules, &ledger, &[guess(4)], &[0], &[], 1, 7),
        Err(Refusal::NotAllowed)
    ));
    // A winning game still requires the guesser's auth, and spends no transfer cap.
    ledger = authorize(rules, &ledger, &[guess(4)], &[0], &auth, 1, 7)
        .ok()
        .unwrap();
    assert_eq!(snapshot(&ledger), vec![(0, vec![]), (0, vec![])]);
    ledger = authorize(
        rules,
        &ledger,
        &[guess(4), transfer(40)],
        &[0, 1],
        &auth,
        1,
        7,
    )
    .ok()
    .unwrap();
    assert_eq!(ledger[1].total, 40);
    let before = snapshot(&ledger);
    // First transfer could succeed alone, second makes the batch overdraw.
    let refused = authorize(
        rules,
        &ledger,
        &[guess(4), transfer(30), transfer(40)],
        &[0, 1, 1],
        &auth,
        2,
        7,
    );
    assert!(matches!(refused, Err(Refusal::Cap(_))));
    // Account simulation commits only a returned success; errors return no records.
    if let Ok(next) = refused {
        ledger = next;
    }
    assert_eq!(snapshot(&ledger), before);
    ledger = authorize(
        rules,
        &ledger,
        &[guess(4), transfer(60)],
        &[0, 1],
        &auth,
        2,
        7,
    )
    .ok()
    .unwrap();
    assert_eq!(ledger[1].total, 100);
    assert!(matches!(
        authorize(
            rules,
            &ledger,
            &[guess(4), transfer(1)],
            &[0, 1],
            &auth,
            3,
            7
        ),
        Err(Refusal::Cap(_))
    ));
    assert!(matches!(
        authorize(rules, &ledger, &[guess(4)], &[1], &auth, 3, 7),
        Err(Refusal::NotAllowed)
    ));
    assert!(matches!(
        authorize(rules, &ledger, &[guess(4)], &[], &auth, 3, 7),
        Err(Refusal::ChoicesMismatch)
    ));
    assert!(matches!(
        authorize(rules, &ledger, &[guess(4)], &[0], &auth, 1001, 7),
        Err(Refusal::Expired)
    ));
    assert!(matches!(
        authorize(rules, &ledger, &[guess(4)], &[0], &auth, 3, 8),
        Err(Refusal::StaleGeneration)
    ));
    // The eligibility layer intentionally omits state; no Cedar/account conflation.
    let pair = compiled.compare(&[guess(4)], 0, &auth[0]).unwrap();
    assert!(pair.cedar && pair.rule_core);
    let renewed = authorize(
        rules,
        &ledger,
        &[guess(4), transfer(100)],
        &[0, 1],
        &auth,
        12,
        7,
    )
    .ok()
    .unwrap();
    assert_eq!(renewed[1].total, 100);
    assert_eq!(renewed[1].history.len(), 1);
}

#[test]
fn exact_entry_root_cannot_be_borrowed_and_local_screening_is_insufficient() {
    let compiled = compiled();
    let rules = compiled.rules();
    let records = records();
    let auth = [signer(1)];
    assert!(authorize(rules, &records, &[guess(4)], &[0], &auth, 1, 7).is_ok());
    // A different, already-authorized entry has no effect on this direct entry.
    assert!(matches!(
        authorize(rules, &records, &[transfer(1)], &[1], &auth, 1, 7),
        Err(Refusal::NotAllowed)
    ));
    for root in [
        call(5, "guess", vec![]),
        call(3, "other", vec![]),
        transfer(1),
    ] {
        let entry = [root, transfer(1)];
        assert!(matches!(
            authorize(rules, &records, &entry, &[0, 1], &auth, 1, 7),
            Err(Refusal::NotAllowed)
        ));
        let pair = compiled.compare(&entry, 1, &auth[0]).unwrap();
        assert!(!pair.cedar && !pair.rule_core);
    }
    assert!(rule_eval::rule_allows(&rules[1], &transfer(1), &auth));
    assert!(!rule_eval::rule_allows_in(
        &rules[1],
        None,
        &transfer(1),
        &auth
    ));
    assert!(!rule_eval::allows_batch(rules, &[transfer(1)], &auth));
    assert!(rule_eval::allows_batch(
        rules,
        &[guess(4), transfer(1)],
        &auth
    ));
    // Deleting the game rule cannot erase the restriction on the transfer rule.
    assert!(matches!(
        authorize(
            &rules[1..],
            &records[1..],
            &[transfer(1)],
            &[0],
            &auth,
            1,
            7
        ),
        Err(Refusal::NotAllowed)
    ));
}
