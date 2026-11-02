//! Signers: exact comparison, the threshold requirement on distinct
//! authenticated signers, and how it enters `allows` and `allows_all`.

mod common;

use common::*;
use rule_eval::{Signer, allows, allows_all, rule_allows, signer_eq, signer_in, signers_met};

fn send() -> rule_eval::Context {
    call("token", "transfer", Vec::new())
}

/// Every signer list of up to three signers over three universe signers, two
/// of which hold equal bytes under different constructors, so repeats occur.
fn signer_lists() -> Vec<Vec<usize>> {
    let pool = [0, 3, 2];
    let mut out = vec![Vec::new()];
    let mut frontier = vec![Vec::new()];
    for _ in 0..3 {
        let mut next = Vec::new();
        for list in &frontier {
            for &k in &pool {
                let mut longer: Vec<usize> = list.clone();
                longer.push(k);
                next.push(longer);
            }
        }
        out.extend(next.iter().cloned());
        frontier = next;
    }
    out
}

fn signers_of(list: &[usize]) -> Vec<Signer> {
    list.iter().map(|&k| signer(k)).collect()
}

#[test]
fn signers_compare_exactly() {
    for k in 0..SIGNERS {
        for l in 0..SIGNERS {
            assert_eq!(
                signer_eq(&signer(k), &signer(l)),
                k == l,
                "signer {k} vs {l}"
            );
        }
    }
    // The same bytes under the other constructor.
    assert!(!signer_eq(&delegated("a"), &external("a", "")));
    assert!(!signer_eq(&external("a", ""), &delegated("a")));
    assert!(!signer_eq(&delegated("ab"), &external("a", "b")));
    // Prefixes and extensions.
    assert!(!signer_eq(&delegated("a"), &delegated("ab")));
    assert!(!signer_eq(&external("v", "k"), &external("v", "k2")));
    assert!(!signer_eq(&external("v", "k"), &external("v2", "k")));
    assert!(signer_eq(&external("v", "k"), &external("v", "k")));
}

#[test]
fn signer_in_needs_an_exact_member() {
    let list = vec![delegated("a"), external("v", "k")];
    assert!(signer_in(&delegated("a"), &list));
    assert!(signer_in(&external("v", "k"), &list));
    assert!(!signer_in(&external("a", ""), &list));
    assert!(!signer_in(&delegated("v"), &list));
    assert!(!signer_in(&delegated("a"), &[]));
}

#[test]
fn threshold_zero_needs_no_signer() {
    let r = signed_rule(
        "token",
        &["transfer"],
        Vec::new(),
        vec![delegated("a"), delegated("b")],
        0,
    );
    assert!(rule_allows(&r, &send(), &[]));
    assert!(rule_allows(&r, &send(), &[delegated("c")]));
    assert!(signers_met(&[], 0, &[]));
}

#[test]
fn thresholds_count_distinct_authenticated_signers() {
    let signers = vec![delegated("a"), delegated("b"), external("v", "k")];
    let none: Vec<Signer> = Vec::new();
    let one = vec![delegated("a")];
    let two = vec![delegated("b"), external("v", "k")];
    let all = vec![external("v", "k"), delegated("a"), delegated("b")];
    // Threshold 0, 1, k = 2, n = 3, and above n.
    let expect = [
        (0, [true, true, true, true]),
        (1, [false, true, true, true]),
        (2, [false, false, true, true]),
        (3, [false, false, false, true]),
        (4, [false, false, false, false]),
    ];
    for (threshold, verdicts) in expect {
        for (auth, want) in [&none, &one, &two, &all].into_iter().zip(verdicts) {
            assert_eq!(signers_met(&signers, threshold, auth), want, "{threshold}");
        }
    }
    // Signers outside the rule's list never count.
    assert!(!signers_met(
        &signers,
        1,
        &[delegated("c"), external("v", "x")]
    ));
}

#[test]
fn repeats_in_either_list_count_once() {
    let signers = vec![delegated("a"), delegated("a"), delegated("b")];
    assert!(!signers_met(&signers, 2, &[delegated("a")]));
    assert!(!signers_met(&signers, 2, &[delegated("a"), delegated("a")]));
    assert!(signers_met(&signers, 2, &[delegated("b"), delegated("a")]));
    // Three entries but two distinct signers: threshold 3 is above n.
    assert!(!signers_met(
        &signers,
        3,
        &[delegated("a"), delegated("b"), delegated("a")]
    ));
}

#[test]
fn delegated_and_external_with_equal_bytes_are_different_signers() {
    let r = signed_rule("token", &["transfer"], Vec::new(), vec![delegated("a")], 1);
    assert!(rule_allows(&r, &send(), &[delegated("a")]));
    assert!(!rule_allows(&r, &send(), &[external("a", "")]));
    assert!(!rule_allows(&r, &send(), &[external("a", "a")]));
    let r = signed_rule(
        "token",
        &["transfer"],
        Vec::new(),
        vec![external("a", "")],
        1,
    );
    assert!(!rule_allows(&r, &send(), &[delegated("a")]));
    assert!(rule_allows(&r, &send(), &[external("a", "")]));
}

#[test]
fn missing_signers_refuse_only_the_rule_that_needs_them() {
    let rs = vec![
        signed_rule("token", &["transfer"], Vec::new(), vec![delegated("a")], 1),
        rule("token", &["approve"], Vec::new()),
    ];
    let approve = call("token", "approve", Vec::new());
    assert!(!allows(&rs, &send(), &[]));
    assert!(allows(&rs, &approve, &[]));
    assert!(allows(&rs, &send(), &[delegated("a")]));
}

#[test]
fn signers_met_agrees_with_the_reference_reading() {
    let auths = authenticated_lists();
    let mut checked = 0usize;
    for list in signer_lists() {
        let signers = signers_of(&list);
        for threshold in 0..=4 {
            for auth in &auths {
                assert_eq!(
                    signers_met(&signers, threshold, auth),
                    ref_signers_met(&signers, threshold, auth),
                    "{list:?} {threshold}"
                );
                checked += 1;
            }
        }
    }
    assert!(checked > 10_000);
}

/// Whether every signer of `small` is in `big`.
fn subset(small: &[Signer], big: &[Signer]) -> bool {
    small
        .iter()
        .all(|s| big.iter().any(|t| ref_signer_eq(s, t)))
}

#[test]
fn authenticating_more_signers_never_refuses() {
    let auths = authenticated_lists();
    for list in signer_lists() {
        for threshold in 0..=4 {
            let rs = vec![signed_rule(
                "token",
                &["transfer"],
                Vec::new(),
                signers_of(&list),
                threshold,
            )];
            for small in &auths {
                if !allows(&rs, &send(), small) {
                    continue;
                }
                for big in &auths {
                    if subset(small, big) {
                        assert!(allows(&rs, &send(), big), "{list:?} {threshold}");
                    }
                }
            }
        }
    }
}

#[test]
fn the_same_authenticated_signers_in_another_order_or_repeated_give_the_same_verdict() {
    let auths = authenticated_lists();
    for list in signer_lists() {
        for threshold in 0..=4 {
            let rs = vec![signed_rule(
                "token",
                &["transfer"],
                Vec::new(),
                signers_of(&list),
                threshold,
            )];
            for auth in &auths {
                let mut reordered: Vec<Signer> = auth.iter().rev().map(copy_signer).collect();
                if let Some(s) = auth.last() {
                    reordered.push(copy_signer(s));
                }
                assert_eq!(allows(&rs, &send(), auth), allows(&rs, &send(), &reordered));
            }
        }
    }
}

#[test]
fn the_batch_shares_one_authenticated_list() {
    let rs = vec![
        signed_rule("token", &["transfer"], Vec::new(), vec![delegated("a")], 1),
        signed_rule("vault", &["deposit"], Vec::new(), vec![delegated("b")], 1),
    ];
    let batch = [send(), call("vault", "deposit", Vec::new())];
    assert!(allows_all(&rs, &batch, &[delegated("a"), delegated("b")]));
    assert!(!allows_all(&rs, &batch, &[delegated("a")]));
    assert!(!allows_all(&rs, &batch, &[delegated("b")]));
    assert!(allows_all(&rs, &[], &[]));
}

#[test]
fn allows_agrees_with_the_reference_reading_under_signers() {
    let auths = authenticated_lists();
    let contexts = [
        send(),
        call("token", "approve", Vec::new()),
        call("vault", "transfer", Vec::new()),
        create("token"),
    ];
    let lists = signer_lists();
    for (x, list) in lists.iter().enumerate().step_by(3) {
        for threshold in 0..=3 {
            let rs = vec![
                signed_rule(
                    "token",
                    &["transfer"],
                    Vec::new(),
                    signers_of(list),
                    threshold,
                ),
                signed_rule(
                    "token",
                    &["transfer", "approve"],
                    Vec::new(),
                    signers_of(&lists[(x * 7 + 5) % lists.len()]),
                    (threshold + 1) % 4,
                ),
            ];
            for auth in &auths {
                for c in &contexts {
                    assert_eq!(allows(&rs, c, auth), ref_allows(&rs, c, auth));
                }
            }
        }
    }
}
