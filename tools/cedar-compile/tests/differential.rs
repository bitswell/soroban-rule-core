mod common;
use cedar_to_rule_core::{ArgumentType, compile};
use common::*;
use rule_eval::{Context, Val};

#[test]
fn deterministic_and_generated_eligibility() {
    let compiled = compiled();
    let mut count = 0;
    for amount in [i64::MIN, -1, 0, 1, 99, 100, 101, i64::MAX] {
        for root in 0..4 {
            for principal in [1, 2] {
                for from in [1, 2] {
                    for to in [3, 5] {
                        let r = match root {
                            0 => guess(4),
                            1 => call(5, "guess", vec![]),
                            2 => call(3, "other", vec![]),
                            _ => transfer(50),
                        };
                        let entry = [r, transfer_to(i128::from(amount), from, to)];
                        let pair = compiled.compare(&entry, 1, &signer(principal)).unwrap();
                        assert_eq!(
                            pair.cedar, pair.rule_core,
                            "amount={amount}, root={root}, signer={principal}, from={from}, to={to}"
                        );
                        assert_eq!(
                            pair.cedar,
                            (0..=100).contains(&amount)
                                && root == 0
                                && principal == 1
                                && from == 1
                                && to == 3
                        );
                        count += 1;
                    }
                }
            }
        }
    }
    for n in -2..=11 {
        for principal in [1, 2] {
            let pair = compiled
                .compare(&[guess(n)], 0, &signer(principal))
                .unwrap();
            assert_eq!(pair.cedar, pair.rule_core);
            assert_eq!(pair.cedar, (0..=9).contains(&n) && principal == 1);
            count += 1;
        }
    }
    assert_eq!(count, 284);
    println!("deterministic eligibility comparisons: {count}");

    let mut seed = 0x6ce_da4_u64;
    let mut generated = 0;
    // Vary the SOURCE interval/operator form too, not just requests. No rand dep.
    for policy_case in 0..32_i64 {
        let lo = policy_case - 16;
        let hi = lo + policy_case % 11;
        let bounds = match policy_case % 3 {
            0 => format!("context.amount >= {lo} && context.amount <= {hi}"),
            1 => format!("context.amount > {} && context.amount < {}", lo - 1, hi + 1),
            _ => format!("context.amount <= {hi} && context.amount >= {lo}"),
        };
        let source = SOURCE.replace("context.amount >= 0 && context.amount <= 100", &bounds);
        let compiled = compile(&source, bindings()).unwrap();
        for case in 0..64 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            let amount = match case {
                0 => lo - 1,
                1 => lo,
                2 => hi,
                3 => hi + 1,
                4 => i64::MIN,
                5 => i64::MAX,
                _ => (seed % 71) as i64 - 35,
            };
            let principal = if seed & 1 == 0 { 1 } else { 2 };
            let valid_root = seed & 2 == 0;
            let entry = [
                if valid_root {
                    guess(4)
                } else {
                    call(5, "guess", vec![])
                },
                transfer(i128::from(amount)),
            ];
            let pair = compiled.compare(&entry, 1, &signer(principal)).unwrap();
            assert_eq!(
                pair.cedar, pair.rule_core,
                "source-case={policy_case}, request={case}"
            );
            assert_eq!(
                pair.cedar,
                (lo..=hi).contains(&amount) && principal == 1 && valid_root
            );
            generated += 1;
        }
    }
    assert_eq!(generated, 2048);
    println!("generated eligibility comparisons: {generated} across 32 source policies");
}

#[test]
fn integer_extremes_equality_and_scalar_constructors() {
    let mut count = 0;
    for value in [i64::MIN, i64::MIN + 1, -1, 0, 1, i64::MAX - 1, i64::MAX] {
        let source = SOURCE.replace(
            "context.amount >= 0 && context.amount <= 100",
            &format!("context.amount == {value}"),
        );
        let compiled = compile(&source, bindings()).unwrap();
        for actual in [i64::MIN, value, i64::MAX] {
            let pair = compiled
                .compare(&[guess(4), transfer(i128::from(actual))], 1, &signer(1))
                .unwrap();
            assert_eq!(pair.cedar, pair.rule_core);
            assert_eq!(pair.cedar, value == actual);
            count += 1;
        }
    }
    for (kind, condition, values) in [
        (
            ArgumentType::Bool,
            "context.guess == true",
            vec![Val::Bool(true), Val::Bool(false)],
        ),
        (
            ArgumentType::String,
            "context.guess == \"雪\"",
            vec![
                Val::String("雪".as_bytes().to_vec()),
                Val::String(b"x".to_vec()),
            ],
        ),
    ] {
        let mut b = bindings();
        b.calls[0].arguments[0].kind = kind;
        let source = SOURCE.replace("context.guess >= 0 && context.guess <= 9", condition);
        let compiled = compile(&source, b).unwrap();
        for (i, value) in values.into_iter().enumerate() {
            let pair = compiled
                .compare(&[call(3, "guess", vec![value])], 0, &signer(1))
                .unwrap();
            assert_eq!(pair.cedar, pair.rule_core);
            assert_eq!(pair.cedar, i == 0);
            count += 1;
        }
    }
    assert_eq!(count, 25);
    println!("extreme/equality/scalar comparisons: {count}");
}

#[test]
fn malformed_requests_are_domain_refusals() {
    let compiled = compiled();
    let bad = [
        vec![],
        vec![Context::Create { wasm_hash: vec![] }, transfer(1)],
        vec![guess(4), Context::Create { wasm_hash: vec![] }],
        vec![guess(4), call(4, "transfer", vec![])],
        vec![
            guess(4),
            call(
                4,
                "transfer",
                vec![
                    Val::Address(account(1)),
                    Val::Address(contract(3)),
                    Val::Bool(true),
                ],
            ),
        ],
        vec![guess(4), transfer(i128::from(i64::MAX) + 1)],
        vec![guess(4), transfer(i128::from(i64::MIN) - 1)],
        vec![guess(4), transfer(i128::MAX)],
        vec![guess(4), transfer(i128::MIN)],
        vec![guess(4), transfer_to(1, 99, 3)],
        vec![guess(4), call(4, "unknown", vec![])],
        vec![call(99, "guess", vec![]), transfer(1)],
        vec![
            guess(4),
            call(
                4,
                "transfer",
                vec![
                    Val::Address(account(1)),
                    Val::Address(contract(3)),
                    Val::I128(1),
                    Val::Bool(true),
                ],
            ),
        ],
    ];
    for entry in &bad {
        assert!(compiled.compare(entry, 1, &signer(1)).is_err());
    }
    assert!(compiled.compare(&[guess(4)], 0, &signer(99)).is_err());
    assert!(compiled.compare(&[guess(4)], 2, &signer(1)).is_err());
    println!("malformed/out-of-domain refusals: 15 (not counted as Cedar verdict agreement)");
}
