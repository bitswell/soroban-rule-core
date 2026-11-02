//! The spending-cap check: each refusal and its precedence, eviction at the
//! cutoff and near ledger 0, the history bound, checked sums, and an
//! exhaustive comparison with a plain reading of the check over small runs.

use rule_eval::{
    CapError, CapParams, MAX_HISTORY_ENTRIES, SpendEntry, SpendRecord, check_spend, empty_record,
    params_valid,
};

/// The record after a spend, as its entries and total, or the refusal's name.
type Outcome = Result<(Vec<(u32, i128)>, i128), &'static str>;

fn record(entries: &[(u32, i128)], total: i128) -> SpendRecord {
    SpendRecord {
        history: entries
            .iter()
            .map(|&(ledger, amount)| SpendEntry { ledger, amount })
            .collect(),
        total,
    }
}

fn entries(r: &SpendRecord) -> Vec<(u32, i128)> {
    r.history.iter().map(|e| (e.ledger, e.amount)).collect()
}

fn same(a: &SpendRecord, b: &SpendRecord) -> bool {
    entries(a) == entries(b) && a.total == b.total
}

fn error_name(e: &CapError) -> &'static str {
    match e {
        CapError::NegativeAmount => "negative_amount",
        CapError::LedgerBeforeNewest => "ledger_before_newest",
        CapError::Overflow => "overflow",
        CapError::LimitExceeded => "limit_exceeded",
        CapError::HistoryFull => "history_full",
    }
}

fn outcome(r: &SpendRecord, limit: i128, period: u32, now: u32, amount: i128) -> Outcome {
    match check_spend(r, limit, period, now, amount) {
        Ok(out) => Ok((entries(&out), out.total)),
        Err(e) => Err(error_name(&e)),
    }
}

#[test]
fn params_need_a_positive_limit_and_a_nonzero_period() {
    let valid = |limit, period| params_valid(&CapParams { limit, period });
    assert!(valid(1, 1));
    assert!(valid(i128::MAX, u32::MAX));
    assert!(!valid(0, 1));
    assert!(!valid(-1, 1));
    assert!(!valid(i128::MIN, 1));
    assert!(!valid(1, 0));
    assert!(!valid(0, 0));
}

#[test]
fn the_empty_record_holds_nothing() {
    let r = empty_record();
    assert!(r.history.is_empty());
    assert_eq!(r.total, 0);
}

#[test]
fn a_negative_amount_is_refused() {
    let r = record(&[(5, 10)], 10);
    assert_eq!(outcome(&r, 100, 10, 6, -1), Err("negative_amount"));
    assert_eq!(outcome(&r, 100, 10, 6, i128::MIN), Err("negative_amount"));
    // Refused before the clock check.
    assert_eq!(outcome(&r, 100, 10, 0, -1), Err("negative_amount"));
}

#[test]
fn a_zero_amount_passes_and_changes_nothing() {
    let r = record(&[(5, 10), (7, 20)], 30);
    let out = check_spend(&r, 100, 10, 100, 0).ok().unwrap();
    assert!(same(&out, &r));
    // Even when the total already exceeds a lowered limit.
    let over = record(&[(5, 80)], 80);
    let out = check_spend(&over, 50, 10, 6, 0).ok().unwrap();
    assert!(same(&out, &over));
    // And at a ledger before the newest entry: nothing is recorded.
    let out = check_spend(&r, 100, 10, 0, 0).ok().unwrap();
    assert!(same(&out, &r));
}

#[test]
fn a_spend_within_the_limit_is_appended() {
    let r = empty_record();
    assert_eq!(outcome(&r, 100, 10, 1, 40), Ok((vec![(1, 40)], 40)));
    let r = record(&[(1, 40)], 40);
    assert_eq!(
        outcome(&r, 100, 10, 2, 60),
        Ok((vec![(1, 40), (2, 60)], 100))
    );
}

#[test]
fn the_limit_is_inclusive() {
    let r = record(&[(1, 40)], 40);
    assert_eq!(
        outcome(&r, 100, 10, 2, 60),
        Ok((vec![(1, 40), (2, 60)], 100))
    );
    assert_eq!(outcome(&r, 100, 10, 2, 61), Err("limit_exceeded"));
    assert_eq!(
        outcome(&empty_record(), 100, 10, 1, 101),
        Err("limit_exceeded")
    );
}

#[test]
fn eviction_drops_entries_at_or_before_the_cutoff() {
    let r = record(&[(10, 30), (11, 30), (12, 30)], 90);
    // At ledger 20 with period 10 the cutoff is 10: ledger 10 is evicted,
    // ledger 11 is kept.
    assert_eq!(
        outcome(&r, 100, 10, 20, 40),
        Ok((vec![(11, 30), (12, 30), (20, 40)], 100))
    );
    assert_eq!(outcome(&r, 100, 10, 20, 41), Err("limit_exceeded"));
    // At ledger 19 nothing is evicted yet.
    assert_eq!(outcome(&r, 100, 10, 19, 11), Err("limit_exceeded"));
    assert_eq!(
        outcome(&r, 100, 10, 19, 10),
        Ok((vec![(10, 30), (11, 30), (12, 30), (19, 10)], 100))
    );
    // Far later, everything is evicted.
    assert_eq!(
        outcome(&r, 100, 10, 1000, 100),
        Ok((vec![(1000, 100)], 100))
    );
}

#[test]
fn a_refusal_does_not_keep_the_eviction() {
    let r = record(&[(10, 30), (11, 30)], 60);
    // The spend is refused after evicting ledger 10; the caller keeps `r`.
    assert_eq!(outcome(&r, 100, 10, 20, 80), Err("limit_exceeded"));
    assert_eq!(entries(&r), vec![(10, 30), (11, 30)]);
}

#[test]
fn eviction_stops_at_the_first_entry_after_the_cutoff() {
    // Eviction walks from the front: an entry after the cutoff shields the
    // ones behind it. Records the check builds are in ledger order, so this
    // only shows on a record built some other way.
    let r = record(&[(15, 10), (5, 10), (16, 10)], 30);
    assert_eq!(
        outcome(&r, 100, 10, 20, 1),
        Ok((vec![(15, 10), (5, 10), (16, 10), (20, 1)], 31))
    );
}

#[test]
fn the_cutoff_saturates_at_ledger_zero() {
    // Before ledger `period` the cutoff is 0, so only entries at ledger 0 are
    // evicted, even though they are inside the window.
    let r = record(&[(0, 100)], 100);
    assert_eq!(outcome(&r, 100, 10, 5, 100), Ok((vec![(5, 100)], 100)));
    let r = record(&[(1, 100)], 100);
    assert_eq!(outcome(&r, 100, 10, 5, 1), Err("limit_exceeded"));
    // Repeated spends at ledger 0 each evict the one before.
    let r = check_spend(&empty_record(), 100, 10, 0, 100).ok().unwrap();
    assert_eq!(outcome(&r, 100, 10, 0, 100), Ok((vec![(0, 100)], 100)));
    // The largest ledger and period.
    let r = record(&[(0, 50), (1, 50)], 100);
    assert_eq!(
        outcome(&r, 100, u32::MAX, u32::MAX, 50),
        Ok((vec![(1, 50), (u32::MAX, 50)], 100))
    );
    assert_eq!(
        outcome(&r, 100, u32::MAX, u32::MAX, 51),
        Err("limit_exceeded")
    );
}

#[test]
fn a_spend_before_the_newest_entry_is_refused() {
    let r = record(&[(5, 10), (9, 10)], 20);
    assert_eq!(outcome(&r, 100, 10, 8, 1), Err("ledger_before_newest"));
    assert_eq!(outcome(&r, 100, 10, 0, 1), Err("ledger_before_newest"));
    // The newest ledger itself, and later ones, pass.
    assert_eq!(
        outcome(&r, 100, 10, 9, 1),
        Ok((vec![(5, 10), (9, 10), (9, 1)], 21))
    );
    assert_eq!(
        outcome(&r, 100, 10, 10, 1),
        Ok((vec![(5, 10), (9, 10), (10, 1)], 21))
    );
    // An empty history has no newest entry.
    assert_eq!(
        outcome(&empty_record(), 100, 10, 0, 1),
        Ok((vec![(0, 1)], 1))
    );
    // Refused before eviction and the limit.
    assert_eq!(outcome(&r, 100, 10, 8, 1000), Err("ledger_before_newest"));
}

fn full(n: usize, ledger: u32) -> SpendRecord {
    let entries: Vec<(u32, i128)> = (0..n).map(|_| (ledger, 1)).collect();
    record(&entries, i128::try_from(n).unwrap())
}

#[test]
fn the_history_holds_at_most_max_entries() {
    assert_eq!(MAX_HISTORY_ENTRIES, 1000);
    let r = full(MAX_HISTORY_ENTRIES - 1, 1);
    let out = check_spend(&r, 10_000, 10, 1, 1).ok().unwrap();
    assert_eq!(out.history.len(), MAX_HISTORY_ENTRIES);
    assert_eq!(outcome(&out, 10_000, 10, 1, 1), Err("history_full"));
    // Eviction makes room.
    assert_eq!(outcome(&out, 10_000, 10, 11, 1), Ok((vec![(11, 1)], 1)));
    // The limit is checked before the history bound.
    assert_eq!(outcome(&out, 1000, 10, 1, 1), Err("limit_exceeded"));
}

#[test]
fn sums_that_overflow_are_refused() {
    // The new total.
    let r = record(&[(1, i128::MAX - 1)], i128::MAX - 1);
    assert_eq!(
        outcome(&r, i128::MAX, 10, 2, 1),
        Ok((vec![(1, i128::MAX - 1), (2, 1)], i128::MAX))
    );
    assert_eq!(outcome(&r, i128::MAX, 10, 2, 2), Err("overflow"));
    // The evicted amounts, on a record the check does not build.
    let r = record(&[(1, i128::MAX), (2, 1), (30, 1)], 1);
    assert_eq!(outcome(&r, 100, 10, 30, 1), Err("overflow"));
    // The remaining total, on a record the check does not build.
    let r = record(&[(1, 1)], i128::MIN);
    assert_eq!(outcome(&r, 100, 10, 30, 1), Err("overflow"));
}

// A plain reading of the check, with iterators and `Vec` operations, for the
// exhaustive comparison below. It sums in a wider integer and maps each
// out-of-range sum to the overflow refusal.

fn reference(
    h: &[(u32, i128)],
    total: i128,
    limit: i128,
    period: u32,
    now: u32,
    amount: i128,
) -> Outcome {
    if amount < 0 {
        return Err("negative_amount");
    }
    if amount == 0 {
        return Ok((h.to_vec(), total));
    }
    if h.last().is_some_and(|&(l, _)| now < l) {
        return Err("ledger_before_newest");
    }
    let cutoff = now.saturating_sub(period);
    let evicted = h.iter().take_while(|&&(l, _)| l <= cutoff).count();
    let mut removed: i128 = 0;
    for &(_, a) in &h[..evicted] {
        removed = removed.checked_add(a).ok_or("overflow")?;
    }
    let remaining = total.checked_sub(removed).ok_or("overflow")?;
    let new_total = remaining.checked_add(amount).ok_or("overflow")?;
    if new_total > limit {
        return Err("limit_exceeded");
    }
    if h.len() - evicted >= MAX_HISTORY_ENTRIES {
        return Err("history_full");
    }
    let mut kept = h[evicted..].to_vec();
    kept.push((now, amount));
    Ok((kept, new_total))
}

const LEDGERS: [u32; 5] = [0, 1, 2, 3, 6];
const AMOUNTS: [i128; 5] = [-1, 0, 1, 2, 3];

fn calls() -> Vec<(u32, i128)> {
    LEDGERS
        .iter()
        .flat_map(|&l| AMOUNTS.iter().map(move |&a| (l, a)))
        .collect()
}

/// A check of one run under one cap: the limit, the period and the calls.
type RunCheck<'a> = &'a mut dyn FnMut(i128, u32, &[(u32, i128)]);

/// Every run of up to three calls from the universe, under each small cap.
fn runs(f: RunCheck) {
    let calls = calls();
    for limit in [0, 1, 3, 4] {
        for period in [0, 1, 2, 3] {
            f(limit, period, &[]);
            for a in &calls {
                f(limit, period, &[*a]);
                for b in &calls {
                    f(limit, period, &[*a, *b]);
                    for c in &calls {
                        f(limit, period, &[*a, *b, *c]);
                    }
                }
            }
        }
    }
}

#[test]
fn check_spend_agrees_with_the_reference_reading() {
    runs(&mut |limit, period, run| {
        let mut r = empty_record();
        for &(now, amount) in run {
            let want = reference(&entries(&r), r.total, limit, period, now, amount);
            let got = outcome(&r, limit, period, now, amount);
            assert_eq!(got, want, "limit {limit} period {period} run {run:?}");
            if let Ok(out) = check_spend(&r, limit, period, now, amount) {
                r = out;
            }
        }
    });
}

#[test]
fn every_short_run_stays_within_every_window() {
    runs(&mut |limit, period, run| {
        if limit < 0 {
            return;
        }
        let mut r = empty_record();
        let mut recorded: Vec<(u32, i128)> = Vec::new();
        for &(now, amount) in run {
            if let Ok(out) = check_spend(&r, limit, period, now, amount) {
                if amount > 0 {
                    recorded.push((now, amount));
                }
                r = out;
            }
        }
        // The window eviction leaves at every ledger `t`.
        for t in 0..10u32 {
            let sum: i128 = recorded
                .iter()
                .filter(|&&(l, _)| t.saturating_sub(period) < l && l <= t)
                .map(|&(_, a)| a)
                .sum();
            assert!(
                sum <= limit,
                "limit {limit} period {period} run {run:?} t {t}"
            );
        }
        // The stored total is the sum of the stored history.
        assert_eq!(r.total, r.history.iter().map(|e| e.amount).sum::<i128>());
    });
}
