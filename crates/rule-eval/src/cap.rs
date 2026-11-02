//! Spending caps: at most `limit` spent within a rolling window of `period`
//! ledgers.
//!
//! A capped rule keeps a [`SpendRecord`]: the spends still inside the window,
//! oldest first, and their total. [`check_spend`] takes the record, the cap,
//! the current ledger and the amount of a new spend, and returns the record
//! after the spend or the reason it is refused. It is pure: the shell loads
//! the record before the call and stores what `check_spend` returns. A
//! refusal returns no record, so the stored one stays as it was.
//!
//! The check mirrors `enforce` and `cleanup_old_entries` of the spending-limit
//! policy in OpenZeppelin's `stellar-accounts`, at the revision Perch pins:
//!
//! 1. a negative amount is refused;
//! 2. a zero amount passes and changes nothing;
//! 3. the entries at the front of the history whose ledger is at most
//!    `now.saturating_sub(period)` are evicted, and their amounts taken off
//!    the total;
//! 4. the spend is refused if the remaining total plus the amount exceeds
//!    `limit`;
//! 5. the spend is refused if the remaining history already holds
//!    [`MAX_HISTORY_ENTRIES`] entries;
//! 6. otherwise the entry `(now, amount)` is appended and the total
//!    increased.
//!
//! Two refusals are added. Between steps 2 and 3, a spend is refused when
//! `now` is earlier than the ledger of the newest recorded entry, so nothing
//! about the ledger clock is assumed. Every sum is checked, and one that
//! overflows `i128` is refused with [`CapError::Overflow`].

use alloc::vec::Vec;

/// The most entries a record holds: a spend is refused when the history left
/// after eviction already holds this many.
pub const MAX_HISTORY_ENTRIES: usize = 1000;

/// One recorded spend: the ledger it was made in and its amount.
pub struct SpendEntry {
    pub ledger: u32,
    pub amount: i128,
}

/// What a capped rule has spent: its recorded spends in the order they were
/// made, and their total.
pub struct SpendRecord {
    pub history: Vec<SpendEntry>,
    pub total: i128,
}

/// A cap: at most `limit` spent within `period` consecutive ledgers.
pub struct CapParams {
    pub limit: i128,
    pub period: u32,
}

/// Why a spend was refused.
pub enum CapError {
    /// The amount is negative.
    NegativeAmount,
    /// The current ledger is earlier than the ledger of the newest recorded
    /// spend.
    LedgerBeforeNewest,
    /// A sum of amounts does not fit in an `i128`.
    Overflow,
    /// The spend would take the total within the window above the limit.
    LimitExceeded,
    /// The history left after eviction already holds
    /// [`MAX_HISTORY_ENTRIES`] entries.
    HistoryFull,
}

/// Whether `params` may be installed: a positive limit and a nonzero period.
#[must_use]
pub fn params_valid(params: &CapParams) -> bool {
    params.limit > 0 && params.period > 0
}

/// The record of a cap with no spends.
#[must_use]
pub fn empty_record() -> SpendRecord {
    SpendRecord {
        history: Vec::new(),
        total: 0,
    }
}

/// What eviction did.
enum Eviction {
    /// It stopped at position `kept_from`, the first entry kept, having taken
    /// off `removed`, the total of the entries before it.
    Stopped { kept_from: usize, removed: i128 },
    /// The evicted amounts do not sum within an `i128`.
    Overflow,
}

/// Whether `now` is earlier than the ledger of the last entry of `history`.
fn before_newest(history: &[SpendEntry], now: u32) -> bool {
    let len = history.len();
    if len == 0 {
        return false;
    }
    now < history[len - 1].ledger
}

/// Evicts the entries at the front of `history` whose ledger is at most
/// `cutoff`, stopping at the first later one.
fn evict(history: &[SpendEntry], cutoff: u32) -> Eviction {
    let mut removed: i128 = 0;
    let mut i = 0;
    while i < history.len() {
        if history[i].ledger > cutoff {
            return Eviction::Stopped {
                kept_from: i,
                removed,
            };
        }
        match removed.checked_add(history[i].amount) {
            Some(sum) => removed = sum,
            None => return Eviction::Overflow,
        }
        i += 1;
    }
    Eviction::Stopped {
        kept_from: i,
        removed,
    }
}

/// A fresh copy of `entry`.
fn entry_copy(entry: &SpendEntry) -> SpendEntry {
    SpendEntry {
        ledger: entry.ledger,
        amount: entry.amount,
    }
}

/// The entries of `history` from position `start` on, in order.
fn entries_from(history: &[SpendEntry], start: usize) -> Vec<SpendEntry> {
    let mut out = Vec::new();
    let mut i = start;
    while i < history.len() {
        out.push(entry_copy(&history[i]));
        i += 1;
    }
    out
}

/// A fresh copy of `record`.
fn record_copy(record: &SpendRecord) -> SpendRecord {
    SpendRecord {
        history: entries_from(&record.history, 0),
        total: record.total,
    }
}

/// The record after a spend of `amount` at ledger `now` under a cap of
/// `limit` per `period` ledgers, or why the spend is refused.
///
/// # Errors
///
/// - [`CapError::NegativeAmount`] if `amount` is negative;
/// - [`CapError::LedgerBeforeNewest`] if `amount` is positive and `now` is
///   earlier than the ledger of the last entry of `record.history`;
/// - [`CapError::Overflow`] if the evicted amounts, the remaining total or
///   the new total does not fit in an `i128`;
/// - [`CapError::LimitExceeded`] if the new total exceeds `limit`;
/// - [`CapError::HistoryFull`] if the history left after eviction holds
///   [`MAX_HISTORY_ENTRIES`] entries or more.
pub fn check_spend(
    record: &SpendRecord,
    limit: i128,
    period: u32,
    now: u32,
    amount: i128,
) -> Result<SpendRecord, CapError> {
    if amount < 0 {
        return Err(CapError::NegativeAmount);
    }
    if amount == 0 {
        return Ok(record_copy(record));
    }
    if before_newest(&record.history, now) {
        return Err(CapError::LedgerBeforeNewest);
    }
    let (kept_from, removed) = match evict(&record.history, now.saturating_sub(period)) {
        Eviction::Stopped { kept_from, removed } => (kept_from, removed),
        Eviction::Overflow => return Err(CapError::Overflow),
    };
    let remaining = match record.total.checked_sub(removed) {
        Some(remaining) => remaining,
        None => return Err(CapError::Overflow),
    };
    let total = match remaining.checked_add(amount) {
        Some(total) => total,
        None => return Err(CapError::Overflow),
    };
    if total > limit {
        return Err(CapError::LimitExceeded);
    }
    if record.history.len() - kept_from >= MAX_HISTORY_ENTRIES {
        return Err(CapError::HistoryFull);
    }
    let mut history = entries_from(&record.history, kept_from);
    history.push(SpendEntry {
        ledger: now,
        amount,
    });
    Ok(SpendRecord { history, total })
}
