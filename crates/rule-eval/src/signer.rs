//! Signers: who may authorize the calls a rule matches.

use alloc::vec::Vec;

use crate::bytes::{bytes_copy, bytes_eq};

/// A signer, following OpenZeppelin's smart-account signer kinds.
pub enum Signer {
    /// An address that authorizes for itself, as its `ScAddress` XDR.
    Delegated(Vec<u8>),
    /// A key checked by a verifier contract: the verifier's address, as its
    /// `ScAddress` XDR, and the key's bytes.
    External(Vec<u8>, Vec<u8>),
}

/// Whether `a` and `b` are the same signer: same constructor, equal bytes in
/// every field.
#[must_use]
pub fn signer_eq(a: &Signer, b: &Signer) -> bool {
    match (a, b) {
        (Signer::Delegated(x), Signer::Delegated(y)) => bytes_eq(x, y),
        (Signer::External(v, k), Signer::External(w, l)) => bytes_eq(v, w) && bytes_eq(k, l),
        _ => false,
    }
}

/// Whether `x` equals one of the signers in `list`.
#[must_use]
pub fn signer_in(x: &Signer, list: &[Signer]) -> bool {
    let mut i = 0;
    while i < list.len() {
        if signer_eq(x, &list[i]) {
            return true;
        }
        i += 1;
    }
    false
}

/// Whether `x` equals one of the signers of `list` before position `before`.
fn signer_in_first(x: &Signer, list: &[Signer], before: usize) -> bool {
    let mut i = 0;
    while i < list.len() {
        if i >= before {
            return false;
        }
        if signer_eq(x, &list[i]) {
            return true;
        }
        i += 1;
    }
    false
}

/// The number of distinct signers of `signers` that appear in
/// `authenticated`. Each signer counts once, at its first position in
/// `signers`, so a signer repeated in either list never counts twice.
fn signed_count(signers: &[Signer], authenticated: &[Signer]) -> usize {
    let mut count = 0;
    let mut i = 0;
    while i < signers.len() {
        if !signer_in_first(&signers[i], signers, i) && signer_in(&signers[i], authenticated) {
            count += 1;
        }
        i += 1;
    }
    count
}

/// Whether at least `threshold` distinct signers of `signers` appear in
/// `authenticated`. A threshold of 0 always holds.
#[must_use]
pub fn signers_met(signers: &[Signer], threshold: u32, authenticated: &[Signer]) -> bool {
    threshold as usize <= signed_count(signers, authenticated)
}

/// A fresh copy of `s`.
pub(crate) fn signer_copy(s: &Signer) -> Signer {
    match s {
        Signer::Delegated(x) => Signer::Delegated(bytes_copy(x)),
        Signer::External(v, k) => Signer::External(bytes_copy(v), bytes_copy(k)),
    }
}

/// A fresh copy of `list`, keeping order.
pub(crate) fn signers_copy(list: &[Signer]) -> Vec<Signer> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < list.len() {
        out.push(signer_copy(&list[i]));
        i += 1;
    }
    out
}

/// The signers of `list` that are not in `remove`, in order.
pub(crate) fn signers_without(list: &[Signer], remove: &[Signer]) -> Vec<Signer> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < list.len() {
        if !signer_in(&list[i], remove) {
            out.push(signer_copy(&list[i]));
        }
        i += 1;
    }
    out
}
