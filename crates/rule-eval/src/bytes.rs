//! Byte strings: contract ids, function names and value payloads.

use alloc::vec::Vec;

/// Whether `a` and `b` are the same byte string: equal length, equal bytes.
#[must_use]
pub fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// Whether `x` equals one of the byte strings in `list`.
#[must_use]
pub fn bytes_in(x: &[u8], list: &[Vec<u8>]) -> bool {
    let mut i = 0;
    while i < list.len() {
        if bytes_eq(x, &list[i]) {
            return true;
        }
        i += 1;
    }
    false
}

/// A fresh copy of `s`.
pub(crate) fn bytes_copy(s: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < s.len() {
        out.push(s[i]);
        i += 1;
    }
    out
}

/// A fresh copy of `list`, keeping order.
pub(crate) fn bytes_list_copy(list: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < list.len() {
        out.push(bytes_copy(&list[i]));
        i += 1;
    }
    out
}

/// The byte strings of `list` that are not in `remove`, in order.
pub(crate) fn bytes_list_without(list: &[Vec<u8>], remove: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < list.len() {
        if !bytes_in(&list[i], remove) {
            out.push(bytes_copy(&list[i]));
        }
        i += 1;
    }
    out
}
