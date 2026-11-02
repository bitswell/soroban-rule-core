//! Contract-call argument values.

use alloc::vec::Vec;

use crate::bytes::{bytes_copy, bytes_eq};

/// A contract-call argument, following Soroban's `ScVal`.
pub enum Val {
    I128(i128),
    U64(u64),
    Bool(bool),
    Bytes(Vec<u8>),
    /// An address, as its `ScAddress` XDR.
    Address(Vec<u8>),
    Symbol(Vec<u8>),
    /// An argument of any other type (`u32`, `i64`, `string`, `vec`, `map`,
    /// ...), as its full `ScVal` XDR. The XDR begins with the type's
    /// discriminant, so two `Other` values are equal only when the arguments
    /// have the same type and the same value.
    Other(Vec<u8>),
}

/// Whether `a` and `b` are the same value: same constructor, equal payload.
#[must_use]
pub fn val_eq(a: &Val, b: &Val) -> bool {
    match (a, b) {
        (Val::I128(x), Val::I128(y)) => *x == *y,
        (Val::U64(x), Val::U64(y)) => *x == *y,
        (Val::Bool(x), Val::Bool(y)) => *x == *y,
        (Val::Bytes(x), Val::Bytes(y))
        | (Val::Address(x), Val::Address(y))
        | (Val::Symbol(x), Val::Symbol(y))
        | (Val::Other(x), Val::Other(y)) => bytes_eq(x, y),
        _ => false,
    }
}

/// A fresh copy of `v`.
pub(crate) fn val_copy(v: &Val) -> Val {
    match v {
        Val::I128(x) => Val::I128(*x),
        Val::U64(x) => Val::U64(*x),
        Val::Bool(x) => Val::Bool(*x),
        Val::Bytes(x) => Val::Bytes(bytes_copy(x)),
        Val::Address(x) => Val::Address(bytes_copy(x)),
        Val::Symbol(x) => Val::Symbol(bytes_copy(x)),
        Val::Other(x) => Val::Other(bytes_copy(x)),
    }
}
