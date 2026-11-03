//! The `ScVal` and `ScAddress` XDR of values, as `stellar-xdr` 28.0.0 writes
//! them.
//!
//! [`encode`] is `Val.xdr` of the Lean model (`formal/RuleCore/Soroban/Val.lean`).
//! [`decode`] reads one whole value back: it returns `None` for bytes that are
//! not the XDR of one value, for the `ScVal`s no contract holds as a value
//! (a contract instance, the two ledger keys, and claimable balance and
//! liquidity pool addresses), and for an executable tag (CAP-85), which the
//! facade does not model. A value
//! of a kind [`Val`] does not model is [`Val::Other`] of its XDR, so for every
//! value `v`, `decode(&encode(&v)) == Some(v)` when every `Other` in `v` holds
//! the XDR of such a kind.

use alloc::vec::Vec;

use crate::val::{Address, Val};

/// The deepest nesting [`decode`] reads; the host allows less.
pub const MAX_DEPTH: u32 = 128;

const SCV_BOOL: u32 = 0;
const SCV_VOID: u32 = 1;
const SCV_ERROR: u32 = 2;
const SCV_U32: u32 = 3;
const SCV_I32: u32 = 4;
const SCV_U64: u32 = 5;
const SCV_I64: u32 = 6;
const SCV_TIMEPOINT: u32 = 7;
const SCV_DURATION: u32 = 8;
const SCV_U128: u32 = 9;
const SCV_I128: u32 = 10;
const SCV_U256: u32 = 11;
const SCV_I256: u32 = 12;
const SCV_BYTES: u32 = 13;
const SCV_STRING: u32 = 14;
const SCV_SYMBOL: u32 = 15;
const SCV_VEC: u32 = 16;
const SCV_MAP: u32 = 17;
const SCV_ADDRESS: u32 = 18;

const SC_ADDRESS_ACCOUNT: u32 = 0;
const SC_ADDRESS_CONTRACT: u32 = 1;
const SC_ADDRESS_MUXED_ACCOUNT: u32 = 2;
const PUBLIC_KEY_ED25519: u32 = 0;

/// The value's `ScVal` XDR.
#[must_use]
pub fn encode(v: &Val) -> Vec<u8> {
    let mut out = Vec::new();
    encode_into(v, &mut out);
    out
}

/// The address's `ScAddress` XDR.
#[must_use]
pub fn address_xdr(a: &Address) -> Vec<u8> {
    let mut out = Vec::new();
    address_into(a, &mut out);
    out
}

fn u32_into(n: u32, out: &mut Vec<u8>) {
    out.extend_from_slice(&n.to_be_bytes());
}

fn opaque_into(b: &[u8], out: &mut Vec<u8>) {
    // Lengths of host values fit in a u32; a longer slice cannot be a value.
    u32_into(u32::try_from(b.len()).unwrap_or(u32::MAX), out);
    out.extend_from_slice(b);
    out.resize(out.len() + (4 - b.len() % 4) % 4, 0);
}

fn len_into(n: usize, out: &mut Vec<u8>) {
    u32_into(u32::try_from(n).unwrap_or(u32::MAX), out);
}

fn address_into(a: &Address, out: &mut Vec<u8>) {
    match a {
        Address::Account(key) => {
            u32_into(SC_ADDRESS_ACCOUNT, out);
            u32_into(PUBLIC_KEY_ED25519, out);
            out.extend_from_slice(key);
        }
        Address::Contract(id) => {
            u32_into(SC_ADDRESS_CONTRACT, out);
            out.extend_from_slice(id);
        }
        Address::MuxedAccount { id, key } => {
            u32_into(SC_ADDRESS_MUXED_ACCOUNT, out);
            out.extend_from_slice(&id.to_be_bytes());
            out.extend_from_slice(key);
        }
    }
}

fn encode_into(v: &Val, out: &mut Vec<u8>) {
    match v {
        Val::Bool(b) => {
            u32_into(SCV_BOOL, out);
            u32_into(u32::from(*b), out);
        }
        Val::Void => u32_into(SCV_VOID, out),
        Val::U32(n) => {
            u32_into(SCV_U32, out);
            u32_into(*n, out);
        }
        Val::U64(n) => {
            u32_into(SCV_U64, out);
            out.extend_from_slice(&n.to_be_bytes());
        }
        Val::I128(n) => {
            u32_into(SCV_I128, out);
            out.extend_from_slice(&n.to_be_bytes());
        }
        Val::Bytes(b) => {
            u32_into(SCV_BYTES, out);
            opaque_into(b, out);
        }
        Val::String(b) => {
            u32_into(SCV_STRING, out);
            opaque_into(b, out);
        }
        Val::Symbol(b) => {
            u32_into(SCV_SYMBOL, out);
            opaque_into(b, out);
        }
        Val::Vec(items) => {
            u32_into(SCV_VEC, out);
            u32_into(1, out);
            len_into(items.len(), out);
            for item in items {
                encode_into(item, out);
            }
        }
        Val::Map(entries) => {
            u32_into(SCV_MAP, out);
            u32_into(1, out);
            len_into(entries.len(), out);
            for (k, val) in entries {
                encode_into(k, out);
                encode_into(val, out);
            }
        }
        Val::Address(a) => {
            u32_into(SCV_ADDRESS, out);
            address_into(a, out);
        }
        Val::Other(x) => out.extend_from_slice(x),
    }
}

/// The value whose `ScVal` XDR is exactly `bytes`.
#[must_use]
pub fn decode(bytes: &[u8]) -> Option<Val> {
    let mut r = Reader { bytes, pos: 0 };
    let v = r.val(0)?;
    if r.pos == bytes.len() { Some(v) } else { None }
}

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl Reader<'_> {
    fn take(&mut self, n: usize) -> Option<&[u8]> {
        let end = self.pos.checked_add(n)?;
        let s = self.bytes.get(self.pos..end)?;
        self.pos = end;
        Some(s)
    }

    fn array<const N: usize>(&mut self) -> Option<[u8; N]> {
        self.take(N)?.try_into().ok()
    }

    fn u32(&mut self) -> Option<u32> {
        Some(u32::from_be_bytes(self.array()?))
    }

    fn len(&mut self) -> Option<usize> {
        usize::try_from(self.u32()?).ok()
    }

    fn opaque(&mut self) -> Option<Vec<u8>> {
        let n = self.len()?;
        let b = self.take(n)?.to_vec();
        let pad = self.take((4 - n % 4) % 4)?;
        if pad.iter().all(|x| *x == 0) {
            Some(b)
        } else {
            None
        }
    }

    /// The XDR from `start` to the current position, as an `Other` value.
    fn other_since(&self, start: usize) -> Option<Val> {
        Some(Val::Other(self.bytes.get(start..self.pos)?.to_vec()))
    }

    fn val(&mut self, depth: u32) -> Option<Val> {
        if depth > MAX_DEPTH {
            return None;
        }
        let start = self.pos;
        match self.u32()? {
            SCV_BOOL => match self.u32()? {
                0 => Some(Val::Bool(false)),
                1 => Some(Val::Bool(true)),
                _ => None,
            },
            SCV_VOID => Some(Val::Void),
            SCV_U32 => Some(Val::U32(self.u32()?)),
            SCV_U64 => Some(Val::U64(u64::from_be_bytes(self.array()?))),
            SCV_I128 => Some(Val::I128(i128::from_be_bytes(self.array()?))),
            SCV_BYTES => Some(Val::Bytes(self.opaque()?)),
            SCV_STRING => Some(Val::String(self.opaque()?)),
            SCV_SYMBOL => Some(Val::Symbol(self.opaque()?)),
            SCV_VEC => {
                if self.u32()? != 1 {
                    return None;
                }
                let n = self.len()?;
                let mut items = Vec::new();
                for _ in 0..n {
                    items.push(self.val(depth + 1)?);
                }
                Some(Val::Vec(items))
            }
            SCV_MAP => {
                if self.u32()? != 1 {
                    return None;
                }
                let n = self.len()?;
                let mut entries = Vec::new();
                for _ in 0..n {
                    let k = self.val(depth + 1)?;
                    let v = self.val(depth + 1)?;
                    entries.push((k, v));
                }
                Some(Val::Map(entries))
            }
            SCV_ADDRESS => self.address(),
            SCV_ERROR => {
                if self.u32()? > 9 {
                    return None;
                }
                self.take(4)?;
                self.other_since(start)
            }
            SCV_I32 => {
                self.take(4)?;
                self.other_since(start)
            }
            SCV_I64 | SCV_TIMEPOINT | SCV_DURATION => {
                self.take(8)?;
                self.other_since(start)
            }
            SCV_U128 => {
                self.take(16)?;
                self.other_since(start)
            }
            SCV_U256 | SCV_I256 => {
                self.take(32)?;
                self.other_since(start)
            }
            _ => None,
        }
    }

    fn address(&mut self) -> Option<Val> {
        match self.u32()? {
            SC_ADDRESS_ACCOUNT => {
                if self.u32()? != PUBLIC_KEY_ED25519 {
                    return None;
                }
                Some(Val::Address(Address::Account(self.array()?)))
            }
            SC_ADDRESS_CONTRACT => Some(Val::Address(Address::Contract(self.array()?))),
            SC_ADDRESS_MUXED_ACCOUNT => {
                let id = u64::from_be_bytes(self.array()?);
                let key = self.array()?;
                Some(Val::Address(Address::MuxedAccount { id, key }))
            }
            // Claimable balance and liquidity pool addresses (CAP-67) are no
            // values a contract holds: the host refuses them.
            _ => None,
        }
    }
}
