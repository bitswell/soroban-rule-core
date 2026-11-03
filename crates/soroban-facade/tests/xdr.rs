//! The facade's XDR: what it writes, what it reads back and what it refuses.

use soroban_facade::xdr::{MAX_DEPTH, address_xdr, decode, encode};
use soroban_facade::{Address, Val, val_to_rule_eval};

fn values() -> Vec<Val> {
    let muxed = Address::MuxedAccount {
        id: 7,
        key: [1; 32],
    };
    vec![
        Val::Void,
        Val::Bool(true),
        Val::U32(u32::MAX),
        Val::U64(u64::MAX),
        Val::I128(i128::MIN),
        Val::I128(-1),
        Val::Bytes(vec![1, 2, 3]),
        Val::String(b"abcd".to_vec()),
        Val::Symbol(b"transfer".to_vec()),
        Val::Address(Address::Account([2; 32])),
        Val::Address(Address::Contract([3; 32])),
        Val::Address(muxed),
        Val::Vec(vec![Val::U32(1), Val::Vec(vec![])]),
        Val::Map(vec![(Val::U32(1), Val::Bool(false))]),
        // An i64, as its XDR.
        Val::Other([&[0, 0, 0, 6][..], &7i64.to_be_bytes()].concat()),
    ]
}

#[test]
fn every_value_reads_back_as_itself() {
    for v in values() {
        assert_eq!(decode(&encode(&v)), Some(v.clone()), "{v:?}");
    }
}

#[test]
fn bytes_pad_to_four() {
    for n in 0..9 {
        let x = encode(&Val::Bytes(vec![0xff; n]));
        assert_eq!(x.len(), 8 + n.div_ceil(4) * 4, "{n} bytes");
    }
}

#[test]
fn trailing_bytes_are_refused() {
    let mut x = encode(&Val::U32(1));
    x.push(0);
    assert_eq!(decode(&x), None);
}

#[test]
fn nonzero_padding_is_refused() {
    let mut x = encode(&Val::Bytes(vec![1]));
    *x.last_mut().unwrap() = 1;
    assert_eq!(decode(&x), None);
}

#[test]
fn a_bool_is_zero_or_one() {
    assert_eq!(decode(&[0, 0, 0, 0, 0, 0, 0, 2]), None);
}

#[test]
fn an_absent_vector_or_map_is_refused() {
    assert_eq!(decode(&[0, 0, 0, 16, 0, 0, 0, 0]), None);
    assert_eq!(decode(&[0, 0, 0, 17, 0, 0, 0, 0]), None);
}

/// A contract instance, the two ledger keys, and claimable balance and
/// liquidity pool addresses are no values a contract holds.
#[test]
fn kinds_no_contract_holds_are_refused() {
    assert_eq!(decode(&[0, 0, 0, 20]), None);
    assert_eq!(decode(&[[0, 0, 0, 21], [0; 4], [0; 4]].concat()), None);
    let claimable = [&[0, 0, 0, 18, 0, 0, 0, 3, 0, 0, 0, 0][..], &[5; 32]].concat();
    assert_eq!(decode(&claimable), None);
    let pool = [&[0, 0, 0, 18, 0, 0, 0, 4][..], &[6; 32]].concat();
    assert_eq!(decode(&pool), None);
    assert_eq!(decode(&[0, 0, 0, 22]), None);
}

#[test]
fn nesting_past_the_limit_is_refused() {
    let mut v = Val::Void;
    for _ in 0..MAX_DEPTH {
        v = Val::Vec(vec![v]);
    }
    assert_eq!(decode(&encode(&v)), Some(v.clone()));
    let deeper = Val::Vec(vec![v]);
    assert_eq!(decode(&encode(&deeper)), None);
}

#[test]
fn addresses_are_their_scaddress_xdr() {
    let a = Address::Contract([9; 32]);
    assert_eq!(address_xdr(&a), [&[0, 0, 0, 1][..], &[9; 32]].concat());
    assert_eq!(
        encode(&Val::Address(a.clone())),
        [&[0, 0, 0, 18][..], &address_xdr(&a)].concat()
    );
    let account = Address::Account([4; 32]);
    assert_eq!(
        address_xdr(&account),
        [&[0, 0, 0, 0, 0, 0, 0, 0][..], &[4; 32]].concat()
    );
}

/// A `u32` reaches `rule-eval` as `Other` of the XDR Perch's lowering
/// compares a `u32` argument with.
#[test]
fn a_u32_is_what_the_lowering_compares_with() {
    for v in [0, 1, 7, 256, u32::MAX] {
        let rule_eval::Val::Other(x) = val_to_rule_eval(&Val::U32(v)) else {
            panic!("a u32 is Other")
        };
        assert_eq!(x, rule_eval::u32_xdr(v), "{v}");
    }
}
