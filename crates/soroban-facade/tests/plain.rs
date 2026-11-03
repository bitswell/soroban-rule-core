//! The plain implementation: storage as a map, and `require_auth` against
//! the addresses that have authorized.

use soroban_facade::{Address, Auth, Durability, PlainHost, Refusal, Storage, Val};

fn key(s: &str) -> Val {
    Val::Symbol(s.as_bytes().to_vec())
}

#[test]
fn storage_is_a_map_by_durability_and_key() {
    let mut h = PlainHost::new();
    assert_eq!(h.get(Durability::Persistent, &key("a")), Ok(None));
    h.set(Durability::Persistent, &key("a"), &Val::U32(1))
        .unwrap();
    h.set(Durability::Temporary, &key("a"), &Val::U32(2))
        .unwrap();
    assert_eq!(
        h.get(Durability::Persistent, &key("a")),
        Ok(Some(Val::U32(1)))
    );
    assert_eq!(
        h.get(Durability::Temporary, &key("a")),
        Ok(Some(Val::U32(2)))
    );
    assert_eq!(h.has(Durability::Instance, &key("a")), Ok(false));
    h.set(Durability::Persistent, &key("a"), &Val::U32(3))
        .unwrap();
    assert_eq!(
        h.get(Durability::Persistent, &key("a")),
        Ok(Some(Val::U32(3)))
    );
    h.remove(Durability::Persistent, &key("a")).unwrap();
    h.remove(Durability::Persistent, &key("a")).unwrap();
    assert_eq!(h.has(Durability::Persistent, &key("a")), Ok(false));
    assert_eq!(
        h.get(Durability::Temporary, &key("a")),
        Ok(Some(Val::U32(2)))
    );
}

#[test]
fn a_key_holding_a_muxed_address_is_refused() {
    let muxed = Val::Address(Address::MuxedAccount {
        id: 1,
        key: [1; 32],
    });
    let mut h = PlainHost::new();
    for k in [
        muxed.clone(),
        Val::Vec(vec![muxed.clone()]),
        Val::Map(vec![(Val::U32(1), muxed.clone())]),
    ] {
        assert_eq!(
            h.set(Durability::Persistent, &k, &Val::U32(1)),
            Err(Refusal::MuxedAddress)
        );
        assert_eq!(
            h.get(Durability::Persistent, &k),
            Err(Refusal::MuxedAddress)
        );
        assert_eq!(h.has(Durability::Temporary, &k), Err(Refusal::MuxedAddress));
        assert_eq!(
            h.remove(Durability::Instance, &k),
            Err(Refusal::MuxedAddress)
        );
    }
    h.set(Durability::Persistent, &key("m"), &muxed).unwrap();
    assert_eq!(h.get(Durability::Persistent, &key("m")), Ok(Some(muxed)));
}

#[test]
fn require_auth_holds_for_authorized_addresses() {
    let a = Address::Contract([1; 32]);
    let b = Address::Contract([2; 32]);
    let mut h = PlainHost::new();
    h.authorize(a.clone());
    assert_eq!(h.require_auth(&a), Ok(()));
    assert_eq!(h.require_auth(&b), Err(Refusal::Unauthorized));
    assert_eq!(
        h.require_auth(&Address::MuxedAccount {
            id: 1,
            key: [1; 32]
        }),
        Err(Refusal::MuxedAddress)
    );
    assert_eq!(h.required, vec![a, b]);
}
