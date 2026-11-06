#![allow(dead_code)]
use cedar_to_rule_core::{Address, Bindings, Compiled, compile};
use rule_eval::{Context, Signer, SpendRecord, Val};
pub const SOURCE: &str = include_str!("../../fixtures/guess-transfer.cedar");
pub const BINDINGS: &str = include_str!("../../fixtures/bindings.json");
pub fn bindings() -> Bindings {
    Bindings::from_json(BINDINGS).unwrap()
}
pub fn compiled() -> Compiled {
    compile(SOURCE, bindings()).unwrap()
}
pub fn account(n: u8) -> Vec<u8> {
    Address::Account([n; 32]).xdr()
}
pub fn contract(n: u8) -> Vec<u8> {
    Address::Contract([n; 32]).xdr()
}
pub fn signer(n: u8) -> Signer {
    Signer::Delegated(account(n))
}
pub fn call(c: u8, f: &str, args: Vec<Val>) -> Context {
    Context::Call {
        contract: contract(c),
        function: f.as_bytes().to_vec(),
        args,
    }
}
pub fn guess(n: i128) -> Context {
    call(3, "guess", vec![Val::I128(n)])
}
pub fn transfer(n: i128) -> Context {
    transfer_to(n, 1, 3)
}
pub fn transfer_to(n: i128, from: u8, to: u8) -> Context {
    call(
        4,
        "transfer",
        vec![
            Val::Address(account(from)),
            Val::Address(contract(to)),
            Val::I128(n),
        ],
    )
}
pub fn records() -> Vec<SpendRecord> {
    (0..2)
        .map(|_| SpendRecord {
            total: 0,
            history: vec![],
        })
        .collect()
}
pub fn snapshot(records: &[SpendRecord]) -> Vec<(i128, Vec<(u32, i128)>)> {
    records
        .iter()
        .map(|r| {
            (
                r.total,
                r.history.iter().map(|h| (h.ledger, h.amount)).collect(),
            )
        })
        .collect()
}
