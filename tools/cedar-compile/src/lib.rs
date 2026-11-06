//! Experimental OFF-CHAIN Cedar frontend. No formal compiler correctness claim.
//! See ../README.md for the exact fragment, trust boundary and checked domain.
mod bindings;
mod compiler;
mod request;

pub use bindings::*;
use cedar_policy::PolicySet;
pub use request::Comparison;
use rule_eval::{Cond, Functions, Rule, Val};
use serde_json::{Value, json};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(pub String);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;
pub const MAX_RANGE_VALUES: i128 = 256;

pub struct Compiled {
    pub(crate) source: PolicySet,
    pub(crate) bindings: Bindings,
    pub(crate) ids: Vec<String>,
    pub(crate) rules: Vec<Rule>,
}
impl Compiled {
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }
    pub fn policy_ids(&self) -> &[String] {
        &self.ids
    }
    /// Diagnostic JSON, NOT a Perch installation document, commitment or wire ABI.
    /// The library's `rules()` returns the actual existing rule-eval representation.
    pub fn emitted_json(&self) -> Value {
        let rows: Vec<_> = self.rules.iter().zip(&self.ids).map(|(r,id)| {
            let Functions::Only(functions) = &r.functions else { unreachable!() };
            let conditions: Vec<_> = r.conds.iter().map(|c| match c {
                Cond::ArgEq(i,v) => json!({"ArgEq":{"index":i,"value":val_json(v)}}),
                Cond::ArgIn(i,vs) => json!({"ArgIn":{"index":i,"values":vs.iter().map(val_json).collect::<Vec<_>>()}}),
                _ => unreachable!(),
            }).collect();
            let signer = self.bindings.principals.iter().find(|p| rule_eval::signer_eq(&p.signer.to_signer(), &r.signers[0])).unwrap();
            json!({"policy_id":id,"contract_xdr":hex(&r.contract),
                "functions":functions.iter().map(|f|String::from_utf8_lossy(f)).collect::<Vec<_>>(),
                "conditions":conditions,"signer":signer,"threshold":r.threshold,
                "auth_root":r.auth_root.as_ref().map(|root|json!({"contract_xdr":hex(&root.contract),"function":String::from_utf8_lossy(&root.function)})),
                "cap":r.cap.as_ref().map(|c|json!({"amount_arg":c.amount_arg,"limit":c.limit.to_string(),"period":c.period})),
                "valid_until":r.valid_until,"generation":r.generation})
        }).collect();
        json!({"format":"cedar-to-rule-core-diagnostic-v1","cedar_version":"4.14.1","rules":rows})
    }
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn val_json(v: &Val) -> Value {
    match v {
        Val::I128(i) => json!({"I128":i.to_string()}),
        Val::Address(a) => json!({"AddressXdr":hex(a)}),
        Val::String(s) => json!({"String":String::from_utf8_lossy(s)}),
        Val::Bool(b) => json!({"Bool":b}),
        _ => unreachable!(),
    }
}
/// Parse with pinned official Cedar, reject the WHOLE set on any unsupported
/// construct/binding, then emit existing Rule/Cond/AuthRoot values.
pub fn compile(source: &str, bindings: Bindings) -> Result<Compiled> {
    compiler::compile(source, bindings)
}
