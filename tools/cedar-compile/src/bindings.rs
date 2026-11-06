use crate::{Error, Result};
use cedar_policy::EntityUid;
use rule_eval::Signer;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

/// Explicit canonical ScAddress XDR binding. This does not authenticate an address.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "id",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum Address {
    Account([u8; 32]),
    Contract([u8; 32]),
}
impl Address {
    pub fn xdr(&self) -> Vec<u8> {
        match self {
            Self::Account(id) => [vec![0; 8], id.to_vec()].concat(),
            Self::Contract(id) => [vec![0, 0, 0, 1], id.to_vec()].concat(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum SignerBinding {
    Delegated { address: Address },
    External { verifier: Address, key: Vec<u8> },
}
impl SignerBinding {
    pub fn to_signer(&self) -> Signer {
        match self {
            Self::Delegated { address } => Signer::Delegated(address.xdr()),
            Self::External { verifier, key } => Signer::External(verifier.xdr(), key.clone()),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PrincipalBinding {
    pub uid: String,
    pub signer: SignerBinding,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EntityBinding {
    pub uid: String,
    pub address: Address,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ArgumentType {
    Integer,
    Address,
    String,
    Bool,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArgumentBinding {
    pub name: String,
    pub kind: ArgumentType,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallBinding {
    pub action: String,
    pub resource: String,
    pub function: String,
    pub arguments: Vec<ArgumentBinding>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CapBinding {
    pub amount: String,
    pub limit: i64,
    pub period: u32,
}
/// These are Perch state constraints, not Cedar predicates or annotations.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PolicyBinding {
    pub id: String,
    pub cap: Option<CapBinding>,
    pub valid_until: Option<u32>,
    pub generation: Option<u64>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Bindings {
    pub version: u32,
    pub principals: Vec<PrincipalBinding>,
    pub entities: Vec<EntityBinding>,
    pub calls: Vec<CallBinding>,
    pub policies: Vec<PolicyBinding>,
}

pub(crate) fn uid(value: &str, kind: &str) -> Result<EntityUid> {
    let parsed: EntityUid = value
        .parse()
        .map_err(|e| Error(format!("invalid {kind} UID: {e}")))?;
    if value.len() > 128 || parsed.type_name().to_string() != kind || parsed.to_string() != value {
        return Err(Error(format!(
            "expected canonical {kind} UID (at most 128 bytes): {value}"
        )));
    }
    Ok(parsed)
}
pub(crate) fn symbol(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 32
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
}
impl Bindings {
    pub fn from_json(input: &str) -> Result<Self> {
        if input.len() > 65_536 {
            return Err(Error("bindings exceed 65536 bytes".into()));
        }
        let result: Self =
            serde_json::from_str(input).map_err(|e| Error(format!("bindings JSON: {e}")))?;
        result.validate()?;
        Ok(result)
    }
    pub(crate) fn entity(&self, name: &str) -> Result<&EntityBinding> {
        self.entities
            .iter()
            .find(|e| e.uid == name)
            .ok_or_else(|| Error(format!("missing address binding for {name}")))
    }
    pub(crate) fn validate(&self) -> Result<()> {
        if self.version != 1 {
            return Err(Error("unsupported bindings version; expected 1".into()));
        }
        if self.principals.is_empty()
            || self.principals.len() > 16
            || self.entities.len() > 16
            || self.calls.is_empty()
            || self.calls.len() > 16
            || self.policies.is_empty()
            || self.policies.len() > 8
        {
            return Err(Error(
                "binding limits: 1..16 principals/calls, <=16 entities, 1..8 policies".into(),
            ));
        }
        let mut ids = BTreeSet::new();
        for (i, p) in self.principals.iter().enumerate() {
            uid(&p.uid, "Signer")?;
            if !ids.insert(&p.uid) || self.principals[..i].iter().any(|q| q.signer == p.signer) {
                return Err(Error(
                    "duplicate principal or signer alias; bindings must be injective".into(),
                ));
            }
            if let SignerBinding::External { verifier, key } = &p.signer
                && (!matches!(verifier, Address::Contract(_)) || key.is_empty() || key.len() > 256)
            {
                return Err(Error(
                    "external signer requires a contract verifier and 1..256 key bytes".into(),
                ));
            }
        }
        ids.clear();
        for (i, e) in self.entities.iter().enumerate() {
            uid(
                &e.uid,
                match e.address {
                    Address::Account(_) => "Account",
                    Address::Contract(_) => "Contract",
                },
            )?;
            if !ids.insert(&e.uid)
                || self.entities[..i]
                    .iter()
                    .any(|other| other.address == e.address)
            {
                return Err(Error(
                    "duplicate entity or address alias; bindings must be injective".into(),
                ));
            }
        }
        for (i, c) in self.calls.iter().enumerate() {
            uid(&c.action, "Action")?;
            if !matches!(self.entity(&c.resource)?.address, Address::Contract(_))
                || !symbol(&c.function)
                || c.arguments.len() > 8
            {
                return Err(Error(
                    "call requires contract resource, 1..32-byte symbol function, <=8 arguments"
                        .into(),
                ));
            }
            for other in &self.calls[..i] {
                if (other.resource == c.resource
                    && (other.function == c.function || other.action == c.action))
                    || (other.action == c.action && other.function != c.function)
                {
                    return Err(Error("conflicting action/resource/function binding".into()));
                }
            }
            let mut args = BTreeSet::new();
            for arg in &c.arguments {
                if !symbol(&arg.name) || arg.name.starts_with("authRoot") || !args.insert(&arg.name)
                {
                    return Err(Error(
                        "argument names must be unique symbols, excluding reserved authRoot fields"
                            .into(),
                    ));
                }
            }
        }
        ids.clear();
        for p in &self.policies {
            if !ids.insert(&p.id) || p.id.len() > 32 {
                return Err(Error("duplicate or oversized policy binding".into()));
            }
            if let Some(cap) = &p.cap
                && (cap.limit <= 0 || cap.period == 0)
            {
                return Err(Error("cap requires positive limit and period".into()));
            }
        }
        Ok(())
    }
}
