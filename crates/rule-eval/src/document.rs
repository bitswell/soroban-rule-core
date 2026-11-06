//! The document: the subset of a Perch policy document that reaches Perch's
//! lowering, as plain data.
//!
//! The types mirror `perch_ir`'s (`crates/perch-ir/src/doc.rs` of
//! `bitswell-hq/stellar-registry__perch` at `dff2a73`) with identifiers as
//! bytes: an address is its `ScAddress` XDR, a key its decoded bytes, and a
//! function name or a string its bytes. Decoding strkeys and hex is the
//! caller's job. What the lowering never reads is left out: a document's
//! version and network, a rule's name, a cap's token (validation makes it the
//! rule's own contract), and the parts of the recovery configuration other
//! than the contracts it names. Self-authenticating principals, which Perch's
//! lowering refuses, are not part of the subset.

use alloc::vec::Vec;

use crate::rule::AuthRoot;
use crate::signer::Signer;

/// Where a document rule applies.
pub enum Scope {
    /// Calls to this contract, as its `ScAddress` XDR.
    Contract(Vec<u8>),
    /// Calls to the account itself.
    SelfAdmin,
}

/// Who a document rule authorizes, by the ids of declared signers.
pub enum Principals {
    /// Every one of these signers must authorize.
    All(Vec<Vec<u8>>),
    /// At least this many of these signers must authorize.
    Threshold(Vec<Vec<u8>>, u32),
}

/// A predicate on one argument of a call.
pub enum Pred {
    /// The argument is the account's own address.
    IsSelf,
    /// The argument is this address, as its `ScAddress` XDR.
    AddressEq(Vec<u8>),
    /// The argument is a string of at most 256 bytes equal to one of these.
    StringIn(Vec<Vec<u8>>),
    /// The argument is a string that starts with these bytes.
    StringPrefix(Vec<u8>),
    /// The argument is this `u32`.
    U32Eq(u32),
}

/// A predicate on the argument at `index`, counting from zero.
pub struct ArgConstraint {
    pub index: u32,
    pub pred: Pred,
}

/// A rule's cumulative spending cap: at most `limit` within `period_ledgers`
/// consecutive ledgers, on the rule's own contract.
pub struct DocCap {
    pub limit: i128,
    pub period_ledgers: u32,
}

/// A document rule.
pub struct DocRule {
    pub scope: Scope,
    pub principals: Principals,
    /// The functions the rule covers, or every function when `None`.
    pub functions: Option<Vec<Vec<u8>>>,
    /// Predicates on the call's arguments, or none when `None`.
    pub args: Option<Vec<ArgConstraint>>,
    /// The ledger at which the rule stops authorizing, if it has one.
    pub not_after_ledger: Option<u32>,
    pub cap: Option<DocCap>,
    /// Optional exact authorization root for ordinary contract rules.
    /// Self-admin lowering ignores this field to preserve eligibility;
    /// document validators must reject it on self-admin input.
    pub auth_root: Option<AuthRoot>,
}

/// A declared signer: the id rules name it by, and the signer.
pub struct SignerDecl {
    pub id: Vec<u8>,
    pub signer: Signer,
}

/// The contracts a recovery configuration's zero-knowledge factor names.
pub struct ZkFactor {
    pub adapter: Vec<u8>,
    pub pool: Vec<u8>,
}

/// The contracts a recovery configuration names: its controller and, when
/// it has a zero-knowledge factor, that factor's adapter and pool.
pub struct Recovery {
    pub controller: Vec<u8>,
    pub zk: Option<ZkFactor>,
}

/// A document: declared signers, rules and, optionally, a recovery
/// configuration.
pub struct Doc {
    pub signers: Vec<SignerDecl>,
    pub rules: Vec<DocRule>,
    pub recovery: Option<Recovery>,
}
