import RuleCore.Vocab.Chain

/-!
# Documents

A Perch policy document, as far as Perch's lowering reads it, and what it
means on chain. The types mirror `perch_ir`'s
(`crates/perch-ir/src/doc.rs` of `bitswell-hq/stellar-registry__perch` at
`dff2a73`), with identifiers as bytes: an address is its `ScAddress` XDR, a
key its decoded bytes, a function name or a string its bytes. What the
lowering never reads is left out: a document's version and network, a rule's
name, a cap's token (Perch's validation makes it the rule's own contract), and
the parts of a recovery configuration other than the contracts it names.
Self-authenticating principals, which Perch's lowering refuses, are not part
of the subset.

## Meaning

The meaning is written from what Perch's smart account installs for a
document on OpenZeppelin's smart account (`theahaco/stellar-contracts-OZ` at
`33726766`, the revision Perch pins) and how that account checks an
authorization. It does not mention the lowering.

* A rule applies to calls to its scope's contract, the account itself for a
  self-admin scope (OpenZeppelin's `CallContract` context rule type).
* Its functions are those it lists, or every function when it lists none
  (Perch's `FnIn` program leaf, absent when the rule lists none).
* A capped rule allows only a `transfer` whose argument 2 is an `i128`:
  OpenZeppelin's spending-limit policy meters exactly those calls and refuses
  every other (`policies/spending_limit.rs`, lines 242–245 and 297–301).
* Each argument predicate holds of the argument at its index, as Perch's
  program leaves read it (`crates/perch-program/src/leaf.rs`): `isSelf` and
  `addressEq` an address equal to the account or to the one named; `u32Eq` the
  `u32` named, which a shell gives as `other` of its `ScVal` XDR (`u32Xdr`);
  `stringIn` a string of at most 256 bytes equal to one of the values, so a
  value over 256 bytes never matches; `stringPrefix` a string starting with
  the prefix.
* `all` principals need every signer they name to be authenticated,
  `threshold _ m` at least `m` of them, each counted once.
* A rule stops authorizing at its not-after ledger: it authorizes at a ledger
  `now` only when `now` is before it.

`Doc.allows` is local screening without roots, time, generation or caps.
`Doc.checkAuth` additionally checks ordinary rules' exact entry-root constraints. `Doc.checkAuth`
checks an authorization as OpenZeppelin's `do_check_auth` does over the rules
installed for the document (`Doc.installed`): one rule per context, each live
and allowing its context, every authenticated signer named by a chosen rule,
then each capped rule's spend charged with the cap model of
`RuleCore.Model.Cap`, which mirrors OpenZeppelin's spending-limit policy. The
recovery rule, installed when the document configures recovery, is checked by
the recovery controller against its own state; `Doc.checkAuth` takes that
check as a parameter `ctl`.

## Validity

`Doc.Valid` is what the theorems take of a document. Every document Perch's
validation (`crates/perch-ir/src/validate.rs`) and document compiler accept
satisfies it.
-/

namespace RuleCore.Document

open RuleCore RuleCore.Chain

/-- Where a document rule applies. -/
inductive Scope where
  /-- Calls to this contract, as its `ScAddress` XDR. -/
  | contract (address : Bytes)
  /-- Calls to the account itself. -/
  | selfAdmin
  deriving DecidableEq, Repr

/-- Who a document rule authorizes, by the ids of declared signers. -/
inductive Principals where
  /-- Every one of these signers. -/
  | all (ids : List Bytes)
  /-- At least `m` of these signers. -/
  | threshold (ids : List Bytes) (m : UInt32)
  deriving DecidableEq, Repr

def Principals.ids : Principals → List Bytes
  | .all ids => ids
  | .threshold ids _ => ids

/-- A predicate on one argument of a call. -/
inductive Pred where
  | isSelf
  | addressEq (address : Bytes)
  | stringIn (values : List Bytes)
  | stringPrefix (pre : Bytes)
  | u32Eq (v : UInt32)
  deriving DecidableEq, Repr

/-- A predicate on the argument at `index`, counting from zero. -/
structure ArgConstraint where
  index : UInt32
  pred : Pred
  deriving DecidableEq, Repr

/-- A cumulative spending cap: at most `limit` within `periodLedgers`
consecutive ledgers, on the rule's own contract. -/
structure Cap where
  limit : I128
  periodLedgers : UInt32
  deriving DecidableEq, Repr

structure Rule where
  scope : Scope
  principals : Principals
  /-- The functions covered, or every function when `none`. -/
  functions : Option (List Bytes) := none
  /-- Predicates on the call's arguments, or none when `none`. -/
  args : Option (List ArgConstraint) := none
  /-- The ledger at which the rule stops authorizing. -/
  notAfterLedger : Option UInt32 := none
  cap : Option Cap := none
  authRoot : Option Chain.AuthRoot := none
  deriving DecidableEq, Repr

/-- A declared signer: the id rules name it by, and the signer. -/
structure SignerDecl where
  id : Bytes
  signer : Signer
  deriving DecidableEq, Repr

/-- The contracts a zero-knowledge recovery factor names. -/
structure ZkFactor where
  adapter : Bytes
  pool : Bytes
  deriving DecidableEq, Repr

/-- The contracts a recovery configuration names. -/
structure Recovery where
  controller : Bytes
  zk : Option ZkFactor := none
  deriving DecidableEq, Repr

structure Doc where
  signers : List SignerDecl
  rules : List Rule
  recovery : Option Recovery := none
  deriving DecidableEq, Repr

/-! ## Names and encodings -/

/-- The function name `transfer`, as its bytes. -/
def transfer : Bytes := [116, 114, 97, 110, 115, 102, 101, 114]

/-- The function name `apply_doc`, as its bytes. -/
def applyDoc : Bytes := [97, 112, 112, 108, 121, 95, 100, 111, 99]

/-- The longest string Perch's `stringIn` compares (`MAX_STR_ARG_LEN` in
`crates/perch-program/src/leaf.rs`, line 21). -/
def maxStringLen : Nat := 256

/-- The `ScVal` XDR of the `u32` value `v`: the discriminant `SCV_U32`, which is
3, then the value, each as four big-endian bytes (`Stellar-contract.x`;
`stellar-xdr` 30.0.0, `src/generated/sc_val_type.rs` line 81, and its `u32`
encoding, `to_be_bytes`, in `src/generated.rs` line 821). -/
def u32Xdr (v : UInt32) : Bytes :=
  [0, 0, 0, 3, UInt8.ofNat (v.toNat / 16777216), UInt8.ofNat (v.toNat / 65536 % 256),
    UInt8.ofNat (v.toNat / 256 % 256), UInt8.ofNat (v.toNat % 256)]

/-! ## Signers -/

/-- The signer declared under `id`: the first declaration with that id. -/
def Doc.resolve (d : Doc) (id : Bytes) : Option Signer :=
  (d.signers.find? fun s => decide (s.id = id)).map (·.signer)

/-- The signers `p` names, in order. An id no signer is declared under names
none; Perch's validation refuses one (`UnknownSignerRef`). -/
def Doc.named (d : Doc) (p : Principals) : List Signer :=
  p.ids.filterMap d.resolve

/-- The signer requirement of `p` under the authenticated signers `auth`. -/
def Doc.signed (d : Doc) (p : Principals) (auth : List Signer) : Bool :=
  match p with
  | .all _ => (d.named p).all fun s => decide (s ∈ auth)
  | .threshold _ m =>
    decide (m.toNat ≤ ((d.named p).eraseDups.filter fun s => decide (s ∈ auth)).length)

/-! ## Meaning without time -/

/-- The contract a rule of scope `s` applies to on the account `acct`. -/
def Scope.contractOn (s : Scope) (acct : Bytes) : Bytes :=
  match s with
  | .contract a => a
  | .selfAdmin => acct

/-- Whether predicate `p` holds of an argument, `none` when the call has no
argument at its index. -/
def Pred.holds (acct : Bytes) : Pred → Option Val → Bool
  | .isSelf, arg => decide (arg = some (.address acct))
  | .addressEq a, arg => decide (arg = some (.address a))
  | .stringIn values, arg =>
    match arg with
    | some (.string s) => decide (s.length ≤ maxStringLen ∧ s ∈ values)
    | _ => false
  | .stringPrefix pre, arg =>
    match arg with
    | some (.string s) => decide (pre <+: s)
    | _ => false
  | .u32Eq v, arg => decide (arg = some (.other (u32Xdr v)))

/-- Whether rule `r` covers a call to `function` of `contract`. -/
def Rule.covers (r : Rule) (acct contract function : Bytes) : Bool :=
  decide (contract = r.scope.contractOn acct) &&
    (match r.functions with
      | none => true
      | some fs => decide (function ∈ fs)) &&
    (match r.cap with
      | none => true
      | some _ => decide (function = transfer))

/-- Whether a call's arguments satisfy rule `r`: every argument predicate
holds, and a capped rule's call has an `i128` at argument 2. -/
def Rule.argsHold (r : Rule) (acct : Bytes) (args : List Val) : Bool :=
  (r.args.getD []).all (fun c => c.pred.holds acct args[c.index.toNat]?) &&
    (match r.cap with
      | none => true
      | some _ =>
        match (args[2]? : Option Val) with
        | some (.i128 _) => true
        | _ => false)

/-- Whether document rule `r` allows context `c` under `auth`, without time,
generation or caps. No rule allows a contract creation. -/
def Doc.ruleAllows (d : Doc) (acct : Bytes) (r : Rule) (c : Context) (auth : List Signer) :
    Bool :=
  match c with
  | .call contract function args =>
    r.covers acct contract function && r.argsHold acct args && d.signed r.principals auth
  | .create _ => false

/-- Whether some rule of `d` allows `c` under `auth`. -/
def Doc.allows (d : Doc) (acct : Bytes) (c : Context) (auth : List Signer) : Bool :=
  d.rules.any fun r => d.ruleAllows acct r c auth

/-! ## Authorization -/

/-- Self-administration retains its unrestricted eligibility. Validators
reject root constraints on self-admin input; the total semantics ignores them. -/
def Rule.effectiveRoot (r : Rule) : Option Chain.AuthRoot :=
  match r.scope with
  | .contract _ => r.authRoot
  | .selfAdmin => none

def Rule.rootMatches (r : Rule) (root : Option Context) : Bool :=
  match r.effectiveRoot with
  | none => true
  | some expected => match root with
    | some c => expected.matches c
    | none => false

/-- Rule `r` authorizes at ledger `now`: it has no not-after ledger, or `now` is
before it. -/
def Rule.live (r : Rule) (now : Nat) : Bool :=
  match r.notAfterLedger with
  | none => true
  | some x => decide (now < x.toNat)

/-- A rule installed for a document: one of its rules, or the recovery rule. -/
inductive Installed where
  | rule (r : Rule)
  | recovery
  deriving DecidableEq, Repr

/-- The rules installed for `d`, in order: its rules, then the recovery rule
when it configures recovery (`crates/perch-smart-account/src/rules.rs`,
lines 135–164). -/
def Doc.installed (d : Doc) : List Installed :=
  d.rules.map .rule ++ (if d.recovery.isSome then [.recovery] else [])

/-- A call to a contract of the account `acct`, any function. -/
def onAccount (acct : Bytes) : Context → Bool
  | .call contract _ _ => decide (contract = acct)
  | .create _ => false

/-- The first pass for one context and its chosen installed rule: the rule
exists, is live, carries the current generation when the document was issued
under one (`issued`), and allows the context. The recovery rule allows a call
to the account that the controller's check `ctl` accepts. -/
def Doc.validates (d : Doc) (acct : Bytes) (ctl : Context → List Signer → Bool)
    (issued : Option UInt64) (a : Chain.Authorization) (x : Context × UInt32) : Bool :=
  match d.installed[x.2.toNat]? with
  | some (.rule r) =>
    r.live a.now.toNat && (issued.all fun g => decide (g = a.generation)) &&
      (r.rootMatches a.contexts.head? && d.ruleAllows acct r x.1 a.auth)
  | some .recovery => onAccount acct x.1 && ctl x.1 a.auth
  | none => false

/-- Signer `s` is named by a document rule some choice selects. The recovery
rule has no signers. -/
def Doc.signerChosen (d : Doc) (choices : List UInt32) (s : Signer) : Bool :=
  choices.any fun j =>
    match d.installed[j.toNat]? with
    | some (.rule r) => decide (s ∈ d.named r.principals)
    | _ => false

/-- The amount a capped rule's call spends: its `i128` argument 2. -/
def spendAmount : Context → Option Int
  | .call _ _ args =>
    match (args[2]? : Option Val) with
    | some (.i128 v) => some v.toInt
    | _ => none
  | .create _ => none

/-- The third pass for one context and its chosen installed rule: a capped
rule's record charged with the context's amount, as OpenZeppelin's
spending-limit policy charges its record. -/
def Doc.charge (d : Doc) (now : Nat) (records : List RuleCore.Cap.Record)
    (x : Context × UInt32) : Option (List RuleCore.Cap.Record) :=
  match d.installed[x.2.toNat]? with
  | some (.rule r) =>
    match r.cap with
    | some k =>
      match spendAmount x.1, records[x.2.toNat]? with
      | some amount, some rec =>
        match (RuleCore.Cap.Params.mk k.limit.toInt k.periodLedgers.toNat).check rec now amount with
        | .ok rec' => some (records.set x.2.toNat rec')
        | .error _ => none
      | _, _ => none
    | none => some records
  | some .recovery => some records
  | none => none

/-- The records after authorization `a` of the rules installed for `d`, one
record per installed rule, or `none` when it is refused. `ctl` is the recovery
controller's check of the recovery rule's contexts, and `issued` the generation
a scoped document was issued under. -/
def Doc.checkAuth (d : Doc) (acct : Bytes) (ctl : Context → List Signer → Bool)
    (issued : Option UInt64) (records : List RuleCore.Cap.Record) (a : Chain.Authorization) :
    Option (List RuleCore.Cap.Record) :=
  if a.choices.length = a.contexts.length ∧ records.length = d.installed.length ∧
      (a.contexts.zip a.choices).all (d.validates acct ctl issued a) ∧
      a.auth.all (d.signerChosen a.choices) then
    (a.contexts.zip a.choices).foldlM (d.charge a.now.toNat) records
  else none

/-! ## Validity -/

/-- What the theorems take of a document rule. -/
structure Rule.Valid (d : Doc) (r : Rule) : Prop where
  /-- The signers an `all` rule names are distinct: Perch's validation refuses a
  repeated id in principals, a repeated signer id and one key under two ids
  (`DuplicatePrincipalSigner`, `DuplicateSignerId`, `DuplicateSignerKey`;
  `validate.rs` lines 718, 737, 766 and 824). -/
  allDistinct : ∀ ids, r.principals = .all ids → (d.named r.principals).Nodup
  /-- An `all` rule names fewer than `2^32` signers: Perch's document compiler
  accepts at most 8 (`MAX_DOC_SIGNERS`, `crates/perch-doc-compiler/src/lib.rs`
  line 57). -/
  allFits : ∀ ids, r.principals = .all ids → (d.named r.principals).length < 2 ^ 32
  /-- A not-after ledger is not 0: Perch's validation refuses one
  (`ZeroNotAfterLedger`, `validate.rs` line 971). -/
  notAfterPos : ∀ x, r.notAfterLedger = some x → 0 < x.toNat

/-- What the theorems take of a document: every rule is valid. -/
def Doc.Valid (d : Doc) : Prop := ∀ r ∈ d.rules, Rule.Valid d r

end RuleCore.Document
