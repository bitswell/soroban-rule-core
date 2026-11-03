import RuleCore.Vocab.Document

/-!
# The lowering

The rules a document lowers to, as `crates/rule-lower` computes them, written
for the proofs to compare with the document's meaning.

`Doc.lower d acct` is the admin document's lowering on the account `acct`:
one rule per document rule (`Doc.lowerRule`), then the recovery rule
(`recoveryRule`) when `d` configures recovery. A document rule lowers to

* its scope's contract, or `acct` for a self-admin scope;
* its functions, or the wildcard when it lists none; a capped rule's functions
  are `transfer` when the rule covers it and none otherwise;
* one condition per argument predicate (`Pred.lower`), then, for a capped
  rule, `amountCond`, that argument 2 is an `i128`: every `i128` is at most
  `i128Max`;
* the signers its principals name, with threshold their number for `all`
  (`u32::MAX` if that does not fit a `u32`) and `m` for `threshold _ m`;
* its cap, reading the amount from argument 2;
* the last ledger one before its not-after ledger, as OpenZeppelin's
  `valid_until` is the last ledger a rule authorizes in (Perch's
  `perch_compile`, `crates/perch-compile/src/lib.rs` line 256).

The recovery rule is a sound over-approximation of what Perch installs: the
account's `apply_doc`, with no conditions, no signers and threshold 0. On chain
the recovery controller allows only the completion of an authorized recovery
attempt through that rule.

A scoped document is a grant the owner issues under the admin document.
`Doc.lowerScoped d acct ex g` lowers it like the admin document, each rule
carrying the generation `g`, and refuses it when it configures recovery or
when a rule has a self-admin scope or a contract scope on `acct` or on a
contract of `ex`. `Doc.excluded admin acct` is the excluded set the admin
document gives: the account, its recovery controller, and its zero-knowledge
factor's adapter and pool.
-/

namespace RuleCore.Document

open RuleCore RuleCore.Chain

/-- The largest `i128`, `2^127 - 1`. -/
def i128Max : I128 := BitVec.ofInt 128 (2 ^ 127 - 1)

/-- The argument OpenZeppelin's spending-limit policy reads a transfer's amount
from. -/
def amountArg : UInt32 := 2

/-- The condition that argument 2 is an `i128`. -/
def amountCond : Cond := .argI128AtMost amountArg i128Max

/-- Whether a rule's functions cover `transfer`. -/
def coversTransfer : Option (List Bytes) → Bool
  | none => true
  | some fs => decide (transfer ∈ fs)

/-- The functions rule `r` lowers to. -/
def Rule.lowerFunctions (r : Rule) : Functions :=
  match r.cap with
  | some _ => .only (if coversTransfer r.functions then [transfer] else [])
  | none =>
    match r.functions with
    | some fs => .only fs
    | none => .anyExcept []

/-- The condition predicate `p` on argument `i` lowers to. -/
def Pred.lower (acct : Bytes) (i : UInt32) : Pred → Cond
  | .isSelf => .argEq i (.address acct)
  | .addressEq a => .argEq i (.address a)
  | .stringIn values =>
    .argIn i ((values.filter fun v => decide (v.length ≤ maxStringLen)).map .string)
  | .stringPrefix pre => .argStrPrefix i pre
  | .u32Eq v => .argEq i (.other (u32Xdr v))

/-- The condition an argument constraint lowers to. -/
def ArgConstraint.lower (acct : Bytes) (c : ArgConstraint) : Cond :=
  c.pred.lower acct c.index

/-- The conditions rule `r` lowers to. -/
def Rule.lowerConds (r : Rule) (acct : Bytes) : List Cond :=
  (r.args.getD []).map (ArgConstraint.lower acct) ++
    (match r.cap with
      | some _ => [amountCond]
      | none => [])

/-- The threshold principals `p` lower to. -/
def Doc.threshold (d : Doc) (p : Principals) : UInt32 :=
  match p with
  | .all _ => UInt32.ofNat (min (d.named p).length 4294967295)
  | .threshold _ m => m

/-- The cap a document cap lowers to. -/
def Cap.lower (k : Cap) : Chain.Cap :=
  ⟨k.limit, k.periodLedgers, amountArg⟩

/-- The last ledger a rule with not-after ledger `x` authorizes in. -/
def lastLedger (x : UInt32) : UInt32 :=
  UInt32.ofNat (x.toNat - 1)

/-- The rule document rule `r` lowers to on `acct`, carrying `gen`. -/
def Doc.lowerRule (d : Doc) (acct : Bytes) (gen : Option UInt64) (r : Rule) : Chain.Rule where
  contract := r.scope.contractOn acct
  functions := r.lowerFunctions
  conds := r.lowerConds acct
  signers := d.named r.principals
  threshold := d.threshold r.principals
  cap := r.cap.map Cap.lower
  validUntil := r.notAfterLedger.map lastLedger
  generation := gen

/-- The recovery rule on `acct`. -/
def recoveryRule (acct : Bytes) : Chain.Rule where
  contract := acct
  functions := .only [applyDoc]
  conds := []
  signers := []
  threshold := 0

/-- The rules the rules of `d` lower to on `acct`, each carrying `gen`. -/
def Doc.lowerRules (d : Doc) (acct : Bytes) (gen : Option UInt64) : Chain.RuleSet :=
  d.rules.map (d.lowerRule acct gen)

/-- The recovery rule when `d` configures recovery. -/
def Doc.recoveryRules (d : Doc) (acct : Bytes) : Chain.RuleSet :=
  match d.recovery with
  | some _ => [recoveryRule acct]
  | none => []

/-- The rules the admin document `d` lowers to on `acct`. -/
def Doc.lower (d : Doc) (acct : Bytes) : Chain.RuleSet :=
  d.lowerRules acct none ++ d.recoveryRules acct

/-- The rule an installed rule lowers to. -/
def Installed.lower (d : Doc) (acct : Bytes) (gen : Option UInt64) : Installed → Chain.Rule
  | .rule r => d.lowerRule acct gen r
  | .recovery => recoveryRule acct

/-- The recovery controller's check read as the recovery rule's lowering reads
it: every call to `apply_doc`, under any signers. -/
def applyDocCheck (c : Context) (_ : List Signer) : Bool :=
  match c with
  | .call _ function _ => decide (function = applyDoc)
  | .create _ => false

/-! ## Scoped documents -/

/-- The excluded set of the admin document `admin` on `acct`. -/
def Doc.excluded (admin : Doc) (acct : Bytes) : List Bytes :=
  acct ::
    match admin.recovery with
    | none => []
    | some rc =>
      rc.controller ::
        match rc.zk with
        | none => []
        | some z => [z.adapter, z.pool]

/-- Why a scoped document was refused. -/
inductive ScopeError where
  /-- It configures recovery. -/
  | recoveryConfigured
  /-- A rule applies to the account or to a contract of the excluded set. -/
  | excludedScope
  deriving DecidableEq, Repr

/-- Whether scope `s` applies to `acct` or to a contract of `ex`. -/
def Scope.excludedBy (s : Scope) (acct : Bytes) (ex : List Bytes) : Bool :=
  match s with
  | .selfAdmin => true
  | .contract a => decide (a = acct) || decide (a ∈ ex)

/-- The rules the scoped document `d` lowers to on `acct` under the excluded
set `ex` and the current generation `gen`, or why it is refused. -/
def Doc.lowerScoped (d : Doc) (acct : Bytes) (ex : List Bytes) (gen : UInt64) :
    Except ScopeError Chain.RuleSet :=
  match d.recovery with
  | some _ => .error .recoveryConfigured
  | none =>
    if d.rules.any fun r => r.scope.excludedBy acct ex then .error .excludedScope
    else .ok (d.lowerRules acct (some gen))

end RuleCore.Document
