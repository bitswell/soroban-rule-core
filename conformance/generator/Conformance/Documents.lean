import Conformance.Authorize
import RuleCore.Vocab.Lowering

/-!
# Document traces

A `Trace` is the specification of one document trace: a document, the account
it belongs to, optionally the admin document it is issued under as a scoped
document and the generation it is issued in, and a list of authorizations.
`Trace.toJson` writes, from the Lean model:

* the rules the document lowers to (`Doc.lower`, or `Doc.lowerScoped` under
  the admin document's `Doc.excluded` set), or the scoped lowering's refusal;
* every authorization with the document's own verdict on it (`Doc.authorize`):
  the records after it, one per installed rule, or a refusal, each on the
  records the authorizations before it left.

The verdicts are the document's meaning, written from Perch's specification,
not the lowering's: an implementation that lowers the document and checks the
authorizations with its own evaluator should reach the same verdicts. Every
document is one Perch's validation accepts: unique signer ids and keys,
non-empty principals with `1 ≤ m ≤ N`, non-empty function and argument
lists, string predicates of at most 256 bytes where Perch bounds them, a cap
only on a contract scope with a positive limit and period, a non-zero
not-after ledger, and, in an admin document, a constraint-free self-admin rule
that Perch's `admin_survives` requires. No authorization chooses the recovery
rule: on chain the recovery controller checks it against its own state, which
the model over-approximates.

The named traces follow the probes Perch's own harness runs on OpenZeppelin's
smart account (a capped rule listing `approve`, a capped rule without
functions, an extra authenticated signer, `not-after-ledger`, an over-long
`string-in` value, a constraint-free rule, `string-prefix` on strings and
symbols), and the scoped cases: the generation stamp, a stale generation, and
each refusal. The randomized traces draw valid documents over a small universe
and authorizations built from their rules.
-/

namespace Conformance.Documents

open RuleCore RuleCore.Chain RuleCore.Document Conformance.Cases
open Conformance.Random (Gen below pick listOf pad)

/-- The version of the document trace format in `conformance/README.md`. -/
def formatVersion : Nat := 1

/-- The number of committed randomized traces; their seed is the vectors'. -/
def defaultCount : Nat := 40

structure Trace where
  /-- The file name, without `.json`. -/
  name : String
  description : String
  doc : Doc
  account : Bytes
  /-- For a scoped document: the admin document and the generation it is
  issued in. -/
  under : Option (Doc × UInt64) := none
  authorizations : List Authorization

/-! ## The model's results -/

def Trace.lowered (t : Trace) : Except ScopeError RuleSet :=
  match t.under with
  | none => .ok (t.doc.lower t.account)
  | some (admin, gen) => t.doc.lowerScoped t.account (admin.excluded t.account) gen

def Trace.issued (t : Trace) : Option UInt64 :=
  t.under.map (·.2)

/-! ## Encoding -/

def encodeScope : Scope → Json
  | .contract a => tagged "contract" (.str (hex a))
  | .selfAdmin => .str "self_admin"

def encodePrincipals : Principals → Json
  | .all ids => tagged "all" (encodeBytesList ids)
  | .threshold ids m =>
    tagged "threshold" (.obj [("ids", encodeBytesList ids), ("m", .num m.toNat)])

def encodePred : Pred → Json
  | .isSelf => .str "is_self"
  | .addressEq a => tagged "address_eq" (.str (hex a))
  | .stringIn values => tagged "string_in" (encodeBytesList values)
  | .stringPrefix pre => tagged "string_prefix" (.str (hex pre))
  | .u32Eq v => tagged "u32_eq" (.num v.toNat)

def encodeArg (c : ArgConstraint) : Json :=
  .obj [("index", encodeIndex c.index), ("pred", encodePred c.pred)]

def encodeDocCap (k : Document.Cap) : Json :=
  .obj [("limit", encodeLimit k.limit), ("period_ledgers", .num k.periodLedgers.toNat)]

def encodeOpt {α : Type} (f : α → Json) : Option α → Json
  | some x => f x
  | none => .null

def encodeDocRule (r : Document.Rule) : Json :=
  .obj ([
    ("scope", encodeScope r.scope),
    ("principals", encodePrincipals r.principals),
    ("functions", encodeOpt encodeBytesList r.functions),
    ("args", encodeOpt (fun cs => .arr (cs.map encodeArg)) r.args),
    ("not_after_ledger", encodeOpt (fun x => .num x.toNat) r.notAfterLedger),
    ("cap", encodeOpt encodeDocCap r.cap)] ++ encodeRootField r.authRoot)

def encodeDecl (sd : SignerDecl) : Json :=
  .obj [("id", .str (hex sd.id)), ("signer", encodeSigner sd.signer)]

def encodeRecovery (rc : Recovery) : Json :=
  .obj [
    ("controller", .str (hex rc.controller)),
    ("zk", encodeOpt (fun z => .obj [("adapter", .str (hex z.adapter)),
      ("pool", .str (hex z.pool))]) rc.zk)]

def encodeDoc (d : Doc) : Json :=
  .obj [
    ("signers", .arr (d.signers.map encodeDecl)),
    ("rules", .arr (d.rules.map encodeDocRule)),
    ("recovery", encodeOpt encodeRecovery d.recovery)]

def scopeErrorName : ScopeError → String
  | .recoveryConfigured => "recovery_configured"
  | .excludedScope => "excluded_scope"

/-- Each authorization with the document's verdict, applied to the records the
authorizations before it left. -/
def authorizationsJson (t : Trace) : List RuleCore.Cap.Record → List Authorization → List Json
  | _, [] => []
  | records, a :: rest =>
    let entry (expected : Json) : Json :=
      .obj [("batch", .arr (a.contexts.map encodeContext)),
        ("choices", .arr (a.choices.map encodeIndex)), ("authenticated", encodeSigners a.auth),
        ("now", .num a.now.toNat), ("generation", .str (toString a.generation.toNat)),
        ("expected", expected)]
    match t.doc.authorize t.account applyDocCheck t.issued records a with
    | some records' =>
      entry (tagged "ok" (.arr (records'.map Caps.encodeRecord))) ::
        authorizationsJson t records' rest
    | none => entry (.str "refused") :: authorizationsJson t records rest

def Trace.toJson (t : Trace) : Json :=
  let (lowered, auths) : Json × List Json :=
    match t.lowered with
    | .ok rs =>
      (tagged "ok" (encodeRuleSet rs),
        authorizationsJson t (rs.map fun _ => .empty) t.authorizations)
    | .error e => (tagged "error" (.str (scopeErrorName e)), [])
  .obj [
    ("format", .num formatVersion),
    ("name", .str t.name),
    ("description", .str t.description),
    ("document", encodeDoc t.doc),
    ("account", .str (hex t.account)),
    ("scoped", match t.under with
      | none => .null
      | some (admin, gen) =>
        .obj [("admin", encodeDoc admin), ("generation", .str (toString gen.toNat))]),
    ("lowered", lowered),
    ("authorizations", .arr auths)]

/-! ## Checks -/

/-- Whether a document rule satisfies `Rule.Valid`. -/
def ruleValid (d : Doc) (r : Document.Rule) : Bool :=
  (match r.principals with
    | .all _ =>
      decide (d.named r.principals).Nodup && decide ((d.named r.principals).length < 2 ^ 32)
    | .threshold _ _ => true) &&
    r.notAfterLedger.all fun x => decide (0 < x.toNat)

/-- Whether every document of the trace satisfies `Doc.Valid`, so the
lowering's verdicts are the document's. -/
def Trace.valid (t : Trace) : Bool :=
  t.doc.rules.all (ruleValid t.doc) &&
    (t.under.all fun (admin, _) => admin.rules.all (ruleValid admin))

/-- Whether some authorization chooses the recovery rule. -/
def Trace.choosesRecovery (t : Trace) : Bool :=
  t.doc.recovery.isSome && t.authorizations.any fun a =>
    a.choices.any fun j => j.toNat = t.doc.rules.length

/-! ## Named traces -/

def acct : Bytes := s "account"
def tokenB : Bytes := s "token"
def ciKey : Signer := .external (s "verifier") (s "ci-key")
def opsAddr : Signer := .delegated (s "ops")

def decls : List SignerDecl := [⟨s "ci", ciKey⟩, ⟨s "ops", opsAddr⟩]

/-- The constraint-free self-admin rule an admin document keeps. -/
def adminRule : Document.Rule := { scope := .selfAdmin, principals := .all [s "ops"] }

/-- A rule on the token that `ci` signs. -/
def ciRule (functions : Option (List String)) : Document.Rule :=
  { scope := .contract tokenB, principals := .all [s "ci"],
    functions := functions.map (·.map s) }

def capped (r : Document.Rule) : Document.Rule :=
  { r with cap := some ⟨BitVec.ofInt 128 10, 1000⟩ }

/-- An admin document: the admin rule, then `rules`. Choice `j` of an
authorization names rule `j`, so the admin rule is 0. -/
def adminDoc (rules : List Document.Rule) : Doc :=
  { signers := decls, rules := adminRule :: rules }

def i128 (n : Int) : Val := .i128 (BitVec.ofInt 128 n)

def tokenCall (function : String) (args : List Val) : Context :=
  .call tokenB (s function) args

def transferOf (n : Int) : Context :=
  tokenCall "transfer" [.address (s "a"), .address (s "b"), i128 n]

def authAt (contexts : List Context) (choices : List UInt32) (now : UInt32)
    (signers : List Signer := [ciKey]) (generation : UInt64 := 0) : Authorization :=
  ⟨contexts, choices, signers, now, generation⟩

def cappedApprove : Trace where
  name := "document-capped-approve"
  description := "A capped rule listing transfer and approve authorizes a transfer of 5 and refuses an approve of 5, which OpenZeppelin's spending-limit policy does not meter; the cap reaches its limit of 10 within its window."
  doc := adminDoc [capped (ciRule (some ["transfer", "approve"]))]
  account := acct
  authorizations := [
    authAt [transferOf 5] [1] 500,
    authAt [tokenCall "approve" [.address (s "a"), .address (s "s"), i128 5, .other (u32Xdr 1000)]]
      [1] 501,
    authAt [transferOf 5] [1] 502,
    authAt [transferOf 1] [1] 503]

def cappedNoFunctions : Trace where
  name := "document-capped-no-functions"
  description := "A capped rule listing no functions authorizes transfer only: burn and a transfer whose argument 2 is not an i128 are refused."
  doc := adminDoc [capped (ciRule none)]
  account := acct
  authorizations := [
    authAt [transferOf 5] [1] 500,
    authAt [tokenCall "burn" [.address (s "a"), i128 5]] [1] 500,
    authAt [tokenCall "transfer" [.address (s "a"), .address (s "b"), .u64 5]] [1] 500]

def extraSigner : Trace where
  name := "document-extra-signer"
  description := "An authorization signed by the rule's signer is accepted; one that also authenticates a signer of no chosen rule is refused."
  doc := adminDoc [ciRule (some ["transfer"])]
  account := acct
  authorizations := [
    authAt [transferOf 5] [1] 500,
    authAt [transferOf 5] [1] 500 [ciKey, .external (s "verifier") (s "stranger")],
    authAt [transferOf 5] [1] 500 []]

def notAfterLedger : Trace where
  name := "document-not-after-ledger"
  description := "A rule with not-after-ledger 600 authorizes at ledger 599 and not at 600 or later."
  doc := adminDoc [{ ciRule (some ["publish"]) with notAfterLedger := some 600 }]
  account := acct
  authorizations := [
    authAt [tokenCall "publish" []] [1] 599,
    authAt [tokenCall "publish" []] [1] 600,
    authAt [tokenCall "publish" []] [1] 601]

def longString : Bytes := List.replicate 300 97

def stringInLong : Trace where
  name := "document-string-in-long"
  description := "string-in with a 300-byte value and ok: ok is authorized; the 300-byte string, which Perch's interpreter never matches, is refused."
  doc := adminDoc [{ ciRule (some ["f"]) with
    args := some [⟨0, .stringIn [longString, s "ok"]⟩] }]
  account := acct
  authorizations := [
    authAt [tokenCall "f" [.string (s "ok")]] [1] 500,
    authAt [tokenCall "f" [.string longString]] [1] 500,
    authAt [tokenCall "f" [.symbol (s "ok")]] [1] 500]

def constraintFree : Trace where
  name := "document-constraint-free"
  description := "A rule with no function list, arguments or cap authorizes every function of its contract, and nothing on another contract; the admin rule authorizes any call to the account."
  doc := adminDoc [ciRule none]
  account := acct
  authorizations := [
    authAt [tokenCall "anything_at_all" [.other (u32Xdr 42)]] [1] 500,
    authAt [.call (s "other") (s "anything_at_all") []] [1] 500,
    authAt [.call acct (s "execute") []] [0] 500 [opsAddr],
    authAt [.call acct (s "execute") []] [0] 500 [ciKey]]

def stringPrefix : Trace where
  name := "document-string-prefix"
  description := "string-prefix pkg_ reads strings: the string pkg_a is authorized, the string pk and the symbol pkg_a are refused."
  doc := adminDoc [{ ciRule (some ["f"]) with args := some [⟨0, .stringPrefix (s "pkg_")⟩] }]
  account := acct
  authorizations := [
    authAt [tokenCall "f" [.string (s "pkg_a")]] [1] 500,
    authAt [tokenCall "f" [.string (s "pk")]] [1] 500,
    authAt [tokenCall "f" [.symbol (s "pkg_a")]] [1] 500]

def predicates : Trace where
  name := "document-predicates"
  description := "is-self, address-eq and u32-eq read an address equal to the account, an address equal to the one named, and the u32 named, given as the XDR of its ScVal."
  doc := adminDoc [{ ciRule (some ["send"]) with
    args := some [⟨0, .isSelf⟩, ⟨1, .addressEq (s "dest")⟩, ⟨2, .u32Eq 7⟩] }]
  account := acct
  authorizations := [
    authAt [tokenCall "send" [.address acct, .address (s "dest"), .other (u32Xdr 7)]] [1] 500,
    authAt [tokenCall "send" [.address (s "x"), .address (s "dest"), .other (u32Xdr 7)]] [1] 500,
    authAt [tokenCall "send" [.address acct, .address (s "x"), .other (u32Xdr 7)]] [1] 500,
    authAt [tokenCall "send" [.address acct, .address (s "dest"), .other (u32Xdr 8)]] [1] 500,
    authAt [tokenCall "send" [.address acct, .address (s "dest"), .u64 7]] [1] 500]

def thresholds : Trace where
  name := "document-thresholds"
  description := "An all rule needs both of its signers; a threshold rule of 1 of the two needs either."
  doc := adminDoc [
    { ciRule (some ["f"]) with principals := .all [s "ci", s "ops"] },
    { ciRule (some ["g"]) with principals := .threshold [s "ci", s "ops"] 1 }]
  account := acct
  authorizations := [
    authAt [tokenCall "f" []] [1] 500 [ciKey, opsAddr],
    authAt [tokenCall "f" []] [1] 500 [ciKey],
    authAt [tokenCall "g" []] [2] 500 [opsAddr],
    authAt [tokenCall "g" []] [2] 500 []]

def withRecovery : Trace where
  name := "document-with-recovery"
  description := "A document configuring recovery lowers to its rules and then the recovery rule; the records hold one record per installed rule, and its own rules authorize as before."
  doc := { adminDoc [capped (ciRule none)] with
    recovery := some { controller := s "controller", zk := some ⟨s "adapter", s "pool"⟩ } }
  account := acct
  authorizations := [
    authAt [transferOf 4] [1] 500,
    authAt [.call acct (s "apply_doc") []] [0] 500 [opsAddr]]

/-- The admin document scoped documents are issued under. -/
def scopeAdmin : Doc :=
  { adminDoc [] with
    recovery := some { controller := s "controller", zk := some ⟨s "adapter", s "pool"⟩ } }

def scopedIssued : Trace where
  name := "document-scoped-issued"
  description := "A scoped document issued in generation 3 authorizes in generation 3 and nothing once the generation is 4."
  doc := { signers := decls, rules := [ciRule none, capped (ciRule (some ["transfer"]))] }
  account := acct
  under := some (scopeAdmin, 3)
  authorizations := [
    authAt [tokenCall "mint" []] [0] 500 [ciKey] 3,
    authAt [transferOf 10] [1] 500 [ciKey] 3,
    authAt [transferOf 1] [1] 501 [ciKey] 3,
    authAt [tokenCall "mint" []] [0] 502 [ciKey] 4,
    authAt [] [] 502 [] 4]

def scopedRefused (name what : String) (scope : Scope) : Trace where
  name := s!"document-scoped-{name}"
  description := s!"A scoped document with a rule on {what} is refused."
  doc := { signers := decls, rules := [ciRule none, { ciRule none with scope }] }
  account := acct
  under := some (scopeAdmin, 0)
  authorizations := []

def scopedRecovery : Trace where
  name := "document-scoped-recovery"
  description := "A scoped document configuring recovery is refused."
  doc := { signers := decls, rules := [ciRule none], recovery := some { controller := s "c" } }
  account := acct
  under := some (scopeAdmin, 0)
  authorizations := []

def exactAuthRoot : Trace where
  name := "document-exact-root"
  description := "Root-bearing document lowering and encoding preserve the exact pair; a game win has no charge, a loss charges and a separate direct transfer is refused."
  doc := adminDoc [
    { ciRule (some ["guess"]) with scope := .contract (s "game") },
    { capped (ciRule (some ["transfer"])) with authRoot := some ⟨s "game", s "guess"⟩ }]
  account := acct
  authorizations := [
    authAt [.call (s "game") (s "guess") []] [1] 500,
    authAt [.call (s "game") (s "guess") [], transferOf 4] [1, 2] 501,
    authAt [transferOf 1] [2] 502,
    authAt [.call (s "game") (s "guess") [], transferOf 6] [1, 2] 503]

def named : List Trace := [
  exactAuthRoot,   cappedApprove, cappedNoFunctions, extraSigner, notAfterLedger, stringInLong, constraintFree,
  stringPrefix, predicates, thresholds, withRecovery, scopedIssued,
  scopedRefused "self-admin" "the account, by a self-admin scope" .selfAdmin,
  scopedRefused "account" "the account's address" (.contract acct),
  scopedRefused "controller" "the recovery controller" (.contract (s "controller")),
  scopedRefused "adapter" "the ZK adapter" (.contract (s "adapter")),
  scopedRefused "pool" "the ZK pool" (.contract (s "pool")),
  scopedRecovery]

/-! ## Randomized traces -/

def contracts : List Bytes := [tokenB, s "vault", s "registry"]
def functionNames : List Bytes := ["transfer", "approve", "publish", "f"].map s
def ids : List Bytes := ["s0", "s1", "s2", "s3"].map s
def signerPool : List Signer :=
  [.delegated (s "a"), .external (s "v") (s "k"), .external (s "v") (s "k2"), .delegated (s "ab")]
def strings : List Bytes := [s "pkg_a", s "pkg_b", s "ok", [], longString]

instance : Inhabited Document.Rule := ⟨adminRule⟩

/-- `k` distinct elements of `xs`, in order. -/
def distinct {α : Type} (xs : List α) (k : Nat) : Gen (List α) := do
  let start ← below xs.length
  return ((xs.drop start) ++ xs.take start).take k

def pred (fs : List Bytes) : Gen Pred := do
  match ← below 5 with
  | 0 => return .isSelf
  | 1 => return .addressEq (← pick [s "a", s "dest"])
  | 2 => return .stringIn (← distinct strings ((← below 3) + 1))
  | 3 => return .stringPrefix (← pick [s "pkg_", s "p", []])
  | _ => let _ := fs; return .u32Eq (← pick [0, 7, 1000])

def principals : Gen Principals := do
  let n ← pick [1, 1, 2, 3]
  let chosen ← distinct ids n
  if (← below 2) = 0 then return .all chosen
  return .threshold chosen (UInt32.ofNat ((← below n) + 1))

def docRule : Gen Document.Rule := do
  let contract ← pick contracts
  let principals ← principals
  let functions ← if (← below 3) = 0 then pure none
    else some <$> distinct functionNames ((← below 3) + 1)
  let args ← if (← below 2) = 0 then pure none else do
    let n ← (← below 2) + 1 |> pure
    let idxs ← distinct [0, 1, 3] n
    some <$> idxs.mapM fun i => do return ⟨UInt32.ofNat i, ← pred functionNames⟩
  let notAfterLedger ← if (← below 4) = 0 then some <$> pick [1, 505, 520] else pure none
  let cap ← if (← below 3) = 0 then
      some <$> (do return ⟨BitVec.ofInt 128 (← pick [1, 10, 100]), ← pick [1, 10, 1000]⟩)
    else pure none
  return { scope := .contract contract, principals, functions, args, notAfterLedger, cap }

/-- A valid argument for predicate `p`, or sometimes another value. -/
def argFor (p : Pred) : Gen Val := do
  if (← below 6) = 0 then return ← pick [.u64 7, .symbol (s "pkg_a"), .address (s "x")]
  match p with
  | .isSelf => return .address acct
  | .addressEq a => return .address a
  | .stringIn values => return .string (← pick values)
  | .stringPrefix pre => return .string (pre ++ (← pick [s "x", []]))
  | .u32Eq v => return .other (u32Xdr v)

/-- A call built from document rule `r`: usually its contract and one of its
functions, with arguments for its predicates and, for a capped rule, an amount
at argument 2. -/
def callFor (r : Document.Rule) : Gen Context := do
  let contract := r.scope.contractOn acct
  let fs := match r.cap, r.functions with
    | some _, _ => [s "transfer", s "transfer", s "approve"]
    | none, some fs => fs
    | none, none => functionNames
  let function ← if (← below 8) = 0 then pick functionNames else pick fs
  let preds := r.args.getD []
  let base : List Val := [.address (s "a"), .address (s "b"), i128 1, .bool false]
  let args ← (List.range 4).mapM fun j => do
    match preds.find? (·.index.toNat = j) with
    | some c => argFor c.pred
    | none =>
      if j = 2 && r.cap.isSome then return i128 (← pick [0, 1, 5, 10, 11])
      else return base.getD j (.bool false)
  return .call contract function args

def signersFor (d : Doc) (r : Document.Rule) : Gen (List Signer) := do
  let own := d.named r.principals
  let n ← below (own.length + 2)
  let picked ← distinct own n
  if (← below 6) = 0 then return picked ++ [← pick signerPool] else return picked

def authorizationFor (d : Doc) (now : Nat) (gen : UInt64) : Gen Authorization := do
  let j ← below d.rules.length
  let r := d.rules.getD j default
  let c ← callFor r
  let choice := if (← below 12) = 0 then UInt32.ofNat (d.installed.length + 1) else UInt32.ofNat j
  return ⟨[c], [choice], ← signersFor d r, UInt32.ofNat now, gen⟩

def authorizationsFor (d : Doc) (gens : List UInt64) : Nat → Nat → Gen (List Authorization)
  | 0, _ => return []
  | n + 1, now => do
    let now' := now + (← pick [0, 1, 2, 5])
    let a ← authorizationFor d now' (← pick gens)
    return a :: (← authorizationsFor d gens n now')

def trace (seed : UInt64) (k : Nat) : Trace :=
  let g : Gen Trace := do
    let signers := ids.zip signerPool |>.map fun (id, sg) => (⟨id, sg⟩ : SignerDecl)
    let rules ← listOf ((← below 3) + 1) docRule
    let isScoped := (← below 3) = 0
    let n ← below 6
    if isScoped then
      let doc : Doc := { signers, rules }
      let gen := UInt64.ofNat (← below 3)
      let auths ← authorizationsFor doc [gen, gen, gen, gen + 1] (n + 1) 500
      return {
        name := s!"document-random-{pad 2 k}"
        description := s!"Randomized scoped document trace {k} of seed {seed}."
        doc, account := acct, under := some (scopeAdmin, gen), authorizations := auths }
    else
      let doc : Doc := { signers, rules := { adminRule with principals := .all [s "s0"] } :: rules }
      let auths ← authorizationsFor doc [0] (n + 1) 500
      return {
        name := s!"document-random-{pad 2 k}"
        description := s!"Randomized admin document trace {k} of seed {seed}."
        doc, account := acct, authorizations := auths }
  (g.run ⟨seed + UInt64.ofNat k⟩).1

def traces (seed : UInt64) (count : Nat) : List Trace :=
  named ++ (List.range count).map (trace seed)

end Conformance.Documents
