import Conformance.Caps
import Conformance.Random

/-!
# Authorization traces

A `Trace` is the specification of one authorization trace: a rule set, the
records it starts from, and a list of authorizations. `Trace.toJson` runs the
authorizations through the Lean model's `RuleCore.Chain.RuleSet.authorize`,
each on the records the authorizations before it left (the same records after
a refusal), and writes every authorization with its expected outcome: the
records after it, or the refusal.

The named traces exercise each refusal and its precedence, two contexts
charging one rule, a refusal discarding a batch's charges, windows rolling,
the cutoff at ledger 0, rules keeping their own records, expiry, generations,
authenticated signers outside the chosen rules, and the rule sets each cap
step, `lowerValidUntil`, `restrictFunctions` and `dropRule` derive from a
common one, run on the same authorizations. The randomized traces draw rule
sets with caps, each matching at least one function and most of them without a
signer requirement and with at most one condition, batches built from their
rules with amounts near their limits, choices that usually name the rule a call
was built from, signers that usually belong to the chosen rules, ledgers that
mostly advance, and a current generation that sometimes moves.
-/

namespace Conformance.Authorize

open RuleCore RuleCore.Chain Conformance.Cases
open Conformance.Random (Gen below pick listOf pad)

/-- The version of the authorization trace format in `conformance/README.md`. -/
def formatVersion : Nat := 2

/-- The seed of the committed randomized traces is the vectors' seed; this is
their number. -/
def defaultCount : Nat := 50

structure Trace where
  /-- The file name, without `.json`. -/
  name : String
  description : String
  rules : RuleSet
  /-- The records the first authorization starts from; one empty record per
  rule when absent. -/
  start : Option (List Cap.Record) := none
  authorizations : List Authorization

def Trace.startRecords (t : Trace) : List Cap.Record :=
  t.start.getD t.rules.emptyRecords

/-! ## Encoding -/

def refusalName : Refusal → String
  | .choicesMismatch => "choices_mismatch"
  | .recordsMismatch => "records_mismatch"
  | .noSuchRule => "no_such_rule"
  | .expired => "expired"
  | .staleGeneration => "stale_generation"
  | .notAllowed => "not_allowed"
  | .unauthorizedSigner => "unauthorized_signer"
  | .noAmount => "no_amount"
  | .cap .negativeAmount => "cap_negative_amount"
  | .cap .ledgerBeforeNewest => "cap_ledger_before_newest"
  | .cap .overflow => "cap_overflow"
  | .cap .limitExceeded => "cap_limit_exceeded"
  | .cap .historyFull => "cap_history_full"

/-- Each authorization with the model's outcome, applied to the records the
authorizations before it left. -/
def authorizationsJson (rs : RuleSet) : List Cap.Record → List Authorization → List Json
  | _, [] => []
  | records, a :: rest =>
    let entry (expected : Json) : Json :=
      .obj [("batch", .arr (a.contexts.map encodeContext)),
        ("choices", .arr (a.choices.map encodeIndex)), ("authenticated", encodeSigners a.auth),
        ("now", .num a.now.toNat), ("generation", .str (toString a.generation.toNat)),
        ("expected", expected)]
    match rs.authorize records a with
    | .ok records' =>
      entry (tagged "ok" (.arr (records'.map Caps.encodeRecord))) ::
        authorizationsJson rs records' rest
    | .error e => entry (tagged "error" (.str (refusalName e))) :: authorizationsJson rs records rest

def Trace.toJson (t : Trace) : Json :=
  .obj [
    ("format", .num formatVersion),
    ("name", .str t.name),
    ("description", .str t.description),
    ("rules", encodeRuleSet t.rules),
    ("start", .arr (t.startRecords.map Caps.encodeRecord)),
    ("authorizations", .arr (authorizationsJson t.rules t.startRecords t.authorizations))]

/-- Every ledger and amount of the starting records fits the Rust types. -/
def Trace.inRange (t : Trace) : Bool :=
  t.startRecords.all fun r =>
    Caps.inI128 r.total && r.history.all fun e => Caps.inU32 e.ledger && Caps.inI128 e.amount

/-! ## Named traces -/

def auth (contexts : List Context) (choices : List UInt32) (now : UInt32)
    (signers : List Signer := []) (generation : UInt64 := 0) : Authorization :=
  ⟨contexts, choices, signers, now, generation⟩

/-- A transfer rule capped at 100 per 10 ledgers, on the amount at argument 2. -/
def capped100 : Rule := { rule token ["transfer"] [] with cap := some (cap 100 10) }

/-- A vault rule that needs alice. -/
def vault : Rule := { signedRule "vault" [sAlice] 1 with functions := .only [s "deposit"] }

def deposit : Context := call "vault" "deposit" []

def batchSameRule : Trace where
  name := "authorize-batch-same-rule"
  description := "Two contexts choosing one capped rule are charged one after the other: 60 then 40 reach the limit together, one more is refused, and once the window has passed both are evicted."
  rules := [capped100]
  authorizations := [
    auth [transfer 60, transfer 40] [0, 0] 1,
    auth [transfer 1] [0] 2,
    auth [transfer 50, transfer 51] [0, 0] 11,
    auth [transfer 50, transfer 50] [0, 0] 11]

def choicesMismatch : Trace where
  name := "authorize-choices-mismatch"
  description := "The choices must hold exactly one rule index per context: fewer or more are refused with choices_mismatch, and an empty batch with an empty choice list is accepted."
  rules := [capped100]
  authorizations := [
    auth [transfer 1] [] 1,
    auth [transfer 1] [0, 0] 1,
    auth [] [0] 1,
    auth [transfer 1, transfer 2] [0] 1,
    auth [] [] 1]

def recordsMismatch : Trace where
  name := "authorize-records-mismatch"
  description := "The records must hold exactly one record per rule: starting from one record for two rules, every authorization is refused with records_mismatch, after the choice length check."
  rules := [capped100, vault]
  start := some [.empty]
  authorizations := [
    auth [transfer 1] [0] 1,
    auth [] [] 1,
    auth [transfer 1] [] 1]

def noSuchRule : Trace where
  name := "authorize-no-such-rule"
  description := "A chosen index at the length, 2^31 or 2^32 - 1 is refused with no_such_rule, also after a context whose choice is valid."
  rules := [capped100, vault]
  authorizations := [
    auth [transfer 1] [2] 1,
    auth [transfer 1] [u32Half] 1,
    auth [transfer 1] [u32Max] 1,
    auth [transfer 1, transfer 1] [0, 2] 1,
    auth [transfer 1] [0] 1]

def notAllowed : Trace where
  name := "authorize-not-allowed"
  description := "The chosen rule must allow its context: a call another rule allows, a call missing the rule's signer, and a creation are refused with not_allowed."
  rules := [capped100, vault]
  authorizations := [
    auth [transfer 1] [1] 1 [sAlice],
    auth [deposit] [1] 1,
    auth [deposit] [0] 1 [sAlice],
    auth [create token] [0] 1,
    auth [deposit] [1] 1 [sAlice]]

def missingAmount : Trace where
  name := "authorize-missing-amount"
  description := "A context chosen for a capped rule must hold an i128 at the cap's argument index: a missing argument, a u64 and bytes are refused with no_amount; an uncapped rule reads no amount; a cap on argument 0 reads argument 0."
  rules := [
    { rule token ["transfer"] [] with cap := some (cap 100 10) },
    rule token ["transfer"] [],
    { rule token ["transfer"] [] with cap := some (cap 100 10 0) }]
  authorizations := [
    auth [call token "transfer" [alice, bob]] [0] 1,
    auth [call token "transfer" [alice, bob, .u64 5]] [0] 1,
    auth [call token "transfer" [alice, bob, .bytes (s "5")]] [0] 1,
    auth [call token "transfer" [alice, bob]] [1] 1,
    auth [call token "transfer" [.i128 (BitVec.ofInt 128 7), bob, .u64 5]] [2] 1,
    auth [call token "transfer" [alice, bob, .i128 (BitVec.ofInt 128 7)]] [2] 1]

def windowRolls : Trace where
  name := "authorize-window-rolls"
  description := "Charges at successive ledgers: each spend waits until the ones before it leave the window of 10 ledgers, evicted at or before now - period."
  rules := [capped100]
  authorizations := [
    auth [transfer 100] [0] 1,
    auth [transfer 1] [0] 5,
    auth [transfer 1] [0] 10,
    auth [transfer 100] [0] 11,
    auth [transfer 1] [0] 20,
    auth [transfer 50] [0] 21,
    auth [transfer 50] [0] 22,
    auth [transfer 1] [0] 22,
    auth [transfer 1] [0] 31,
    auth [transfer 50] [0] 32]

def refusalDiscardsBatch : Trace where
  name := "authorize-refusal-discards-batch"
  description := "A refusal discards the charges of the earlier contexts of its batch: 60 then 50 on one rule is refused, and the records stay empty, so 60 alone is then accepted."
  rules := [capped100, capped100]
  authorizations := [
    auth [transfer 60, transfer 50] [0, 0] 1,
    auth [transfer 60, transfer 50, transfer 50] [1, 0, 0] 1,
    auth [transfer 60] [0] 1,
    auth [transfer 40, transfer 41] [1, 0] 2]

def choicesBeforeCharges : Trace where
  name := "authorize-choices-before-charges"
  description := "Every chosen rule is checked before any charge: a batch whose first context would exceed its cap and whose second chooses a rule that does not allow it is refused with not_allowed; with the signer authenticated, the cap refusal shows."
  rules := [capped100, vault]
  authorizations := [
    auth [transfer 101, deposit] [0, 1] 1,
    auth [transfer 101, deposit] [0, 1] 1 [sAlice],
    auth [transfer 100, deposit] [0, 1] 1 [sAlice]]

def capRefusals : Trace where
  name := "authorize-cap-refusals"
  description := "Each refusal of the cap check passes on as cap_ followed by its name: a negative amount, a ledger before the newest recorded spend, and an exceeded limit; a zero amount is accepted and records nothing."
  rules := [capped100]
  start := some [⟨[⟨50, 10⟩], 10⟩]
  authorizations := [
    auth [transfer (-1)] [0] 51,
    auth [transfer 1] [0] 49,
    auth [transfer 91] [0] 51,
    auth [transfer 0] [0] 49,
    auth [transfer 90] [0] 51]

def capOverflow : Trace where
  name := "authorize-cap-overflow"
  description := "A charge whose new total does not fit in an i128 is refused with cap_overflow."
  rules := [{ rule token ["transfer"] [] with cap := some (cap ((2 : Int) ^ 127 - 1) 10) }]
  start := some [⟨[⟨1, 2 ^ 127 - 2⟩], 2 ^ 127 - 2⟩]
  authorizations := [
    auth [transfer 2] [0] 2,
    auth [transfer 1] [0] 2]

def historyFull : Trace where
  name := "authorize-history-full"
  description := "A record holding 1000 entries refuses a spend under the limit with cap_history_full until eviction makes room."
  rules := [{ rule token ["transfer"] [] with cap := some (cap 10000 10) }]
  start := some [⟨List.replicate 1000 ⟨5, 1⟩, 1000⟩]
  authorizations := [
    auth [transfer 1] [0] 6,
    auth [transfer 1] [0] 15]

def ownRecords : Trace where
  name := "authorize-own-records"
  description := "Two capped rules for the same call keep their own records, and a rule without a cap keeps its record as it was."
  rules := [capped100, { rule token ["transfer"] [] with cap := some (cap 50 10) }, vault]
  start := some [.empty, .empty, ⟨[⟨3, 7⟩], 7⟩]
  authorizations := [
    auth [transfer 100, transfer 50] [0, 1] 1,
    auth [transfer 1] [0] 2,
    auth [transfer 1] [1] 2,
    auth [deposit] [2] 9 [sAlice]]

def ledgerZero : Trace where
  name := "authorize-ledger-zero"
  description := "At ledger 0 the cutoff saturates to 0 and evicts entries at ledger 0, so each charge of the whole limit at ledger 0 is accepted alone; at ledger 1 the entry at ledger 0 is still in the window."
  rules := [capped100]
  authorizations := [
    auth [transfer 100] [0] 0,
    auth [transfer 100] [0] 0,
    auth [transfer 1] [0] 1]

def emptyBatch : Trace where
  name := "authorize-empty-batch"
  description := "An empty batch is accepted and changes nothing, whatever the records; on the empty rule set too."
  rules := [capped100]
  start := some [⟨[⟨5, 100⟩], 100⟩]
  authorizations := [
    auth [] [] 0,
    auth [] [] 6]

/-! ### Expiry, generations and signers -/

/-- Every vault function for alice, valid until ledger 10, issued under
generation 3. -/
def grant : Rule :=
  { signedRule "vault" [sAlice] 1 with
    functions := .any, validUntil := some 10, generation := some 3 }

/-- The vault's withdraw for alice, with no last ledger and no generation. -/
def admin : Rule := { signedRule "vault" [sAlice] 1 with functions := .only [s "withdraw"] }

def withdraw : Context := call "vault" "withdraw" []

def expired : Trace where
  name := "authorize-expired"
  description := "A rule authorizes up to and at its last ledger and is refused with expired after it, as OpenZeppelin refuses valid_until < ledger; a rule without a last ledger is never refused for time."
  rules := [grant, admin]
  authorizations := [
    auth [withdraw] [0] 0 [sAlice] 3,
    auth [withdraw] [0] 10 [sAlice] 3,
    auth [withdraw] [0] 11 [sAlice] 3,
    auth [withdraw] [0] u32Max [sAlice] 3,
    auth [withdraw] [1] u32Max [sAlice] 3]

def staleGeneration : Trace where
  name := "authorize-stale-generation"
  description := "A rule issued under generation 3 authorizes in generation 3 and is refused with stale_generation in any other, 2^64 - 1 included; a rule without a generation is not refused for it."
  rules := [grant, admin]
  authorizations := [
    auth [withdraw] [0] 1 [sAlice] 3,
    auth [withdraw] [0] 1 [sAlice] 4,
    auth [withdraw] [0] 1 [sAlice] 2,
    auth [withdraw] [0] 1 [sAlice] u64Max,
    auth [withdraw] [1] 1 [sAlice] 4]

def unauthorizedSigner : Trace where
  name := "authorize-unauthorized-signer"
  description := "Every authenticated signer must be a signer of some chosen rule, as OpenZeppelin refuses UnauthorizedSigner: a further signer is refused even when the threshold is met, a signer of another chosen rule is accepted, an external signer holding alice's bytes is not alice, and an empty batch accepts only no signers."
  rules := [vault, { signedRule "vault" [sBob] 1 with functions := .only [s "withdraw"] }]
  authorizations := [
    auth [deposit] [0] 1 [sAlice],
    auth [deposit] [0] 1 [sAlice, sBob],
    auth [deposit, withdraw] [0, 1] 1 [sAlice, sBob],
    auth [deposit] [0] 1 [sAlice, .external (s "alice") []],
    auth [] [] 1 [],
    auth [] [] 1 [sAlice]]

def refusalOrder : Trace where
  name := "authorize-refusal-order"
  description := "For each context in order: no_such_rule, then expired, then stale_generation, then not_allowed; then unauthorized_signer; then every charge."
  rules := [
    { rule "vault" ["deposit"] [] with validUntil := some 0, generation := some 1 },
    capped100]
  authorizations := [
    auth [deposit] [0] 5 [] 2,
    auth [deposit] [0] 0 [] 2,
    auth [deposit] [2] 5 [] 2,
    auth [transfer 1, deposit] [1, 0] 5 [] 1,
    auth [deposit, transfer 1] [0, 0] 0 [] 1,
    auth [transfer 101] [1] 0 [sAlice] 1,
    auth [transfer 101] [1] 0 [] 1]

/-! ### The rule sets the steps derive -/

/-- An uncapped transfer rule, a transfer rule capped at 30 per 10 ledgers and
an approve rule capped at 20 per 5, from which the step traces derive. -/
def stepBase : RuleSet := [
  rule token ["transfer"] [],
  { rule token ["transfer"] [] with cap := some (cap 30 10) },
  { rule token ["approve"] [] with cap := some (cap 20 5) }]

def approve (amount : Int) : Context :=
  call token "approve" [alice, bob, .i128 (BitVec.ofInt 128 amount)]

/-- One run, choosing each of the three rules, that the steps narrow in
different ways. -/
def stepRun (r0 r1 r2 : UInt32) : List Authorization := [
  auth [transfer 25] [r0] 1,
  auth [transfer 25] [r1] 1,
  auth [transfer 10, approve 15] [r1, r2] 3,
  auth [approve 10] [r2] 6,
  auth [transfer 20, transfer 5] [r1, r0] 9,
  auth [transfer 30] [r1] 12,
  auth [approve 20] [r2] 12]

/-- The rule set after `step`, computed by the model; the base when the step is
refused. -/
def derive (step : Attenuation) : RuleSet :=
  match stepBase.attenuate step with
  | .ok rs => rs
  | .error _ => stepBase

def stepTrace (name what : String) (step : Attenuation) : Trace where
  name := s!"authorize-step-{name}"
  description := s!"The run of authorize-step-base on the rule set {what}."
  rules := derive step
  authorizations := stepRun 0 1 2

def stepBaseTrace : Trace where
  name := "authorize-step-base"
  description := "An uncapped transfer rule, a transfer rule capped at 30 per 10 ledgers and an approve rule capped at 20 per 5, under a run choosing each; the authorize-step traces run it on the rule sets each step derives from these rules."
  rules := stepBase
  authorizations := stepRun 0 1 2

def stepTraces : List Trace := [
  stepBaseTrace,
  stepTrace "add-cap" "after addCap 0 with 40 per 10 ledgers" (.addCap 0 (cap 40 10)),
  stepTrace "lower-cap-limit" "after lowerCapLimit 1 to 25" (.lowerCapLimit 1 (BitVec.ofInt 128 25)),
  stepTrace "lengthen-cap-period" "after lengthenCapPeriod 2 to 8"
    (.lengthenCapPeriod 2 8),
  stepTrace "lower-valid-until" "after lowerValidUntil 1 to 6" (.lowerValidUntil 1 6),
  stepTrace "restrict-functions" "after restrictFunctions 2 to transfer"
    (.restrictFunctions 2 [s "transfer"]),
  { name := "authorize-step-drop-rule"
    description := "The run of authorize-step-base on the rule set after dropRule 0, with each choice renumbered: rule 1 is now rule 0 and rule 2 is rule 1; the context that chose the dropped rule chooses an index past the end."
    rules := derive (.dropRule 0)
    authorizations := stepRun 2 0 1 }]

def named : List Trace := [
  batchSameRule, choicesMismatch, recordsMismatch, noSuchRule, notAllowed, missingAmount,
  windowRolls, refusalDiscardsBatch, choicesBeforeCharges, capRefusals, capOverflow, historyFull,
  ownRecords, ledgerZero, emptyBatch, expired, staleGeneration, unauthorizedSigner,
  refusalOrder] ++ stepTraces

/-! ## Randomized traces -/

def amounts (limit : Int) : List Int :=
  [0, 1, 1, 2, 3, limit / 2, limit / 2, limit, limit + 1, -1]

/-- A context for rule `r`, built as the rule vectors build calls, with an
amount near the cap's limit at the cap's argument index when the rule has one. -/
def contextFor (r : Rule) : Gen Context := do
  let c ← Random.callFrom r
  match r.cap, c with
  | some k, .call contract function args =>
    let j := k.amountArg.toNat
    if j < 4 && (← below 8) ≠ 0 then
      let a ← pick (amounts k.limit.toInt)
      let padded := args ++ List.replicate (j + 1 - args.length) (.bool false)
      return .call contract function (padded.set j (.i128 (BitVec.ofInt 128 a)))
    else return c
  | _, _ => return c

/-- The signers of an authorization choosing `choices`: usually some signers
of the chosen rules, sometimes a further one. -/
def signersFor (rs : RuleSet) (choices : List UInt32) : Gen (List Signer) := do
  let own := choices.flatMap fun j => (rs[j.toNat]?.map (·.signers)).getD []
  let fromRules ← listOf (← below (own.length + 1)) (pick own)
  let extra ← if (← below 5) = 0 then listOf 1 (pick Random.signers) else pure []
  return fromRules ++ extra

/-- One authorization of up to three contexts, each usually choosing the rule
it was built from, in generation `gen`. -/
def authorization (rs : RuleSet) (now : Nat) (gen : UInt64) : Gen Authorization := do
  let n ← pick [0, 1, 1, 1, 1, 2, 2, 3]
  let parts ← listOf n do
    if rs.isEmpty then return (← Random.context rs, (0 : UInt32))
    let j ← below rs.length
    let r := rs.getD j default
    let c ← contextFor r
    let choice ← if (← below 10) = 0 then Random.ruleIndex rs else pure (UInt32.ofNat j)
    return (c, choice)
  let choices := parts.map (·.2)
  let choices ← if (← below 20) = 0 then pure (choices.drop 1) else pure choices
  return ⟨parts.map (·.1), choices, ← signersFor rs choices, UInt32.ofNat now, gen⟩

/-- `n` authorizations at ledgers that mostly advance by less than a period, in
a generation that sometimes moves on by one. -/
def authorizations (rs : RuleSet) : Nat → Nat → UInt64 → Gen (List Authorization)
  | 0, _, _ => return []
  | n + 1, now, gen => do
    let now' ← Caps.step 10 now
    let gen' := if (← below 6) = 0 then gen + 1 else gen
    let a ← authorization rs now' gen'
    return a :: (← authorizations rs n now' gen')

def trace (seed : UInt64) (k : Nat) : Trace :=
  let g : Gen Trace := do
    let rs ← Random.ruleSet
    let rs ← rs.mapM fun r => do
      let r ← if r.cap.isNone && (← below 2) = 0 then pure { r with cap := some (← Random.cap) }
        else pure r
      let r ← if (← below 3) = 0 then pure r else pure { r with threshold := 0 }
      let r := match r.functions with
        | .only [] => { r with functions := .only [s "f"] }
        | _ => r
      if (← below 2) = 0 then return r else return { r with conds := r.conds.take 1 }
    let n ← below 8
    let auths ← authorizations rs (n + 1) (← pick [0, 1, 1, 5, 100]) (← pick [0, 0, 1, 2])
    return {
      name := s!"authorize-random-{pad 2 k}"
      description := s!"Randomized authorization trace {k} of seed {seed}."
      rules := rs
      authorizations := auths }
  (g.run ⟨seed + UInt64.ofNat k⟩).1

def traces (seed : UInt64) (count : Nat) : List Trace :=
  named ++ (List.range count).map (trace seed)

end Conformance.Authorize
