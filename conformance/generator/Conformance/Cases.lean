import Conformance.Vector

/-!
# Named cases

The hand-written vector specifications, one per behaviour the evaluator must
agree on. Only the inputs are written here; every expected verdict and
attenuation result is computed by the Lean model when the vectors are
generated.
-/

namespace Conformance.Cases

open RuleCore RuleCore.Chain

/-- The UTF-8 bytes of `x`. -/
def s (x : String) : Bytes := Bytes.ofString x

def call (contract function : String) (args : List Val) : Context :=
  .call (s contract) (s function) args

def create (wasmHash : String) : Context :=
  .create (s wasmHash)

/-- A rule with no signer requirement. -/
def rule (contract : String) (functions : List String) (conds : List Cond) : Rule :=
  { contract := s contract, functions := .only (functions.map s), conds := conds, signers := [],
    threshold := 0 }

/-- A rule on `contract`'s `transfer` that needs `threshold` of `signers`. -/
def signedRule (contract : String) (signers : List Signer) (threshold : UInt32) : Rule :=
  { rule contract ["transfer"] [] with signers, threshold }

def i128Min : I128 := BitVec.intMin 128
def i128Max : I128 := BitVec.intMax 128
def u64Max : UInt64 := 0xFFFFFFFFFFFFFFFF
def u32Max : UInt32 := 0xFFFFFFFF
/-- The first index past `i32`'s range, to catch a reader that holds indices
as signed 32-bit integers. -/
def u32Half : UInt32 := 0x80000000

def alice : Val := .address (s "alice")
def bob : Val := .address (s "bob")

/-- A token contract's `transfer`, `approve` and `burn`, the shape most
cases use. -/
def token : String := "token"

/-! ## Values and conditions -/

def argEqI128 : Case where
  name := "arg-eq-i128"
  description := "argEq on an i128: equal value, other values, the same number as a u64, and the extremes."
  rules := [rule token ["transfer"] [.argEq 0 (.i128 100)]]
  batch := [
    call token "transfer" [.i128 100],
    call token "transfer" [.i128 101],
    call token "transfer" [.i128 (-100)],
    call token "transfer" [.u64 100],
    call token "transfer" [.i128 i128Min],
    call token "transfer" [.i128 i128Max]]

def argEqU64 : Case where
  name := "arg-eq-u64"
  description := "argEq on a u64: equal value, another value, the same number as an i128, and the maximum."
  rules := [rule token ["transfer"] [.argEq 0 (.u64 7), .argEq 1 (.u64 u64Max)]]
  batch := [
    call token "transfer" [.u64 7, .u64 u64Max],
    call token "transfer" [.u64 8, .u64 u64Max],
    call token "transfer" [.u64 7, .u64 0],
    call token "transfer" [.i128 7, .u64 u64Max],
    call token "transfer" [.u64 7, .i128 (-1)]]

def argEqBool : Case where
  name := "arg-eq-bool"
  description := "argEq on a bool: equal value, the other value, and integers holding one."
  rules := [rule token ["transfer"] [.argEq 0 (.bool true)]]
  batch := [
    call token "transfer" [.bool true],
    call token "transfer" [.bool false],
    call token "transfer" [.u64 1],
    call token "transfer" [.i128 1]]

/-- Each byte-string constructor against an equal payload, a prefix, an
extension, a case change, and the same payload under every other byte-string
constructor. -/
def byteCase (name ctor : String) (mk : Bytes → Val) : Case where
  name := s!"arg-eq-{name}"
  description := s!"argEq on {ctor}: the same bytes, a prefix, an extension, another case, and the same bytes under every other byte-string constructor."
  rules := [rule token ["transfer"] [.argEq 0 (mk (s "ab"))]]
  batch := [
    call token "transfer" [mk (s "ab")],
    call token "transfer" [mk (s "a")],
    call token "transfer" [mk (s "abc")],
    call token "transfer" [mk (s "aB")],
    call token "transfer" [mk (s "")],
    call token "transfer" [.bytes (s "ab")],
    call token "transfer" [.address (s "ab")],
    call token "transfer" [.symbol (s "ab")],
    call token "transfer" [.other (s "ab")]]

def argEqBytes : Case := byteCase "bytes" "bytes" .bytes
def argEqAddress : Case := byteCase "address" "an address" .address
def argEqSymbol : Case := byteCase "symbol" "a symbol" .symbol
def argEqOther : Case := byteCase "other" "an other value's XDR" .other

def argEqEmptyPayload : Case where
  name := "arg-eq-empty-payload"
  description := "argEq on empty bytes holds only for empty bytes, not an empty address, symbol or other value."
  rules := [rule token ["transfer"] [.argEq 0 (.bytes [])]]
  batch := [
    call token "transfer" [.bytes []],
    call token "transfer" [.address []],
    call token "transfer" [.symbol []],
    call token "transfer" [.other []],
    call token "transfer" [.bytes [0]]]

def argEqRawBytes : Case where
  name := "arg-eq-raw-bytes"
  description := "Payloads are raw bytes, not text: a zero byte, a high byte, and their prefixes and extensions."
  rules := [rule token ["transfer"] [.argEq 0 (.other [0x00, 0xff])]]
  batch := [
    call token "transfer" [.other [0x00, 0xff]],
    call token "transfer" [.other [0x00]],
    call token "transfer" [.other [0x00, 0xff, 0x00]],
    call token "transfer" [.other [0xff, 0x00]],
    call token "transfer" [.bytes [0x00, 0xff]]]

def argI128AtMost : Case where
  name := "arg-i128-at-most"
  description := "argI128AtMost 100: below, at and above the bound, negative values, the extremes, a u64, and a missing argument."
  rules := [rule token ["transfer"] [.argI128AtMost 0 100]]
  batch := [
    call token "transfer" [.i128 99],
    call token "transfer" [.i128 100],
    call token "transfer" [.i128 101],
    call token "transfer" [.i128 (-5)],
    call token "transfer" [.i128 i128Min],
    call token "transfer" [.i128 i128Max],
    call token "transfer" [.u64 5],
    call token "transfer" [.other (s "5")],
    call token "transfer" []]

def argI128AtMostExtremes : Case where
  name := "arg-i128-at-most-extremes"
  description := "Bounds at the i128 extremes and at -1: the comparison is signed."
  rules := [
    rule "min" ["f"] [.argI128AtMost 0 i128Min],
    rule "max" ["f"] [.argI128AtMost 0 i128Max],
    rule "neg" ["f"] [.argI128AtMost 0 (-1)]]
  batch := [
    call "min" "f" [.i128 i128Min],
    call "min" "f" [.i128 (i128Min + 1)],
    call "max" "f" [.i128 i128Max],
    call "max" "f" [.i128 i128Min],
    call "neg" "f" [.i128 (-1)],
    call "neg" "f" [.i128 0],
    call "neg" "f" [.i128 i128Max]]

def missingArguments : Case where
  name := "missing-arguments"
  description := "Conditions on argument 2: calls with zero, one and two arguments are refused; three or more are read."
  rules := [rule token ["transfer"] [.argEq 0 alice, .argI128AtMost 2 100]]
  batch := [
    call token "transfer" [],
    call token "transfer" [alice],
    call token "transfer" [alice, bob],
    call token "transfer" [alice, bob, .i128 100],
    call token "transfer" [alice, bob, .i128 100, .bool true],
    call token "transfer" [bob, alice, .i128 100]]

def indexEdges : Case where
  name := "index-edges"
  description := "Argument indices at the u32 edges: 0 on empty arguments, 2^31 and 2^32 - 1 are always missing."
  rules := [
    rule "zero" ["f"] [.argEq 0 (.bool true)],
    rule "half" ["f"] [.argEq u32Half (.bool true)],
    rule "max" ["f"] [.argEq u32Max (.bool true)],
    rule "max" ["g"] [.argI128AtMost u32Max i128Max]]
  batch := [
    call "zero" "f" [],
    call "zero" "f" [.bool true],
    call "half" "f" [.bool true, .bool true],
    call "max" "f" [.bool true],
    call "max" "g" [.i128 0],
    call "max" "g" []]

def rulesWithoutConditions : Case where
  name := "rule-without-conditions"
  description := "A rule with no conditions allows its calls whatever their arguments."
  rules := [rule token ["transfer"] []]
  batch := [
    call token "transfer" [],
    call token "transfer" [alice, bob, .i128 i128Max],
    call token "transfer" [.other (s "anything")]]

/-! ## Contracts and functions -/

def contractExactBytes : Case where
  name := "contract-exact-bytes"
  description := "Contract ids compare exactly: a prefix, an extension, another case and the empty id are refused, as are prefixes and extensions of a non-text id."
  rules := [
    rule token ["transfer"] [],
    { rule "" ["transfer"] [] with contract := [0x00, 0xff] }]
  batch := [
    call token "transfer" [],
    call "toke" "transfer" [],
    call "tokens" "transfer" [],
    call "Token" "transfer" [],
    call "" "transfer" [],
    .call [0x00, 0xff] (s "transfer") [],
    .call [0x00] (s "transfer") [],
    .call [0x00, 0xff, 0x00] (s "transfer") []]

def functionExactBytes : Case where
  name := "function-exact-bytes"
  description := "Function names compare exactly: a prefix, an extension, another case and the empty name are refused."
  rules := [rule token ["transfer", "approve"] []]
  batch := [
    call token "transfer" [],
    call token "approve" [],
    call token "transfe" [],
    call token "transfer_from" [],
    call token "Transfer" [],
    call token "" []]

def emptyFunctionList : Case where
  name := "empty-function-list"
  description := "A rule with an empty function list allows nothing; a rule listing the empty name allows only the empty name."
  rules := [
    rule "none" [] [],
    rule "empty-name" [""] []]
  batch := [
    call "none" "" [],
    call "none" "transfer" [],
    call "empty-name" "" [],
    call "empty-name" "transfer" []]

def duplicateFunctions : Case where
  name := "duplicate-functions"
  description := "A function listed twice is matched like one listed once."
  rules := [rule token ["transfer", "transfer", "approve"] []]
  batch := [
    call token "transfer" [],
    call token "approve" [],
    call token "burn" []]

/-! ## Creations -/

def creations : Case where
  name := "creations"
  description := "No rule allows a creation, even one whose wasm hash equals a rule's contract id."
  rules := [rule token ["transfer"] [], rule "" [""] []]
  batch := [
    create token,
    create "",
    create "transfer"]

def creationEmptyRuleSet : Case where
  name := "creation-empty-rule-set"
  description := "The empty rule set refuses a creation."
  rules := []
  batch := [create token]

def batchWithCreation : Case where
  name := "batch-with-creation"
  description := "A batch of allowed calls with one creation is refused."
  rules := [rule token ["transfer", "approve"] []]
  batch := [
    call token "transfer" [],
    create token,
    call token "approve" []]

/-! ## Rule sets and batches -/

def multiRuleOneMatches : Case where
  name := "multi-rule-one-matches"
  description := "Three rules on different contracts and functions; each call is matched by at most one of them."
  rules := [
    rule token ["transfer"] [.argI128AtMost 2 100],
    rule "pool" ["deposit"] [.argEq 0 alice],
    rule "dex" ["swap", "quote"] []]
  batch := [
    call token "transfer" [alice, bob, .i128 50],
    call "pool" "deposit" [alice],
    call "dex" "quote" [],
    call token "deposit" [alice],
    call "pool" "transfer" [alice, bob, .i128 50],
    call "dex" "transfer" [],
    call "other" "swap" []]

def conditionsBelongToTheirRule : Case where
  name := "conditions-belong-to-their-rule"
  description := "A cap on argument 2 of transfer does not read argument 2 of approve, and approve's condition does not constrain transfer."
  rules := [
    rule token ["transfer"] [.argI128AtMost 2 100],
    rule token ["approve"] [.argEq 0 alice]]
  batch := [
    call token "transfer" [bob, bob, .i128 100],
    call token "transfer" [alice, bob, .i128 101],
    call token "approve" [alice, bob, .i128 i128Max],
    call token "approve" [bob, bob, .i128 0]]

def overlappingRules : Case where
  name := "overlapping-rules"
  description := "Two rules for the same call: a context is allowed when either rule's conditions hold."
  rules := [
    rule token ["transfer"] [.argI128AtMost 2 100],
    rule token ["transfer"] [.argEq 1 alice]]
  batch := [
    call token "transfer" [bob, bob, .i128 50],
    call token "transfer" [bob, alice, .i128 500],
    call token "transfer" [bob, bob, .i128 500]]

def batchMixed : Case where
  name := "batch-mixed"
  description := "A batch of allowed and refused calls is refused as a whole."
  rules := [rule token ["transfer"] [.argI128AtMost 2 100], rule "dex" ["swap"] []]
  batch := [
    call "dex" "swap" [],
    call token "transfer" [alice, bob, .i128 10],
    call token "transfer" [alice, bob, .i128 1000],
    call "dex" "swap" [.bool true]]

def batchAllAllowed : Case where
  name := "batch-all-allowed"
  description := "A batch whose every call is allowed is allowed."
  rules := [rule token ["transfer"] [.argI128AtMost 2 100], rule "dex" ["swap"] []]
  batch := [
    call "dex" "swap" [],
    call token "transfer" [alice, bob, .i128 10],
    call token "transfer" [alice, bob, .i128 100]]

def emptyBatch : Case where
  name := "empty-batch"
  description := "Every rule set allows the empty batch; a caller collecting batches from an authorization tree never builds one."
  rules := [rule token ["transfer"] [.argEq 0 alice]]
  batch := []

def emptyBatchEmptyRuleSet : Case where
  name := "empty-batch-empty-rule-set"
  description := "The empty rule set allows the empty batch."
  rules := []
  batch := []

def emptyRuleSet : Case where
  name := "empty-rule-set"
  description := "The empty rule set refuses every call."
  rules := []
  batch := [call token "transfer" [], call "" "" []]

/-! ## Attenuation -/

/-- Three rules and a batch that tells each of them apart, for the attenuation
cases. -/
def threeRules : RuleSet := [
  rule token ["transfer", "approve", "burn", "transfer"] [.argI128AtMost 2 100],
  rule "pool" ["deposit"] [],
  rule "dex" ["swap"] [.argEq 0 alice]]

def threeRulesBatch : List Context := [
  call token "transfer" [alice, bob, .i128 50],
  call token "approve" [alice, bob, .i128 50],
  call token "burn" [alice, bob, .i128 50],
  call "pool" "deposit" [bob],
  call "dex" "swap" [alice],
  call "dex" "swap" [bob]]

def dropRule : Case where
  name := "attenuate-drop-rule"
  description := "dropRule at each index, at the length, and at 2^31 and 2^32 - 1."
  rules := threeRules
  batch := threeRulesBatch
  attenuations := [
    [.dropRule 0], [.dropRule 1], [.dropRule 2], [.dropRule 3],
    [.dropRule u32Half], [.dropRule u32Max]]

def emptyRuleSetSteps : Case where
  name := "attenuate-empty-rule-set"
  description := "Every attenuation step on the empty rule set is refused."
  rules := []
  batch := [call token "transfer" []]
  attenuations := [
    [.dropRule 0],
    [.addCond 0 (.argEq 0 alice)],
    [.removeFunctions 0 [s "transfer"]],
    [.removeSigners 0 [.delegated (s "alice")]],
    [.raiseThreshold 0 0]]

def addCond : Case where
  name := "attenuate-add-cond"
  description := "addCond of each condition kind at each index, of a condition on a missing argument, and at the length, 2^31 and 2^32 - 1."
  rules := threeRules
  batch := threeRulesBatch
  attenuations := [
    [.addCond 0 (.argEq 0 alice)],
    [.addCond 0 (.argI128AtMost 2 10)],
    [.addCond 1 (.argEq 0 bob)],
    [.addCond 2 (.argEq 5 alice)],
    [.addCond 2 (.argEq u32Max alice)],
    [.addCond 3 (.argEq 0 alice)],
    [.addCond u32Half (.argEq 0 alice)],
    [.addCond u32Max (.argEq 0 alice)]]

def removeFunctions : Case where
  name := "attenuate-remove-functions"
  description := "removeFunctions at each index removes every occurrence, keeps order, ignores absent names and prefixes, can empty the list, and is refused at the length, 2^31 and 2^32 - 1."
  rules := threeRules
  batch := threeRulesBatch
  attenuations := [
    [.removeFunctions 0 [s "transfer"]],
    [.removeFunctions 0 [s "approve"]],
    [.removeFunctions 0 []],
    [.removeFunctions 0 [s "mint"]],
    [.removeFunctions 0 [s "trans", s "transfer_from", s ""]],
    [.removeFunctions 0 [s "transfer", s "approve", s "burn"]],
    [.removeFunctions 1 [s "deposit", s "deposit"]],
    [.removeFunctions 2 [s "swap"]],
    [.removeFunctions 3 [s "transfer"]],
    [.removeFunctions u32Half [s "transfer"]],
    [.removeFunctions u32Max [s "transfer"]]]

def chains : Case where
  name := "attenuate-chains"
  description := "Lists of steps applied in order: the empty list, steps whose indices shift after a drop, and a list refused part-way through."
  rules := threeRules
  batch := threeRulesBatch
  attenuations := [
    [],
    [.addCond 0 (.argEq 0 alice), .removeFunctions 0 [s "burn"], .dropRule 1],
    [.dropRule 0, .dropRule 0],
    [.dropRule 0, .dropRule 0, .dropRule 0],
    [.dropRule 0, .dropRule 0, .dropRule 0, .dropRule 0],
    [.dropRule 2, .addCond 2 (.argEq 0 alice)],
    [.removeFunctions 0 [s "transfer"], .dropRule u32Max, .dropRule 0]]

/-! ## Signers -/

def sAlice : Signer := .delegated (s "alice")
def sBob : Signer := .delegated (s "bob")
/-- A key checked by a verifier contract. -/
def sKey : Signer := .external (s "verifier") (s "key")

/-- Five rules needing 0, 1, 2, 3 and 4 of the same three signers, one
contract each, and a call to each. -/
def thresholdRules : RuleSet :=
  [0, 1, 2, 3, 4].map fun k => signedRule s!"t{k}" [sAlice, sBob, sKey] k

def thresholdBatch : List Context :=
  [0, 1, 2, 3, 4].map fun k => call s!"t{k}" "transfer" []

def thresholdCase (name : String) (what : String) (auth : List Signer) : Case where
  name := s!"signers-threshold-{name}"
  description := s!"Thresholds 0, 1, 2, 3 (all three signers) and 4 (above the number of signers), with {what} authenticated."
  rules := thresholdRules
  batch := thresholdBatch
  authenticated := auth

def thresholdNone : Case := thresholdCase "none" "no signer" []
def thresholdOne : Case := thresholdCase "one" "one of the signers" [sAlice]
def thresholdTwo : Case := thresholdCase "two" "two of the signers" [sBob, sKey]
def thresholdAll : Case := thresholdCase "all" "every signer, in another order" [sKey, sAlice, sBob]

def ruleSignerRepeats : Case where
  name := "signers-repeated-in-rule"
  description := "A signer listed twice in a rule counts once: [alice, alice, bob] has two distinct signers, so threshold 3 is never met."
  rules := [
    signedRule "two" [sAlice, sAlice, sBob] 2,
    signedRule "three" [sAlice, sAlice, sBob] 3,
    signedRule "one" [sAlice, sAlice] 1]
  batch := [call "two" "transfer" [], call "three" "transfer" [], call "one" "transfer" []]
  authenticated := [sAlice, sBob, sAlice]

def authenticatedRepeats : Case where
  name := "signers-repeated-in-authenticated"
  description := "A signer authenticated twice counts once."
  rules := [signedRule "two" [sAlice, sBob] 2, signedRule "one" [sAlice, sBob] 1]
  batch := [call "two" "transfer" [], call "one" "transfer" []]
  authenticated := [sAlice, sAlice]

/-- A delegated signer and external signers whose bytes equal its address,
split between verifier and key in every way. -/
def equalBytesRules : RuleSet := [
  signedRule "delegated" [.delegated (s "ab")] 1,
  signedRule "external" [.external (s "ab") []] 1,
  signedRule "split" [.external (s "a") (s "b")] 1,
  signedRule "key" [.external [] (s "ab")] 1]

def equalBytesBatch : List Context :=
  ["delegated", "external", "split", "key"].map fun c => call c "transfer" []

def delegatedVersusExternal : Case where
  name := "signers-delegated-versus-external"
  description := "Signers compare constructor first: an authenticated delegated signer satisfies only the delegated rule, though the external rules' signers hold the same bytes."
  rules := equalBytesRules
  batch := equalBytesBatch
  authenticated := [.delegated (s "ab")]

def externalVersusDelegated : Case where
  name := "signers-external-versus-delegated"
  description := "An external signer equals only an external signer with the same verifier and the same key."
  rules := equalBytesRules
  batch := equalBytesBatch
  authenticated := [.external (s "ab") []]

def missingSigners : Case where
  name := "signers-missing"
  description := "Signers outside the rule, and signers whose bytes are a prefix or an extension of a rule signer's, do not count; a rule with no signers and threshold 1 allows nothing."
  rules := [
    signedRule "alice" [sAlice] 1,
    signedRule "key" [sKey] 1,
    signedRule "nobody" [] 1,
    signedRule "free" [] 0]
  batch := [call "alice" "transfer" [], call "key" "transfer" [], call "nobody" "transfer" [],
    call "free" "transfer" []]
  authenticated := [sBob, .delegated (s "alic"), .delegated (s "alice2"),
    .external (s "verifier") (s "key2")]

def signersBatch (name what : String) (auth : List Signer) : Case where
  name := s!"signers-batch-{name}"
  description := s!"One authenticated list covers the whole batch: a batch needing alice for token and bob for the vault, with {what}."
  rules := [signedRule token [sAlice] 1, { signedRule "vault" [sBob] 1 with functions := .only [s "deposit"] }]
  batch := [call token "transfer" [alice, bob, .i128 5], call "vault" "deposit" []]
  authenticated := auth

def batchOneMissing : Case := signersBatch "one-missing" "only alice authenticated" [sAlice]
def batchAllPresent : Case := signersBatch "all-present" "both authenticated" [sBob, sAlice]

/-- A two-of-three rule, a rule without signers, and a batch that tells them
apart, for the signer attenuation cases. -/
def signedRules : RuleSet := [
  signedRule token [sAlice, sBob, sKey, sAlice] 2,
  rule "pool" ["deposit"] []]

def signedBatch : List Context := [call token "transfer" [], call "pool" "deposit" []]

def removeSigners : Case where
  name := "attenuate-remove-signers"
  description := "removeSigners removes every occurrence of each listed signer, keeps the threshold and the order, matches signers exactly, can empty the list, and is refused at the length, 2^31 and 2^32 - 1."
  rules := signedRules
  batch := signedBatch
  authenticated := [sAlice, sKey]
  attenuations := [
    [.removeSigners 0 [sAlice]],
    [.removeSigners 0 [sBob]],
    [.removeSigners 0 []],
    [.removeSigners 0 [.external (s "alice") [], .delegated (s "verifier"), .delegated (s "alic")]],
    [.removeSigners 0 [sAlice, sBob, sKey]],
    [.removeSigners 1 [sAlice]],
    [.removeSigners 2 [sAlice]],
    [.removeSigners u32Half [sAlice]],
    [.removeSigners u32Max [sAlice]]]

def raiseThreshold : Case where
  name := "attenuate-raise-threshold"
  description := "raiseThreshold to the same threshold, a higher one, the number of distinct signers, above it and 2^32 - 1; lowering is refused with threshold_lowered; an index out of range is refused with no_such_rule whatever the threshold."
  rules := signedRules
  batch := signedBatch
  authenticated := [sAlice, sKey]
  attenuations := [
    [.raiseThreshold 0 2],
    [.raiseThreshold 0 3],
    [.raiseThreshold 0 4],
    [.raiseThreshold 0 u32Max],
    [.raiseThreshold 0 1],
    [.raiseThreshold 0 0],
    [.raiseThreshold 1 0],
    [.raiseThreshold 1 1],
    [.raiseThreshold 2 5],
    [.raiseThreshold 2 0],
    [.raiseThreshold u32Max 0]]

def signerChains : Case where
  name := "attenuate-signer-chains"
  description := "Lists of all five step kinds: a threshold raised then a signer removed, a refusal for lowering part-way through, and a threshold raised past the remaining signers."
  rules := signedRules
  batch := signedBatch
  authenticated := [sAlice, sBob, sKey]
  attenuations := [
    [.raiseThreshold 0 3, .removeSigners 0 [sKey]],
    [.removeSigners 0 [sBob], .raiseThreshold 0 2, .addCond 1 (.argEq 0 alice)],
    [.raiseThreshold 0 3, .raiseThreshold 0 2, .dropRule 0],
    [.dropRule 0, .raiseThreshold 0 1, .removeFunctions 0 [s "deposit"]],
    [.removeSigners 0 [sAlice, sKey], .raiseThreshold 0 2]]

/-! ## Caps -/

/-- A cap on argument 2 (a transfer's amount): at most `limit` within `period`
ledgers. -/
def cap (limit : Int) (period : UInt32) (amountArg : UInt32 := 2) : Cap :=
  ⟨BitVec.ofInt 128 limit, period, amountArg⟩

def transfer (amount : Int) : Context :=
  call token "transfer" [alice, bob, .i128 (BitVec.ofInt 128 amount)]

/-- An uncapped transfer rule, a transfer rule capped at 100 per 10 ledgers,
and a vault rule, for the cap step cases. -/
def capRules : RuleSet := [
  rule token ["transfer"] [],
  { rule token ["transfer", "approve"] [] with cap := some (cap 100 10) },
  rule "vault" ["deposit"] []]

def capBatch : List Context := [transfer 5, transfer 1000, call "vault" "deposit" []]

def capsLeaveVerdicts : Case where
  name := "caps-leave-verdicts"
  description := "allows and allows_all do not read a rule's cap: a capped rule allows a call whose amount exceeds its limit, and one with no amount at all."
  rules := [{ rule token ["transfer"] [] with cap := some (cap 10 5) }]
  batch := [transfer 5, transfer 1000, call token "transfer" [], call token "transfer" [.u64 1]]

def addCap : Case where
  name := "attenuate-add-cap"
  description := "addCap on a rule without a cap, with the largest limit, period and argument index; refused with cap_present on a capped rule, with invalid_cap for a limit that is not positive or a period of 0, and with no_such_rule at the length, 2^31 and 2^32 - 1, before any other refusal."
  rules := capRules
  batch := capBatch
  attenuations := [
    [.addCap 0 (cap 50 5)],
    [.addCap 2 (cap 1 1 0)],
    [.addCap 0 (cap ((2 : Int) ^ 127 - 1) u32Max u32Max)],
    [.addCap 1 (cap 50 5)],
    [.addCap 1 (cap 0 0)],
    [.addCap 0 (cap 0 5)],
    [.addCap 0 (cap (-1) 5)],
    [.addCap 0 (cap (-(2 : Int) ^ 127) 5)],
    [.addCap 0 (cap 50 0)],
    [.addCap 3 (cap 50 5)],
    [.addCap 3 (cap 0 0)],
    [.addCap u32Half (cap 50 5)],
    [.addCap u32Max (cap 50 5)]]

def lowerCapLimit : Case where
  name := "attenuate-lower-cap-limit"
  description := "lowerCapLimit to the same limit, a lower one and 1; refused with limit_raised above the current limit, with invalid_cap at 0 and below, with no_cap on a rule without a cap, and with no_such_rule out of range."
  rules := capRules
  batch := capBatch
  attenuations := [
    [.lowerCapLimit 1 (BitVec.ofInt 128 100)],
    [.lowerCapLimit 1 (BitVec.ofInt 128 60)],
    [.lowerCapLimit 1 (BitVec.ofInt 128 1)],
    [.lowerCapLimit 1 (BitVec.ofInt 128 101)],
    [.lowerCapLimit 1 i128Max],
    [.lowerCapLimit 1 (BitVec.ofInt 128 0)],
    [.lowerCapLimit 1 (BitVec.ofInt 128 (-5))],
    [.lowerCapLimit 1 i128Min],
    [.lowerCapLimit 0 (BitVec.ofInt 128 50)],
    [.lowerCapLimit 3 (BitVec.ofInt 128 50)],
    [.lowerCapLimit u32Max (BitVec.ofInt 128 50)]]

def lengthenCapPeriod : Case where
  name := "attenuate-lengthen-cap-period"
  description := "lengthenCapPeriod to the same period, a longer one and 2^32 - 1; refused with period_shortened below the current period, 0 included, with no_cap on a rule without a cap, and with no_such_rule out of range."
  rules := capRules
  batch := capBatch
  attenuations := [
    [.lengthenCapPeriod 1 10],
    [.lengthenCapPeriod 1 11],
    [.lengthenCapPeriod 1 u32Max],
    [.lengthenCapPeriod 1 9],
    [.lengthenCapPeriod 1 0],
    [.lengthenCapPeriod 0 20],
    [.lengthenCapPeriod 2 20],
    [.lengthenCapPeriod 3 20],
    [.lengthenCapPeriod u32Half 20]]

def capChains : Case where
  name := "attenuate-cap-chains"
  description := "Lists mixing the cap steps with the others: a cap added then lowered and lengthened, a drop that moves the capped rule's index, a cap added twice, and a refusal part-way through."
  rules := capRules
  batch := capBatch
  attenuations := [
    [.addCap 0 (cap 50 5), .lowerCapLimit 0 (BitVec.ofInt 128 20), .lengthenCapPeriod 0 8],
    [.dropRule 0, .lowerCapLimit 0 (BitVec.ofInt 128 10), .lengthenCapPeriod 0 30],
    [.dropRule 0, .lowerCapLimit 1 (BitVec.ofInt 128 10)],
    [.addCap 2 (cap 5 5 0), .addCap 2 (cap 4 5 0)],
    [.lowerCapLimit 1 (BitVec.ofInt 128 50), .lowerCapLimit 1 (BitVec.ofInt 128 60)],
    [.addCond 1 (.argI128AtMost 2 (BitVec.ofInt 128 10)), .lengthenCapPeriod 1 12,
      .removeFunctions 1 [s "approve"]]]

/-! ## Wildcards, expiry and generations -/

/-- A rule matching every function of `contract` but `except`. -/
def wildcard (contract : String) (except : List String) (conds : List Cond) : Rule :=
  { rule contract [] conds with functions := .anyExcept (except.map s) }

def wildcardFunctions : Case where
  name := "wildcard-functions"
  description := "A wildcard rule allows every function of its contract, the empty name and names it was never told about included, except the ones it excludes, compared exactly; never another contract or a creation."
  rules := [wildcard token [] [], wildcard "vault" ["withdraw", ""] []]
  batch := [
    call token "transfer" [],
    call token "" [],
    call token "anything_at_all" [.u64 42],
    call "tokens" "transfer" [],
    call "vault" "deposit" [],
    call "vault" "withdraw" [],
    call "vault" "withdraw_all" [],
    call "vault" "" [],
    create token]

def ruleTimeIgnored : Case where
  name := "allows-reads-no-time-or-generation"
  description := "allows and allows_all read neither a rule's last ledger nor its generation: rules valid until ledger 0 and issued under generation 2^64 - 1 allow as they would without them."
  rules := [
    { rule token ["transfer"] [] with validUntil := some 0, generation := some u64Max },
    { rule "vault" ["deposit"] [] with validUntil := some u32Max }]
  batch := [call token "transfer" [], call "vault" "deposit" [], call "vault" "withdraw" []]

def strPkg : Bytes := s "pkg_"

def argIn : Case where
  name := "arg-in"
  description := "argIn holds when the argument equals one of its values, compared as argEq compares: each listed value, an unlisted one, the same bytes under another constructor, a missing argument, and an empty list that allows nothing."
  rules := [
    rule token ["transfer"] [.argIn 0 [.string (s "ok"), .u64 7, .symbol (s "sym")]],
    rule "vault" ["deposit"] [.argIn 0 []]]
  batch := [
    call token "transfer" [.string (s "ok")],
    call token "transfer" [.u64 7],
    call token "transfer" [.symbol (s "sym")],
    call token "transfer" [.string (s "no")],
    call token "transfer" [.symbol (s "ok")],
    call token "transfer" [.string (s "sym")],
    call token "transfer" [.i128 7],
    call token "transfer" [],
    call "vault" "deposit" [.u64 7]]

def argStrPrefix : Case where
  name := "arg-str-prefix"
  description := "argStrPrefix holds only for a string argument whose bytes start with the prefix: the prefix itself, a longer string, a shorter one, another case, the prefix inside, and a symbol, bytes or other value with the same bytes; the empty prefix holds on every string."
  rules := [
    rule token ["publish"] [.argStrPrefix 1 strPkg],
    rule "vault" ["deposit"] [.argStrPrefix 0 []]]
  batch := [
    call token "publish" [.bool true, .string (s "pkg_a")],
    call token "publish" [.bool true, .string strPkg],
    call token "publish" [.bool true, .string (s "pkg")],
    call token "publish" [.bool true, .string (s "Pkg_a")],
    call token "publish" [.bool true, .string (s "xpkg_a")],
    call token "publish" [.bool true, .symbol (s "pkg_a")],
    call token "publish" [.bool true, .bytes (s "pkg_a")],
    call token "publish" [.bool true, .other (s "pkg_a")],
    call token "publish" [.string (s "pkg_a")],
    call "vault" "deposit" [.string []],
    call "vault" "deposit" [.symbol []]]

def argEqString : Case where
  name := "arg-eq-string"
  description := "argEq on a string: the same bytes, a prefix, an extension, and the same bytes as a symbol, bytes or other value."
  rules := [rule token ["transfer"] [.argEq 0 (.string (s "abc"))]]
  batch := [
    call token "transfer" [.string (s "abc")],
    call token "transfer" [.string (s "ab")],
    call token "transfer" [.string (s "abcd")],
    call token "transfer" [.symbol (s "abc")],
    call token "transfer" [.bytes (s "abc")],
    call token "transfer" [.other (s "abc")]]

/-- A wildcard token rule excluding `burn`, a vault rule listing two
functions, and a capped token rule, for the function and validity steps. -/
def m4Rules : RuleSet := [
  wildcard token ["burn"] [],
  rule "vault" ["deposit", "withdraw"] [],
  { rule token ["transfer"] [] with validUntil := some 10, cap := some ⟨100, 10, 2⟩ }]

def m4Batch : List Context := [
  call token "transfer" [alice, bob, .i128 5],
  call token "burn" [],
  call token "approve" [],
  call "vault" "deposit" [],
  call "vault" "withdraw" []]

def removeFunctionsWildcard : Case where
  name := "attenuate-remove-functions-wildcard"
  description := "removeFunctions on a wildcard adds the removed names to the ones it excludes, repeats and names it already excludes included; on a list it removes them."
  rules := m4Rules
  batch := m4Batch
  attenuations := [
    [.removeFunctions 0 [s "approve"]],
    [.removeFunctions 0 [s "burn", s "approve", s "approve"]],
    [.removeFunctions 0 []],
    [.removeFunctions 0 [s "transfer"], .removeFunctions 0 [s "approve"]],
    [.removeFunctions 1 [s "deposit"]]]

def restrictFunctions : Case where
  name := "attenuate-restrict-functions"
  description := "restrictFunctions turns a wildcard into the list of named functions it does not exclude, and keeps a list's functions that are also named, in the list's order; refused at the length, 2^31 and 2^32 - 1."
  rules := m4Rules
  batch := m4Batch
  attenuations := [
    [.restrictFunctions 0 [s "transfer", s "approve"]],
    [.restrictFunctions 0 [s "burn", s "transfer"]],
    [.restrictFunctions 0 []],
    [.restrictFunctions 1 [s "withdraw", s "deposit", s "mint"]],
    [.restrictFunctions 1 [s "Deposit", s "depo"]],
    [.removeFunctions 0 [s "approve"], .restrictFunctions 0 [s "approve", s "transfer"]],
    [.restrictFunctions 3 [s "transfer"]],
    [.restrictFunctions u32Half [s "transfer"]],
    [.restrictFunctions u32Max [s "transfer"]]]

def lowerValidUntil : Case where
  name := "attenuate-lower-valid-until"
  description := "lowerValidUntil gives a rule without a last ledger one, and moves one earlier or keeps it; refused with valid_until_raised past the current one, and with no_such_rule out of range first. allows reads no last ledger, so the verdicts stay as they were."
  rules := m4Rules
  batch := m4Batch
  attenuations := [
    [.lowerValidUntil 0 5],
    [.lowerValidUntil 0 u32Max],
    [.lowerValidUntil 2 10],
    [.lowerValidUntil 2 0],
    [.lowerValidUntil 2 11],
    [.lowerValidUntil 2 u32Max],
    [.lowerValidUntil 0 7, .lowerValidUntil 0 8],
    [.lowerValidUntil 0 7, .lowerValidUntil 0 6],
    [.lowerValidUntil 3 0],
    [.lowerValidUntil u32Max 0]]

def all : List Case := [
  argEqI128, argEqU64, argEqBool, argEqBytes, argEqAddress, argEqSymbol, argEqOther,
  argEqEmptyPayload, argEqRawBytes, argI128AtMost, argI128AtMostExtremes, missingArguments,
  indexEdges, rulesWithoutConditions,
  contractExactBytes, functionExactBytes, emptyFunctionList, duplicateFunctions,
  creations, creationEmptyRuleSet, batchWithCreation,
  multiRuleOneMatches, conditionsBelongToTheirRule, overlappingRules, batchMixed,
  batchAllAllowed, emptyBatch, emptyBatchEmptyRuleSet, emptyRuleSet,
  dropRule, emptyRuleSetSteps, addCond, removeFunctions, chains,
  thresholdNone, thresholdOne, thresholdTwo, thresholdAll, ruleSignerRepeats, authenticatedRepeats,
  delegatedVersusExternal, externalVersusDelegated, missingSigners, batchOneMissing,
  batchAllPresent, removeSigners, raiseThreshold, signerChains,
  capsLeaveVerdicts, addCap, lowerCapLimit, lengthenCapPeriod, capChains,
  wildcardFunctions, ruleTimeIgnored, argIn, argStrPrefix, argEqString, removeFunctionsWildcard,
  restrictFunctions, lowerValidUntil]

end Conformance.Cases
