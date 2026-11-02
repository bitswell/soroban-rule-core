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

def rule (contract : String) (functions : List String) (conds : List Cond) : Rule :=
  { contract := s contract, functions := functions.map s, conds := conds }

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
    { contract := [0x00, 0xff], functions := [s "transfer"], conds := [] }]
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
    [.removeFunctions 0 [s "transfer"]]]

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

def all : List Case := [
  argEqI128, argEqU64, argEqBool, argEqBytes, argEqAddress, argEqSymbol, argEqOther,
  argEqEmptyPayload, argEqRawBytes, argI128AtMost, argI128AtMostExtremes, missingArguments,
  indexEdges, rulesWithoutConditions,
  contractExactBytes, functionExactBytes, emptyFunctionList, duplicateFunctions,
  creations, creationEmptyRuleSet, batchWithCreation,
  multiRuleOneMatches, conditionsBelongToTheirRule, overlappingRules, batchMixed,
  batchAllAllowed, emptyBatch, emptyBatchEmptyRuleSet, emptyRuleSet,
  dropRule, emptyRuleSetSteps, addCond, removeFunctions, chains]

end Conformance.Cases
