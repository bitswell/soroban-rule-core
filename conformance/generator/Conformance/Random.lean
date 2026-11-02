import Conformance.Cases

/-!
# Randomized cases

A seeded generator of vector specifications. Rule sets, contexts, signers, caps
and attenuation steps are drawn from small universes of contract ids, function
names, payloads, integers, signers and cap parameters that include each other's
prefixes and extensions, the integer extremes, and delegated and external
signers with equal bytes, so random contexts often hit a rule and random
comparisons often meet the edge cases. Calls are mostly built from a rule in the set, with arguments
that usually satisfy that rule's conditions, and the authenticated signers
usually include some of the rules' signers, so that the vectors mix allowed and
refused contexts.

The generator is SplitMix64, written out here so that a seed always produces
the same vectors whatever the Lean release. Case `k` of seed `seed` is drawn
from its own stream, seeded with `seed + k`.
-/

namespace Conformance.Random

open RuleCore RuleCore.Chain Conformance.Cases

/-- The seed and number of the committed randomized vectors. -/
def defaultSeed : UInt64 := 20261102
def defaultCount : Nat := 100

/-- SplitMix64 state. -/
structure Rng where
  state : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

abbrev Gen := StateM Rng

def next : Gen UInt64 :=
  modifyGet Rng.next

/-- A number below `n`, or `0` when `n` is `0`. -/
def below (n : Nat) : Gen Nat := do
  let x ← next
  return if n = 0 then 0 else x.toNat % n

/-- The defaults `pick` never returns, since every list it is given is
non-empty. -/
instance : Inhabited Val := ⟨.bool false⟩
instance : Inhabited Cond := ⟨.argEq 0 (.bool false)⟩
instance : Inhabited Rule :=
  ⟨{ contract := [], functions := [], conds := [], signers := [], threshold := 0 }⟩
instance : Inhabited Cap := ⟨⟨0, 0, 0⟩⟩
instance : Inhabited Signer := ⟨.delegated []⟩

def pick {α : Type} [Inhabited α] (xs : List α) : Gen α := do
  return xs.getD (← below xs.length) default

def listOf {α : Type} (n : Nat) (g : Gen α) : Gen (List α) :=
  (List.range n).mapM fun _ => g

/-! ## Universes -/

def contracts : List Bytes := ["", "c", "c1", "c10", "c2"].map s
def functions : List Bytes := ["", "f", "fo", "foo", "g"].map s
def payloads : List Bytes := [[], s "a", s "ab", s "abc", s "b", [0x00, 0xff]]
def i128s : List I128 := [i128Min, i128Min + 1, -1, 0, 1, 7, 100, i128Max - 1, i128Max]
def u64s : List UInt64 := [0, 1, 7, 100, u64Max]
/-- Argument indices, weighted towards the first few so that conditions often
read an argument a call has. -/
def argIndices : List UInt32 := [0, 0, 0, 0, 1, 1, 1, 2, 2, 3, u32Half, u32Max]

/-- Signers: two delegated, two external, one external whose verifier holds a
delegated signer's address, and a delegated address that extends another. -/
def signers : List Signer := [
  .delegated (s "a"), .delegated (s "b"), .external (s "v") (s "k"), .external (s "v") (s "k2"),
  .external (s "a") [], .delegated (s "ab")]

def val : Gen Val := do
  match ← below 7 with
  | 0 => return .i128 (← pick i128s)
  | 1 => return .u64 (← pick u64s)
  | 2 => return .bool ((← below 2) = 1)
  | 3 => return .bytes (← pick payloads)
  | 4 => return .address (← pick payloads)
  | 5 => return .symbol (← pick payloads)
  | _ => return .other (← pick payloads)

def cond : Gen Cond := do
  let i ← pick argIndices
  if (← below 2) = 0 then return .argEq i (← val)
  else return .argI128AtMost i (← pick i128s)

/-- A threshold for a rule listing `n` signers: half the time 0, otherwise
anything from 0 to one more than `n`. -/
def threshold (n : Nat) : Gen UInt32 := do
  if (← below 2) = 0 then return 0
  return UInt32.ofNat (← below (n + 2))

/-- Cap limits, periods and amount indices, with the invalid values and the
extremes. -/
def capLimits : List Int := [0, 1, 5, 10, 100, 2 ^ 127 - 1]
def capPeriods : List UInt32 := [0, 1, 2, 3, 10, u32Max]
def capArgs : List UInt32 := [0, 1, 2, 2, 2, 3, u32Max]

def cap : Gen Cap := do
  return ⟨BitVec.ofInt 128 (← pick capLimits), ← pick capPeriods, ← pick capArgs⟩

def rule : Gen Rule := do
  let contract ← pick contracts
  let functions ← listOf (← pick [0, 1, 1, 1, 2, 2, 3, 3]) (pick functions)
  let conds ← listOf (← below 3) cond
  let ss ← listOf (← pick [0, 0, 1, 1, 2, 3]) (pick signers)
  let threshold ← threshold ss.length
  let cap ← if (← below 3) = 0 then some <$> cap else pure none
  return { contract, functions, conds, signers := ss, threshold, cap }

def ruleSet : Gen RuleSet := do
  listOf (← pick [0, 1, 2, 2, 3, 4]) rule

def condIndex : Cond → UInt32
  | .argEq i _ => i
  | .argI128AtMost i _ => i

/-- A value that satisfies `c` when it is `c`'s argument. -/
def satisfying : Cond → Gen Val
  | .argEq _ v => pure v
  | .argI128AtMost _ n => do
    pick (.i128 n :: (i128s.filter (·.toInt ≤ n.toInt)).map .i128)

/-- Argument `j` of a call built from `r`: seven times in eight, a value
satisfying one of `r`'s conditions on argument `j`, if there is one. -/
def argAt (r : Rule) (j : Nat) : Gen Val := do
  match r.conds.filter (fun c => (condIndex c).toNat = j) with
  | [] => val
  | cs => if (← below 8) = 0 then val else satisfying (← pick cs)

/-- A call built from `r`: usually its contract, one of its functions, and
enough arguments for its conditions on the first few indices. -/
def callFrom (r : Rule) : Gen Context := do
  let contract ← if (← below 8) = 0 then pick contracts else pure r.contract
  let fs := if r.functions.isEmpty then functions else r.functions
  let function ← if (← below 8) = 0 then pick functions else pick fs
  let needed := (r.conds.map fun c => (condIndex c).toNat + 1).filter (· ≤ 4) |>.foldl max 0
  let len ← if (← below 4) = 0 then below 5 else pure needed
  let args ← (List.range len).mapM (argAt r)
  return .call contract function args

def context (rs : RuleSet) : Gen Context := do
  let k ← below 10
  if k = 0 then
    return .create (← pick (contracts ++ payloads))
  else if k ≤ 8 && !rs.isEmpty then
    callFrom (← pick rs)
  else
    callFrom (← rule)

/-- A rule index: usually in range for `rs`, sometimes its length, and
sometimes at the `u32` edges. -/
def ruleIndex (rs : RuleSet) : Gen UInt32 := do
  match ← below 10 with
  | 0 => return UInt32.ofNat rs.length
  | 1 => pick [u32Half, u32Max]
  | _ => return UInt32.ofNat (← below rs.length)

/-- The signers the batch's authorization authenticated: usually some of the
rules' signers, plus random ones, sometimes repeated. -/
def authenticated (rs : RuleSet) : Gen (List Signer) := do
  let own := rs.flatMap (·.signers)
  let fromRules ← listOf (← below (own.length + 1)) (pick own)
  let extra ← listOf (← pick [0, 0, 1, 2]) (pick signers)
  return fromRules ++ extra

def step (rs : RuleSet) : Gen Attenuation := do
  let i ← ruleIndex rs
  let current := (rs[i.toNat]?.bind (·.cap))
  match ← below 8 with
  | 0 => return .dropRule i
  | 1 => return .addCond i (← cond)
  | 2 =>
    let names := functions ++ rs.flatMap (·.functions)
    return .removeFunctions i (← listOf (← below 3) (pick names))
  | 3 =>
    let pool := signers ++ rs.flatMap (·.signers)
    return .removeSigners i (← listOf (← below 3) (pick pool))
  | 4 =>
    let current := (rs[i.toNat]?.map (·.threshold.toNat)).getD 0
    return .raiseThreshold i (UInt32.ofNat (current + (← below 3) - 1))
  | 5 => return .addCap i (← cap)
  | 6 =>
    let limit := (current.map (·.limit.toInt)).getD 10
    return .lowerCapLimit i (BitVec.ofInt 128 (← pick [limit, limit - 1, limit + 1, 0, 1]))
  | _ =>
    let period := (current.map (·.period.toNat)).getD 10
    return .lengthenCapPeriod i (UInt32.ofNat (← pick [period, period + 1, period - 1, 0]))

/-- `n` as a decimal string of at least `w` digits. -/
def pad (w n : Nat) : String :=
  let d := toString n
  String.ofList (List.replicate (w - d.length) '0') ++ d

def case (seed : UInt64) (k : Nat) : Case :=
  let gen : Gen Case := do
    let rules ← ruleSet
    let batch ← listOf (← pick [0, 1, 1, 2, 2, 3, 4, 5]) (context rules)
    let authenticated ← authenticated rules
    let attenuations ← listOf 3 do listOf ((← below 2) + 1) (step rules)
    return {
      name := s!"random-{pad 3 k}"
      description := s!"Randomized case {k} of seed {seed}."
      rules, batch, authenticated, attenuations }
  (gen.run ⟨seed + UInt64.ofNat k⟩).1

def cases (seed : UInt64) (count : Nat) : List Case :=
  (List.range count).map (case seed)

end Conformance.Random
