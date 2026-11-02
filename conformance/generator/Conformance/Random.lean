import Conformance.Cases

/-!
# Randomized cases

A seeded generator of vector specifications. Rule sets, contexts and
attenuation steps are drawn from small universes of contract ids, function
names, payloads and integers that include each other's prefixes and
extensions and the integer extremes, so random contexts often hit a rule and
random comparisons often meet the edge cases. Calls are mostly built from a
rule in the set, with arguments that usually satisfy that rule's conditions,
so that the vectors mix allowed and refused contexts.

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
instance : Inhabited Rule := ⟨{ contract := [], functions := [], conds := [] }⟩

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

def rule : Gen Rule := do
  let contract ← pick contracts
  let functions ← listOf (← pick [0, 1, 1, 1, 2, 2, 3, 3]) (pick functions)
  let conds ← listOf (← below 3) cond
  return { contract, functions, conds }

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

def step (rs : RuleSet) : Gen Attenuation := do
  let i ← ruleIndex rs
  match ← below 3 with
  | 0 => return .dropRule i
  | 1 => return .addCond i (← cond)
  | _ =>
    let names := functions ++ rs.flatMap (·.functions)
    return .removeFunctions i (← listOf (← below 3) (pick names))

/-- `n` as a decimal string of at least `w` digits. -/
def pad (w n : Nat) : String :=
  let d := toString n
  String.ofList (List.replicate (w - d.length) '0') ++ d

def case (seed : UInt64) (k : Nat) : Case :=
  let gen : Gen Case := do
    let rules ← ruleSet
    let batch ← listOf (← pick [0, 1, 1, 2, 2, 3, 4, 5]) (context rules)
    let attenuations ← listOf 3 do listOf ((← below 2) + 1) (step rules)
    return {
      name := s!"random-{pad 3 k}"
      description := s!"Randomized case {k} of seed {seed}."
      rules, batch, attenuations }
  (gen.run ⟨seed + UInt64.ofNat k⟩).1

def cases (seed : UInt64) (count : Nat) : List Case :=
  (List.range count).map (case seed)

end Conformance.Random
