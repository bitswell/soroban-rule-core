import Conformance.Random
import RuleCore.Model.Budget

/-!
# Budget traces

A `Trace` is the specification of one budget trace: a starting tree and a list
of operations, each a spend, a delegation or a refill. `Trace.toJson` runs the
operations through the Lean model's `RuleCore.Budget.Op.apply`, each on the
tree the operations before it left (the same tree after a refusal), and writes
every operation with its expected outcome: the tree after it, or the refusal.

The named traces exercise oversubscribed siblings, a spend exhausting a middle
ancestor, the refusal naming the nearest overdrawn node, overflowing sums,
malformed trees, delegation then spend, refills, several roots and a tree
whose spent amount starts above its allowance. The randomized traces draw
trees of up to six nodes, with parents below their own index and allowances
from a small universe that includes the `i128` extremes, and operations whose
indices are mostly in range and whose amounts are mostly near the allowances.
-/

namespace Conformance.Budget

open RuleCore.Budget
open RuleCore.Cap (i128Min i128Max)
open Conformance.Random (Gen below pick)

/-- The version of the budget trace format in `conformance/README.md`. -/
def formatVersion : Nat := 1

/-- The number of committed randomized traces, of the vectors' seed. -/
def defaultCount : Nat := 50

def u32Max : Nat := 2 ^ 32 - 1

structure Trace where
  /-- The file name, without `.json`. -/
  name : String
  description : String
  start : Tree
  ops : List Op

/-! ## Encoding -/

def encodeAmount (n : Int) : Json := .str (toString n)

def encodeNode (n : Node) : Json :=
  .obj [
    ("parent", match n.parent with
      | some p => .num p
      | none => .null),
    ("allowance", encodeAmount n.allowance),
    ("spent", encodeAmount n.spent)]

def encodeTree (t : Tree) : Json :=
  .arr (t.map encodeNode)

def encodeBudgetError : BudgetError → Json
  | .malformed => .str "malformed"
  | .noSuchNode i => .obj [("no_such_node", .num i)]
  | .negativeAmount => .str "negative_amount"
  | .overdrawn i => .obj [("overdrawn", .num i)]
  | .overflow => .str "overflow"
  | .treeFull => .str "tree_full"

def encodeOp : Op → List (String × Json)
  | .spend i amount => [("op", .str "spend"), ("node", .num i), ("amount", encodeAmount amount)]
  | .delegate p allowance =>
    [("op", .str "delegate"), ("parent", .num p), ("allowance", encodeAmount allowance)]
  | .refill i amount => [("op", .str "refill"), ("node", .num i), ("amount", encodeAmount amount)]

/-- Each operation with the model's outcome, applied to the tree the
operations before it left. -/
def opsJson : Tree → List Op → List Json
  | _, [] => []
  | t, op :: ops =>
    let entry (expected : Json) : Json := .obj (encodeOp op ++ [("expected", expected)])
    match op.apply t with
    | .ok t' => entry (tagged "ok" (encodeTree t')) :: opsJson t' ops
    | .error e => entry (tagged "error" (encodeBudgetError e)) :: opsJson t ops

def Trace.toJson (tr : Trace) : Json :=
  .obj [
    ("format", .num formatVersion),
    ("name", .str tr.name),
    ("description", .str tr.description),
    ("start", encodeTree tr.start),
    ("valid", .bool tr.start.valid),
    ("ops", .arr (opsJson tr.start tr.ops))]

def inI128 (n : Int) : Bool := decide (i128Min ≤ n ∧ n ≤ i128Max)

def inU32 (n : Nat) : Bool := decide (n ≤ u32Max)

def Node.inRange (n : Node) : Bool :=
  (match n.parent with
    | some p => inU32 p
    | none => true) && inI128 n.allowance && inI128 n.spent

def Op.inRange : Op → Bool
  | .spend i amount => inU32 i && inI128 amount
  | .delegate p allowance => inU32 p && inI128 allowance
  | .refill i amount => inU32 i && inI128 amount

/-- Every index and amount of the trace fits the Rust types: `u32` and
`i128`. -/
def Trace.inRange (tr : Trace) : Bool :=
  tr.start.all Node.inRange && tr.ops.all Op.inRange

/-! ## Named traces -/

def root (allowance : Int) (spent : Int := 0) : Node := ⟨none, allowance, spent⟩

def child (parent : Nat) (allowance : Int) (spent : Int := 0) : Node :=
  ⟨some parent, allowance, spent⟩

def named : List Trace := [
  { name := "budget-oversubscribed-siblings"
    description := "Two children of a root with allowance 10 hold allowance 8 each; after one spends 8, the other's spend of 3 is refused at the root and its spend of 2 passes."
    start := [root 10, child 0 8, child 0 8]
    ops := [.spend 1 8, .spend 2 3, .spend 2 2, .spend 2 1, .spend 1 1, .spend 0 0] },
  { name := "budget-middle-exhausted"
    description := "A spend that uses up a middle ancestor's allowance leaves every node under it unable to spend, while the root and the middle node's sibling still can."
    start := [root 100, child 0 10, child 1 50, child 1 50, child 0 30]
    ops := [.spend 2 7, .spend 3 3, .spend 3 1, .spend 2 1, .spend 4 30, .spend 0 60,
      .spend 0 1] },
  { name := "budget-nearest-overdrawn"
    description := "When several nodes on the chain would be overdrawn, the refusal names the one nearest the spender."
    start := [root 5, child 0 3, child 1 1]
    ops := [.spend 2 6, .spend 2 4, .spend 2 2, .spend 1 4, .spend 2 1, .spend 1 3, .spend 0 2] },
  { name := "budget-chain-to-root"
    description := "A spend at a deep node charges it and every ancestor up to the root, and no other node."
    start := [root 1000, child 0 500, child 1 400, child 2 300, child 3 200, child 0 100]
    ops := [.spend 4 50, .spend 3 25, .spend 5 100, .spend 4 151, .spend 4 150] },
  { name := "budget-overflow"
    description := "A spent amount plus the spend that does not fit in an i128 counts as overdrawn; a refill whose raised allowance does not fit is refused with overflow."
    start := [root i128Max (i128Max - 1), child 0 i128Max]
    ops := [.spend 1 2, .spend 1 1, .spend 1 1, .refill 0 1, .refill 1 0, .spend 0 i128Max,
      .refill 1 i128Max] },
  { name := "budget-malformed-parent-self"
    description := "A node whose parent is itself makes the tree malformed: every operation refuses."
    start := [root 10, child 1 5]
    ops := [.spend 0 1, .spend 1 1, .delegate 0 1, .refill 0 1, .spend 5 1, .spend 0 (-1)] },
  { name := "budget-malformed-parent-later"
    description := "A node whose parent comes after it makes the tree malformed: every operation refuses."
    start := [child 1 10, root 10]
    ops := [.spend 1 1, .delegate 1 1, .refill 1 1] },
  { name := "budget-malformed-negative-allowance"
    description := "A negative allowance anywhere makes the tree malformed: every operation refuses, even at another node."
    start := [root 10, child 0 (-1), child 0 5]
    ops := [.spend 2 1, .delegate 0 1, .refill 1 5] },
  { name := "budget-malformed-negative-spent"
    description := "A negative spent amount anywhere makes the tree malformed: every operation refuses."
    start := [root 10, child 0 5 (-1)]
    ops := [.spend 0 1, .delegate 1 1, .refill 0 1] },
  { name := "budget-delegate-then-spend"
    description := "A delegation appends a child with any allowance, above its parent's included; a spend at the new node is still bounded by every ancestor."
    start := [root 10, child 0 8]
    ops := [.delegate 1 20, .spend 2 9, .spend 2 8, .delegate 2 5, .spend 3 1, .refill 1 3,
      .spend 3 1, .delegate 0 0, .spend 4 0, .spend 4 1] },
  { name := "budget-delegate-refusals"
    description := "A delegation under a missing parent, or with a negative allowance, is refused and changes nothing."
    start := [root 10]
    ops := [.delegate 1 5, .delegate u32Max 5, .delegate 0 (-1), .delegate 0 i128Min,
      .delegate 0 i128Max, .spend 1 11] },
  { name := "budget-refill"
    description := "A refill raises one node's allowance, so a spend refused at that node passes; a negative refill, one at a missing node and a zero refill behave as the model says."
    start := [root 10, child 0 4]
    ops := [.spend 1 4, .spend 1 1, .refill 1 (-1), .refill 2 1, .refill 1 0, .refill 1 2,
      .spend 1 2, .spend 1 1] },
  { name := "budget-negative-amount"
    description := "A negative spend is refused, after the node is checked to exist."
    start := [root 10]
    ops := [.spend 0 (-1), .spend 0 i128Min, .spend 1 (-1), .spend 0 10] },
  { name := "budget-no-such-node"
    description := "A spend or refill at an index past the tree is refused and changes nothing."
    start := [root 10, child 0 5]
    ops := [.spend 2 1, .spend u32Max 1, .refill 2 1, .refill u32Max 1, .spend 1 5] },
  { name := "budget-empty-tree"
    description := "On a tree with no nodes, every operation is refused with no_such_node."
    start := []
    ops := [.spend 0 0, .delegate 0 1, .refill 0 1] },
  { name := "budget-several-roots"
    description := "A tree may have several roots; a spend charges only its own root's chain."
    start := [root 10, root 20, child 0 10, child 1 10]
    ops := [.spend 2 10, .spend 3 10, .spend 3 1, .spend 1 10, .spend 1 1, .spend 2 1] },
  { name := "budget-start-overspent"
    description := "A well-formed tree may start with a node spent above its allowance; even a zero spend through it is refused until a refill covers it."
    start := [root 5 8, child 0 5]
    ops := [.spend 1 0, .spend 0 0, .refill 0 2, .spend 1 0, .refill 0 1, .spend 1 0,
      .spend 1 1] },
  { name := "budget-zero-spend"
    description := "A zero spend passes on a chain with nothing left and charges nothing."
    start := [root 3, child 0 3]
    ops := [.spend 1 3, .spend 1 0, .spend 0 0, .spend 1 1] },
  { name := "budget-empty-run"
    description := "A trace with no operations."
    start := [root 1]
    ops := [] }
]

/-! ## Randomized traces -/

def allowances : List Int := [0, 1, 2, 5, 10, 10, 50, 100, i128Max - 1, i128Max]

/-- The default `pick` never returns, since every list it is given is
non-empty. -/
instance : Inhabited Node := ⟨⟨none, 0, 0⟩⟩

/-- A random well-formed tree of `n` nodes, mostly with nothing spent; one
node in ten starts with a spent amount, and one tree in eight has a node made
malformed. -/
def tree (n : Nat) : Gen Tree := do
  let mut t : Tree := []
  for i in List.range n do
    let parent ← if i = 0 then pure none
      else do
        let r ← below 6
        if r = 0 then pure none else pure (some (← below i))
    let allowance ← pick allowances
    let spent ← do
      let r ← below 10
      if r = 0 then pick [0, 1, allowance / 2, allowance] else pure 0
    t := t ++ [⟨parent, allowance, spent⟩]
  let r ← below 8
  if r = 0 && n > 0 then
    let i ← below n
    let bad ← pick [
      (⟨some i, 1, 0⟩ : Node), ⟨some (i + 1), 1, 0⟩, ⟨none, -1, 0⟩, ⟨none, 1, -1⟩]
    t := t.set i bad
  return t

def amount : Gen Int := do
  pick [-1, 0, 1, 1, 2, 3, 5, 5, 10, 25, 50, 100, i128Max, i128Min]

def op (size : Nat) : Gen Op := do
  let r ← below 10
  let i ← do
    let s ← below 8
    if s = 0 then pick [size, size + 1, u32Max] else below (max size 1)
  if r < 6 then return .spend i (← amount)
  if r < 8 then return .delegate i (← pick allowances)
  return .refill i (← amount)

def ops (size : Nat) : Nat → Gen (List Op)
  | 0 => return []
  | k + 1 => do
    let o ← op size
    let size' := match o with
      | .delegate _ _ => size + 1
      | _ => size
    let rest ← ops size' k
    return o :: rest

def trace (seed : UInt64) (k : Nat) : Trace :=
  let g : Gen Trace := do
    let n ← below 7
    let t ← tree n
    let m ← below 12
    let os ← ops n (m + 1)
    return {
      name := s!"budget-random-{if k < 10 then "0" else ""}{k}"
      description := s!"Randomized trace {k} of seed {seed}."
      start := t
      ops := os }
  (g.run ⟨seed + UInt64.ofNat k⟩).1

def traces (seed : UInt64) (count : Nat) : List Trace :=
  named ++ (List.range count).map (trace seed)

end Conformance.Budget
