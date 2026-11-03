import RuleCore.Model.Cap

/-!
# Budgets on the delegation tree

Allowances sit on the delegation tree. A tree is a list of nodes, indexed from
zero; each node holds its parent's index, or `none` for a root, its allowance
and what has been spent at or under it. A tree is well formed (`Tree.valid`)
when every node's parent index is below its own index and no allowance or
spent amount is negative. Parent indices below their own make the tree acyclic
by construction: the walk from a node to its root moves to a strictly smaller
index at every step, so it ends within as many steps as the tree has nodes.
Every operation refuses a tree that is not well formed (`malformed`).

* `Tree.spend t i amount` charges node `i` and every ancestor up to its root
  by `amount`, or refuses. It first walks the chain and checks every node on it
  (`Tree.walk`), and only then builds the new tree (`Tree.charge`), so a
  refusal returns no tree. A node can take `amount` when `spent + amount` fits
  in an `i128` and is at most its allowance (`Node.fits`); a sum that does not
  fit counts as overdrawn. The refusal `overdrawn j` names the first node on
  the chain, counting from `i`, that cannot take the amount: the node a refill
  request goes to.
* `Tree.delegate t p allowance` appends a child of `p` with `allowance` and
  nothing spent. The allowance is not checked against the parent's, so
  children's allowances may sum to more than their parent's: oversubscription
  is allowed.
* `Tree.refill t i amount` raises node `i`'s allowance by `amount`. It refuses
  a negative amount, which would lower the allowance, and a raised allowance
  that does not fit in an `i128`. A refill is the owner's action, not a
  holder's.

Amounts and allowances are integers, `i128` in Rust; sums are computed with
`Cap.addI128`, Rust's `i128::checked_add`. Node indices are natural numbers,
`u32` in Rust. `maxNodes` is `u32::MAX`: a delegation onto a tree that already
holds that many nodes is refused (`treeFull`), so every node a delegation
appends has an index that fits in a `u32`.

A run is a list of operations applied in order. `Tree.run` keeps the tree on a
refused operation and logs every successful spend as its node and amount.
`Tree.Within t i a` says node `a` is `i` or one of its ancestors, so a spend at
`i` charges `a`. `spentUnder t log a` is the total of the logged spends made at
or under `a`. The theorems in `RuleCore.Theorems.Budget` are stated over these.
-/

namespace RuleCore.Budget

open RuleCore.Cap (addI128)

/-- The most nodes a delegation leaves in a tree: `u32::MAX`. -/
def maxNodes : Nat := 2 ^ 32 - 1

/-- One node of the delegation tree. -/
structure Node where
  /-- The parent's index, or `none` for a root. -/
  parent : Option Nat
  /-- The most that may be spent at or under this node. -/
  allowance : Int
  /-- What has been spent at or under this node. -/
  spent : Int
  deriving DecidableEq, Repr

/-- The delegation tree, indexed from zero. -/
abbrev Tree := List Node

/-- Why an operation on the tree was refused. -/
inductive BudgetError where
  /-- A node's parent index is not below its own index, or an allowance or a
  spent amount is negative. -/
  | malformed
  /-- No node has this index. -/
  | noSuchNode (i : Nat)
  /-- The amount, or the allowance, is negative. -/
  | negativeAmount
  /-- Charging this node would take its spent amount above its allowance, or
  past the largest `i128`. -/
  | overdrawn (i : Nat)
  /-- The raised allowance does not fit in an `i128`. -/
  | overflow
  /-- The tree already holds `maxNodes` nodes. -/
  | treeFull
  deriving DecidableEq, Repr

/-- Node `n`, at position `i`, is well formed: its parent index is below `i`,
and its allowance and spent amount are not negative. -/
def Node.valid (i : Nat) (n : Node) : Bool :=
  (match n.parent with
    | some p => decide (p < i)
    | none => true) &&
  decide (0 ≤ n.allowance) && decide (0 ≤ n.spent)

/-- Every node of `t`, the first of them at position `k`, is well formed. -/
def Tree.validFrom : Tree → Nat → Bool
  | [], _ => true
  | n :: t, k => n.valid k && Tree.validFrom t (k + 1)

/-- Every node of `t` is well formed. -/
def Tree.valid (t : Tree) : Bool :=
  t.validFrom 0

/-- Node `n` can take `amount`: `spent + amount` fits in an `i128` and is at
most the allowance. -/
def Node.fits (n : Node) (amount : Int) : Bool :=
  match addI128 n.spent amount with
  | some total => decide (total ≤ n.allowance)
  | none => false

namespace Tree

/-- The parent index of node `i`, if `i` exists and has a parent. -/
def parentOf (t : Tree) (i : Nat) : Option Nat :=
  t[i]?.bind (·.parent)

/-- `Within t i a`: node `a` is `i` or one of its ancestors, so a spend at `i`
charges `a`. Equivalently, `i` is at or under `a`. -/
inductive Within (t : Tree) : Nat → Nat → Prop where
  | self (i : Nat) : Within t i i
  | up {i p a : Nat} : t.parentOf i = some p → Within t p a → Within t i a

/-- The walk from node `i` toward its root, checking that each node can take
`amount`. It returns the nodes to charge, the spender first, or the first
refusal. Each step moves to a smaller index, so on a well-formed tree `fuel`
steps, the tree's length, suffice and the walk never refuses as `malformed`. -/
def walk (t : Tree) (amount : Int) : Nat → Nat → Except BudgetError (List Nat)
  | 0, _ => .error .malformed
  | fuel + 1, i =>
    match t[i]? with
    | none => .error .malformed
    | some n =>
      if !n.fits amount then .error (.overdrawn i)
      else
        match n.parent with
        | none => .ok [i]
        | some p =>
          if p < i then (walk t amount fuel p).map (i :: ·)
          else .error .malformed

/-- `t` with `amount` added to the spent amount of every node in `path`. -/
def charge (t : Tree) (path : List Nat) (amount : Int) : Tree :=
  t.mapIdx fun j n => if j ∈ path then { n with spent := n.spent + amount } else n

/-- The tree after a spend of `amount` at node `i`, or why it is refused. -/
def spend (t : Tree) (i : Nat) (amount : Int) : Except BudgetError Tree :=
  if !t.valid then .error .malformed
  else if t.length ≤ i then .error (.noSuchNode i)
  else if amount < 0 then .error .negativeAmount
  else (t.walk amount t.length i).map (t.charge · amount)

/-- The tree with a child of `parent` appended, with `allowance` and nothing
spent, or why the delegation is refused. The new node's index is `t.length`. -/
def delegate (t : Tree) (parent : Nat) (allowance : Int) : Except BudgetError Tree :=
  if !t.valid then .error .malformed
  else if t.length ≤ parent then .error (.noSuchNode parent)
  else if allowance < 0 then .error .negativeAmount
  else if maxNodes ≤ t.length then .error .treeFull
  else .ok (t ++ [⟨some parent, allowance, 0⟩])

/-- The tree with node `i`'s allowance raised by `amount`, or why the refill
is refused. The owner's action. -/
def refill (t : Tree) (i : Nat) (amount : Int) : Except BudgetError Tree :=
  if !t.valid then .error .malformed
  else
    match t[i]? with
    | none => .error (.noSuchNode i)
    | some n =>
      if amount < 0 then .error .negativeAmount
      else
        match addI128 n.allowance amount with
        | none => .error .overflow
        | some allowance => .ok (t.set i { n with allowance })

/-- Every node's spent amount is within its allowance. -/
def WithinAllowance (t : Tree) : Prop :=
  ∀ n ∈ t, n.spent ≤ n.allowance

end Tree

/-! ## Runs -/

/-- One operation on the tree. -/
inductive Op where
  | spend (i : Nat) (amount : Int)
  | delegate (parent : Nat) (allowance : Int)
  | refill (i : Nat) (amount : Int)
  deriving DecidableEq, Repr

/-- What one operation returns. -/
def Op.apply (t : Tree) : Op → Except BudgetError Tree
  | .spend i amount => t.spend i amount
  | .delegate p allowance => t.delegate p allowance
  | .refill i amount => t.refill i amount

/-- The tree after one operation: what it returns, or the same tree when it is
refused. -/
def Tree.step (t : Tree) (op : Op) : Tree :=
  match op.apply t with
  | .ok t' => t'
  | .error _ => t

/-- The spends `op` logs when it succeeds on `t`: its node and amount, for a
spend. -/
def Op.logged (t : Tree) : Op → List (Nat × Int)
  | .spend i amount =>
    match t.spend i amount with
    | .ok _ => [(i, amount)]
    | .error _ => []
  | _ => []

/-- Apply `ops` in order, each refused operation leaving the tree as it was.
Returns the final tree and the successful spends, oldest first. -/
def Tree.run : Tree → List Op → Tree × List (Nat × Int)
  | t, [] => (t, [])
  | t, op :: ops =>
    let r := (t.step op).run ops
    (r.1, op.logged t ++ r.2)

open Classical in
/-- The total of the logged spends made at or under node `a` in tree `t`. -/
noncomputable def spentUnder (t : Tree) (log : List (Nat × Int)) (a : Nat) : Int :=
  ((log.filter fun e => decide (t.Within e.1 a)).map (·.2)).sum

end RuleCore.Budget
