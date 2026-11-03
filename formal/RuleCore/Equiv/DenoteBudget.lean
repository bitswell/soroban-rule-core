import RuleCore.Model.Budget
import RuleCore.Extracted.RuleEval

/-!
# Denotation of the extracted budget types

The functions below map the types Aeneas generates for the `budget` module of
`crates/rule-eval` to the model of `RuleCore/Model/Budget.lean`. Like the maps
in `RuleCore/Equiv/Denote.lean` and `RuleCore/Equiv/DenoteCap.lean`, they are
part of the specification, and each is structural:

* a `u32` (a node index) is its value, a natural number, and an `i128` (an
  amount, an allowance or a spent amount) is its value, an integer;
* `Node` maps each field to the field of the same name, and a tree, a slice or
  vector of nodes, to the list of its nodes' denotations;
* `BudgetError` maps each constructor to the constructor of the same name, and
  a Rust `Result` of `spend`, `delegate` or `refill` is the `Except` with the
  denoted payload.

So a Rust tree denotes a model tree whose indices fit in a `u32` and whose
amounts fit in an `i128`, and the equivalence theorems hold for every Rust
tree. Every denotation is injective (`denoteNode_injective`,
`denoteTree_injective`, `denoteBudgetError_injective`,
`denoteBudget_injective`).
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std

def denoteNode (n : rule_eval.budget.Node) : Budget.Node :=
  ⟨n.parent.map (·.val), n.allowance.val, n.spent.val⟩

def denoteTree (l : List rule_eval.budget.Node) : Budget.Tree :=
  l.map denoteNode

def denoteBudgetError : rule_eval.budget.BudgetError → Budget.BudgetError
  | .Malformed => .malformed
  | .NoSuchNode i => .noSuchNode i.val
  | .NegativeAmount => .negativeAmount
  | .Overdrawn i => .overdrawn i.val
  | .Overflow => .overflow
  | .TreeFull => .treeFull

/-- What `spend`, `delegate` or `refill` returned, as the model's outcome. -/
def denoteBudget :
    core.result.Result (alloc.vec.Vec rule_eval.budget.Node) rule_eval.budget.BudgetError →
      Except Budget.BudgetError Budget.Tree
  | .Ok t => .ok (denoteTree t.val)
  | .Err e => .error (denoteBudgetError e)

/-! ## Injectivity -/

theorem denoteNode_injective : Function.Injective denoteNode := by
  intro a b h
  obtain ⟨pa, aa, sa⟩ := a
  obtain ⟨pb, ab, sb⟩ := b
  simp only [denoteNode, Budget.Node.mk.injEq] at h
  obtain ⟨hp, ha, hs⟩ := h
  have hp' : pa = pb := by
    cases pa <;> cases pb <;> simp_all
    exact UScalar.eq_of_val_eq hp
  subst hp'
  simp only [rule_eval.budget.Node.mk.injEq, true_and]
  exact ⟨IScalar.eq_of_val_eq ha, IScalar.eq_of_val_eq hs⟩

theorem denoteTree_injective : Function.Injective denoteTree :=
  List.map_injective_iff.mpr denoteNode_injective

theorem denoteBudgetError_injective : Function.Injective denoteBudgetError := by
  intro a b h
  cases a <;> cases b <;> simp_all [denoteBudgetError] <;> exact UScalar.eq_of_val_eq h

theorem denoteBudget_injective : Function.Injective denoteBudget := by
  intro a b h
  cases a with
  | Ok t =>
    cases b with
    | Ok t' =>
      simp only [denoteBudget, Except.ok.injEq] at h
      rw [alloc.vec.Vec.ext _ _ (denoteTree_injective h)]
    | Err e => simp [denoteBudget] at h
  | Err e =>
    cases b with
    | Ok t => simp [denoteBudget] at h
    | Err e' =>
      simp only [denoteBudget, Except.error.injEq] at h
      rw [denoteBudgetError_injective h]

end RuleCore.Equiv
