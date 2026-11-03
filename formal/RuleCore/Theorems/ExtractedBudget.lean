import RuleCore.Equiv.Budget

/-!
# Theorems on the extracted budget operations

`runBudget` runs the extracted `spend`, `delegate` and `refill` over a list of
calls, keeping the tree on a refusal, as a contract shell does when it stores
what an operation returns only on `Ok`, and logs every successful spend.
`runBudget_eq` proves that it returns `ok` of a tree and a log whose
denotations are the model's `Tree.run`, so every theorem of
`RuleCore.Theorems.Budget` about runs holds of the tree the Rust code
computes:

* `runBudget_valid`, `runBudget_withinAllowance`: a run keeps the tree well
  formed and every node's spent amount within its allowance;
* `runBudget_spentUnder_eq_spent`, `runBudget_spentUnder_le_allowance`: budget
  safety, from a well-formed tree with nothing spent, after any run the total
  successfully spent at or under each node is that node's spent amount and
  never exceeds its allowance.

The remaining theorems state single outcomes on the extracted functions:

* `budget_spend_charges`, `budget_spend_unchanged`: a successful `spend`
  charges exactly the spender and its ancestors by the amount;
* `budget_spend_overdrawn`: an `Overdrawn` refusal names a node on the
  spender's chain that cannot take the amount, and every node before it on the
  chain can;
* `budget_spend_accepts_iff`: on a well-formed tree, a spend of a non-negative
  amount at an existing node succeeds exactly when every node on its chain can
  take the amount;
* `budget_delegate_appends`, `budget_refill_raises`: what a successful
  delegation and refill return.
-/

namespace RuleCore.Extracted

open Aeneas Aeneas.Std Result RuleCore.Equiv RuleCore.Budget

/-- One budget operation, as Rust values. -/
inductive BudgetCall where
  | spend (node : Std.U32) (amount : Std.I128)
  | delegate (parent : Std.U32) (allowance : Std.I128)
  | refill (node : Std.U32) (amount : Std.I128)

/-- The model's operation a call denotes. -/
def BudgetCall.op : BudgetCall → Op
  | .spend node amount => .spend node.val amount.val
  | .delegate parent allowance => .delegate parent.val allowance.val
  | .refill node amount => .refill node.val amount.val

/-- What the extracted operation returns on `tree`. -/
def BudgetCall.apply (tree : Slice rule_eval.budget.Node) :
    BudgetCall →
      Result (core.result.Result (alloc.vec.Vec rule_eval.budget.Node) rule_eval.budget.BudgetError)
  | .spend node amount => rule_eval.budget.spend tree node amount
  | .delegate parent allowance => rule_eval.budget.delegate tree parent allowance
  | .refill node amount => rule_eval.budget.refill tree node amount

/-- The spends a call logs when it succeeds: its node and amount, for a spend. -/
def BudgetCall.logged : BudgetCall → List (Std.U32 × Std.I128)
  | .spend node amount => [(node, amount)]
  | _ => []

/-- A run of the extracted operations from `tree`: each call's returned tree,
or the same tree when the call is refused. Returns the final tree and the
successful spends, oldest first. -/
def runBudget (tree : Slice rule_eval.budget.Node) :
    List BudgetCall → Result (Slice rule_eval.budget.Node × List (Std.U32 × Std.I128))
  | [] => ok (tree, [])
  | call :: calls => do
    let res ← call.apply tree
    match res with
    | .Ok out => do
      let r ← runBudget (alloc.vec.Vec.deref out) calls
      ok (r.1, call.logged ++ r.2)
    | .Err _ => runBudget tree calls

/-- A logged spend, as model values. -/
def loggedOf (e : Std.U32 × Std.I128) : Nat × Int := (e.1.val, e.2.val)

theorem apply_eq (tree : Slice rule_eval.budget.Node) (call : BudgetCall) :
    ∃ r, call.apply tree = ok r ∧ denoteBudget r = call.op.apply (denoteTree tree.val) := by
  cases call with
  | spend node amount => exact spend_eq tree node amount
  | delegate parent allowance => exact delegate_eq tree parent allowance
  | refill node amount => exact refill_eq tree node amount

/-- On every input, a run of the extracted operations returns `ok` of a tree
and a log whose denotations are the model's run on the denoted operations. -/
theorem runBudget_eq :
    ∀ (calls : List BudgetCall) (tree : Slice rule_eval.budget.Node),
      ∃ out log, runBudget tree calls = ok (out, log) ∧
        denoteTree out.val = ((denoteTree tree.val).run (calls.map BudgetCall.op)).1 ∧
        log.map loggedOf = ((denoteTree tree.val).run (calls.map BudgetCall.op)).2
  | [], tree => ⟨tree, [], rfl, rfl, rfl⟩
  | call :: calls, tree => by
    obtain ⟨res, hres, hden⟩ := apply_eq tree call
    cases res with
    | Ok out =>
      have hstep : (denoteTree tree.val).step call.op = denoteTree out.val := by
        simp [Tree.step, ← hden, denoteBudget]
      have hlog : call.op.logged (denoteTree tree.val) = call.logged.map loggedOf := by
        cases call with
        | spend node amount =>
          have : (denoteTree tree.val).spend node.val amount.val = .ok (denoteTree out.val) :=
            hden.symm
          simp [BudgetCall.op, Op.logged, this, BudgetCall.logged, loggedOf]
        | delegate parent allowance => rfl
        | refill node amount => rfl
      obtain ⟨out', log, hr, hd, hl⟩ := runBudget_eq calls (alloc.vec.Vec.deref out)
      simp only [vec_deref_val] at hd hl
      refine ⟨out', call.logged ++ log, ?_, ?_, ?_⟩
      · simp [runBudget, hres, hr]
      · simp only [List.map_cons, Tree.run, hstep]
        rw [← hd]
      · simp only [List.map_cons, Tree.run, hstep, hlog, List.map_append]
        rw [← hl]
    | Err e =>
      have he : call.op.apply (denoteTree tree.val) = .error (denoteBudgetError e) := hden.symm
      obtain ⟨out', log, hr, hd, hl⟩ := runBudget_eq calls tree
      refine ⟨out', log, ?_, ?_, ?_⟩
      · simp [runBudget, hres, hr]
      · rw [List.map_cons, Tree.run_cons_of_error _ he]; exact hd
      · rw [List.map_cons, Tree.run_cons_of_error _ he]; exact hl

/-- A run keeps the tree well formed. -/
theorem runBudget_valid (tree : Slice rule_eval.budget.Node) (calls : List BudgetCall)
    (hv : (denoteTree tree.val).valid = true) :
    ∃ out log, runBudget tree calls = ok (out, log) ∧ (denoteTree out.val).valid = true := by
  obtain ⟨out, log, hr, hd, -⟩ := runBudget_eq calls tree
  exact ⟨out, log, hr, by rw [hd]; exact Tree.run_valid hv _⟩

/-- A run keeps every node's spent amount within its allowance. -/
theorem runBudget_withinAllowance (tree : Slice rule_eval.budget.Node) (calls : List BudgetCall)
    (hw : ∀ n ∈ tree.val, n.spent.val ≤ n.allowance.val) :
    ∃ out log, runBudget tree calls = ok (out, log) ∧
      ∀ n ∈ out.val, n.spent.val ≤ n.allowance.val := by
  obtain ⟨out, log, hr, hd, -⟩ := runBudget_eq calls tree
  have hw' : (denoteTree tree.val).WithinAllowance := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    exact hw m hm
  have := Tree.run_withinAllowance hw' (calls.map BudgetCall.op)
  rw [← hd] at this
  refine ⟨out, log, hr, fun n hn => ?_⟩
  exact this (denoteNode n) (List.mem_map_of_mem hn)

/-- From a tree with nothing spent, after any run of the extracted operations,
the total successfully spent at or under each node is that node's spent
amount. -/
theorem runBudget_spentUnder_eq_spent (tree : Slice rule_eval.budget.Node)
    (calls : List BudgetCall) (h0 : ∀ n ∈ tree.val, n.spent.val = 0) :
    ∃ out log, runBudget tree calls = ok (out, log) ∧
      ∀ (a : Nat) (n : rule_eval.budget.Node), out.val[a]? = some n →
        spentUnder (denoteTree out.val) (log.map loggedOf) a = n.spent.val := by
  obtain ⟨out, log, hr, hd, hl⟩ := runBudget_eq calls tree
  refine ⟨out, log, hr, fun a n hn => ?_⟩
  have h0' : ∀ m ∈ denoteTree tree.val, m.spent = 0 := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
    exact h0 k hk
  have ha : ((denoteTree tree.val).run (calls.map BudgetCall.op)).1[a]? = some (denoteNode n) := by
    rw [← hd, getElem?_denoteTree, hn]; rfl
  have := Tree.spentUnder_eq_spent h0' (calls.map BudgetCall.op) ha
  rw [← hd, ← hl] at this
  exact this

/-- Budget safety for the Rust code: from a well-formed tree with nothing
spent, after any run of the extracted operations, the total successfully spent
at or under each node never exceeds that node's allowance, however much its
children's allowances oversubscribe it. -/
theorem runBudget_spentUnder_le_allowance (tree : Slice rule_eval.budget.Node)
    (calls : List BudgetCall) (hv : (denoteTree tree.val).valid = true)
    (h0 : ∀ n ∈ tree.val, n.spent.val = 0) :
    ∃ out log, runBudget tree calls = ok (out, log) ∧
      ∀ (a : Nat) (n : rule_eval.budget.Node), out.val[a]? = some n →
        spentUnder (denoteTree out.val) (log.map loggedOf) a ≤ n.allowance.val := by
  obtain ⟨out, log, hr, hd, hl⟩ := runBudget_eq calls tree
  refine ⟨out, log, hr, fun a n hn => ?_⟩
  have h0' : ∀ m ∈ denoteTree tree.val, m.spent = 0 := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
    exact h0 k hk
  have ha : ((denoteTree tree.val).run (calls.map BudgetCall.op)).1[a]? = some (denoteNode n) := by
    rw [← hd, getElem?_denoteTree, hn]; rfl
  have := Tree.spentUnder_le_allowance hv h0' (calls.map BudgetCall.op) ha
  rw [← hd, ← hl] at this
  exact this

/-! ## Single operations -/

theorem spend_ok_denote {tree : Slice rule_eval.budget.Node} {node : Std.U32} {x : Std.I128}
    {out : alloc.vec.Vec rule_eval.budget.Node}
    (h : rule_eval.budget.spend tree node x = ok (.Ok out)) :
    (denoteTree tree.val).spend node.val x.val = .ok (denoteTree out.val) := by
  obtain ⟨r, hr, hd⟩ := spend_eq tree node x
  rw [h, ok.injEq] at hr
  subst hr
  exact hd.symm

/-- A successful `spend` charges the spender and every ancestor by the
amount. -/
theorem budget_spend_charges {tree : Slice rule_eval.budget.Node} {node : Std.U32}
    {x : Std.I128} {out : alloc.vec.Vec rule_eval.budget.Node}
    (h : rule_eval.budget.spend tree node x = ok (.Ok out)) {a : Nat}
    (w : (denoteTree tree.val).Within node.val a) :
    ∃ n, tree.val[a]? = some n ∧
      (denoteTree out.val)[a]? = some { denoteNode n with spent := n.spent.val + x.val } := by
  obtain ⟨m, hm, hm'⟩ := Tree.spend_ok_charges (spend_ok_denote h) w
  rw [getElem?_denoteTree] at hm
  cases hn : tree.val[a]? with
  | none => simp [hn] at hm
  | some n =>
    simp only [hn, Option.map_some, Option.some.injEq] at hm
    subst hm
    exact ⟨n, rfl, hm'⟩

/-- A successful `spend` changes no node off the spender's chain. -/
theorem budget_spend_unchanged {tree : Slice rule_eval.budget.Node} {node : Std.U32}
    {x : Std.I128} {out : alloc.vec.Vec rule_eval.budget.Node}
    (h : rule_eval.budget.spend tree node x = ok (.Ok out)) {a : Nat}
    (w : ¬ (denoteTree tree.val).Within node.val a) : out.val[a]? = tree.val[a]? := by
  have := Tree.spend_ok_unchanged (spend_ok_denote h) w
  rw [getElem?_denoteTree, getElem?_denoteTree] at this
  exact (Option.map_injective denoteNode_injective) this

/-- The node an `Overdrawn` refusal names is on the spender's chain and cannot
take the amount, and every node before it on the chain can. -/
theorem budget_spend_overdrawn {tree : Slice rule_eval.budget.Node} {node j : Std.U32}
    {x : Std.I128} (h : rule_eval.budget.spend tree node x = ok (.Err (.Overdrawn j))) :
    let t := denoteTree tree.val
    t.Within node.val j.val ∧ (∃ n, t[j.val]? = some n ∧ n.fits x.val = false) ∧
      ∀ b, t.Within node.val b → t.Within b j.val → b ≠ j.val →
        ∃ m, t[b]? = some m ∧ m.fits x.val = true := by
  obtain ⟨r, hr, hd⟩ := spend_eq tree node x
  rw [h, ok.injEq] at hr
  subst hr
  exact Tree.spend_overdrawn hd.symm

/-- On a well-formed tree, a spend of a non-negative amount at an existing node
succeeds exactly when every node on its chain can take the amount. -/
theorem budget_spend_accepts_iff (tree : Slice rule_eval.budget.Node) (node : Std.U32)
    (x : Std.I128) (hv : (denoteTree tree.val).valid = true) (hi : node.val < tree.length)
    (hx : 0 ≤ x.val) :
    (∃ out, rule_eval.budget.spend tree node x = ok (.Ok out)) ↔
      ∀ a, (denoteTree tree.val).Within node.val a →
        ∃ n, (denoteTree tree.val)[a]? = some n ∧ n.fits x.val = true := by
  obtain ⟨r, hr, hd⟩ := spend_eq tree node x
  rw [hr, ← Tree.spend_accepts_iff hv (by rw [length_denoteTree]; exact hi) hx, ← hd]
  constructor
  · rintro ⟨out, hout⟩
    rw [ok.injEq] at hout
    subst hout
    exact ⟨_, rfl⟩
  · rintro ⟨t', ht'⟩
    cases r with
    | Ok out => exact ⟨out, rfl⟩
    | Err e => simp [denoteBudget] at ht'

/-- A successful `delegate` appends exactly the new child, with nothing spent,
whatever its allowance and its parent's. -/
theorem budget_delegate_appends {tree : Slice rule_eval.budget.Node} {parent : Std.U32}
    {x : Std.I128} {out : alloc.vec.Vec rule_eval.budget.Node}
    (h : rule_eval.budget.delegate tree parent x = ok (.Ok out)) :
    denoteTree out.val = denoteTree tree.val ++ [⟨some parent.val, x.val, 0⟩] := by
  obtain ⟨r, hr, hd⟩ := delegate_eq tree parent x
  rw [h, ok.injEq] at hr
  subst hr
  exact (Tree.delegate_ok_iff.mp hd.symm).2.2.2.2

/-- A successful `refill` raises exactly one node's allowance by the amount. -/
theorem budget_refill_raises {tree : Slice rule_eval.budget.Node} {node : Std.U32}
    {x : Std.I128} {out : alloc.vec.Vec rule_eval.budget.Node}
    (h : rule_eval.budget.refill tree node x = ok (.Ok out)) :
    ∃ n, tree.val[node.val]? = some n ∧ 0 ≤ x.val ∧
      denoteTree out.val = (denoteTree tree.val).set node.val
        { denoteNode n with allowance := n.allowance.val + x.val } := by
  obtain ⟨r, hr, hd⟩ := refill_eq tree node x
  rw [h, ok.injEq] at hr
  subst hr
  obtain ⟨-, m, hm, hx, -, heq⟩ := Tree.refill_ok_iff.mp hd.symm
  rw [getElem?_denoteTree] at hm
  cases hn : tree.val[node.val]? with
  | none => simp [hn] at hm
  | some n =>
    simp only [hn, Option.map_some, Option.some.injEq] at hm
    subst hm
    exact ⟨n, rfl, hx, heq⟩

end RuleCore.Extracted
