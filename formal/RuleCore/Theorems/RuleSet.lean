import RuleCore.Model.RuleSet

/-!
# Rule sets: evaluation and narrowing

* `Rule.allows_iff`, `RuleSet.allows_iff`, `RuleSet.allowsAll_iff`: what each
  verdict means.
* `RuleSet.allowsAll_nil`: every rule set allows the empty batch.
* `RuleSet.narrower_refl`, `RuleSet.narrower_trans`: `narrower` is a preorder.
* `RuleSet.allowsAll_of_narrower`: a narrower rule set allows a batch only if
  its ancestor does.
-/

namespace RuleCore

variable {Ctx : Type}

theorem Rule.allows_iff (r : Rule Ctx) (c : Ctx) :
    r.allows c = true ↔ r.scope c = true ∧ ∀ p ∈ r.conds, p c = true := by
  simp [Rule.allows]

theorem RuleSet.allows_iff (rs : RuleSet Ctx) (c : Ctx) :
    rs.allows c = true ↔ ∃ r ∈ rs.rules, r.allows c = true :=
  List.any_eq_true

theorem RuleSet.allowsAll_iff (rs : RuleSet Ctx) (cs : List Ctx) :
    rs.allowsAll cs = true ↔ ∀ c ∈ cs, rs.allows c = true := by
  simp [RuleSet.allowsAll]

/-- The empty batch is allowed by every rule set, the empty one included. A
Soroban authorization tree always has a root context, so a batch built from
one is never empty. -/
@[simp] theorem RuleSet.allowsAll_nil (rs : RuleSet Ctx) : rs.allowsAll [] = true := rfl

theorem RuleSet.narrower_refl (rs : RuleSet Ctx) : rs.narrower rs :=
  fun _ h => h

theorem RuleSet.narrower_trans {rs'' rs' rs : RuleSet Ctx} :
    rs''.narrower rs' → rs'.narrower rs → rs''.narrower rs :=
  fun h₁ h₂ c h => h₂ c (h₁ c h)

/-- A narrower rule set allows a batch only if its ancestor does, so checking
every context of an authorization tree against a derived rule set never
accepts a tree its ancestor would reject. -/
theorem RuleSet.allowsAll_of_narrower {rs' rs : RuleSet Ctx} (h : rs'.narrower rs)
    (cs : List Ctx) : rs'.allowsAll cs = true → rs.allowsAll cs = true := by
  simp only [RuleSet.allowsAll_iff]
  exact fun h' c hc => h c (h' c hc)

end RuleCore
