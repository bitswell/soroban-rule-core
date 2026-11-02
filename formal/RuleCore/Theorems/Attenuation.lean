import RuleCore.Model.Attenuation
import RuleCore.Theorems.RuleSet

/-!
# Attenuation narrows

* `RuleSet.dropRule_narrower`, `RuleSet.addCond_narrower`,
  `RuleSet.restrictScope_narrower`: each attenuation step yields a rule set
  narrower than the one it started from.
* `RuleSet.attenuate_narrower`: so does any single step.
* `RuleSet.Derives.narrower`: every rule set reachable from a root by
  attenuation steps is narrower than the root.
* `RuleSet.attenuateAll_derives`, `RuleSet.attenuateAll_narrower`: applying a
  list of steps is such a derivation.
* `RuleSet.dropRule_eq_error_iff`, `RuleSet.addCond_eq_error_iff`,
  `RuleSet.restrictScope_eq_error_iff`: a step is refused with `noSuchRule`
  exactly when its index is not below the number of rules.
-/

namespace RuleCore

variable {Ctx : Type}

/-! ## Rules -/

theorem Rule.allows_of_allows_addCond {r : Rule Ctx} {p : Ctx → Bool} {c : Ctx}
    (h : (r.addCond p).allows c = true) : r.allows c = true := by
  simp only [Rule.allows_iff, Rule.addCond, List.mem_append, List.mem_singleton] at h ⊢
  exact ⟨h.1, fun q hq => h.2 q (.inl hq)⟩

theorem Rule.allows_of_allows_restrictScope {r : Rule Ctx} {s : Ctx → Bool} {c : Ctx}
    (h : (r.restrictScope s).allows c = true) : r.allows c = true := by
  simp only [Rule.allows_iff, Rule.restrictScope, Bool.and_eq_true] at h ⊢
  exact ⟨h.1.1, h.2⟩

/-! ## Rule sets -/

/-- Replacing a rule by one that allows no more yields a narrower rule set. -/
theorem RuleSet.modifyRule_narrower {rs rs' : RuleSet Ctx} {i : Nat}
    {f : Rule Ctx → Rule Ctx} (hf : ∀ r c, (f r).allows c = true → r.allows c = true)
    (h : rs.modifyRule i f = .ok rs') : rs'.narrower rs := by
  unfold RuleSet.modifyRule at h
  split at h
  · rename_i r hr
    cases h
    intro c hc
    rw [RuleSet.allows_iff] at hc ⊢
    obtain ⟨r', hr', hc⟩ := hc
    rcases List.mem_or_eq_of_mem_set hr' with hmem | rfl
    · exact ⟨r', hmem, hc⟩
    · exact ⟨r, List.mem_of_getElem? hr, hf r c hc⟩
  · cases h

theorem RuleSet.dropRule_narrower {rs rs' : RuleSet Ctx} {i : Nat}
    (h : rs.dropRule i = .ok rs') : rs'.narrower rs := by
  unfold RuleSet.dropRule at h
  split at h
  · cases h
    intro c hc
    rw [RuleSet.allows_iff] at hc ⊢
    obtain ⟨r, hr, hc⟩ := hc
    exact ⟨r, List.mem_of_mem_eraseIdx hr, hc⟩
  · cases h

theorem RuleSet.addCond_narrower {rs rs' : RuleSet Ctx} {i : Nat} {p : Ctx → Bool}
    (h : rs.addCond i p = .ok rs') : rs'.narrower rs :=
  RuleSet.modifyRule_narrower (fun _ _ => Rule.allows_of_allows_addCond) h

theorem RuleSet.restrictScope_narrower {rs rs' : RuleSet Ctx} {i : Nat} {s : Ctx → Bool}
    (h : rs.restrictScope i s = .ok rs') : rs'.narrower rs :=
  RuleSet.modifyRule_narrower (fun _ _ => Rule.allows_of_allows_restrictScope) h

theorem RuleSet.attenuate_narrower {rs rs' : RuleSet Ctx} {a : Attenuation Ctx}
    (h : rs.attenuate a = .ok rs') : rs'.narrower rs := by
  cases a with
  | dropRule i => exact RuleSet.dropRule_narrower h
  | addCond i p => exact RuleSet.addCond_narrower h
  | restrictScope i s => exact RuleSet.restrictScope_narrower h

/-! ## Chains of steps -/

/-- Every rule set derived from a root by attenuation steps stays inside the
root. -/
theorem RuleSet.Derives.narrower {root rs : RuleSet Ctx} (h : RuleSet.Derives root rs) :
    rs.narrower root := by
  induction h with
  | refl => exact RuleSet.narrower_refl root
  | step a _ ha ih => exact RuleSet.narrower_trans (RuleSet.attenuate_narrower ha) ih

theorem RuleSet.attenuateAll_derives {root rs : RuleSet Ctx} {steps : List (Attenuation Ctx)}
    (h : root.attenuateAll steps = .ok rs) : RuleSet.Derives root rs := by
  suffices ∀ (steps : List (Attenuation Ctx)) (rs₀ : RuleSet Ctx),
      RuleSet.Derives root rs₀ → steps.foldlM RuleSet.attenuate rs₀ = .ok rs →
      RuleSet.Derives root rs from
    this steps root .refl h
  intro steps
  induction steps with
  | nil =>
    intro rs₀ h₀ h
    simp only [List.foldlM_nil] at h
    cases h
    exact h₀
  | cons a steps ih =>
    intro rs₀ h₀ h
    rw [List.foldlM_cons] at h
    cases ha : rs₀.attenuate a with
    | error e => rw [ha] at h; cases h
    | ok rs₁ =>
      rw [ha] at h
      exact ih rs₁ (.step a h₀ ha) h

theorem RuleSet.attenuateAll_narrower {root rs : RuleSet Ctx} {steps : List (Attenuation Ctx)}
    (h : root.attenuateAll steps = .ok rs) : rs.narrower root :=
  (RuleSet.attenuateAll_derives h).narrower

/-! ## Failure -/

theorem RuleSet.modifyRule_eq_error_iff (rs : RuleSet Ctx) (i : Nat) (f : Rule Ctx → Rule Ctx) :
    rs.modifyRule i f = .error .noSuchRule ↔ rs.rules.length ≤ i := by
  unfold RuleSet.modifyRule
  split <;> rename_i h
  · simp only [reduceCtorEq, false_iff, Nat.not_le]
    exact (List.getElem?_eq_some_iff.mp h).1
  · simp only [true_iff]
    exact List.getElem?_eq_none_iff.mp h

theorem RuleSet.dropRule_eq_error_iff (rs : RuleSet Ctx) (i : Nat) :
    rs.dropRule i = .error .noSuchRule ↔ rs.rules.length ≤ i := by
  unfold RuleSet.dropRule
  split <;> simp_all

theorem RuleSet.addCond_eq_error_iff (rs : RuleSet Ctx) (i : Nat) (p : Ctx → Bool) :
    rs.addCond i p = .error .noSuchRule ↔ rs.rules.length ≤ i :=
  RuleSet.modifyRule_eq_error_iff rs i _

theorem RuleSet.restrictScope_eq_error_iff (rs : RuleSet Ctx) (i : Nat) (s : Ctx → Bool) :
    rs.restrictScope i s = .error .noSuchRule ↔ rs.rules.length ≤ i :=
  RuleSet.modifyRule_eq_error_iff rs i _

end RuleCore
