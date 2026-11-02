import RuleCore.Model.Attenuation
import RuleCore.Theorems.RuleSet

/-!
# Attenuation narrows

* `RuleSet.dropRule_narrower`, `RuleSet.addCond_narrower`,
  `RuleSet.restrictScope_narrower`, `RuleSet.removeSigners_narrower`,
  `RuleSet.raiseThreshold_narrower`: each attenuation step yields a rule set
  narrower than the one it started from, under every list of authenticated
  signers.
* `RuleSet.attenuate_narrower`: so does any single step.
* `RuleSet.Derives.narrower`: every rule set reachable from a root by
  attenuation steps is narrower than the root.
* `RuleSet.attenuateAll_derives`, `RuleSet.attenuateAll_narrower`: applying a
  list of steps is such a derivation.
* `RuleSet.dropRule_eq_error_iff`, `RuleSet.addCond_eq_error_iff`,
  `RuleSet.restrictScope_eq_error_iff`, `RuleSet.removeSigners_eq_error_iff`,
  `RuleSet.raiseThreshold_eq_noSuchRule_iff`: a step is refused with
  `noSuchRule` exactly when its index is not below the number of rules.
* `RuleSet.raiseThreshold_eq_thresholdLowered_iff`: `raiseThreshold` is
  refused with `thresholdLowered` exactly when the rule exists and the new
  threshold is below its current one.
-/

namespace RuleCore

variable {Ctx Sig : Type} [DecidableEq Sig]

/-! ## Rules -/

theorem Rule.allows_of_allows_addCond {r : Rule Ctx Sig} {p : Ctx → Bool} {c : Ctx}
    {auth : List Sig} (h : (r.addCond p).allows c auth = true) : r.allows c auth = true := by
  simp only [Rule.allows_iff, Rule.addCond, List.mem_append, List.mem_singleton] at h ⊢
  exact ⟨h.1, fun q hq => h.2.1 q (.inl hq), h.2.2⟩

theorem Rule.allows_of_allows_restrictScope {r : Rule Ctx Sig} {s : Ctx → Bool} {c : Ctx}
    {auth : List Sig} (h : (r.restrictScope s).allows c auth = true) :
    r.allows c auth = true := by
  simp only [Rule.allows_iff, Rule.restrictScope, Bool.and_eq_true] at h ⊢
  exact ⟨h.1.1, h.2⟩

/-- Removing signers from a rule leaves at most as many of its distinct
signers authenticated, so its signer requirement only gets harder to meet. -/
theorem Rule.signed_of_signed_removeSigners {r : Rule Ctx Sig} {ss auth : List Sig}
    (h : (r.removeSigners ss).signed auth = true) : r.signed auth = true := by
  rw [Rule.signed_iff] at h ⊢
  refine Nat.le_trans h ((Rule.nodup_present _ auth).length_le_of_subset fun s hs => ?_)
  rw [Rule.mem_present] at hs ⊢
  exact ⟨(List.mem_filter.mp hs.1).1, hs.2⟩

theorem Rule.allows_of_allows_removeSigners {r : Rule Ctx Sig} {ss : List Sig} {c : Ctx}
    {auth : List Sig} (h : (r.removeSigners ss).allows c auth = true) :
    r.allows c auth = true := by
  rw [Rule.allows_iff] at h ⊢
  exact ⟨h.1, h.2.1, Rule.signed_of_signed_removeSigners h.2.2⟩

theorem Rule.allows_of_allows_threshold_le {r : Rule Ctx Sig} {k : Nat} (hk : r.threshold ≤ k)
    {c : Ctx} {auth : List Sig} (h : { r with threshold := k }.allows c auth = true) :
    r.allows c auth = true := by
  simp only [Rule.allows_iff, Rule.signed_iff, Rule.present] at h ⊢
  exact ⟨h.1, h.2.1, Nat.le_trans hk h.2.2⟩

/-! ## Rule sets -/

/-- Replacing a rule by one that allows no more yields a narrower rule set. -/
theorem RuleSet.modifyRule_narrower {rs rs' : RuleSet Ctx Sig} {i : Nat}
    {f : Rule Ctx Sig → Rule Ctx Sig}
    (hf : ∀ r c auth, (f r).allows c auth = true → r.allows c auth = true)
    (h : rs.modifyRule i f = .ok rs') : rs'.narrower rs := by
  unfold RuleSet.modifyRule at h
  split at h
  · rename_i r hr
    cases h
    intro c auth hc
    rw [RuleSet.allows_iff] at hc ⊢
    obtain ⟨r', hr', hc⟩ := hc
    rcases List.mem_or_eq_of_mem_set hr' with hmem | rfl
    · exact ⟨r', hmem, hc⟩
    · exact ⟨r, List.mem_of_getElem? hr, hf r c auth hc⟩
  · cases h

theorem RuleSet.dropRule_narrower {rs rs' : RuleSet Ctx Sig} {i : Nat}
    (h : rs.dropRule i = .ok rs') : rs'.narrower rs := by
  unfold RuleSet.dropRule at h
  split at h
  · cases h
    intro c auth hc
    rw [RuleSet.allows_iff] at hc ⊢
    obtain ⟨r, hr, hc⟩ := hc
    exact ⟨r, List.mem_of_mem_eraseIdx hr, hc⟩
  · cases h

theorem RuleSet.addCond_narrower {rs rs' : RuleSet Ctx Sig} {i : Nat} {p : Ctx → Bool}
    (h : rs.addCond i p = .ok rs') : rs'.narrower rs :=
  RuleSet.modifyRule_narrower (fun _ _ _ => Rule.allows_of_allows_addCond) h

theorem RuleSet.restrictScope_narrower {rs rs' : RuleSet Ctx Sig} {i : Nat} {s : Ctx → Bool}
    (h : rs.restrictScope i s = .ok rs') : rs'.narrower rs :=
  RuleSet.modifyRule_narrower (fun _ _ _ => Rule.allows_of_allows_restrictScope) h

theorem RuleSet.removeSigners_narrower {rs rs' : RuleSet Ctx Sig} {i : Nat} {ss : List Sig}
    (h : rs.removeSigners i ss = .ok rs') : rs'.narrower rs :=
  RuleSet.modifyRule_narrower (fun _ _ _ => Rule.allows_of_allows_removeSigners) h

theorem RuleSet.raiseThreshold_narrower {rs rs' : RuleSet Ctx Sig} {i k : Nat}
    (h : rs.raiseThreshold i k = .ok rs') : rs'.narrower rs := by
  unfold RuleSet.raiseThreshold at h
  split at h
  · rename_i r hr
    split at h
    · cases h
    · rename_i hk
      cases h
      intro c auth hc
      rw [RuleSet.allows_iff] at hc ⊢
      obtain ⟨r', hr', hc⟩ := hc
      rcases List.mem_or_eq_of_mem_set hr' with hmem | rfl
      · exact ⟨r', hmem, hc⟩
      · exact ⟨r, List.mem_of_getElem? hr,
          Rule.allows_of_allows_threshold_le (Nat.le_of_not_lt hk) hc⟩
  · cases h

theorem RuleSet.attenuate_narrower {rs rs' : RuleSet Ctx Sig} {a : Attenuation Ctx Sig}
    (h : rs.attenuate a = .ok rs') : rs'.narrower rs := by
  cases a with
  | dropRule i => exact RuleSet.dropRule_narrower h
  | addCond i p => exact RuleSet.addCond_narrower h
  | restrictScope i s => exact RuleSet.restrictScope_narrower h
  | removeSigners i ss => exact RuleSet.removeSigners_narrower h
  | raiseThreshold i k => exact RuleSet.raiseThreshold_narrower h

/-! ## Chains of steps -/

/-- Every rule set derived from a root by attenuation steps stays inside the
root. -/
theorem RuleSet.Derives.narrower {root rs : RuleSet Ctx Sig} (h : RuleSet.Derives root rs) :
    rs.narrower root := by
  induction h with
  | refl => exact RuleSet.narrower_refl root
  | step a _ ha ih => exact RuleSet.narrower_trans (RuleSet.attenuate_narrower ha) ih

theorem RuleSet.attenuateAll_derives {root rs : RuleSet Ctx Sig}
    {steps : List (Attenuation Ctx Sig)} (h : root.attenuateAll steps = .ok rs) :
    RuleSet.Derives root rs := by
  suffices ∀ (steps : List (Attenuation Ctx Sig)) (rs₀ : RuleSet Ctx Sig),
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

theorem RuleSet.attenuateAll_narrower {root rs : RuleSet Ctx Sig}
    {steps : List (Attenuation Ctx Sig)} (h : root.attenuateAll steps = .ok rs) :
    rs.narrower root :=
  (RuleSet.attenuateAll_derives h).narrower

/-! ## Failure -/

omit [DecidableEq Sig] in
theorem RuleSet.modifyRule_eq_error_iff (rs : RuleSet Ctx Sig) (i : Nat)
    (f : Rule Ctx Sig → Rule Ctx Sig) :
    rs.modifyRule i f = .error .noSuchRule ↔ rs.rules.length ≤ i := by
  unfold RuleSet.modifyRule
  split <;> rename_i h
  · simp only [reduceCtorEq, false_iff, Nat.not_le]
    exact (List.getElem?_eq_some_iff.mp h).1
  · simp only [true_iff]
    exact List.getElem?_eq_none_iff.mp h

omit [DecidableEq Sig] in
theorem RuleSet.dropRule_eq_error_iff (rs : RuleSet Ctx Sig) (i : Nat) :
    rs.dropRule i = .error .noSuchRule ↔ rs.rules.length ≤ i := by
  unfold RuleSet.dropRule
  split <;> simp_all

omit [DecidableEq Sig] in
theorem RuleSet.addCond_eq_error_iff (rs : RuleSet Ctx Sig) (i : Nat) (p : Ctx → Bool) :
    rs.addCond i p = .error .noSuchRule ↔ rs.rules.length ≤ i :=
  RuleSet.modifyRule_eq_error_iff rs i _

omit [DecidableEq Sig] in
theorem RuleSet.restrictScope_eq_error_iff (rs : RuleSet Ctx Sig) (i : Nat) (s : Ctx → Bool) :
    rs.restrictScope i s = .error .noSuchRule ↔ rs.rules.length ≤ i :=
  RuleSet.modifyRule_eq_error_iff rs i _

theorem RuleSet.removeSigners_eq_error_iff (rs : RuleSet Ctx Sig) (i : Nat) (ss : List Sig) :
    rs.removeSigners i ss = .error .noSuchRule ↔ rs.rules.length ≤ i :=
  RuleSet.modifyRule_eq_error_iff rs i _

omit [DecidableEq Sig] in
theorem RuleSet.raiseThreshold_eq_noSuchRule_iff (rs : RuleSet Ctx Sig) (i k : Nat) :
    rs.raiseThreshold i k = .error .noSuchRule ↔ rs.rules.length ≤ i := by
  unfold RuleSet.raiseThreshold
  split <;> rename_i h
  · have hi := (List.getElem?_eq_some_iff.mp h).1
    constructor
    · intro he
      split at he <;> cases he
    · intro hle
      exact absurd hi (Nat.not_lt.mpr hle)
  · simp only [true_iff]
    exact List.getElem?_eq_none_iff.mp h

omit [DecidableEq Sig] in
/-- `raiseThreshold` refuses to lower a threshold, and refuses nothing else
with `thresholdLowered`. -/
theorem RuleSet.raiseThreshold_eq_thresholdLowered_iff (rs : RuleSet Ctx Sig) (i k : Nat) :
    rs.raiseThreshold i k = .error .thresholdLowered ↔
      ∃ r, rs.rules[i]? = some r ∧ k < r.threshold := by
  unfold RuleSet.raiseThreshold
  split <;> rename_i h
  · split <;> rename_i hk
    · simp [h, hk]
    · simp [h, hk]
  · simp [h]

end RuleCore
