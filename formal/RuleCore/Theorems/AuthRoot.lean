import RuleCore.Theorems.Chain
import RuleCore.Theorems.Lowering

/-! Exact entry roots, root-aware trace acceptance and spending. -/
namespace RuleCore.Chain

/-- The root check in the generic denotation is the exact optional pair. -/
theorem Rule.rootMatches_eq (r : Rule) (root : Option Context) :
    r.denote.rootMatches root = AuthRoot.matchesOpt r.authRoot root := by
  simp only [Rule.denote, RuleCore.Rule.rootMatches, AuthRoot.matchesOpt]
  cases r.authRoot <;> cases root <;> rfl

/-- The structural root narrowing check is exactly implication of root
acceptance, including missing roots. Erasing or changing an exact requirement
cannot be certified by this check. -/
theorem AuthRoot.narrows_iff (child parent : Option AuthRoot) :
    AuthRoot.narrows child parent = true ↔
      ∀ root, AuthRoot.matchesOpt child root = true →
        AuthRoot.matchesOpt parent root = true := by
  cases parent with
  | none => simp [narrows, matchesOpt]
  | some p =>
    cases child with
    | none =>
      simp only [narrows, Bool.false_eq_true, false_iff]
      intro h
      have := h none rfl
      cases this
    | some c =>
      constructor
      · intro h
        have he : c = p := by
          cases c; cases p
          simpa [narrows, AuthRoot.mk.injEq] using h
        subst c
        exact fun _ h => h
      · intro h
        have hm := h (some (.call c.contract c.function [])) (by simp [matchesOpt, AuthRoot.matches])
        simpa [narrows, matchesOpt, AuthRoot.matches] using hm

/-- Missing/creation roots and wrong pairs cannot satisfy an exact rule. -/
theorem AuthRoot.exact_iff (expected : AuthRoot) (root : Option Context) :
    AuthRoot.matchesOpt (some expected) root = true ↔
      ∃ args, root = some (.call expected.contract expected.function args) := by
  cases root with
  | none => simp [matchesOpt]
  | some ctx =>
    cases ctx with
    | create w => simp [matchesOpt, AuthRoot.matches]
    | call contract function args => simp [matchesOpt, AuthRoot.matches]

/-- Adding a root to an unrestricted rule, or preserving an exact root,
refines root-aware acceptance and retains every spending/time/signer check. -/
theorem Rule.withRoot_refines (r : Rule) (child : Option AuthRoot)
    (h : AuthRoot.narrows child r.authRoot = true) :
    ({ r with authRoot := child } : Rule).denote.Refines r.denote := by
  refine ⟨?_, RuleCore.RuleCap.NarrowerOpt.refl _, fun _ _ h => h, fun _ h => h⟩
  intro root c auth ha
  simp only [RuleCore.Rule.allowsIn, Bool.and_eq_true] at ha ⊢
  refine ⟨?_, ha.2⟩
  rw [Rule.rootMatches_eq] at ha ⊢
  exact (AuthRoot.narrows_iff child r.authRoot).mp h root ha.1

/-- Root narrowing of one installed rule includes complete accepted traces,
not merely local-context screening. Choices and cap state stay aligned. -/
theorem RuleSet.withRoot_traceNarrower (rs : RuleSet) {i : Nat} {r : Rule}
    (hr : rs[i]? = some r) (child : Option AuthRoot)
    (h : AuthRoot.narrows child r.authRoot = true) :
    RuleSet.TraceNarrower (rs.set i { r with authRoot := child }) rs (fun j => j) := by
  have hg : rs.denote.rules[i]? = some r.denote := by simp [hr]
  have href := RuleCore.RuleSet.Refines.set hg (r.withRoot_refines child h)
  apply RuleCore.RuleSet.Refines.traceNarrower
  simpa only [RuleSet.denote, List.map_set, RuleCore.RuleSet.rules_ofRules] using href

/-- Every selected restricted rule of an accepted entry sees its exact pair
at the head of this entry, regardless of other entries or the transaction root. -/
theorem RuleSet.authorize_exactRoot {rs : RuleSet} {records out : List RuleCore.Cap.Record}
    {a : Authorization} (h : rs.authorize records a = .ok out)
    {ctx : Context} {j : Nat} (hx : (ctx, j) ∈ a.denote.chosen)
    {r : Rule} (hr : rs[j]? = some r) {expected : AuthRoot}
    (he : r.authRoot = some expected) :
    ∃ args, a.contexts.head? = some (.call expected.contract expected.function args) := by
  obtain ⟨r', hr', ha⟩ := RuleCore.RuleSet.authorize_chosen_root h (ctx, j) hx
  have hd : rs.denote.rules[j]? = some r.denote := by simp [hr]
  rw [hd] at hr'
  cases hr'
  simp only [RuleCore.Rule.allowsIn, Bool.and_eq_true] at ha
  apply (AuthRoot.exact_iff expected a.contexts.head?).mp
  rw [← he, ← Rule.rootMatches_eq]
  exact ha.1

end RuleCore.Chain

namespace RuleCore
variable {Ctx Sig : Type} [DecidableEq Sig]

/-- Every accepted trace satisfies the root-aware predicate entry by entry. -/
theorem RuleSet.accepts_allowsBatch {rs : RuleSet Ctx Sig} :
    ∀ {as : List (Authorization Ctx Sig)} {records : List Cap.Record},
      rs.Accepts records as → ∀ a ∈ as, rs.allowsBatch a.contexts a.auth = true
  | [], _, _, _, h => by cases h
  | a :: as, records, h, b, hb => by
    obtain ⟨out, hout⟩ := h
    simp only [RuleSet.authorizeAll, List.foldlM_cons] at hout
    cases ha : rs.authorize records a with
    | error e => simp [ha, bind, Except.bind] at hout
    | ok next =>
      simp only [ha, bind, Except.bind] at hout
      rcases List.mem_cons.mp hb with rfl | hb
      · exact RuleSet.authorize_allowsBatch ha
      · exact RuleSet.accepts_allowsBatch ⟨out, hout⟩ b hb

/-- A charge comes from a selected call in an accepted entry whose root the
selected rule accepts. Refused entries contribute no charges, including
entries whose cap pass fails after earlier tentative charges. -/
theorem RuleSet.mem_charged_root {rs : RuleSet Ctx Sig} {j : Nat}
    {r : Rule Ctx Sig} (hr : rs.rules[j]? = some r) (k : RuleCap Ctx) :
    ∀ {as : List (Authorization Ctx Sig)} {records : List Cap.Record} {x : Cap.Call},
      x ∈ rs.charged k j records as → ∃ a ∈ as,
        r.rootMatches a.contexts.head? = true ∧ ∃ c,
          (c, j) ∈ a.chosen ∧ k.amount c = some x.amount ∧ x.now = a.now
  | [], _, _, h => by simp [RuleSet.charged] at h
  | a :: as, records, x, h => by
    unfold RuleSet.charged at h
    cases ha : rs.authorize records a with
    | error e =>
      rw [ha] at h
      obtain ⟨b, hb, hroot, rest⟩ := RuleSet.mem_charged_root hr k h
      exact ⟨b, List.mem_cons_of_mem a hb, hroot, rest⟩
    | ok next =>
      rw [ha] at h
      rcases List.mem_append.mp h with h | h
      · simp only [Authorization.charges, List.mem_filterMap] at h
        obtain ⟨y, hy, hcharge⟩ := h
        split at hcharge
        · rename_i hj
          obtain ⟨amount, hamt, he⟩ := Option.map_eq_some_iff.mp hcharge
          cases he
          obtain ⟨r', hr', hallow⟩ := RuleSet.authorize_chosen_root ha y hy
          rw [hj, hr] at hr'
          cases hr'
          simp only [Rule.allowsIn, Bool.and_eq_true] at hallow
          exact ⟨a, List.mem_cons_self, hallow.1, y.1, by rw [← hj]; exact hy, hamt, rfl⟩
        · cases hcharge
      · obtain ⟨b, hb, hroot, rest⟩ := RuleSet.mem_charged_root hr k h
        exact ⟨b, List.mem_cons_of_mem a hb, hroot, rest⟩

end RuleCore
