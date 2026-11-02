import RuleCore.Model.RuleSet

/-!
# Rule sets: evaluation and narrowing

* `Rule.allows_iff`, `RuleSet.allows_iff`, `RuleSet.allowsAll_iff`: what each
  verdict means.
* `RuleSet.allowsAll_nil`: every rule set allows the empty batch.
* `RuleSet.narrower_refl`, `RuleSet.narrower_trans`: `narrower` is a preorder.
* `RuleSet.allowsAll_of_narrower`: a narrower rule set allows a batch only if
  its ancestor does.

Signers:

* `Rule.signed_iff`, `Rule.mem_present`: the signer requirement holds exactly
  when at least `threshold` distinct rule signers are authenticated.
* `Rule.signed_of_threshold_zero`, `Rule.allows_of_threshold_zero`: a
  threshold of 0 is no requirement, so the verdict does not depend on the
  authenticated signers.
* `Rule.signed_iff_of_threshold_eq`: a threshold equal to the number of
  distinct signers requires every signer.
* `Rule.signed_false_of_lt`, `Rule.allows_false_of_lt`: a threshold above the
  number of distinct signers is never met, so the rule allows nothing.
* `Rule.signed_of_subset`, `Rule.allows_of_subset`, `RuleSet.allows_of_subset`,
  `RuleSet.allowsAll_of_subset`: authenticating more signers never turns an
  allow into a refusal.
* `Rule.signed_congr`, `RuleSet.allows_congr`, `RuleSet.allowsAll_congr`,
  `RuleSet.allows_eraseDups`: the verdict depends only on which signers are
  authenticated, not on their order or repeats.
* `Rule.signed_congr_signers`, `Rule.allows_congr_signers`,
  `Rule.signed_eraseDups_signers`: likewise for the rule's own signer list.
-/

namespace RuleCore

variable {Ctx Sig : Type} [DecidableEq Sig]

theorem Rule.allows_iff (r : Rule Ctx Sig) (c : Ctx) (auth : List Sig) :
    r.allows c auth = true ↔
      r.scope c = true ∧ (∀ p ∈ r.conds, p c = true) ∧ r.signed auth = true := by
  simp [Rule.allows, and_assoc]

theorem RuleSet.allows_iff (rs : RuleSet Ctx Sig) (c : Ctx) (auth : List Sig) :
    rs.allows c auth = true ↔ ∃ r ∈ rs.rules, r.allows c auth = true :=
  List.any_eq_true

theorem RuleSet.allowsAll_iff (rs : RuleSet Ctx Sig) (cs : List Ctx) (auth : List Sig) :
    rs.allowsAll cs auth = true ↔ ∀ c ∈ cs, rs.allows c auth = true := by
  simp [RuleSet.allowsAll]

/-- The empty batch is allowed by every rule set, the empty one included. A
Soroban authorization tree always has a root context, so a batch built from
one is never empty. -/
@[simp] theorem RuleSet.allowsAll_nil (rs : RuleSet Ctx Sig) (auth : List Sig) :
    rs.allowsAll [] auth = true := rfl

theorem RuleSet.narrower_refl (rs : RuleSet Ctx Sig) : rs.narrower rs :=
  fun _ _ h => h

theorem RuleSet.narrower_trans {rs'' rs' rs : RuleSet Ctx Sig} :
    rs''.narrower rs' → rs'.narrower rs → rs''.narrower rs :=
  fun h₁ h₂ c auth h => h₂ c auth (h₁ c auth h)

/-- A narrower rule set allows a batch only if its ancestor does, so checking
every context of an authorization tree against a derived rule set never
accepts a tree its ancestor would reject. -/
theorem RuleSet.allowsAll_of_narrower {rs' rs : RuleSet Ctx Sig} (h : rs'.narrower rs)
    (cs : List Ctx) (auth : List Sig) :
    rs'.allowsAll cs auth = true → rs.allowsAll cs auth = true := by
  simp only [RuleSet.allowsAll_iff]
  exact fun h' c hc => h c auth (h' c hc)

/-! ## Signers -/

/-- `eraseDups` leaves no repeats. -/
theorem nodup_eraseDups : ∀ l : List Sig, l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: l => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_, nodup_eraseDups _⟩
    simp
termination_by l => l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem Rule.mem_present (r : Rule Ctx Sig) (auth : List Sig) (s : Sig) :
    s ∈ r.present auth ↔ s ∈ r.signers ∧ s ∈ auth := by
  simp [Rule.present]

theorem Rule.nodup_present (r : Rule Ctx Sig) (auth : List Sig) : (r.present auth).Nodup :=
  (nodup_eraseDups r.signers).filter _

theorem Rule.signed_iff (r : Rule Ctx Sig) (auth : List Sig) :
    r.signed auth = true ↔ r.threshold ≤ (r.present auth).length := by
  simp [Rule.signed]

omit [DecidableEq Sig] in
/-- Two lists without repeats and with the same members have the same
length. -/
theorem length_eq_of_nodup_of_mem_iff {l l' : List Sig} (hl : l.Nodup) (hl' : l'.Nodup)
    (h : ∀ s, s ∈ l ↔ s ∈ l') : l.length = l'.length :=
  ((List.perm_ext_iff_of_nodup hl hl').mpr h).length_eq

/-- Every distinct signer present under `auth` is present under a larger
`auth'`, so there are at least as many. -/
theorem Rule.present_length_le_of_subset (r : Rule Ctx Sig) {auth auth' : List Sig}
    (h : auth ⊆ auth') : (r.present auth).length ≤ (r.present auth').length :=
  (r.nodup_present auth).length_le_of_subset fun s hs => by
    rw [Rule.mem_present] at hs ⊢
    exact ⟨hs.1, h hs.2⟩

/-- A threshold of 0 is no signer requirement. -/
theorem Rule.signed_of_threshold_zero {r : Rule Ctx Sig} (h : r.threshold = 0)
    (auth : List Sig) : r.signed auth = true := by
  simp [Rule.signed, h]

/-- With a threshold of 0, a rule's verdict is its scope and conditions alone,
whatever signers are authenticated. -/
theorem Rule.allows_of_threshold_zero {r : Rule Ctx Sig} (h : r.threshold = 0) (c : Ctx)
    (auth : List Sig) : r.allows c auth = (r.scope c && r.conds.all (· c)) := by
  simp [Rule.allows, Rule.signed_of_threshold_zero h]

/-- A threshold equal to the number of distinct signers is met exactly when
every signer of the rule is authenticated. -/
theorem Rule.signed_iff_of_threshold_eq {r : Rule Ctx Sig}
    (h : r.threshold = r.signers.eraseDups.length) (auth : List Sig) :
    r.signed auth = true ↔ ∀ s ∈ r.signers, s ∈ auth := by
  rw [Rule.signed_iff, h, Rule.present]
  constructor
  · intro hle s hs
    have hlen : (r.signers.eraseDups.filter (· ∈ auth)).length = r.signers.eraseDups.length :=
      Nat.le_antisymm (List.length_filter_le _ _) hle
    have := List.length_filter_eq_length_iff.mp hlen s (List.mem_eraseDups.mpr hs)
    simpa using this
  · intro hall
    rw [List.filter_eq_self.mpr (fun s hs => by simpa using hall s (List.mem_eraseDups.mp hs))]
    exact Nat.le_refl _

/-- A threshold above the number of distinct signers is never met. -/
theorem Rule.signed_false_of_lt {r : Rule Ctx Sig} (h : r.signers.eraseDups.length < r.threshold)
    (auth : List Sig) : r.signed auth = false := by
  have : (r.present auth).length ≤ r.signers.eraseDups.length := List.length_filter_le _ _
  simp [Rule.signed]
  omega

/-- A rule whose threshold is above its number of distinct signers allows
nothing. -/
theorem Rule.allows_false_of_lt {r : Rule Ctx Sig} (h : r.signers.eraseDups.length < r.threshold)
    (c : Ctx) (auth : List Sig) : r.allows c auth = false := by
  simp [Rule.allows, Rule.signed_false_of_lt h]

/-- Authenticating more signers keeps the signer requirement met. -/
theorem Rule.signed_of_subset (r : Rule Ctx Sig) {auth auth' : List Sig} (h : auth ⊆ auth') :
    r.signed auth = true → r.signed auth' = true := by
  rw [Rule.signed_iff, Rule.signed_iff]
  exact fun hle => Nat.le_trans hle (r.present_length_le_of_subset h)

theorem Rule.allows_of_subset (r : Rule Ctx Sig) (c : Ctx) {auth auth' : List Sig}
    (h : auth ⊆ auth') : r.allows c auth = true → r.allows c auth' = true := by
  rw [Rule.allows_iff, Rule.allows_iff]
  exact fun ⟨hs, hc, hg⟩ => ⟨hs, hc, r.signed_of_subset h hg⟩

/-- Authenticating more signers never turns an allow into a refusal. -/
theorem RuleSet.allows_of_subset (rs : RuleSet Ctx Sig) (c : Ctx) {auth auth' : List Sig}
    (h : auth ⊆ auth') : rs.allows c auth = true → rs.allows c auth' = true := by
  rw [RuleSet.allows_iff, RuleSet.allows_iff]
  exact fun ⟨r, hr, ha⟩ => ⟨r, hr, r.allows_of_subset c h ha⟩

theorem RuleSet.allowsAll_of_subset (rs : RuleSet Ctx Sig) (cs : List Ctx)
    {auth auth' : List Sig} (h : auth ⊆ auth') :
    rs.allowsAll cs auth = true → rs.allowsAll cs auth' = true := by
  rw [RuleSet.allowsAll_iff, RuleSet.allowsAll_iff]
  exact fun ha c hc => rs.allows_of_subset c h (ha c hc)

/-- The signer requirement depends only on which signers are authenticated:
not on their order, and not on repeats. -/
theorem Rule.signed_congr (r : Rule Ctx Sig) {auth auth' : List Sig}
    (h : ∀ s, s ∈ auth ↔ s ∈ auth') : r.signed auth = r.signed auth' := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨r.signed_of_subset fun s hs => (h s).mp hs, r.signed_of_subset fun s hs => (h s).mpr hs⟩

theorem RuleSet.allows_congr (rs : RuleSet Ctx Sig) (c : Ctx) {auth auth' : List Sig}
    (h : ∀ s, s ∈ auth ↔ s ∈ auth') : rs.allows c auth = rs.allows c auth' := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨rs.allows_of_subset c fun s hs => (h s).mp hs,
    rs.allows_of_subset c fun s hs => (h s).mpr hs⟩

theorem RuleSet.allowsAll_congr (rs : RuleSet Ctx Sig) (cs : List Ctx) {auth auth' : List Sig}
    (h : ∀ s, s ∈ auth ↔ s ∈ auth') : rs.allowsAll cs auth = rs.allowsAll cs auth' := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨rs.allowsAll_of_subset cs fun s hs => (h s).mp hs,
    rs.allowsAll_of_subset cs fun s hs => (h s).mpr hs⟩

/-- Authenticating a signer twice is authenticating it once. -/
theorem RuleSet.allows_eraseDups (rs : RuleSet Ctx Sig) (c : Ctx) (auth : List Sig) :
    rs.allows c auth.eraseDups = rs.allows c auth :=
  rs.allows_congr c fun _ => List.mem_eraseDups

/-- The signer requirement depends only on which signers the rule lists: not
on their order, and not on repeats. -/
theorem Rule.signed_congr_signers {r r' : Rule Ctx Sig} (hs : ∀ s, s ∈ r.signers ↔ s ∈ r'.signers)
    (ht : r.threshold = r'.threshold) (auth : List Sig) : r.signed auth = r'.signed auth := by
  have : (r.present auth).length = (r'.present auth).length :=
    length_eq_of_nodup_of_mem_iff (r.nodup_present auth) (r'.nodup_present auth) fun s => by
      rw [Rule.mem_present, Rule.mem_present, hs]
  simp [Rule.signed, this, ht]

theorem Rule.allows_congr_signers {r r' : Rule Ctx Sig} (hscope : r.scope = r'.scope)
    (hconds : r.conds = r'.conds) (hs : ∀ s, s ∈ r.signers ↔ s ∈ r'.signers)
    (ht : r.threshold = r'.threshold) (c : Ctx) (auth : List Sig) :
    r.allows c auth = r'.allows c auth := by
  simp [Rule.allows, hscope, hconds, Rule.signed_congr_signers hs ht auth]

/-- Listing a signer twice in a rule is listing it once. -/
theorem Rule.signed_eraseDups_signers (r : Rule Ctx Sig) (auth : List Sig) :
    { r with signers := r.signers.eraseDups }.signed auth = r.signed auth :=
  Rule.signed_congr_signers (r := { r with signers := r.signers.eraseDups }) (r' := r)
    (fun _ => List.mem_eraseDups) rfl auth

end RuleCore
