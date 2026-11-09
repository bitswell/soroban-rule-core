import RuleCore.Vocab.Account
import RuleCore.Theorems.Lowering

/-!
# Scoped documents, the generation and the containment chain

Scoped lowering:

* `Doc.lowerScoped_eq_ok`: what an accepted scoped lowering is: no recovery
  configured, no rule on the account or the excluded set, and the document's
  rules lowered with the generation.
* `Doc.lowerScoped_allows`, `Doc.lowerScoped_checkAuth`: compile soundness for
  scoped documents. The scoped lowering allows exactly what the document
  allows, and through `checkAuth` accepts exactly what the document accepts
  issued under that generation, with the same records.

Exclusion:

* `Doc.lowerScoped_contract`: every rule a scoped document lowers to applies
  to a contract that is neither the account nor in the excluded set.
* `Doc.lowerScoped_allows_excluded`: no such rule set allows a call to the
  account or to a contract of the excluded set, under any signers.
* `Doc.lowerScoped_attenuateAll_excluded`: nor does any rule set attenuated
  from it.

Generation:

* `Doc.lowerScoped_generation`, `Doc.lower_generation`: every scoped rule
  carries the generation it was issued under; every admin rule carries none.
* `RuleSet.checkAuth_generation_none`: a rule set whose rules carry no
  generation authorizes the same in every generation.
* `Account.run_address`, `Account.run_generation`: a run keeps the account's
  address, and its generation advances by exactly the recoveries it completes.
* `Account.issued_stale`: after a run that completes a recovery, a grant
  attenuated from a scoped document issued before it authorizes nothing.
* `Account.adminRules_checkAuth_generation`: the admin rules authorize the same
  whatever the generation.

The chain:

* `Account.chain`: anything `checkAuth` accepts under a grant attenuated from
  the rules a scoped document was issued as is allowed by that scoped
  document, touches neither the account nor its recovery controller, ZK
  adapter or pool, and is made in the generation the document was issued
  under.
* `Account.chain_trace`: every run of authorizations the grant accepts from
  empty records, the scoped document's rules accept, with each choice
  renumbered, and those rules accept exactly what the scoped document does.
* `Account.chain_after_recovery`: once the account has completed a recovery
  since the issue, the grant accepts only the empty batch.
-/

namespace RuleCore.Document

open RuleCore RuleCore.Chain

/-! ## Scoped lowering -/

theorem Doc.lowerScoped_eq_ok {d : Doc} {acct : Bytes} {ex : List Bytes} {gen : UInt64}
    {rs : Chain.RuleSet} (h : d.lowerScoped acct ex gen = .ok rs) :
    d.recovery = none ∧ (∀ r ∈ d.rules, r.scope.excludedBy acct ex = false) ∧
      rs = d.lowerRules acct (some gen) := by
  unfold Doc.lowerScoped at h
  cases hr : d.recovery with
  | some _ => rw [hr] at h; cases h
  | none =>
    rw [hr] at h
    simp only at h
    split at h
    · cases h
    · rename_i hany
      cases h
      refine ⟨rfl, fun r hr' => ?_, rfl⟩
      cases he : r.scope.excludedBy acct ex
      · rfl
      · exact absurd (List.any_eq_true.mpr ⟨r, hr', he⟩) hany

theorem Doc.lowerRules_eq_append {d : Doc} (hr : d.recovery = none) (acct : Bytes)
    (gen : Option UInt64) : d.lowerRules acct gen = d.lowerRules acct gen ++ d.recoveryRules acct := by
  simp [Doc.recoveryRules, hr]

/-- A scoped document's lowering allows exactly what the document allows. -/
theorem Doc.lowerScoped_allows {d : Doc} (hv : d.Valid) {acct : Bytes} {ex : List Bytes}
    {gen : UInt64} {rs : Chain.RuleSet} (h : d.lowerScoped acct ex gen = .ok rs) (c : Context)
    (auth : List Signer) : rs.allows c auth = d.allows acct c auth := by
  obtain ⟨-, -, rfl⟩ := Doc.lowerScoped_eq_ok h
  exact Doc.lowerRules_allows hv acct (some gen) c auth

/-- Compile soundness for scoped documents through `checkAuth`: on every
authorization, a scoped document's lowering accepts exactly when the
document, issued under the generation, accepts, with the same records. -/
theorem Doc.lowerScoped_checkAuth {d : Doc} (hv : d.Valid) {acct : Bytes} {ex : List Bytes}
    {gen : UInt64} {rs : Chain.RuleSet} (h : d.lowerScoped acct ex gen = .ok rs)
    (ctl : Context → List Signer → Bool) (records : List RuleCore.Cap.Record)
    (a : Chain.Authorization) :
    (rs.checkAuth records a).toOption = d.checkAuth acct ctl (some gen) records a := by
  obtain ⟨hr, -, rfl⟩ := Doc.lowerScoped_eq_ok h
  rw [Doc.lowerRules_eq_append hr, Doc.checkAuth_lowerAll hv,
    Doc.checkAuth_of_recovery_none hr]

/-! ## Exclusion -/

/-- Every rule a scoped document lowers to applies to a contract that is
neither the account nor in the excluded set. -/
theorem Doc.lowerScoped_contract {d : Doc} {acct : Bytes} {ex : List Bytes} {gen : UInt64}
    {rs : Chain.RuleSet} (h : d.lowerScoped acct ex gen = .ok rs) :
    ∀ r ∈ rs, r.contract ≠ acct ∧ r.contract ∉ ex := by
  obtain ⟨-, hex, rfl⟩ := Doc.lowerScoped_eq_ok h
  intro r hr
  simp only [Doc.lowerRules, List.mem_map] at hr
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  have := hex r₀ hr₀
  simp only [Doc.lowerRule]
  cases hs : r₀.scope with
  | selfAdmin => rw [hs] at this; cases this
  | contract a =>
    rw [hs] at this
    simp only [Scope.excludedBy, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
    exact this

/-- No rule set a scoped document lowers to allows a call to the account or to
a contract of the excluded set, under any signers. -/
theorem Doc.lowerScoped_allows_excluded {d : Doc} {acct : Bytes} {ex : List Bytes}
    {gen : UInt64} {rs : Chain.RuleSet} (h : d.lowerScoped acct ex gen = .ok rs)
    {contract function : Bytes} {args : List Val} {auth : List Signer}
    (ha : rs.allows (.call contract function args) auth = true) :
    contract ≠ acct ∧ contract ∉ ex := by
  obtain ⟨r, hr, hra⟩ := (Chain.RuleSet.allows_iff rs _ auth).mp ha
  obtain ⟨rfl, -⟩ := (Chain.Rule.allows_call_iff r contract function args auth).mp hra
  exact Doc.lowerScoped_contract h r hr

/-- Exclusion survives attenuation: no rule set attenuated from a scoped
document's lowering allows a call to the account or to a contract of the
excluded set. -/
theorem Doc.lowerScoped_attenuateAll_excluded {d : Doc} {acct : Bytes} {ex : List Bytes}
    {gen : UInt64} {rs rs' : Chain.RuleSet} (h : d.lowerScoped acct ex gen = .ok rs)
    {steps : List Chain.Attenuation} (hs : rs.attenuateAll steps = .ok rs')
    {contract function : Bytes} {args : List Val} {auth : List Signer}
    (ha : rs'.allows (.call contract function args) auth = true) :
    contract ≠ acct ∧ contract ∉ ex :=
  Doc.lowerScoped_allows_excluded h (Chain.RuleSet.attenuateAll_narrower hs _ auth ha)

/-- The excluded set the admin document gives holds the account, its recovery
controller, and its zero-knowledge factor's adapter and pool. -/
theorem Doc.mem_excluded (admin : Doc) (acct : Bytes) :
    acct ∈ admin.excluded acct ∧
      ∀ rc, admin.recovery = some rc →
        rc.controller ∈ admin.excluded acct ∧
          ∀ z, rc.zk = some z → z.adapter ∈ admin.excluded acct ∧ z.pool ∈ admin.excluded acct := by
  refine ⟨List.mem_cons_self, fun rc hrc => ?_⟩
  simp only [Doc.excluded, hrc]
  refine ⟨by simp, fun z hz => ?_⟩
  simp [hz]

/-! ## Generation -/

/-- Every rule a scoped document lowers to carries the generation it was
issued under. -/
theorem Doc.lowerScoped_generation {d : Doc} {acct : Bytes} {ex : List Bytes} {gen : UInt64}
    {rs : Chain.RuleSet} (h : d.lowerScoped acct ex gen = .ok rs) :
    ∀ r ∈ rs, r.generation = some gen := by
  obtain ⟨-, -, rfl⟩ := Doc.lowerScoped_eq_ok h
  intro r hr
  simp only [Doc.lowerRules, List.mem_map] at hr
  obtain ⟨r₀, -, rfl⟩ := hr
  rfl

/-- No rule the admin document lowers to carries a generation. -/
theorem Doc.lower_generation (d : Doc) (acct : Bytes) : ∀ r ∈ d.lower acct, r.generation = none := by
  intro r hr
  simp only [Doc.lower, Doc.lowerRules, Doc.recoveryRules, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨r₀, -, rfl⟩ | hr
  · rfl
  · cases hrc : d.recovery <;> simp only [hrc, List.mem_singleton, List.not_mem_nil] at hr
    subst hr
    rfl

/-- A rule set whose rules carry no generation authorizes the same in every
generation. -/
theorem RuleSet.checkAuth_generation_none {rs : Chain.RuleSet}
    (h : ∀ r ∈ rs, r.generation = none) (records : List RuleCore.Cap.Record)
    (a : Chain.Authorization) (g : UInt64) :
    rs.checkAuth records { a with generation := g } = rs.checkAuth records a := by
  have hc : rs.denote.checkChoice a.auth a.now.toNat g.toNat =
      rs.denote.checkChoice a.auth a.now.toNat a.generation.toNat := by
    funext root x
    unfold RuleCore.RuleSet.checkChoice
    cases hx : rs.denote.rules[x.2]? with
    | none => rfl
    | some r =>
      have hg : r.generation = none := by
        rw [Chain.RuleSet.denote_get] at hx
        cases hx' : rs[x.2]? with
        | none => rw [hx'] at hx; cases hx
        | some r₀ =>
          rw [hx'] at hx
          cases hx
          simp [Chain.Rule.denote, h r₀ (List.mem_of_getElem? hx')]
      simp [RuleCore.Rule.stale, hg]
  simp only [Chain.RuleSet.checkAuth, Chain.Authorization.denote, RuleCore.RuleSet.checkAuth, hc,
    RuleCore.Authorization.chosen]
  rfl

theorem Account.step_address {s s' : Account} {e : Event} (h : s.step e = .ok s') :
    s'.address = s.address := by
  cases e with
  | applyDoc d => simp only [Account.step, Except.ok.injEq] at h; subst h; rfl
  | completeRecovery t =>
    simp only [Account.step] at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h; subst h; rfl

/-- A run keeps the account's address. -/
theorem Account.run_address : ∀ (s : Account) (es : List Event), (s.run es).address = s.address
  | _, [] => rfl
  | s, e :: es => by
    simp only [Account.run]
    cases h : s.step e with
    | ok s' => rw [Account.run_address s' es, Account.step_address h]
    | error _ => exact Account.run_address s es

/-- A run advances the generation by exactly the recoveries it completes. -/
theorem Account.run_generation :
    ∀ (s : Account) (es : List Event),
      (s.run es).generation.toNat = s.generation.toNat + s.completions es
  | _, [] => rfl
  | s, e :: es => by
    cases e with
    | applyDoc d =>
      simp only [Account.run, Account.completions, Account.step]
      rw [Account.run_generation]
    | completeRecovery t =>
      by_cases hmax : s.generation = maxGeneration
      · simp only [Account.run, Account.completions, Account.step, ite_eq_left hmax]
        exact Account.run_generation s es
      · simp only [Account.run, Account.completions, Account.step, ite_eq_right hmax]
        rw [Account.run_generation]
        have hlt : s.generation.toNat < 18446744073709551615 := by
          have := s.generation.toNat_lt
          have hne : s.generation.toNat ≠ 18446744073709551615 := fun e =>
            hmax (UInt64.toNat_inj.mp (by simpa [maxGeneration] using e))
          omega
        simp only [UInt64.toNat_add, UInt64.toNat_one]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

/-- After a run that completes a recovery, a grant attenuated from the rules a
scoped document was issued as before the run authorizes nothing: it accepts
only the empty batch in the account's current generation. -/
theorem Account.issued_stale {s : Account} {sd : Doc} {root grant : Chain.RuleSet}
    {steps : List Chain.Attenuation} (hissue : s.issue sd = .ok root)
    (hgrant : root.attenuateAll steps = .ok grant) {es : List Event} (hc : 0 < s.completions es)
    {records records' : List RuleCore.Cap.Record} {a : Chain.Authorization}
    (hgen : a.generation = (s.run es).generation) (ha : grant.checkAuth records a = .ok records') :
    a.contexts = [] := by
  have hall := Chain.RuleSet.attenuateAll_generation_eq hgrant (Doc.lowerScoped_generation hissue)
  refine Chain.RuleSet.checkAuth_contexts_nil_of_stale ha hall ?_
  intro he
  have := Account.run_generation s es
  rw [← hgen, ← he] at this
  omega

/-- The admin rules authorize the same in every generation: a recovery leaves
them as they were. -/
theorem Account.adminRules_checkAuth_generation (s : Account) (records : List RuleCore.Cap.Record)
    (a : Chain.Authorization) (g : UInt64) :
    s.adminRules.checkAuth records { a with generation := g } = s.adminRules.checkAuth records a :=
  RuleSet.checkAuth_generation_none (Doc.lower_generation s.admin s.address) records a g

/-! ## The chain -/

/-- The containment chain: anything `checkAuth` accepts under a grant
attenuated from the rules a valid scoped document was issued as is allowed by
that scoped document, touches neither the account nor a contract of the
excluded set its admin document gives (its recovery controller, ZK adapter and
pool), and is made in the generation the document was issued under. -/
theorem Account.chain {s : Account} {sd : Doc} (hv : sd.Valid) {root grant : Chain.RuleSet}
    {steps : List Chain.Attenuation} (hissue : s.issue sd = .ok root)
    (hgrant : root.attenuateAll steps = .ok grant) {records records' : List RuleCore.Cap.Record}
    {a : Chain.Authorization} (ha : grant.checkAuth records a = .ok records') :
    (∀ c ∈ a.contexts, sd.allows s.address c a.auth = true) ∧
      (∀ c ∈ a.contexts, ∀ contract function args, c = .call contract function args →
        contract ∉ s.admin.excluded s.address) ∧
      (a.contexts ≠ [] → a.generation = s.generation) := by
  have hall := (Chain.RuleSet.allowsAll_iff grant a.contexts a.auth).mp
    (Chain.RuleSet.checkAuth_allowsAll ha)
  have hroot : ∀ c ∈ a.contexts, root.allows c a.auth = true := fun c hc =>
    Chain.RuleSet.attenuateAll_narrower hgrant c a.auth (hall c hc)
  refine ⟨fun c hc => ?_, fun c hc contract function args he => ?_, fun hne => ?_⟩
  · rw [← Doc.lowerScoped_allows hv hissue]
    exact hroot c hc
  · have := hroot c hc
    rw [he] at this
    exact (Doc.lowerScoped_allows_excluded hissue this).2
  · by_cases hg : a.generation = s.generation
    · exact hg
    · exact absurd (Chain.RuleSet.checkAuth_contexts_nil_of_stale ha
        (Chain.RuleSet.attenuateAll_generation_eq hgrant (Doc.lowerScoped_generation hissue))
        (Ne.symm hg)) hne

/-- The chain through caps: every run of authorizations the grant accepts from
empty records, the scoped document's rules accept from theirs, with each
choice renumbered by the map the attenuation steps induce; and those rules
accept exactly what the scoped document, issued under the generation, accepts,
with the same records. -/
theorem Account.chain_trace {s : Account} {sd : Doc} (hv : sd.Valid) {root grant : Chain.RuleSet}
    {steps : List Chain.Attenuation} (hissue : s.issue sd = .ok root)
    (hgrant : root.attenuateAll steps = .ok grant) :
    grant.TraceNarrower root (Chain.Attenuation.chainSource steps) ∧
      ∀ (ctl : Context → List Signer → Bool) (records : List RuleCore.Cap.Record)
        (a : Chain.Authorization),
        (root.checkAuth records a).toOption =
          sd.checkAuth s.address ctl (some s.generation) records a :=
  ⟨Chain.RuleSet.attenuateAll_traceNarrower hgrant,
    fun ctl records a => Doc.lowerScoped_checkAuth hv hissue ctl records a⟩

/-- After the account completes a recovery, nothing below the admin document
authorizes: a grant attenuated from a scoped document issued before accepts
only the empty batch, while the admin rules authorize as before. -/
theorem Account.chain_after_recovery {s : Account} {sd : Doc} {root grant : Chain.RuleSet}
    {steps : List Chain.Attenuation} (hissue : s.issue sd = .ok root)
    (hgrant : root.attenuateAll steps = .ok grant) {es : List Event} (hc : 0 < s.completions es)
    {records records' : List RuleCore.Cap.Record} {a : Chain.Authorization}
    (hgen : a.generation = (s.run es).generation) (ha : grant.checkAuth records a = .ok records') :
    a.contexts = [] ∧
      ∀ g, (s.run es).adminRules.checkAuth records { a with generation := g } =
        (s.run es).adminRules.checkAuth records a :=
  ⟨Account.issued_stale hissue hgrant hc hgen ha,
    fun g => Account.adminRules_checkAuth_generation (s.run es) records a g⟩

/-! ## Former names

The names these theorems had before the evaluator's entry point was renamed
`check_auth`, kept so that citations of them still resolve. -/

@[deprecated Doc.lowerScoped_checkAuth (since := "2026-11-08")]
theorem Doc.lowerScoped_authorize : type_of% @Doc.lowerScoped_checkAuth := @Doc.lowerScoped_checkAuth

@[deprecated RuleSet.checkAuth_generation_none (since := "2026-11-08")]
theorem RuleSet.authorize_generation_none : type_of% @RuleSet.checkAuth_generation_none := @RuleSet.checkAuth_generation_none

@[deprecated Account.adminRules_checkAuth_generation (since := "2026-11-08")]
theorem Account.adminRules_authorize_generation : type_of% @Account.adminRules_checkAuth_generation := @Account.adminRules_checkAuth_generation

end RuleCore.Document
