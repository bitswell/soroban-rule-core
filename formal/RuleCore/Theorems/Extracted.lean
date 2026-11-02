import RuleCore.Equiv.Attenuation
import RuleCore.Theorems.Chain

/-!
# Theorems on the extracted evaluator

The chain vocabulary's theorems, carried over to the Lean translation of
`crates/rule-eval` through the equivalence theorems of `RuleCore.Equiv`. Each
is stated on the extracted functions alone: `Narrower` is defined by the
extracted `allows`, under every slice of authenticated signers, and a step is a
call of an extracted attenuation function that returned `Ok`.

Attenuation:

* `drop_rule_narrower`, `add_cond_narrower`, `remove_functions_narrower`,
  `remove_signers_narrower`, `raise_threshold_narrower`, `add_cap_narrower`,
  `lower_cap_limit_narrower`, `lengthen_cap_period_narrower`, `Step.narrower`:
  each extracted attenuation step yields a narrower rule set.
* `Narrower.refl`, `Narrower.trans`: `Narrower` is a preorder.
* `Derives.narrower`: any chain of extracted steps stays inside its root.
* `allows_all_of_narrower`, `Derives.allows_all`: a narrower rule set accepts
  a batch only if its ancestor does.
* `add_cond_room`: an `add_cond` that returned `Ok` had room for the condition
  (`CondRoom`), so `add_cond_narrower` needs no hypothesis.

Contract creation:

* `allows_create`, `allows_all_create`: no rule set allows a contract creation,
  and a batch containing one is denied.

Signers:

* `signer_eq_iff`, `signer_eq_delegated_external`: the extracted `signer_eq`
  is equality of the Rust signers; a `Delegated` signer never equals an
  `External` one, whatever their bytes.
* `allows_of_subset`, `allows_all_of_subset`: authenticating more signers never
  turns an allow into a refusal.
* `allows_congr`, `allows_all_congr`: the verdict depends only on which signers
  are authenticated, not on their order or repeats.
* `rule_allows_congr_signers`: nor on the order or repeats of a rule's own
  signer list.
* `rule_allows_threshold_zero`: with threshold 0 a rule's verdict does not
  depend on the authenticated signers.
* `signers_met_all_iff`: a threshold equal to the number of distinct signers is
  met exactly when every signer is authenticated.
* `rule_allows_false_of_lt`: a rule whose threshold is above its number of
  distinct signers allows nothing.

Arguments and byte strings:

* `val_eq_iff`: the extracted `val_eq` is equality of the Rust values.
* `val_eq_kind`, `val_eq_other_bytes`: it holds only for values of the same
  constructor; an `Other` value never equals a `Bytes` value, whatever the
  bytes.
* `cond_holds_argEq_iff`, `cond_holds_argEq_kind`,
  `cond_holds_argEq_false_of_kind_ne`: `ArgEq index v` holds exactly when
  argument `index` is `v`, so only for an argument of `v`'s constructor.
* `bytes_eq_iff`: two byte strings compare equal exactly when they hold the
  same bytes.
* `rule_allows_call`, `rule_allows_extension_false`,
  `rule_allows_prefix_false`: a rule allows only calls to exactly its contract
  and exactly one of its functions; a call to a proper extension or a proper
  prefix of its contract id is denied.
-/

namespace RuleCore.Extracted

open Aeneas Aeneas.Std Result RuleCore.Equiv

/-- `rs'` is narrower than `rs` on the extracted evaluator: every context the
extracted `allows` accepts under `rs'` and some authenticated signers, it
accepts under `rs` and the same signers. -/
def Narrower (rs' rs : Slice rule_eval.rule.Rule) : Prop :=
  ∀ c authenticated, rule_eval.rule_set.allows rs' c authenticated = ok true →
    rule_eval.rule_set.allows rs c authenticated = ok true

theorem Narrower.refl (rs : Slice rule_eval.rule.Rule) : Narrower rs rs :=
  fun _ _ h => h

theorem Narrower.trans {rs'' rs' rs : Slice rule_eval.rule.Rule} :
    Narrower rs'' rs' → Narrower rs' rs → Narrower rs'' rs :=
  fun h₁ h₂ c a h => h₂ c a (h₁ c a h)

/-- The model's `narrower` on the denotations gives `Narrower` on the extracted
evaluator. -/
theorem narrower_of_denote {rs' rs : Slice rule_eval.rule.Rule}
    (h : (denoteRules rs'.val).narrower (denoteRules rs.val)) : Narrower rs' rs := by
  intro c a hc
  rw [allows_eq] at hc ⊢
  exact congrArg ok (h _ _ (Result.ok_injective hc))

/-! ## Attenuation -/

theorem drop_rule_narrower {rules : Slice rule_eval.rule.Rule} {index : Std.U32}
    {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.attenuate.drop_rule rules index = ok (.Ok out)) :
    Narrower (alloc.vec.Vec.deref out) rules := by
  obtain ⟨res, hres, hd⟩ := drop_rule_eq rules index
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  apply narrower_of_denote
  rw [vec_deref_val]
  exact Chain.RuleSet.dropRule_narrower hd.symm

theorem remove_functions_narrower {rules : Slice rule_eval.rule.Rule} {index : Std.U32}
    {functions : Slice (alloc.vec.Vec Std.U8)} {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.attenuate.remove_functions rules index functions = ok (.Ok out)) :
    Narrower (alloc.vec.Vec.deref out) rules := by
  obtain ⟨res, hres, hd⟩ := remove_functions_eq rules index functions
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  apply narrower_of_denote
  rw [vec_deref_val]
  exact Chain.RuleSet.removeFunctions_narrower hd.symm

theorem remove_signers_narrower {rules : Slice rule_eval.rule.Rule} {index : Std.U32}
    {signers : Slice rule_eval.signer.Signer} {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.attenuate.remove_signers rules index signers = ok (.Ok out)) :
    Narrower (alloc.vec.Vec.deref out) rules := by
  obtain ⟨res, hres, hd⟩ := remove_signers_eq rules index signers
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  apply narrower_of_denote
  rw [vec_deref_val]
  exact Chain.RuleSet.removeSigners_narrower hd.symm

theorem raise_threshold_narrower {rules : Slice rule_eval.rule.Rule} {index threshold : Std.U32}
    {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.attenuate.raise_threshold rules index threshold = ok (.Ok out)) :
    Narrower (alloc.vec.Vec.deref out) rules := by
  obtain ⟨res, hres, hd⟩ := raise_threshold_eq rules index threshold
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  apply narrower_of_denote
  rw [vec_deref_val]
  exact Chain.RuleSet.raiseThreshold_narrower hd.symm

/-- An `add_cond` that returned `Ok` had room for the condition. -/
theorem add_cond_room {rules : Slice rule_eval.rule.Rule} {index : Std.U32}
    {cond : rule_eval.rule.Cond} {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.attenuate.add_cond rules index cond = ok (.Ok out)) : CondRoom rules index := by
  intro r hr
  apply Nat.lt_of_not_le
  intro hn
  have hfull : r.conds.val.length = Usize.max := by
    have := r.conds.property
    omega
  rw [add_cond_full rules index cond hr hfull] at h
  simp at h

theorem add_cond_narrower {rules : Slice rule_eval.rule.Rule} {index : Std.U32}
    {cond : rule_eval.rule.Cond} {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.attenuate.add_cond rules index cond = ok (.Ok out)) :
    Narrower (alloc.vec.Vec.deref out) rules := by
  obtain ⟨res, hres, hd⟩ := add_cond_eq rules index cond (add_cond_room h)
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  apply narrower_of_denote
  rw [vec_deref_val]
  exact Chain.RuleSet.addCond_narrower hd.symm

theorem add_cap_narrower {rules : Slice rule_eval.rule.Rule} {index : Std.U32}
    {new_cap : rule_eval.rule.Cap} {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.attenuate.add_cap rules index new_cap = ok (.Ok out)) :
    Narrower (alloc.vec.Vec.deref out) rules := by
  obtain ⟨res, hres, hd⟩ := add_cap_eq rules index new_cap
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  apply narrower_of_denote
  rw [vec_deref_val]
  exact Chain.RuleSet.addCap_narrower hd.symm

theorem lower_cap_limit_narrower {rules : Slice rule_eval.rule.Rule} {index : Std.U32}
    {limit : Std.I128} {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.attenuate.lower_cap_limit rules index limit = ok (.Ok out)) :
    Narrower (alloc.vec.Vec.deref out) rules := by
  obtain ⟨res, hres, hd⟩ := lower_cap_limit_eq rules index limit
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  apply narrower_of_denote
  rw [vec_deref_val]
  exact Chain.RuleSet.lowerCapLimit_narrower hd.symm

theorem lengthen_cap_period_narrower {rules : Slice rule_eval.rule.Rule} {index period : Std.U32}
    {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.attenuate.lengthen_cap_period rules index period = ok (.Ok out)) :
    Narrower (alloc.vec.Vec.deref out) rules := by
  obtain ⟨res, hres, hd⟩ := lengthen_cap_period_eq rules index period
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  apply narrower_of_denote
  rw [vec_deref_val]
  exact Chain.RuleSet.lengthenCapPeriod_narrower hd.symm

/-- One extracted attenuation step from `rs` that returned `Ok`: `Step rs rs'`
when one of the eight steps (`drop_rule`, `add_cond`, `remove_functions`,
`remove_signers`, `raise_threshold`, `add_cap`, `lower_cap_limit` and
`lengthen_cap_period`) on `rs` returned `Ok` of the rules of `rs'`. -/
inductive Step (rs : Slice rule_eval.rule.Rule) : Slice rule_eval.rule.Rule → Prop where
  | dropRule (index : Std.U32) {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.drop_rule rs index = ok (.Ok out) → Step rs (alloc.vec.Vec.deref out)
  | addCond (index : Std.U32) (cond : rule_eval.rule.Cond)
      {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.add_cond rs index cond = ok (.Ok out) →
        Step rs (alloc.vec.Vec.deref out)
  | removeFunctions (index : Std.U32) (functions : Slice (alloc.vec.Vec Std.U8))
      {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.remove_functions rs index functions = ok (.Ok out) →
        Step rs (alloc.vec.Vec.deref out)
  | removeSigners (index : Std.U32) (signers : Slice rule_eval.signer.Signer)
      {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.remove_signers rs index signers = ok (.Ok out) →
        Step rs (alloc.vec.Vec.deref out)
  | raiseThreshold (index threshold : Std.U32) {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.raise_threshold rs index threshold = ok (.Ok out) →
        Step rs (alloc.vec.Vec.deref out)
  | addCap (index : Std.U32) (new_cap : rule_eval.rule.Cap)
      {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.add_cap rs index new_cap = ok (.Ok out) →
        Step rs (alloc.vec.Vec.deref out)
  | lowerCapLimit (index : Std.U32) (limit : Std.I128) {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.lower_cap_limit rs index limit = ok (.Ok out) →
        Step rs (alloc.vec.Vec.deref out)
  | lengthenCapPeriod (index period : Std.U32) {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.lengthen_cap_period rs index period = ok (.Ok out) →
        Step rs (alloc.vec.Vec.deref out)

/-- `Derives root rs`: `rs` is reachable from `root` by zero or more extracted
attenuation steps. -/
inductive Derives (root : Slice rule_eval.rule.Rule) : Slice rule_eval.rule.Rule → Prop where
  | refl : Derives root root
  | step {rs rs' : Slice rule_eval.rule.Rule} : Derives root rs → Step rs rs' → Derives root rs'

theorem Step.narrower {rs rs' : Slice rule_eval.rule.Rule} : Step rs rs' → Narrower rs' rs
  | .dropRule _ h => drop_rule_narrower h
  | .addCond _ _ h => add_cond_narrower h
  | .removeFunctions _ _ h => remove_functions_narrower h
  | .removeSigners _ _ h => remove_signers_narrower h
  | .raiseThreshold _ _ h => raise_threshold_narrower h
  | .addCap _ _ h => add_cap_narrower h
  | .lowerCapLimit _ _ h => lower_cap_limit_narrower h
  | .lengthenCapPeriod _ _ h => lengthen_cap_period_narrower h

/-- Every rule set derived from a root by extracted attenuation steps stays
inside the root. -/
theorem Derives.narrower {root rs : Slice rule_eval.rule.Rule} (h : Derives root rs) :
    Narrower rs root := by
  induction h with
  | refl => exact Narrower.refl root
  | step _ hs ih => exact Narrower.trans hs.narrower ih

/-- A narrower rule set accepts a batch only if its ancestor does. -/
theorem allows_all_of_narrower {rs' rs : Slice rule_eval.rule.Rule} (h : Narrower rs' rs)
    (cs : Slice rule_eval.context.Context) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows_all rs' cs authenticated = ok true →
      rule_eval.rule_set.allows_all rs cs authenticated = ok true := by
  rw [allows_all_eq, allows_all_eq]
  intro hc
  have hc := (Chain.RuleSet.allowsAll_iff _ _ _).mp (Result.ok_injective hc)
  refine congrArg ok ((Chain.RuleSet.allowsAll_iff _ _ _).mpr ?_)
  intro c' hm
  obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hm
  have := h c authenticated (by rw [allows_eq]; exact congrArg ok (hc _ hm))
  rw [allows_eq] at this
  exact Result.ok_injective this

theorem Derives.allows_all {root rs : Slice rule_eval.rule.Rule} (h : Derives root rs)
    (cs : Slice rule_eval.context.Context) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows_all rs cs authenticated = ok true →
      rule_eval.rule_set.allows_all root cs authenticated = ok true :=
  allows_all_of_narrower h.narrower cs authenticated

/-! ## Contract creation -/

/-- No rule set allows a contract creation. -/
theorem allows_create (rules : Slice rule_eval.rule.Rule) (wasmHash : alloc.vec.Vec Std.U8)
    (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows rules (.Create wasmHash) authenticated = ok false := by
  rw [allows_eq]
  simp [denoteContext]

/-- A batch containing a contract creation is denied. -/
theorem allows_all_create (rules : Slice rule_eval.rule.Rule)
    {cs : Slice rule_eval.context.Context} {wasmHash : alloc.vec.Vec Std.U8}
    (h : .Create wasmHash ∈ cs.val) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows_all rules cs authenticated = ok false := by
  rw [allows_all_eq]
  exact congrArg ok (Chain.RuleSet.allowsAll_false_of_create_mem _
    (List.mem_map_of_mem (f := denoteContext) h) _)

/-! ## Signers -/

/-- The extracted `signer_eq` is equality of the Rust signers. -/
theorem signer_eq_iff (a b : rule_eval.signer.Signer) :
    rule_eval.signer.signer_eq a b = ok true ↔ a = b := by
  rw [signer_eq_eq]
  constructor
  · intro h
    exact denoteSigner_injective (of_decide_eq_true (Result.ok_injective h))
  · intro h
    simp [h]

/-- A `Delegated` signer never equals an `External` one, even when the
address is the verifier's or the key's bytes. -/
theorem signer_eq_delegated_external (address verifier key : alloc.vec.Vec Std.U8) :
    rule_eval.signer.signer_eq (.Delegated address) (.External verifier key) = ok false := by
  simp [signer_eq_eq, denoteSigner]

theorem denoteSigners_subset {a a' : Slice rule_eval.signer.Signer}
    (h : ∀ s ∈ a.val, s ∈ a'.val) : denoteSigners a.val ⊆ denoteSigners a'.val := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact List.mem_map_of_mem (h t ht)

theorem denoteSigners_mem_iff {a a' : Slice rule_eval.signer.Signer}
    (h : ∀ s, s ∈ a.val ↔ s ∈ a'.val) (s : Chain.Signer) :
    s ∈ denoteSigners a.val ↔ s ∈ denoteSigners a'.val :=
  ⟨fun hs => denoteSigners_subset (fun t ht => (h t).mp ht) hs,
    fun hs => denoteSigners_subset (fun t ht => (h t).mpr ht) hs⟩

/-- Authenticating more signers never turns an allow into a refusal. -/
theorem allows_of_subset (rules : Slice rule_eval.rule.Rule) (c : rule_eval.context.Context)
    {authenticated authenticated' : Slice rule_eval.signer.Signer}
    (h : ∀ s ∈ authenticated.val, s ∈ authenticated'.val) :
    rule_eval.rule_set.allows rules c authenticated = ok true →
      rule_eval.rule_set.allows rules c authenticated' = ok true := by
  rw [allows_eq, allows_eq]
  intro ha
  exact congrArg ok (Chain.RuleSet.allows_of_subset _ _ (denoteSigners_subset h)
    (Result.ok_injective ha))

theorem allows_all_of_subset (rules : Slice rule_eval.rule.Rule)
    (cs : Slice rule_eval.context.Context)
    {authenticated authenticated' : Slice rule_eval.signer.Signer}
    (h : ∀ s ∈ authenticated.val, s ∈ authenticated'.val) :
    rule_eval.rule_set.allows_all rules cs authenticated = ok true →
      rule_eval.rule_set.allows_all rules cs authenticated' = ok true := by
  rw [allows_all_eq, allows_all_eq]
  intro ha
  exact congrArg ok (Chain.RuleSet.allowsAll_of_subset _ _ (denoteSigners_subset h)
    (Result.ok_injective ha))

/-- The verdict depends only on which signers are authenticated, not on their
order or repeats. -/
theorem allows_congr (rules : Slice rule_eval.rule.Rule) (c : rule_eval.context.Context)
    {authenticated authenticated' : Slice rule_eval.signer.Signer}
    (h : ∀ s, s ∈ authenticated.val ↔ s ∈ authenticated'.val) :
    rule_eval.rule_set.allows rules c authenticated =
      rule_eval.rule_set.allows rules c authenticated' := by
  rw [allows_eq, allows_eq, Chain.RuleSet.allows_congr _ _ (denoteSigners_mem_iff h)]

theorem allows_all_congr (rules : Slice rule_eval.rule.Rule)
    (cs : Slice rule_eval.context.Context)
    {authenticated authenticated' : Slice rule_eval.signer.Signer}
    (h : ∀ s, s ∈ authenticated.val ↔ s ∈ authenticated'.val) :
    rule_eval.rule_set.allows_all rules cs authenticated =
      rule_eval.rule_set.allows_all rules cs authenticated' := by
  rw [allows_all_eq, allows_all_eq, Chain.RuleSet.allowsAll_congr _ _ (denoteSigners_mem_iff h)]

/-- A rule's verdict depends only on which signers it lists, not on their order
or repeats. -/
theorem rule_allows_congr_signers (r : rule_eval.rule.Rule)
    {signers : alloc.vec.Vec rule_eval.signer.Signer}
    (h : ∀ s, s ∈ signers.val ↔ s ∈ r.signers.val) (c : rule_eval.context.Context)
    (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule.rule_allows { r with signers } c authenticated =
      rule_eval.rule.rule_allows r c authenticated := by
  rw [rule_allows_eq, rule_allows_eq]
  congr 1
  exact Chain.Rule.allows_congr_signers (denoteRule r) (ss := denoteSigners signers.val)
    (fun s => by
      simp only [denoteRule, denoteSigners, List.mem_map]
      exact ⟨fun ⟨t, ht, he⟩ => ⟨t, (h t).mp ht, he⟩, fun ⟨t, ht, he⟩ => ⟨t, (h t).mpr ht, he⟩⟩)
    _ _

/-- With threshold 0 a rule's verdict does not depend on the authenticated
signers. -/
theorem rule_allows_threshold_zero {r : rule_eval.rule.Rule} (h : r.threshold.val = 0)
    (c : rule_eval.context.Context) (authenticated authenticated' : Slice rule_eval.signer.Signer) :
    rule_eval.rule.rule_allows r c authenticated = rule_eval.rule.rule_allows r c authenticated' := by
  rw [rule_allows_eq, rule_allows_eq]
  congr 1
  apply Chain.Rule.allows_of_threshold_zero
  apply UInt32.toNat_inj.mp
  simpa [denoteRule] using h

/-- A threshold equal to the number of distinct signers is met exactly when
every signer is authenticated. -/
theorem signers_met_all_iff {signers : Slice rule_eval.signer.Signer} {threshold : Std.U32}
    (h : threshold.val = (denoteSigners signers.val).eraseDups.length)
    (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.signer.signers_met signers threshold authenticated = ok true ↔
      ∀ s ∈ signers.val, s ∈ authenticated.val := by
  let r : RuleCore.Rule Chain.Context Chain.Signer :=
    { scope := fun _ => true, conds := [], signers := denoteSigners signers.val,
      threshold := threshold.val }
  have hall := RuleCore.Rule.signed_iff_of_threshold_eq (r := r) h (denoteSigners authenticated.val)
  rw [signers_met_eq]
  have hsigned : r.signed (denoteSigners authenticated.val) =
      decide (threshold.val ≤ ((denoteSigners signers.val).eraseDups.filter
        (· ∈ denoteSigners authenticated.val)).length) := rfl
  rw [← hsigned]
  constructor
  · intro hok s hs
    have := (hall.mp (Result.ok_injective hok)) (denoteSigner s) (List.mem_map_of_mem hs)
    obtain ⟨t, ht, he⟩ := List.mem_map.mp this
    rw [← denoteSigner_injective he]
    exact ht
  · intro hmem
    refine congrArg ok (hall.mpr fun x hx => ?_)
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map_of_mem (hmem s hs)

/-- A rule whose threshold is above its number of distinct signers allows
nothing. -/
theorem rule_allows_false_of_lt {r : rule_eval.rule.Rule}
    (h : (denoteSigners r.signers.val).eraseDups.length < r.threshold.val)
    (c : rule_eval.context.Context) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule.rule_allows r c authenticated = ok false := by
  rw [rule_allows_eq]
  exact congrArg ok (Chain.Rule.allows_false_of_lt (by simpa [denoteRule] using h) _ _)

/-! ## Arguments -/

/-- The extracted `val_eq` is equality of the Rust values. -/
theorem val_eq_iff (a b : rule_eval.val.Val) :
    rule_eval.val.val_eq a b = ok true ↔ a = b := by
  rw [val_eq_eq]
  constructor
  · intro h
    exact denoteVal_injective (of_decide_eq_true (Result.ok_injective h))
  · intro h
    simp [h]

/-- The extracted `val_eq` holds only for values of the same constructor. -/
theorem val_eq_kind {a b : rule_eval.val.Val} (h : rule_eval.val.val_eq a b = ok true) :
    (denoteVal a).kind = (denoteVal b).kind := by
  rw [(val_eq_iff a b).mp h]

/-- An `Other` value never equals a `Bytes` value, even with the same bytes. -/
theorem val_eq_other_bytes (x y : alloc.vec.Vec Std.U8) :
    rule_eval.val.val_eq (.Other x) (.Bytes y) = ok false := by
  simp [val_eq_eq, denoteVal]

/-- `ArgEq index v` holds exactly when argument `index` exists and is `v`. -/
theorem cond_holds_argEq_iff (index : Std.U32) (v : rule_eval.val.Val)
    (args : Slice rule_eval.val.Val) :
    rule_eval.rule.cond_holds (.ArgEq index v) args = ok true ↔ args.val[index.val]? = some v := by
  rw [cond_holds_eq]
  simp only [denoteCond, Chain.Cond.holds, denoteU32_toNat, List.getElem?_map]
  constructor
  · intro h
    have h := of_decide_eq_true (Result.ok_injective h)
    cases hv : args.val[index.val]? with
    | none => rw [hv] at h; simp at h
    | some w =>
      rw [hv] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [denoteVal_injective h]
  · intro h
    simp [h]

/-- `ArgEq index v` holds only for an argument of `v`'s constructor. -/
theorem cond_holds_argEq_kind {index : Std.U32} {v : rule_eval.val.Val}
    {args : Slice rule_eval.val.Val}
    (h : rule_eval.rule.cond_holds (.ArgEq index v) args = ok true) :
    ∃ w, args.val[index.val]? = some w ∧ (denoteVal w).kind = (denoteVal v).kind :=
  ⟨v, (cond_holds_argEq_iff index v args).mp h, rfl⟩

/-- An argument of another constructor fails `ArgEq`, whatever its payload. -/
theorem cond_holds_argEq_false_of_kind_ne {index : Std.U32} {v w : rule_eval.val.Val}
    {args : Slice rule_eval.val.Val} (hw : args.val[index.val]? = some w)
    (hk : (denoteVal w).kind ≠ (denoteVal v).kind) :
    rule_eval.rule.cond_holds (.ArgEq index v) args = ok false := by
  rw [cond_holds_eq]
  refine congrArg ok ?_
  cases h : (denoteCond (.ArgEq index v)).holds (args.val.map denoteVal)
  · rfl
  · have := (cond_holds_argEq_iff index v args).mp (by rw [cond_holds_eq, h])
    rw [hw] at this
    cases this
    exact absurd rfl hk

/-! ## Byte strings -/

/-- Two byte strings compare equal exactly when they hold the same bytes. -/
theorem bytes_eq_iff (a b : Slice Std.U8) :
    rule_eval.bytes.bytes_eq a b = ok true ↔ a.val = b.val := by
  rw [bytes_eq_eq]
  constructor
  · intro h
    exact of_decide_eq_true (Result.ok_injective h)
  · intro h
    simp [h]

/-- A rule allows only calls to exactly its contract and exactly one of its
functions. -/
theorem rule_allows_call {r : rule_eval.rule.Rule} {contract function : alloc.vec.Vec Std.U8}
    {args : alloc.vec.Vec rule_eval.val.Val} {authenticated : Slice rule_eval.signer.Signer}
    (h : rule_eval.rule.rule_allows r (.Call contract function args) authenticated = ok true) :
    contract = r.contract ∧ function ∈ r.functions.val := by
  rw [rule_allows_eq] at h
  obtain ⟨hc, hf⟩ := Chain.Rule.contract_eq_of_allows (Result.ok_injective h)
  refine ⟨denoteBytes_injective hc, ?_⟩
  obtain ⟨f, hm, he⟩ := List.mem_map.mp hf
  rw [← denoteBytes_injective he]
  exact hm

/-- No prefix match: a call to a proper extension of the rule's contract id is
denied. -/
theorem rule_allows_extension_false (r : rule_eval.rule.Rule)
    {contract function : alloc.vec.Vec Std.U8} {args : alloc.vec.Vec rule_eval.val.Val}
    {ext : List Std.U8} (hc : contract.val = r.contract.val ++ ext) (hne : ext ≠ [])
    (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule.rule_allows r (.Call contract function args) authenticated = ok false := by
  cases h : rule_eval.rule.rule_allows r (.Call contract function args) authenticated with
  | ret b =>
    cases b
    · rfl
    · have he := congrArg (fun v : alloc.vec.Vec Std.U8 => v.val.length) (rule_allows_call h).1
      simp only [hc, List.length_append] at he
      exact absurd (List.length_eq_zero_iff.mp (by omega)) hne
  | vis e k => rw [rule_allows_eq] at h; simp at h
  | div => rw [rule_allows_eq] at h; simp at h

/-- A call to a proper prefix of the rule's contract id is denied. -/
theorem rule_allows_prefix_false (r : rule_eval.rule.Rule)
    {contract function : alloc.vec.Vec Std.U8} {args : alloc.vec.Vec rule_eval.val.Val}
    {ext : List Std.U8} (hc : contract.val ++ ext = r.contract.val) (hne : ext ≠ [])
    (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule.rule_allows r (.Call contract function args) authenticated = ok false := by
  cases h : rule_eval.rule.rule_allows r (.Call contract function args) authenticated with
  | ret b =>
    cases b
    · rfl
    · have he := congrArg (fun v : alloc.vec.Vec Std.U8 => v.val.length) (rule_allows_call h).1
      have hl := congrArg List.length hc
      simp only [List.length_append] at hl he
      exact absurd (List.length_eq_zero_iff.mp (by omega)) hne
  | vis e k => rw [rule_allows_eq] at h; simp at h
  | div => rw [rule_allows_eq] at h; simp at h

end RuleCore.Extracted
