import RuleCore.Equiv.Attenuation
import RuleCore.Theorems.Chain

/-!
# Theorems on the extracted evaluator

The chain vocabulary's theorems, carried over to the Lean translation of
`crates/rule-eval` through the equivalence theorems of `RuleCore.Equiv`. Each
is stated on the extracted functions alone: `Narrower` is defined by the
extracted `allows`, and a step is a call of an extracted attenuation function
that returned `Ok`.

Attenuation:

* `drop_rule_narrower`, `add_cond_narrower`, `remove_functions_narrower`,
  `Step.narrower`: each extracted attenuation step yields a narrower rule set.
* `Narrower.refl`, `Narrower.trans`: `Narrower` is a preorder.
* `Derives.narrower`: any chain of extracted steps stays inside its root.
* `allows_all_of_narrower`, `Derives.allows_all`: a narrower rule set accepts
  a batch only if its ancestor does.
* `add_cond_room`: an `add_cond` that returned `Ok` had room for the condition
  (`CondRoom`), so `add_cond_narrower` needs no hypothesis.

Contract creation:

* `allows_create`, `allows_all_create`: no rule set allows a contract creation,
  and a batch containing one is denied.

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
extracted `allows` accepts under `rs'`, it accepts under `rs`. -/
def Narrower (rs' rs : Slice rule_eval.rule.Rule) : Prop :=
  ∀ c, rule_eval.rule_set.allows rs' c = ok true → rule_eval.rule_set.allows rs c = ok true

theorem Narrower.refl (rs : Slice rule_eval.rule.Rule) : Narrower rs rs :=
  fun _ h => h

theorem Narrower.trans {rs'' rs' rs : Slice rule_eval.rule.Rule} :
    Narrower rs'' rs' → Narrower rs' rs → Narrower rs'' rs :=
  fun h₁ h₂ c h => h₂ c (h₁ c h)

/-- The model's `narrower` on the denotations gives `Narrower` on the extracted
evaluator. -/
theorem narrower_of_denote {rs' rs : Slice rule_eval.rule.Rule}
    (h : (denoteRules rs'.val).narrower (denoteRules rs.val)) : Narrower rs' rs := by
  intro c hc
  rw [allows_eq] at hc ⊢
  exact congrArg ok (h _ (Result.ok_injective hc))

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

/-- One extracted attenuation step from `rs` that returned `Ok`: `Step rs rs'`
when one of `drop_rule`, `add_cond` and `remove_functions` on `rs` returned
`Ok` of the rules of `rs'`. -/
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

/-- `Derives root rs`: `rs` is reachable from `root` by zero or more extracted
attenuation steps. -/
inductive Derives (root : Slice rule_eval.rule.Rule) : Slice rule_eval.rule.Rule → Prop where
  | refl : Derives root root
  | step {rs rs' : Slice rule_eval.rule.Rule} : Derives root rs → Step rs rs' → Derives root rs'

theorem Step.narrower {rs rs' : Slice rule_eval.rule.Rule} : Step rs rs' → Narrower rs' rs
  | .dropRule _ h => drop_rule_narrower h
  | .addCond _ _ h => add_cond_narrower h
  | .removeFunctions _ _ h => remove_functions_narrower h

/-- Every rule set derived from a root by extracted attenuation steps stays
inside the root. -/
theorem Derives.narrower {root rs : Slice rule_eval.rule.Rule} (h : Derives root rs) :
    Narrower rs root := by
  induction h with
  | refl => exact Narrower.refl root
  | step _ hs ih => exact Narrower.trans hs.narrower ih

/-- A narrower rule set accepts a batch only if its ancestor does. -/
theorem allows_all_of_narrower {rs' rs : Slice rule_eval.rule.Rule} (h : Narrower rs' rs)
    (cs : Slice rule_eval.context.Context) :
    rule_eval.rule_set.allows_all rs' cs = ok true →
      rule_eval.rule_set.allows_all rs cs = ok true := by
  rw [allows_all_eq, allows_all_eq]
  intro hc
  have hc := (Chain.RuleSet.allowsAll_iff _ _).mp (Result.ok_injective hc)
  refine congrArg ok ((Chain.RuleSet.allowsAll_iff _ _).mpr ?_)
  intro c' hm
  obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hm
  have := h c (by rw [allows_eq]; exact congrArg ok (hc _ hm))
  rw [allows_eq] at this
  exact Result.ok_injective this

theorem Derives.allows_all {root rs : Slice rule_eval.rule.Rule} (h : Derives root rs)
    (cs : Slice rule_eval.context.Context) :
    rule_eval.rule_set.allows_all rs cs = ok true →
      rule_eval.rule_set.allows_all root cs = ok true :=
  allows_all_of_narrower h.narrower cs

/-! ## Contract creation -/

/-- No rule set allows a contract creation. -/
theorem allows_create (rules : Slice rule_eval.rule.Rule) (wasmHash : alloc.vec.Vec Std.U8) :
    rule_eval.rule_set.allows rules (.Create wasmHash) = ok false := by
  rw [allows_eq]
  simp [denoteContext]

/-- A batch containing a contract creation is denied. -/
theorem allows_all_create (rules : Slice rule_eval.rule.Rule)
    {cs : Slice rule_eval.context.Context} {wasmHash : alloc.vec.Vec Std.U8}
    (h : .Create wasmHash ∈ cs.val) :
    rule_eval.rule_set.allows_all rules cs = ok false := by
  rw [allows_all_eq]
  exact congrArg ok (Chain.RuleSet.allowsAll_false_of_create_mem _
    (List.mem_map_of_mem (f := denoteContext) h))

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
    {args : alloc.vec.Vec rule_eval.val.Val}
    (h : rule_eval.rule.rule_allows r (.Call contract function args) = ok true) :
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
    {ext : List Std.U8} (hc : contract.val = r.contract.val ++ ext) (hne : ext ≠ []) :
    rule_eval.rule.rule_allows r (.Call contract function args) = ok false := by
  cases h : rule_eval.rule.rule_allows r (.Call contract function args) with
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
    {ext : List Std.U8} (hc : contract.val ++ ext = r.contract.val) (hne : ext ≠ []) :
    rule_eval.rule.rule_allows r (.Call contract function args) = ok false := by
  cases h : rule_eval.rule.rule_allows r (.Call contract function args) with
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
