import RuleCore.Equiv.Denote
import RuleCore.Equiv.Loop

/-!
# Evaluation: the extracted evaluator agrees with the model

Each theorem says that an extracted function returns `ok` on every input, so
it neither fails nor diverges, and that the value it returns is the model's on
the denoted inputs:

* `bytes_eq_eq`: `bytes_eq a b` is whether `a` and `b` hold the same bytes;
* `bytes_in_eq`: `bytes_in x list` is whether some element of `list` holds
  the same bytes as `x`;
* `val_eq_eq`: `val_eq a b` is equality of the denoted values;
* `cond_holds_eq`: `cond_holds c args` is `Cond.holds` of the denotations;
* `conds_hold_eq`: `conds_hold conds args` is whether every condition holds;
* `rule_allows_eq`: `rule_allows r c` is `Rule.allows` of the denotations;
* `allows_eq`: `allows rules c` is `RuleSet.allows` of the denotations;
* `allows_all_eq`: `allows_all rules cs` is `RuleSet.allowsAll` of the
  denotations: every context of a Soroban authorization tree.
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std Result ControlFlow

/-! ## The model's verdicts, unfolded -/

theorem chain_rule_allows_call (r : Chain.Rule) (contract function : Bytes)
    (args : List Chain.Val) :
    r.allows (.call contract function args) =
      (decide (contract = r.contract) && decide (function ∈ r.functions) &&
        r.conds.all (·.holds args)) := by
  simp [Chain.Rule.allows, Chain.Rule.denote, RuleCore.Rule.allows, Chain.Rule.scope,
    Chain.Cond.denote, List.all_map, Function.comp_def]

theorem chain_ruleSet_allows (rs : Chain.RuleSet) (c : Chain.Context) :
    rs.allows c = rs.any (·.allows c) := by
  simp only [Chain.RuleSet.allows, Chain.RuleSet.denote, RuleCore.RuleSet.allows,
    RuleCore.RuleSet.ofRules, Chain.Rule.allows]
  rw [List.any_map]
  rfl

theorem chain_ruleSet_allowsAll (rs : Chain.RuleSet) (cs : List Chain.Context) :
    rs.allowsAll cs = cs.all rs.allows := rfl

/-! ## Byte strings -/

/-- Element-wise equality of two lists of the same length is list equality. -/
theorem zip_all_eq {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.length = l₂.length →
      (l₁.zip l₂).all (fun x => decide (x.1 = x.2)) = decide (l₁ = l₂)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zip_cons_cons, List.all_cons, zip_all_eq l₁ l₂ h, List.cons.injEq]
    by_cases hab : a = b <;> simp [hab]

theorem slice_len_bne {α : Type} (a b : Slice α) :
    (Slice.len a != Slice.len b) = !decide (a.length = b.length) := by
  by_cases h : a.length = b.length
  · have : Slice.len a = Slice.len b := by
      apply UScalar.eq_of_val_eq
      simp [h]
    simp [this, h]
  · have : Slice.len a ≠ Slice.len b := by
      intro he
      have := congrArg UScalar.val he
      simp at this
      exact h this
    simp [this, h]

theorem bytes_eq_loop_eq (a b : Slice Std.U8) (hlen : a.length = b.length) (i : Usize) :
    rule_eval.bytes.bytes_eq_loop a b i =
      ok (((a.val.zip b.val).drop i.val).all (fun x => decide (x.1 = x.2))) := by
  simp only [Slice.length] at hlen
  unfold rule_eval.bytes.bytes_eq_loop
  apply loop_all
  · intro i hi
    have hz : i.val < a.val.length ∧ i.val < b.val.length := by
      simpa [List.length_zip] using hi
    have ha : i.val < a.length := hz.1
    have hb : i.val < b.length := hz.2
    obtain ⟨j, hj, hj'⟩ := incr_eq a i ha
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.bytes.bytes_eq_loop.body, slice_len_lt, ha, ↓reduceIte,
      index_usize_eq _ _ ha, index_usize_eq _ _ hb, hj, List.getElem_zip]
    by_cases he : a.val[i.val] = b.val[i.val]
    · simp [he]
    · simp [he]
      exact fun h => he (UScalar.eq_of_val_eq h)
  · intro i hi
    have hz : a.val.length ≤ i.val ∨ b.val.length ≤ i.val := by
      simpa [List.length_zip] using hi
    have ha : ¬ i.val < a.length := by simp only [Slice.length]; omega
    simp [rule_eval.bytes.bytes_eq_loop.body, ha]

/-- Byte strings compare exactly: `bytes_eq` is equality of the byte lists. -/
theorem bytes_eq_eq (a b : Slice Std.U8) :
    rule_eval.bytes.bytes_eq a b = ok (decide (a.val = b.val)) := by
  simp only [rule_eval.bytes.bytes_eq, slice_len_bne]
  by_cases h : a.length = b.length
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have h' : a.val.length = b.val.length := h
    rw [bytes_eq_loop_eq a b h]
    simp [zip_all_eq _ _ h']
  · have hne : a.val ≠ b.val := fun he => h (by simp [Slice.length, he])
    simp [h, hne]

theorem bytes_in_eq (x : Slice Std.U8) (list : Slice (alloc.vec.Vec Std.U8)) :
    rule_eval.bytes.bytes_in x list = ok (list.val.any (fun y => decide (x.val = y.val))) := by
  unfold rule_eval.bytes.bytes_in rule_eval.bytes.bytes_in_loop
  rw [loop_any list.val (fun y => decide (x.val = y.val))]
  · simp
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq list i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.bytes.bytes_in_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, bytes_eq_eq, vec_deref_val, hj]
    by_cases he : x.val = list.val[i.val].val <;> simp [he]
  · intro i hi
    have : ¬ i.val < list.length := by simp only [Slice.length]; omega
    simp [rule_eval.bytes.bytes_in_loop.body, this]

/-- `bytes_in` is membership of the denotation. -/
theorem any_bytes_eq_mem (x : List Std.U8) (list : List (alloc.vec.Vec Std.U8)) :
    list.any (fun y => decide (x = y.val)) = decide (bytesOf x ∈ list.map denoteBytes) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff, List.mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, bytesOf_inj.mpr (of_decide_eq_true he).symm⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, decide_eq_true (bytesOf_inj.mp he).symm⟩

/-! ## Values and conditions -/

theorem val_eq_eq (a b : rule_eval.val.Val) :
    rule_eval.val.val_eq a b = ok (decide (denoteVal a = denoteVal b)) := by
  cases a <;> cases b <;>
    simp [rule_eval.val.val_eq, denoteVal, bytes_eq_eq, denoteBytes_inj, i128_bv_inj,
      denoteU64_inj]

theorem slice_get_eq {α : Type} (s : Slice α) (i : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice α) s i = ok s.val[i.val]? := by
  simp [core.slice.Slice.get]

theorem cond_holds_eq (c : rule_eval.rule.Cond) (args : Slice rule_eval.val.Val) :
    rule_eval.rule.cond_holds c args = ok ((denoteCond c).holds (args.val.map denoteVal)) := by
  cases c with
  | ArgEq index expected =>
    simp only [rule_eval.rule.cond_holds, lift, bind_ok, slice_get_eq, cast_usize_val,
      denoteCond, Chain.Cond.holds, List.getElem?_map, denoteU32_toNat]
    cases args.val[index.val]? with
    | none => simp
    | some v => simp [val_eq_eq]
  | ArgI128AtMost index bound =>
    simp only [rule_eval.rule.cond_holds, lift, bind_ok, slice_get_eq, cast_usize_val,
      denoteCond, Chain.Cond.holds, List.getElem?_map, denoteU32_toNat]
    cases args.val[index.val]? with
    | none => rfl
    | some v => cases v <;> simp [denoteVal]

theorem conds_hold_eq (conds : Slice rule_eval.rule.Cond) (args : Slice rule_eval.val.Val) :
    rule_eval.rule.conds_hold conds args =
      ok (conds.val.all fun c => (denoteCond c).holds (args.val.map denoteVal)) := by
  unfold rule_eval.rule.conds_hold rule_eval.rule.conds_hold_loop
  rw [loop_all conds.val (fun c => (denoteCond c).holds (args.val.map denoteVal))]
  · simp
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq conds i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.rule.conds_hold_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, cond_holds_eq, bind_ok, hj]
    cases (denoteCond conds.val[i.val]).holds (args.val.map denoteVal) <;> simp
  · intro i hi
    have : ¬ i.val < conds.length := by simp only [Slice.length]; omega
    simp [rule_eval.rule.conds_hold_loop.body, this]

/-! ## Rules and rule sets -/

theorem rule_allows_eq (r : rule_eval.rule.Rule) (c : rule_eval.context.Context) :
    rule_eval.rule.rule_allows r c = ok ((denoteRule r).allows (denoteContext c)) := by
  cases c with
  | Create wasmHash => rfl
  | Call contract function args =>
    have hd : ∀ v, denoteBytes v = bytesOf v.val := fun _ => rfl
    simp only [denoteContext, chain_rule_allows_call, denoteRule, rule_eval.rule.rule_allows,
      bytes_eq_eq, vec_deref_val, bind_ok, hd]
    by_cases hc : contract.val = r.contract.val
    · simp only [hc, decide_true, ↓reduceIte, bytes_in_eq, vec_deref_val, bind_ok,
        any_bytes_eq_mem, Bool.true_and]
      cases decide (bytesOf function.val ∈ r.functions.val.map denoteBytes)
      · simp
      · simp [conds_hold_eq, List.all_map, Function.comp_def]
    · have : bytesOf contract.val ≠ bytesOf r.contract.val := fun h => hc (bytesOf_inj.mp h)
      simp [hc, this]

theorem allows_eq (rules : Slice rule_eval.rule.Rule) (c : rule_eval.context.Context) :
    rule_eval.rule_set.allows rules c = ok ((denoteRules rules.val).allows (denoteContext c)) := by
  unfold rule_eval.rule_set.allows rule_eval.rule_set.allows_loop
  rw [loop_any rules.val (fun r => (denoteRule r).allows (denoteContext c))]
  · simp [chain_ruleSet_allows, denoteRules, List.any_map, Function.comp_def]
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.rule_set.allows_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, rule_allows_eq, bind_ok, hj]
    cases (denoteRule rules.val[i.val]).allows (denoteContext c) <;> simp
  · intro i hi
    have : ¬ i.val < rules.length := by simp only [Slice.length]; omega
    simp [rule_eval.rule_set.allows_loop.body, this]

theorem allows_all_eq (rules : Slice rule_eval.rule.Rule)
    (cs : Slice rule_eval.context.Context) :
    rule_eval.rule_set.allows_all rules cs =
      ok ((denoteRules rules.val).allowsAll (cs.val.map denoteContext)) := by
  unfold rule_eval.rule_set.allows_all rule_eval.rule_set.allows_all_loop
  rw [loop_all cs.val (fun c => (denoteRules rules.val).allows (denoteContext c))]
  · simp [chain_ruleSet_allowsAll, List.all_map, Function.comp_def]
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq cs i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.rule_set.allows_all_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, allows_eq, bind_ok, hj]
    cases (denoteRules rules.val).allows (denoteContext cs.val[i.val]) <;> simp
  · intro i hi
    have : ¬ i.val < cs.length := by simp only [Slice.length]; omega
    simp [rule_eval.rule_set.allows_all_loop.body, this]

end RuleCore.Equiv
