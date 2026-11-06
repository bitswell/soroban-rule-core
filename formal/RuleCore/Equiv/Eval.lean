import RuleCore.Equiv.Denote
import RuleCore.Equiv.Loop
import RuleCore.Theorems.AuthRoot

/-!
# Evaluation: the extracted evaluator agrees with the model

Each theorem says that an extracted function returns `ok` on every input, so
it neither fails nor diverges, and that the value it returns is the model's on
the denoted inputs:

* `bytes_eq_eq`: `bytes_eq a b` is whether `a` and `b` hold the same bytes;
* `bytes_in_eq`: `bytes_in x list` is whether some element of `list` holds
  the same bytes as `x`;
* `bytes_starts_with_eq`: `bytes_starts_with s prefix` is whether the bytes of
  `prefix` are a prefix of those of `s`;
* `val_eq_eq`: `val_eq a b` is equality of the denoted values;
* `val_in_eq`: `val_in x list` is membership of the denotation;
* `functions_match_eq`: `functions_match functions function` is membership of
  the function in the denoted functions;
* `cond_holds_eq`: `cond_holds c args` is `Cond.holds` of the denotations;
* `conds_hold_eq`: `conds_hold conds args` is whether every condition holds;
* `signer_eq_eq`: `signer_eq a b` is equality of the denoted signers;
* `signer_in_eq`, `signer_in_first_eq`: `signer_in x list` is membership of
  the denotation, and `signer_in_first x list before` membership in the
  denotation's first `before` signers;
* `signed_count_eq`: `signed_count signers authenticated` is the number of
  distinct denoted signers that are authenticated;
* `signers_met_eq`: `signers_met signers threshold authenticated` is the
  model's signer requirement;
* `rule_allows_eq`: `rule_allows r c authenticated` is `Rule.allows` of the
  denotations;
* `allows_eq`: `allows rules c authenticated` is `RuleSet.allows` of the
  denotations;
* `allows_all_eq`: `allows_all rules cs authenticated` is `RuleSet.allowsAll`
  of the denotations: every context of a Soroban authorization tree, under the
  signers that authenticated it.
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std Result ControlFlow

/-! ## The model's verdicts, unfolded -/

theorem chain_rule_allows_call (r : Chain.Rule) (contract function : Bytes)
    (args : List Chain.Val) (auth : List Chain.Signer) :
    r.allows (.call contract function args) auth =
      (decide (contract = r.contract) && decide (function ∈ r.functions) &&
        r.conds.all (·.holds args) &&
        decide (r.threshold.toNat ≤ (r.signers.eraseDups.filter (· ∈ auth)).length)) := by
  simp [Chain.Rule.allows, Chain.Rule.denote, RuleCore.Rule.allows, Chain.Rule.scope,
    Chain.Cond.denote, List.all_map, Function.comp_def, RuleCore.Rule.signed,
    RuleCore.Rule.present]
  rfl

theorem chain_ruleSet_allows (rs : Chain.RuleSet) (c : Chain.Context) (auth : List Chain.Signer) :
    rs.allows c auth = rs.any (·.allows c auth) := by
  simp only [Chain.RuleSet.allows, Chain.RuleSet.denote, RuleCore.RuleSet.allows,
    RuleCore.RuleSet.ofRules, Chain.Rule.allows]
  rw [List.any_map]
  rfl

theorem chain_ruleSet_allowsAll (rs : Chain.RuleSet) (cs : List Chain.Context)
    (auth : List Chain.Signer) : rs.allowsAll cs auth = cs.all (rs.allows · auth) := rfl

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

theorem slice_get_eq {α : Type} (s : Slice α) (i : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice α) s i = ok s.val[i.val]? := by
  simp [core.slice.Slice.get]

/-- Prefixes compare exactly: `bytes_starts_with s prefix` is whether the bytes
of `prefix` are the first bytes of `s`. -/
theorem bytes_starts_with_eq (s pre : Slice Std.U8) :
    rule_eval.bytes.bytes_starts_with s pre = ok (decide (bytesOf pre.val <+: bytesOf s.val)) := by
  unfold rule_eval.bytes.bytes_starts_with rule_eval.bytes.bytes_starts_with_loop
  rw [loop_all (List.range pre.val.length) (fun k => decide (s.val[k]? = pre.val[k]?))]
  · have h0 : (0#usize).val = 0 := by simp
    rw [h0, List.drop_zero]
    congr 1
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
    simp only [bytesOf]
    rw [List.prefix_map_iff_of_injective byte_injective, List.prefix_iff_getElem?]
    simp only [List.mem_range, decide_eq_true_eq]
    constructor
    · intro h i hi
      rw [h i hi, List.getElem?_eq_getElem hi]
    · intro h i hi
      rw [h i hi, List.getElem?_eq_getElem hi]
  · intro i hi
    have hi' : i.val < pre.length := by simpa [Slice.length] using hi
    obtain ⟨j, hj, hj'⟩ := incr_eq pre i hi'
    refine ⟨j, hj', ?_⟩
    have hp : pre.val[i.val]? = some pre.val[i.val] := List.getElem?_eq_getElem hi'
    simp only [List.getElem_range]
    cases hs : s.val[i.val]? with
    | none =>
      simp [rule_eval.bytes.bytes_starts_with_loop.body, hi', slice_get_eq, hs]
    | some x =>
      by_cases he : x = pre.val[i.val]
      · simp [rule_eval.bytes.bytes_starts_with_loop.body, hi', slice_get_eq, hs,
          index_usize_eq _ _ hi', he, hj]
      · have hne : (x != pre.val[i.val]) = true := bne_iff_ne.mpr he
        simp only [rule_eval.bytes.bytes_starts_with_loop.body, slice_len_lt, hi', ↓reduceIte,
          slice_get_eq, hs, index_usize_eq _ _ hi', bind_ok, hne, hp, Option.some.injEq, he,
          decide_false, Bool.false_eq_true]
  · intro i hi
    have : ¬ i.val < pre.length := by simp only [Slice.length]; simpa using hi
    simp [rule_eval.bytes.bytes_starts_with_loop.body, this]

/-! ## Values and conditions -/

theorem val_eq_eq (a b : rule_eval.val.Val) :
    rule_eval.val.val_eq a b = ok (decide (denoteVal a = denoteVal b)) := by
  cases a <;> cases b <;>
    simp [rule_eval.val.val_eq, denoteVal, bytes_eq_eq, denoteBytes_inj, i128_bv_inj,
      denoteU64_inj]

/-- `val_eq` with one side fixed is membership of the denotation. -/
theorem any_val_eq_mem (x : rule_eval.val.Val) (list : List rule_eval.val.Val) :
    list.any (fun y => decide (denoteVal x = denoteVal y)) =
      decide (denoteVal x ∈ list.map denoteVal) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff, List.mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, (of_decide_eq_true he).symm⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, decide_eq_true he.symm⟩

theorem val_in_eq (x : rule_eval.val.Val) (list : Slice rule_eval.val.Val) :
    rule_eval.val.val_in x list = ok (decide (denoteVal x ∈ list.val.map denoteVal)) := by
  unfold rule_eval.val.val_in rule_eval.val.val_in_loop
  rw [loop_any list.val (fun y => decide (denoteVal x = denoteVal y))]
  · simp [any_val_eq_mem]
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq list i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.val.val_in_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, val_eq_eq, bind_ok, hj]
    cases decide (denoteVal x = denoteVal list.val[i.val]) <;> simp
  · intro i hi
    have : ¬ i.val < list.length := by simp only [Slice.length]; omega
    simp [rule_eval.val.val_in_loop.body, this]

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
  | ArgIn index values =>
    simp only [rule_eval.rule.cond_holds, lift, bind_ok, slice_get_eq, cast_usize_val,
      denoteCond, Chain.Cond.holds, List.getElem?_map, denoteU32_toNat]
    cases args.val[index.val]? with
    | none => rfl
    | some v => simp [val_in_eq]
  | ArgStrPrefix index pre =>
    simp only [rule_eval.rule.cond_holds, lift, bind_ok, slice_get_eq, cast_usize_val,
      denoteCond, Chain.Cond.holds, List.getElem?_map, denoteU32_toNat]
    cases args.val[index.val]? with
    | none => rfl
    | some v =>
      cases v <;> simp [denoteVal, bytes_starts_with_eq, denoteBytes]
      exact decide_eq_decide.mpr Iff.rfl

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

/-! ## Signers -/

theorem signer_eq_eq (a b : rule_eval.signer.Signer) :
    rule_eval.signer.signer_eq a b = ok (decide (denoteSigner a = denoteSigner b)) := by
  cases a with
  | Delegated x =>
    cases b <;> simp [rule_eval.signer.signer_eq, denoteSigner, bytes_eq_eq, denoteBytes_inj]
  | External v k =>
    cases b with
    | Delegated y => simp [rule_eval.signer.signer_eq, denoteSigner]
    | External w l =>
      simp only [rule_eval.signer.signer_eq, bytes_eq_eq, vec_deref_val, bind_ok, denoteSigner,
        Chain.Signer.external.injEq]
      by_cases hv : v.val = w.val
      · simp [hv, denoteBytes_inj]
      · have : denoteBytes v ≠ denoteBytes w := fun h => hv (denoteBytes_inj.mp h)
        simp [hv, this]

/-- `signer_eq` with one side fixed is membership of the denotation. -/
theorem any_signer_eq_mem (x : rule_eval.signer.Signer) (list : List rule_eval.signer.Signer) :
    list.any (fun y => decide (denoteSigner x = denoteSigner y)) =
      decide (denoteSigner x ∈ denoteSigners list) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff, denoteSigners, List.mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, (of_decide_eq_true he).symm⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, decide_eq_true he.symm⟩

theorem signer_in_eq (x : rule_eval.signer.Signer) (list : Slice rule_eval.signer.Signer) :
    rule_eval.signer.signer_in x list = ok (decide (denoteSigner x ∈ denoteSigners list.val)) := by
  unfold rule_eval.signer.signer_in rule_eval.signer.signer_in_loop
  rw [loop_any list.val (fun y => decide (denoteSigner x = denoteSigner y))]
  · simp [any_signer_eq_mem]
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq list i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.signer.signer_in_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, signer_eq_eq, bind_ok, hj]
    cases decide (denoteSigner x = denoteSigner list.val[i.val]) <;> simp
  · intro i hi
    have : ¬ i.val < list.length := by simp only [Slice.length]; omega
    simp [rule_eval.signer.signer_in_loop.body, this]

theorem signer_in_first_eq (x : rule_eval.signer.Signer) (list : Slice rule_eval.signer.Signer)
    (before : Usize) :
    rule_eval.signer.signer_in_first x list before =
      ok (decide (denoteSigner x ∈ (denoteSigners list.val).take before.val)) := by
  unfold rule_eval.signer.signer_in_first rule_eval.signer.signer_in_first_loop
  rw [loop_any (list.val.take before.val) (fun y => decide (denoteSigner x = denoteSigner y))]
  · simp [any_signer_eq_mem, denoteSigners, List.map_take]
    rfl
  · intro i hi
    simp only [List.length_take] at hi
    have hi' : i.val < list.length := by simp only [Slice.length]; omega
    have hb : ¬ before ≤ i := by
      rw [UScalar.le_equiv]
      omega
    obtain ⟨j, hj, hj'⟩ := incr_eq list i hi'
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.signer.signer_in_first_loop.body, slice_len_lt, hi', ↓reduceIte,
      ge_iff_le, hb, index_usize_eq _ _ hi', signer_eq_eq, bind_ok, hj, List.getElem_take]
    cases decide (denoteSigner x = denoteSigner list.val[i.val]) <;> simp
  · intro i hi
    by_cases hl : i.val < list.length
    · have hb : before ≤ i := by
        rw [UScalar.le_equiv]
        simp only [List.length_take] at hi
        simp only [Slice.length] at hl
        omega
      simp [rule_eval.signer.signer_in_first_loop.body, hl, hb]
    · simp [rule_eval.signer.signer_in_first_loop.body, hl]

/-- Whether the signer at position `k` of `list` is counted: it is not among
the signers before it, and it is authenticated. -/
def countedAt (list authenticated : List rule_eval.signer.Signer) (k : Nat)
    (s : rule_eval.signer.Signer) : Bool :=
  !decide (denoteSigner s ∈ (denoteSigners list).take k) &&
    decide (denoteSigner s ∈ denoteSigners authenticated)

theorem signed_count_loop_eq (signers authenticated : Slice rule_eval.signer.Signer)
    (n i : Usize) (hn : n.val ≤ i.val) :
    ∃ n', rule_eval.signer.signed_count_loop signers authenticated n i = ok n' ∧
      n'.val = n.val + countFrom (countedAt signers.val authenticated.val)
        (signers.val.drop i.val) i.val := by
  unfold rule_eval.signer.signed_count_loop
  refine loop_count signers.val _ _ ?_ ?_ n i hn
  · intro n i hi hn
    obtain ⟨j, hj, hj'⟩ := incr_eq signers i hi
    by_cases hf : denoteSigner signers.val[i.val] ∈ (denoteSigners signers.val).take i.val
    · refine ⟨n, j, hj', by simp [countedAt, hf], ?_⟩
      simp [rule_eval.signer.signed_count_loop.body, hi, index_usize_eq _ _ hi,
        signer_in_first_eq, hf, hj]
    · by_cases ha : denoteSigner signers.val[i.val] ∈ denoteSigners authenticated.val
      · obtain ⟨m, hm, hm'⟩ := incr_eq_of_le signers n i hi hn
        refine ⟨m, j, hj', by simp [countedAt, hf, ha, hm'], ?_⟩
        simp [rule_eval.signer.signed_count_loop.body, hi, index_usize_eq _ _ hi,
          signer_in_first_eq, hf, signer_in_eq, ha, hm, hj]
      · refine ⟨n, j, hj', by simp [countedAt, hf, ha], ?_⟩
        simp [rule_eval.signer.signed_count_loop.body, hi, index_usize_eq _ _ hi,
          signer_in_first_eq, hf, signer_in_eq, ha, hj]
  · intro n i hi
    have : ¬ i.val < signers.length := by simp only [Slice.length]; omega
    simp [rule_eval.signer.signed_count_loop.body, this]

/-- `signed_count` is the number of distinct denoted signers that are
authenticated. -/
theorem signed_count_eq (signers authenticated : Slice rule_eval.signer.Signer) :
    ∃ n, rule_eval.signer.signed_count signers authenticated = ok n ∧
      n.val = ((denoteSigners signers.val).eraseDups.filter
        (· ∈ denoteSigners authenticated.val)).length := by
  obtain ⟨n, h, hv⟩ := signed_count_loop_eq signers authenticated 0#usize 0#usize (by simp)
  refine ⟨n, h, ?_⟩
  have h0 : (0#usize).val = 0 := by simp
  rw [hv, ← countFrom_first, h0, Nat.zero_add, List.drop_zero, denoteSigners, countFrom_map]
  rfl

theorem signers_met_eq (signers : Slice rule_eval.signer.Signer) (threshold : Std.U32)
    (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.signer.signers_met signers threshold authenticated =
      ok (decide (threshold.val ≤ ((denoteSigners signers.val).eraseDups.filter
        (· ∈ denoteSigners authenticated.val)).length)) := by
  obtain ⟨n, h, hv⟩ := signed_count_eq signers authenticated
  simp only [rule_eval.signer.signers_met, lift, bind_ok, h]
  congr 1
  rw [← hv]
  simp

/-! ## Rules and rule sets -/

theorem functions_match_eq (fs : rule_eval.rule.Functions) (function : Slice Std.U8) :
    rule_eval.rule.functions_match fs function =
      ok (decide (bytesOf function.val ∈ denoteFunctions fs)) := by
  cases fs <;> simp [rule_eval.rule.functions_match, bytes_in_eq, any_bytes_eq_mem, denoteFunctions]

theorem rule_allows_eq (r : rule_eval.rule.Rule) (c : rule_eval.context.Context)
    (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule.rule_allows r c authenticated =
      ok ((denoteRule r).allows (denoteContext c) (denoteSigners authenticated.val)) := by
  cases c with
  | Create wasmHash => rfl
  | Call contract function args =>
    have hd : ∀ v, denoteBytes v = bytesOf v.val := fun _ => rfl
    simp only [denoteContext, chain_rule_allows_call, denoteRule, rule_eval.rule.rule_allows,
      bytes_eq_eq, vec_deref_val, bind_ok, hd]
    by_cases hc : contract.val = r.contract.val
    · simp only [hc, decide_true, ↓reduceIte, Bool.true_and]
      by_cases hf : bytesOf function.val ∈ denoteFunctions r.functions
      · have hfm : rule_eval.rule.functions_match r.functions (alloc.vec.Vec.deref function) =
            ok true := by
          rw [functions_match_eq, vec_deref_val]
          simpa using hf
        simp only [hfm, bind_ok, ↓reduceIte, hf, decide_true, Bool.true_and, conds_hold_eq,
          List.all_map, Function.comp_def]
        by_cases hconds : ∀ x ∈ r.conds.val, (denoteCond x).holds (args.val.map denoteVal) = true
        · have hall : (r.conds.val.all fun c => (denoteCond c).holds (args.val.map denoteVal)) =
              true := List.all_eq_true.mpr hconds
          simp only [vec_deref_val, hall, ↓reduceIte, signers_met_eq, denoteU32_toNat]
          rfl
        · have hall : (r.conds.val.all fun c => (denoteCond c).holds (args.val.map denoteVal)) =
              false := by simpa using hconds
          simp [hall]
      · have hfm : rule_eval.rule.functions_match r.functions (alloc.vec.Vec.deref function) =
            ok false := by
          rw [functions_match_eq, vec_deref_val]
          simpa using hf
        simp [hfm, hf]
    · have : bytesOf contract.val ≠ bytesOf r.contract.val := fun h => hc (bytesOf_inj.mp h)
      simp [hc, this]

theorem auth_root_matches_eq (requirement : Option rule_eval.rule.AuthRoot)
    (root : Option rule_eval.context.Context) :
    rule_eval.rule.auth_root_matches requirement root =
      ok (Chain.AuthRoot.matchesOpt (requirement.map denoteAuthRoot) (root.map denoteContext)) := by
  cases requirement with
  | none => simp [rule_eval.rule.auth_root_matches, Chain.AuthRoot.matchesOpt]
  | some r =>
    cases root with
    | none => simp [rule_eval.rule.auth_root_matches, Chain.AuthRoot.matchesOpt]
    | some c =>
      cases c with
      | Create w => rfl
      | Call contract function args =>
        simp only [rule_eval.rule.auth_root_matches, bytes_eq_eq, vec_deref_val, bind_ok,
          Option.map_some, denoteContext, denoteAuthRoot, Chain.AuthRoot.matchesOpt,
          Chain.AuthRoot.matches]
        by_cases hc : contract.val = r.contract.val <;>
          simp [hc, denoteBytes, bytesOf_inj]

theorem auth_root_narrows_eq (child parent : Option rule_eval.rule.AuthRoot) :
    rule_eval.rule.auth_root_narrows child parent =
      ok (Chain.AuthRoot.narrows (child.map denoteAuthRoot) (parent.map denoteAuthRoot)) := by
  cases parent with
  | none => rfl
  | some p =>
    cases child with
    | none => rfl
    | some c =>
      simp only [rule_eval.rule.auth_root_narrows, bytes_eq_eq, vec_deref_val, bind_ok,
        Option.map_some, denoteAuthRoot, Chain.AuthRoot.narrows]
      by_cases hc : c.contract.val = p.contract.val <;>
        simp [hc, denoteBytes, bytesOf_inj]

theorem rule_allows_in_eq (r : rule_eval.rule.Rule) (root : Option rule_eval.context.Context)
    (c : rule_eval.context.Context) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule.rule_allows_in r root c authenticated =
      ok ((denoteRule r).allowsIn (root.map denoteContext) (denoteContext c)
        (denoteSigners authenticated.val)) := by
  simp only [rule_eval.rule.rule_allows_in, auth_root_matches_eq, bind_ok,
    Chain.Rule.allowsIn, RuleCore.Rule.allowsIn, Chain.Rule.rootMatches_eq]
  change (if Chain.AuthRoot.matchesOpt (r.auth_root.map denoteAuthRoot) (root.map denoteContext)
    then rule_eval.rule.rule_allows r c authenticated else ok false) =
    ok (Chain.AuthRoot.matchesOpt (r.auth_root.map denoteAuthRoot) (root.map denoteContext) &&
      (denoteRule r).allows (denoteContext c) (denoteSigners authenticated.val))
  cases Chain.AuthRoot.matchesOpt (r.auth_root.map denoteAuthRoot) (root.map denoteContext) <;>
    simp [rule_allows_eq]

theorem allows_eq (rules : Slice rule_eval.rule.Rule) (c : rule_eval.context.Context)
    (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows rules c authenticated =
      ok ((denoteRules rules.val).allows (denoteContext c) (denoteSigners authenticated.val)) := by
  unfold rule_eval.rule_set.allows rule_eval.rule_set.allows_loop
  rw [loop_any rules.val
    (fun r => (denoteRule r).allows (denoteContext c) (denoteSigners authenticated.val))]
  · simp [chain_ruleSet_allows, denoteRules, List.any_map, Function.comp_def]
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.rule_set.allows_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, rule_allows_eq, bind_ok, hj]
    cases (denoteRule rules.val[i.val]).allows (denoteContext c) (denoteSigners authenticated.val) <;>
      simp
  · intro i hi
    have : ¬ i.val < rules.length := by simp only [Slice.length]; omega
    simp [rule_eval.rule_set.allows_loop.body, this]

theorem allows_all_eq (rules : Slice rule_eval.rule.Rule)
    (cs : Slice rule_eval.context.Context) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows_all rules cs authenticated =
      ok ((denoteRules rules.val).allowsAll (cs.val.map denoteContext)
        (denoteSigners authenticated.val)) := by
  unfold rule_eval.rule_set.allows_all rule_eval.rule_set.allows_all_loop
  rw [loop_all cs.val
    (fun c => (denoteRules rules.val).allows (denoteContext c) (denoteSigners authenticated.val))]
  · simp [chain_ruleSet_allowsAll, List.all_map, Function.comp_def]
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq cs i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.rule_set.allows_all_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, allows_eq, bind_ok, hj]
    cases (denoteRules rules.val).allows (denoteContext cs.val[i.val])
      (denoteSigners authenticated.val) <;> simp
  · intro i hi
    have : ¬ i.val < cs.length := by simp only [Slice.length]; omega
    simp [rule_eval.rule_set.allows_all_loop.body, this]

/-- The batch root getter is total and reads only index zero of this entry. -/
theorem entry_root_eq (contexts : Slice rule_eval.context.Context) :
    rule_eval.context.entry_root contexts = ok contexts.val.head? := by
  simp [rule_eval.context.entry_root, slice_get_eq]
  cases contexts.val <;> rfl

theorem allows_in_eq (rules : Slice rule_eval.rule.Rule) (root : Option rule_eval.context.Context)
    (c : rule_eval.context.Context) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows_in rules root c authenticated =
      ok ((denoteRules rules.val).allowsIn (root.map denoteContext) (denoteContext c)
        (denoteSigners authenticated.val)) := by
  unfold rule_eval.rule_set.allows_in rule_eval.rule_set.allows_in_loop
  rw [loop_any rules.val
    (fun r => (denoteRule r).allowsIn (root.map denoteContext) (denoteContext c)
      (denoteSigners authenticated.val))]
  · simp [Chain.RuleSet.allowsIn, RuleCore.RuleSet.allowsIn, Chain.RuleSet.denote, RuleCore.RuleSet.ofRules, denoteRules,
      List.any_map, Function.comp_def, Chain.Rule.allowsIn]
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.rule_set.allows_in_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, rule_allows_in_eq, bind_ok, hj]
    cases (denoteRule rules.val[i.val]).allowsIn (root.map denoteContext) (denoteContext c)
      (denoteSigners authenticated.val) <;> simp
  · intro i hi
    have : ¬ i.val < rules.length := by simp only [Slice.length]; omega
    simp [rule_eval.rule_set.allows_in_loop.body, this]

theorem allows_batch_eq (rules : Slice rule_eval.rule.Rule)
    (cs : Slice rule_eval.context.Context) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows_batch rules cs authenticated =
      ok ((denoteRules rules.val).allowsBatch (cs.val.map denoteContext)
        (denoteSigners authenticated.val)) := by
  unfold rule_eval.rule_set.allows_batch rule_eval.rule_set.allows_batch_loop
  rw [loop_all cs.val
    (fun c => (denoteRules rules.val).allowsIn ((cs.val.map denoteContext).head?)
      (denoteContext c) (denoteSigners authenticated.val))]
  · simp [Chain.RuleSet.allowsBatch, RuleCore.RuleSet.allowsBatch, Chain.RuleSet.allowsIn,
      List.all_map, Function.comp_def]
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq cs i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.rule_set.allows_batch_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, entry_root_eq, allows_in_eq, bind_ok, hj, List.head?_map]
    cases (denoteRules rules.val).allowsIn (cs.val.head?.map denoteContext)
      (denoteContext cs.val[i.val]) (denoteSigners authenticated.val) <;> simp
  · intro i hi
    have : ¬ i.val < cs.length := by simp only [Slice.length]; omega
    simp [rule_eval.rule_set.allows_batch_loop.body, this]

end RuleCore.Equiv
