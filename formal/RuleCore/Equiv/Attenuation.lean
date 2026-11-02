import RuleCore.Equiv.Eval

/-!
# Attenuation: the extracted steps agree with the model

The extracted copies return their input: a fresh Rust copy is the same Lean
value (`bytes_copy_deref`, `val_copy_eq`, `cond_copy_eq`, `conds_copy_deref`,
`bytes_list_copy_deref`, `signer_copy_eq`, `signers_copy_deref`,
`rule_copy_eq`). So each extracted attenuation step builds exactly the model's
list of rules:

* `drop_rule_eq`: `drop_rule rules index` returns `ok` of an outcome whose
  denotation is `RuleSet.dropRule` of the denotations;
* `remove_functions_eq`, `remove_signers_eq`, `raise_threshold_eq`: likewise
  for `RuleSet.removeFunctions`, `RuleSet.removeSigners` and
  `RuleSet.raiseThreshold`, `thresholdLowered` included;
* `add_cond_eq`: likewise for `RuleSet.addCond`, under `CondRoom`.

`add_cond` is the one step whose `Vec::push` is not bounded by a slice it
walks: it appends to the condition vector of the rule at `index`. Aeneas's
model of `Vec` holds at most `Usize.max` elements, so the step needs the rule
stated as `CondRoom rules index`: the rule at `index`, if there is one, holds
fewer than `Usize.max` conditions. `add_cond_full` shows the rule is exact: on a
rule already holding `Usize.max` conditions, the extracted step fails.

`drop_rule_ok`, `drop_rule_err`, `add_cond_ok`, `add_cond_err`,
`remove_functions_ok`, `remove_functions_err`, `remove_signers_ok`,
`remove_signers_err`, `raise_threshold_ok`, `raise_threshold_err` and
`raise_threshold_lowered` state the same results without the denotation: the
vector each step returns, and when it returns `NoSuchRule` or
`ThresholdLowered`.
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std Result ControlFlow

@[simp] theorem slice_len_le {α : Type} (s : Slice α) (i : Usize) :
    (Slice.len s ≤ i) = (s.length ≤ i.val) := by
  apply propext
  show (Slice.len s).val ≤ i.val ↔ _
  rw [Slice.len_val]

/-- Two vectors with the same elements are the same vector: Aeneas's `Vec` is
determined by its list of elements. -/
theorem vec_eq_of_val {α : Type} {v w : alloc.vec.Vec α} (h : v.val = w.val) : v = w :=
  alloc.vec.Vec.ext _ _ h

theorem vec_mk_deref {α : Type} (v : alloc.vec.Vec α) : v = ⟨alloc.vec.Vec.deref v⟩ :=
  vec_eq_of_val (by simp [alloc.vec.Vec.val])

theorem usize_val_eq_iff {i j : Usize} : i.val = j.val ↔ i = j :=
  ⟨UScalar.eq_of_val_eq, fun h => h ▸ rfl⟩

/-- A slice holds fewer than `Usize.max` elements below any of its positions:
pushing onto a vector holding at most `i` elements, with `i` a position of the
slice, succeeds. -/
theorem room_of_lt {α β : Type} (s : Slice α) (out : alloc.vec.Vec β) (i : Usize)
    (hi : i.val < s.length) (hout : out.val.length ≤ i.val) : out.val.length < Usize.max := by
  have := s.property
  simp only [Slice.length] at hi
  omega

/-! ## Copies -/

theorem bytes_copy_loop_eq (s : Slice Std.U8) (out : alloc.vec.Vec Std.U8) (i : Usize)
    (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.bytes.bytes_copy_loop s out i = ok out' ∧
      out'.val.map id = out.val.map id ++
        pushedFrom (fun _ a => some (id a)) (s.val.drop i.val) i.val := by
  unfold rule_eval.bytes.bytes_copy_loop
  refine loop_build s.val (fun _ a => some (id a)) id _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨out', hp, hv⟩ := push_eq out s.val[i.val] (room_of_lt s out i hi hout)
    obtain ⟨j, hj, hj'⟩ := incr_eq s i hi
    refine ⟨out', j, hj', by simp [hv], ?_⟩
    simp [rule_eval.bytes.bytes_copy_loop.body, hi, index_usize_eq _ _ hi, hp, hj]
  · intro out i hi
    have : ¬ i.val < s.length := by simp only [Slice.length]; omega
    simp [rule_eval.bytes.bytes_copy_loop.body, this]

/-- `bytes_copy` returns a vector of the same bytes. -/
theorem bytes_copy_eq (s : Slice Std.U8) :
    rule_eval.bytes.bytes_copy s = ok ⟨s⟩ := by
  obtain ⟨out, h, hv⟩ := bytes_copy_loop_eq s (alloc.vec.Vec.new Std.U8) 0#usize (by simp)
  rw [rule_eval.bytes.bytes_copy, h]
  congr 1
  exact vec_eq_of_val (show out.val = s.val by simpa [pushedFrom_map] using hv)

theorem bytes_copy_deref (v : alloc.vec.Vec Std.U8) :
    rule_eval.bytes.bytes_copy (alloc.vec.Vec.deref v) = ok v := by
  rw [bytes_copy_eq, ← vec_mk_deref]

theorem val_copy_eq (v : rule_eval.val.Val) : rule_eval.val.val_copy v = ok v := by
  cases v <;> simp [rule_eval.val.val_copy, bytes_copy_deref]

theorem cond_copy_eq (c : rule_eval.rule.Cond) : rule_eval.rule.cond_copy c = ok c := by
  cases c <;> simp [rule_eval.rule.cond_copy, val_copy_eq]

theorem conds_copy_loop_eq (s : Slice rule_eval.rule.Cond) (out : alloc.vec.Vec rule_eval.rule.Cond)
    (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.rule.conds_copy_loop s out i = ok out' ∧
      out'.val.map id = out.val.map id ++
        pushedFrom (fun _ a => some (id a)) (s.val.drop i.val) i.val := by
  unfold rule_eval.rule.conds_copy_loop
  refine loop_build s.val (fun _ a => some (id a)) id _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨out', hp, hv⟩ := push_eq out s.val[i.val] (room_of_lt s out i hi hout)
    obtain ⟨j, hj, hj'⟩ := incr_eq s i hi
    refine ⟨out', j, hj', by simp [hv], ?_⟩
    simp [rule_eval.rule.conds_copy_loop.body, hi, index_usize_eq _ _ hi, cond_copy_eq, hp, hj]
  · intro out i hi
    have : ¬ i.val < s.length := by simp only [Slice.length]; omega
    simp [rule_eval.rule.conds_copy_loop.body, this]

theorem conds_copy_deref (v : alloc.vec.Vec rule_eval.rule.Cond) :
    rule_eval.rule.conds_copy (alloc.vec.Vec.deref v) = ok v := by
  obtain ⟨out, h, hv⟩ := conds_copy_loop_eq (alloc.vec.Vec.deref v)
    (alloc.vec.Vec.new rule_eval.rule.Cond) 0#usize (by simp)
  rw [rule_eval.rule.conds_copy, h]
  congr 1
  exact vec_eq_of_val (by simpa [pushedFrom_map] using hv)

theorem bytes_list_copy_loop_eq (s : Slice (alloc.vec.Vec Std.U8))
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.bytes.bytes_list_copy_loop s out i = ok out' ∧
      out'.val.map id = out.val.map id ++
        pushedFrom (fun _ a => some (id a)) (s.val.drop i.val) i.val := by
  unfold rule_eval.bytes.bytes_list_copy_loop
  refine loop_build s.val (fun _ a => some (id a)) id _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨out', hp, hv⟩ := push_eq out s.val[i.val] (room_of_lt s out i hi hout)
    obtain ⟨j, hj, hj'⟩ := incr_eq s i hi
    refine ⟨out', j, hj', by simp [hv], ?_⟩
    simp [rule_eval.bytes.bytes_list_copy_loop.body, hi, index_usize_eq _ _ hi,
      bytes_copy_deref, hp, hj]
  · intro out i hi
    have : ¬ i.val < s.length := by simp only [Slice.length]; omega
    simp [rule_eval.bytes.bytes_list_copy_loop.body, this]

theorem bytes_list_copy_deref (v : alloc.vec.Vec (alloc.vec.Vec Std.U8)) :
    rule_eval.bytes.bytes_list_copy (alloc.vec.Vec.deref v) = ok v := by
  obtain ⟨out, h, hv⟩ := bytes_list_copy_loop_eq (alloc.vec.Vec.deref v)
    (alloc.vec.Vec.new (alloc.vec.Vec Std.U8)) 0#usize (by simp)
  rw [rule_eval.bytes.bytes_list_copy, h]
  congr 1
  exact vec_eq_of_val (by simpa [pushedFrom_map] using hv)

theorem signer_copy_eq (s : rule_eval.signer.Signer) : rule_eval.signer.signer_copy s = ok s := by
  cases s <;> simp [rule_eval.signer.signer_copy, bytes_copy_deref]

theorem signers_copy_loop_eq (s : Slice rule_eval.signer.Signer)
    (out : alloc.vec.Vec rule_eval.signer.Signer) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.signer.signers_copy_loop s out i = ok out' ∧
      out'.val.map id = out.val.map id ++
        pushedFrom (fun _ a => some (id a)) (s.val.drop i.val) i.val := by
  unfold rule_eval.signer.signers_copy_loop
  refine loop_build s.val (fun _ a => some (id a)) id _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨out', hp, hv⟩ := push_eq out s.val[i.val] (room_of_lt s out i hi hout)
    obtain ⟨j, hj, hj'⟩ := incr_eq s i hi
    refine ⟨out', j, hj', by simp [hv], ?_⟩
    simp [rule_eval.signer.signers_copy_loop.body, hi, index_usize_eq _ _ hi, signer_copy_eq, hp,
      hj]
  · intro out i hi
    have : ¬ i.val < s.length := by simp only [Slice.length]; omega
    simp [rule_eval.signer.signers_copy_loop.body, this]

theorem signers_copy_deref (v : alloc.vec.Vec rule_eval.signer.Signer) :
    rule_eval.signer.signers_copy (alloc.vec.Vec.deref v) = ok v := by
  obtain ⟨out, h, hv⟩ := signers_copy_loop_eq (alloc.vec.Vec.deref v)
    (alloc.vec.Vec.new rule_eval.signer.Signer) 0#usize (by simp)
  rw [rule_eval.signer.signers_copy, h]
  congr 1
  exact vec_eq_of_val (by simpa [pushedFrom_map] using hv)

theorem rule_copy_eq (r : rule_eval.rule.Rule) : rule_eval.rule.rule_copy r = ok r := by
  simp [rule_eval.rule.rule_copy, bytes_copy_deref, bytes_list_copy_deref, conds_copy_deref,
    signers_copy_deref]

/-! ## Removing functions from a rule -/

/-- Whether the byte string `a` is one of `remove`, as `bytes_in` computes it. -/
def inList (remove : Slice (alloc.vec.Vec Std.U8)) (a : alloc.vec.Vec Std.U8) : Bool :=
  remove.val.any (fun y => decide (a.val = y.val))

theorem bytes_list_without_loop_eq (s remove : Slice (alloc.vec.Vec Std.U8))
    (out : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.bytes.bytes_list_without_loop s remove out i = ok out' ∧
      out'.val.map id = out.val.map id ++
        pushedFrom (fun _ a => if !inList remove a then some (id a) else none)
          (s.val.drop i.val) i.val := by
  unfold rule_eval.bytes.bytes_list_without_loop
  refine loop_build s.val _ id _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq s i hi
    cases hin : inList remove s.val[i.val]
    · obtain ⟨out', hp, hv⟩ := push_eq out s.val[i.val] (room_of_lt s out i hi hout)
      refine ⟨out', j, hj', by simp [hv], ?_⟩
      simp only [inList] at hin
      simp only [rule_eval.bytes.bytes_list_without_loop.body, slice_len_lt, hi, ↓reduceIte,
        index_usize_eq _ _ hi, bind_ok, bytes_in_eq, vec_deref_val, hin, Bool.false_eq_true,
        bytes_copy_deref, hp, hj]
    · refine ⟨out, j, hj', by simp, ?_⟩
      simp only [inList] at hin
      simp only [rule_eval.bytes.bytes_list_without_loop.body, slice_len_lt, hi, ↓reduceIte,
        index_usize_eq _ _ hi, bind_ok, bytes_in_eq, vec_deref_val, hin, hj]
  · intro out i hi
    have : ¬ i.val < s.length := by simp only [Slice.length]; omega
    simp [rule_eval.bytes.bytes_list_without_loop.body, this]

/-- `bytes_list_without list remove` keeps, in order, the byte strings of
`list` that are not in `remove`. -/
theorem bytes_list_without_eq (s remove : Slice (alloc.vec.Vec Std.U8)) :
    ∃ out, rule_eval.bytes.bytes_list_without s remove = ok out ∧
      out.val = s.val.filter (fun a => !inList remove a) := by
  obtain ⟨out, h, hv⟩ := bytes_list_without_loop_eq s remove
    (alloc.vec.Vec.new (alloc.vec.Vec Std.U8)) 0#usize (by simp)
  refine ⟨out, h, ?_⟩
  rw [pushedFrom_filter (fun a => !inList remove a) id] at hv
  simpa using hv

/-- The denotation of the functions `bytes_list_without` keeps is the model's
filter. -/
theorem denote_filter_inList (l : List (alloc.vec.Vec Std.U8))
    (remove : Slice (alloc.vec.Vec Std.U8)) :
    (l.filter (fun a => !inList remove a)).map denoteBytes =
      (l.map denoteBytes).filter (fun f => decide (f ∉ remove.val.map denoteBytes)) := by
  rw [List.filter_map]
  congr 2
  funext a
  have := any_bytes_eq_mem a.val remove.val
  simp only [inList, Function.comp_def, decide_not]
  rw [this]
  rfl

theorem rule_without_functions_eq (r : rule_eval.rule.Rule)
    (functions : Slice (alloc.vec.Vec Std.U8)) :
    ∃ r', rule_eval.attenuate.rule_without_functions r functions = ok r' ∧
      denoteRule r' = (denoteRule r).removeFunctions (functions.val.map denoteBytes) := by
  obtain ⟨fs, hfs, hv⟩ := bytes_list_without_eq (alloc.vec.Vec.deref r.functions) functions
  refine ⟨{ r with functions := fs }, ?_, ?_⟩
  · simp [rule_eval.attenuate.rule_without_functions, bytes_copy_deref, hfs, conds_copy_deref,
      signers_copy_deref]
  · simp only [denoteRule, Chain.Rule.removeFunctions, hv, vec_deref_val,
      denote_filter_inList]

/-! ## Removing signers from a rule -/

/-- Whether the signer `a` is one of `remove`, as `signer_in` computes it. -/
def signerInList (remove : Slice rule_eval.signer.Signer) (a : rule_eval.signer.Signer) : Bool :=
  decide (denoteSigner a ∈ denoteSigners remove.val)

theorem signers_without_loop_eq (s remove : Slice rule_eval.signer.Signer)
    (out : alloc.vec.Vec rule_eval.signer.Signer) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.signer.signers_without_loop s remove out i = ok out' ∧
      out'.val.map id = out.val.map id ++
        pushedFrom (fun _ a => if !signerInList remove a then some (id a) else none)
          (s.val.drop i.val) i.val := by
  unfold rule_eval.signer.signers_without_loop
  refine loop_build s.val _ id _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq s i hi
    cases hin : signerInList remove s.val[i.val]
    · obtain ⟨out', hp, hv⟩ := push_eq out s.val[i.val] (room_of_lt s out i hi hout)
      refine ⟨out', j, hj', by simp [hv], ?_⟩
      simp only [signerInList] at hin
      simp only [rule_eval.signer.signers_without_loop.body, slice_len_lt, hi, ↓reduceIte,
        index_usize_eq _ _ hi, bind_ok, signer_in_eq, hin, Bool.false_eq_true, signer_copy_eq,
        hp, hj]
    · refine ⟨out, j, hj', by simp, ?_⟩
      simp only [signerInList] at hin
      simp only [rule_eval.signer.signers_without_loop.body, slice_len_lt, hi, ↓reduceIte,
        index_usize_eq _ _ hi, bind_ok, signer_in_eq, hin, hj]
  · intro out i hi
    have : ¬ i.val < s.length := by simp only [Slice.length]; omega
    simp [rule_eval.signer.signers_without_loop.body, this]

/-- `signers_without list remove` keeps, in order, the signers of `list` that
are not in `remove`. -/
theorem signers_without_eq (s remove : Slice rule_eval.signer.Signer) :
    ∃ out, rule_eval.signer.signers_without s remove = ok out ∧
      out.val = s.val.filter (fun a => !signerInList remove a) := by
  obtain ⟨out, h, hv⟩ := signers_without_loop_eq s remove
    (alloc.vec.Vec.new rule_eval.signer.Signer) 0#usize (by simp)
  refine ⟨out, h, ?_⟩
  rw [pushedFrom_filter (fun a => !signerInList remove a) id] at hv
  simpa using hv

theorem denote_filter_signerInList (l : List rule_eval.signer.Signer)
    (remove : Slice rule_eval.signer.Signer) :
    denoteSigners (l.filter (fun a => !signerInList remove a)) =
      (denoteSigners l).filter (fun s => decide (s ∉ denoteSigners remove.val)) := by
  simp only [denoteSigners, List.filter_map]
  congr 2

theorem rule_without_signers_eq (r : rule_eval.rule.Rule)
    (signers : Slice rule_eval.signer.Signer) :
    ∃ r', rule_eval.attenuate.rule_without_signers r signers = ok r' ∧
      denoteRule r' = (denoteRule r).removeSigners (denoteSigners signers.val) := by
  obtain ⟨ss, hss, hv⟩ := signers_without_eq (alloc.vec.Vec.deref r.signers) signers
  refine ⟨{ r with signers := ss }, ?_, ?_⟩
  · simp [rule_eval.attenuate.rule_without_signers, bytes_copy_deref, bytes_list_copy_deref,
      conds_copy_deref, hss]
  · simp only [denoteRule, Chain.Rule.removeSigners, hv, vec_deref_val,
      denote_filter_signerInList]

/-! ## Dropping a rule -/

theorem drop_rule_loop_eq (rules : Slice rule_eval.rule.Rule) (index : Usize)
    (out : alloc.vec.Vec rule_eval.rule.Rule) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.attenuate.drop_rule_loop rules index out i = ok out' ∧
      out'.val.map id = out.val.map id ++
        pushedFrom (fun j a => if j = index.val then none else some (id a))
          (rules.val.drop i.val) i.val := by
  unfold rule_eval.attenuate.drop_rule_loop
  refine loop_build rules.val _ id _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
    by_cases hii : i = index
    · subst hii
      refine ⟨out, j, hj', by simp, ?_⟩
      simp [rule_eval.attenuate.drop_rule_loop.body, hi, hj]
    · have hv : i.val ≠ index.val := fun h => hii (usize_val_eq_iff.mp h)
      obtain ⟨out', hp, hval⟩ := push_eq out rules.val[i.val] (room_of_lt rules out i hi hout)
      refine ⟨out', j, hj', by simp [hval, hv], ?_⟩
      simp [rule_eval.attenuate.drop_rule_loop.body, hi, hii, index_usize_eq _ _ hi,
        rule_copy_eq, hp, hj]
  · intro out i hi
    have : ¬ i.val < rules.length := by simp only [Slice.length]; omega
    simp [rule_eval.attenuate.drop_rule_loop.body, this]

theorem drop_rule_ok (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (h : index.val < rules.length) :
    ∃ out, rule_eval.attenuate.drop_rule rules index = ok (.Ok out) ∧
      out.val = rules.val.eraseIdx index.val := by
  obtain ⟨out, hl, hv⟩ := drop_rule_loop_eq rules (UScalar.cast .Usize index)
    (alloc.vec.Vec.new rule_eval.rule.Rule) 0#usize (by simp)
  refine ⟨out, ?_, ?_⟩
  · have : ¬ rules.length ≤ index.val := by omega
    simp [rule_eval.attenuate.drop_rule, lift, this, hl]
  · simpa [pushedFrom_eraseIdx] using hv

theorem drop_rule_err (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (h : rules.length ≤ index.val) :
    rule_eval.attenuate.drop_rule rules index =
      ok (.Err rule_eval.attenuate.AttenuationError.NoSuchRule) := by
  simp [rule_eval.attenuate.drop_rule, lift, h]

/-- The extracted `drop_rule` returns `ok` on every input, and its outcome is
`RuleSet.dropRule` of the denotations. -/
theorem drop_rule_eq (rules : Slice rule_eval.rule.Rule) (index : Std.U32) :
    ∃ res, rule_eval.attenuate.drop_rule rules index = ok res ∧
      denoteOutcome res = (denoteRules rules.val).dropRule (denoteU32 index) := by
  by_cases h : index.val < rules.length
  · obtain ⟨out, hd, hv⟩ := drop_rule_ok rules index h
    refine ⟨_, hd, ?_⟩
    have : index.val < rules.val.length := h
    simp [denoteOutcome, Chain.RuleSet.dropRule, denoteRules, hv, this,
      List.eraseIdx_eq_take_drop_succ, List.map_take, List.map_drop]
  · refine ⟨_, drop_rule_err rules index (by omega), ?_⟩
    have : ¬ index.val < rules.val.length := h
    simp [denoteOutcome, denoteError, Chain.RuleSet.dropRule, denoteRules, this]

/-! ## Removing functions -/

theorem remove_functions_loop_eq (rules : Slice rule_eval.rule.Rule)
    (functions : Slice (alloc.vec.Vec Std.U8)) (index : Usize)
    (out : alloc.vec.Vec rule_eval.rule.Rule) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.attenuate.remove_functions_loop rules functions index out i = ok out' ∧
      out'.val.map denoteRule = out.val.map denoteRule ++
        pushedFrom (fun j a => some (if j = index.val then
            (fun r : Chain.Rule => r.removeFunctions (functions.val.map denoteBytes)) (denoteRule a)
          else denoteRule a))
          (rules.val.drop i.val) i.val := by
  unfold rule_eval.attenuate.remove_functions_loop
  refine loop_build rules.val _ denoteRule _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
    by_cases hii : i = index
    · subst hii
      obtain ⟨r', hr', hd⟩ := rule_without_functions_eq rules.val[i.val] functions
      obtain ⟨out', hp, hval⟩ := push_eq out r' (room_of_lt rules out i hi hout)
      refine ⟨out', j, hj', by simp [hval, hd], ?_⟩
      simp [rule_eval.attenuate.remove_functions_loop.body, hi, index_usize_eq _ _ hi, hr',
        hp, hj]
    · have hv : i.val ≠ index.val := fun h => hii (usize_val_eq_iff.mp h)
      obtain ⟨out', hp, hval⟩ := push_eq out rules.val[i.val] (room_of_lt rules out i hi hout)
      refine ⟨out', j, hj', by simp [hval, hv], ?_⟩
      simp [rule_eval.attenuate.remove_functions_loop.body, hi, hii, index_usize_eq _ _ hi,
        rule_copy_eq, hp, hj]
  · intro out i hi
    have : ¬ i.val < rules.length := by simp only [Slice.length]; omega
    simp [rule_eval.attenuate.remove_functions_loop.body, this]

theorem remove_functions_ok (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (functions : Slice (alloc.vec.Vec Std.U8)) (h : index.val < rules.length) :
    ∃ out, rule_eval.attenuate.remove_functions rules index functions = ok (.Ok out) ∧
      denoteRules out.val =
        (denoteRules rules.val).set index.val
          ((denoteRule rules.val[index.val]).removeFunctions (functions.val.map denoteBytes)) := by
  obtain ⟨out, hl, hv⟩ := remove_functions_loop_eq rules functions (UScalar.cast .Usize index)
    (alloc.vec.Vec.new rule_eval.rule.Rule) 0#usize (by simp)
  refine ⟨out, ?_, ?_⟩
  · have : ¬ rules.length ≤ index.val := by omega
    simp [rule_eval.attenuate.remove_functions, lift, this, hl]
  · have h0 : (0#usize).val = 0 := by simp
    simp only [vec_new_val, List.map_nil, List.nil_append, cast_usize_val, h0,
      List.drop_zero] at hv
    have key := pushedFrom_set denoteRule
      (fun r : Chain.Rule => r.removeFunctions (functions.val.map denoteBytes)) rules.val index.val h
    beta_reduce at key
    rw [show denoteRules out.val = out.val.map denoteRule from rfl, hv, key]
    rfl

theorem remove_functions_err (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (functions : Slice (alloc.vec.Vec Std.U8)) (h : rules.length ≤ index.val) :
    rule_eval.attenuate.remove_functions rules index functions =
      ok (.Err rule_eval.attenuate.AttenuationError.NoSuchRule) := by
  simp [rule_eval.attenuate.remove_functions, lift, h]

/-- The extracted `remove_functions` returns `ok` on every input, and its
outcome is `RuleSet.removeFunctions` of the denotations. -/
theorem remove_functions_eq (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (functions : Slice (alloc.vec.Vec Std.U8)) :
    ∃ res, rule_eval.attenuate.remove_functions rules index functions = ok res ∧
      denoteOutcome res =
        (denoteRules rules.val).removeFunctions (denoteU32 index)
          (functions.val.map denoteBytes) := by
  by_cases h : index.val < rules.length
  · obtain ⟨out, hd, hv⟩ := remove_functions_ok rules index functions h
    refine ⟨_, hd, ?_⟩
    have : index.val < rules.val.length := h
    simp only [denoteRules] at hv
    simp [denoteOutcome, Chain.RuleSet.removeFunctions, Chain.RuleSet.modifyRule, denoteRules,
      hv, this]
  · refine ⟨_, remove_functions_err rules index functions (by omega), ?_⟩
    have : rules.val.length ≤ index.val := by simp only [Slice.length] at h; omega
    simp [denoteOutcome, denoteError, Chain.RuleSet.removeFunctions, Chain.RuleSet.modifyRule,
      denoteRules, this]

/-! ## Removing signers -/

theorem remove_signers_loop_eq (rules : Slice rule_eval.rule.Rule)
    (signers : Slice rule_eval.signer.Signer) (index : Usize)
    (out : alloc.vec.Vec rule_eval.rule.Rule) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.attenuate.remove_signers_loop rules signers index out i = ok out' ∧
      out'.val.map denoteRule = out.val.map denoteRule ++
        pushedFrom (fun j a => some (if j = index.val then
            (fun r : Chain.Rule => r.removeSigners (denoteSigners signers.val)) (denoteRule a)
          else denoteRule a))
          (rules.val.drop i.val) i.val := by
  unfold rule_eval.attenuate.remove_signers_loop
  refine loop_build rules.val _ denoteRule _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
    by_cases hii : i = index
    · subst hii
      obtain ⟨r', hr', hd⟩ := rule_without_signers_eq rules.val[i.val] signers
      obtain ⟨out', hp, hval⟩ := push_eq out r' (room_of_lt rules out i hi hout)
      refine ⟨out', j, hj', by simp [hval, hd], ?_⟩
      simp [rule_eval.attenuate.remove_signers_loop.body, hi, index_usize_eq _ _ hi, hr',
        hp, hj]
    · have hv : i.val ≠ index.val := fun h => hii (usize_val_eq_iff.mp h)
      obtain ⟨out', hp, hval⟩ := push_eq out rules.val[i.val] (room_of_lt rules out i hi hout)
      refine ⟨out', j, hj', by simp [hval, hv], ?_⟩
      simp [rule_eval.attenuate.remove_signers_loop.body, hi, hii, index_usize_eq _ _ hi,
        rule_copy_eq, hp, hj]
  · intro out i hi
    have : ¬ i.val < rules.length := by simp only [Slice.length]; omega
    simp [rule_eval.attenuate.remove_signers_loop.body, this]

theorem remove_signers_ok (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (signers : Slice rule_eval.signer.Signer) (h : index.val < rules.length) :
    ∃ out, rule_eval.attenuate.remove_signers rules index signers = ok (.Ok out) ∧
      denoteRules out.val =
        (denoteRules rules.val).set index.val
          ((denoteRule rules.val[index.val]).removeSigners (denoteSigners signers.val)) := by
  obtain ⟨out, hl, hv⟩ := remove_signers_loop_eq rules signers (UScalar.cast .Usize index)
    (alloc.vec.Vec.new rule_eval.rule.Rule) 0#usize (by simp)
  refine ⟨out, ?_, ?_⟩
  · have : ¬ rules.length ≤ index.val := by omega
    simp [rule_eval.attenuate.remove_signers, lift, this, hl]
  · have h0 : (0#usize).val = 0 := by simp
    simp only [vec_new_val, List.map_nil, List.nil_append, cast_usize_val, h0,
      List.drop_zero] at hv
    have key := pushedFrom_set denoteRule
      (fun r : Chain.Rule => r.removeSigners (denoteSigners signers.val)) rules.val index.val h
    beta_reduce at key
    rw [show denoteRules out.val = out.val.map denoteRule from rfl, hv, key]
    rfl

theorem remove_signers_err (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (signers : Slice rule_eval.signer.Signer) (h : rules.length ≤ index.val) :
    rule_eval.attenuate.remove_signers rules index signers =
      ok (.Err rule_eval.attenuate.AttenuationError.NoSuchRule) := by
  simp [rule_eval.attenuate.remove_signers, lift, h]

/-- The extracted `remove_signers` returns `ok` on every input, and its
outcome is `RuleSet.removeSigners` of the denotations. -/
theorem remove_signers_eq (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (signers : Slice rule_eval.signer.Signer) :
    ∃ res, rule_eval.attenuate.remove_signers rules index signers = ok res ∧
      denoteOutcome res =
        (denoteRules rules.val).removeSigners (denoteU32 index) (denoteSigners signers.val) := by
  by_cases h : index.val < rules.length
  · obtain ⟨out, hd, hv⟩ := remove_signers_ok rules index signers h
    refine ⟨_, hd, ?_⟩
    have : index.val < rules.val.length := h
    simp only [denoteRules] at hv
    simp [denoteOutcome, Chain.RuleSet.removeSigners, Chain.RuleSet.modifyRule, denoteRules,
      hv, this]
  · refine ⟨_, remove_signers_err rules index signers (by omega), ?_⟩
    have : rules.val.length ≤ index.val := by simp only [Slice.length] at h; omega
    simp [denoteOutcome, denoteError, Chain.RuleSet.removeSigners, Chain.RuleSet.modifyRule,
      denoteRules, this]

/-! ## Raising a threshold -/

theorem raise_threshold_loop_eq (rules : Slice rule_eval.rule.Rule) (threshold : Std.U32)
    (index : Usize) (out : alloc.vec.Vec rule_eval.rule.Rule) (i : Usize)
    (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.attenuate.raise_threshold_loop rules threshold index out i = ok out' ∧
      out'.val.map denoteRule = out.val.map denoteRule ++
        pushedFrom (fun j a => some (if j = index.val then
            (fun r : Chain.Rule => { r with threshold := denoteU32 threshold }) (denoteRule a)
          else denoteRule a))
          (rules.val.drop i.val) i.val := by
  unfold rule_eval.attenuate.raise_threshold_loop
  refine loop_build rules.val _ denoteRule _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
    by_cases hii : i = index
    · subst hii
      obtain ⟨out', hp, hval⟩ := push_eq out { rules.val[i.val] with threshold }
        (room_of_lt rules out i hi hout)
      refine ⟨out', j, hj', by simp [hval, denoteRule], ?_⟩
      simp [rule_eval.attenuate.raise_threshold_loop.body, hi, index_usize_eq _ _ hi,
        rule_copy_eq, hp, hj]
    · have hv : i.val ≠ index.val := fun h => hii (usize_val_eq_iff.mp h)
      obtain ⟨out', hp, hval⟩ := push_eq out rules.val[i.val] (room_of_lt rules out i hi hout)
      refine ⟨out', j, hj', by simp [hval, hv], ?_⟩
      simp [rule_eval.attenuate.raise_threshold_loop.body, hi, hii, index_usize_eq _ _ hi,
        rule_copy_eq, hp, hj]
  · intro out i hi
    have : ¬ i.val < rules.length := by simp only [Slice.length]; omega
    simp [rule_eval.attenuate.raise_threshold_loop.body, this]

theorem raise_threshold_ok (rules : Slice rule_eval.rule.Rule) (index threshold : Std.U32)
    (h : index.val < rules.length) (hk : rules.val[index.val].threshold.val ≤ threshold.val) :
    ∃ out, rule_eval.attenuate.raise_threshold rules index threshold = ok (.Ok out) ∧
      denoteRules out.val =
        (denoteRules rules.val).set index.val
          { denoteRule rules.val[index.val] with threshold := denoteU32 threshold } := by
  obtain ⟨out, hl, hv⟩ := raise_threshold_loop_eq rules threshold (UScalar.cast .Usize index)
    (alloc.vec.Vec.new rule_eval.rule.Rule) 0#usize (by simp)
  refine ⟨out, ?_, ?_⟩
  · have hget : rules.val[index.val]? = some rules.val[index.val] := List.getElem?_eq_getElem h
    simp [rule_eval.attenuate.raise_threshold, lift, slice_get_eq, hget, hk, hl]
  · have h0 : (0#usize).val = 0 := by simp
    simp only [vec_new_val, List.map_nil, List.nil_append, cast_usize_val, h0,
      List.drop_zero] at hv
    have key := pushedFrom_set denoteRule
      (fun r : Chain.Rule => { r with threshold := denoteU32 threshold }) rules.val index.val h
    beta_reduce at key
    rw [show denoteRules out.val = out.val.map denoteRule from rfl, hv, key]
    rfl

theorem raise_threshold_err (rules : Slice rule_eval.rule.Rule) (index threshold : Std.U32)
    (h : rules.length ≤ index.val) :
    rule_eval.attenuate.raise_threshold rules index threshold =
      ok (.Err rule_eval.attenuate.AttenuationError.NoSuchRule) := by
  have hget : rules.val[index.val]? = none := List.getElem?_eq_none_iff.mpr h
  simp [rule_eval.attenuate.raise_threshold, lift, slice_get_eq, hget]

theorem raise_threshold_lowered (rules : Slice rule_eval.rule.Rule) (index threshold : Std.U32)
    (h : index.val < rules.length) (hk : threshold.val < rules.val[index.val].threshold.val) :
    rule_eval.attenuate.raise_threshold rules index threshold =
      ok (.Err rule_eval.attenuate.AttenuationError.ThresholdLowered) := by
  have hget : rules.val[index.val]? = some rules.val[index.val] := List.getElem?_eq_getElem h
  have hle : ¬ rules.val[index.val].threshold.val ≤ threshold.val := by omega
  simp [rule_eval.attenuate.raise_threshold, lift, slice_get_eq, hget, hle]

/-- The extracted `raise_threshold` returns `ok` on every input, and its
outcome is `RuleSet.raiseThreshold` of the denotations, `noSuchRule` and
`thresholdLowered` included. -/
theorem raise_threshold_eq (rules : Slice rule_eval.rule.Rule) (index threshold : Std.U32) :
    ∃ res, rule_eval.attenuate.raise_threshold rules index threshold = ok res ∧
      denoteOutcome res =
        (denoteRules rules.val).raiseThreshold (denoteU32 index) (denoteU32 threshold) := by
  by_cases h : index.val < rules.length
  · have hlen : index.val < rules.val.length := h
    have hget : (denoteRules rules.val)[index.val]? = some (denoteRule rules.val[index.val]) := by
      simp [denoteRules, hlen]
    by_cases hk : threshold.val < rules.val[index.val].threshold.val
    · refine ⟨_, raise_threshold_lowered rules index threshold h hk, ?_⟩
      have : denoteU32 threshold < (denoteRule rules.val[index.val]).threshold := by
        simp only [denoteRule, UInt32.lt_iff_toNat_lt, denoteU32_toNat]
        exact hk
      simp [denoteOutcome, denoteError, Chain.RuleSet.raiseThreshold, hget, this]
    · obtain ⟨out, hd, hv⟩ := raise_threshold_ok rules index threshold h (by omega)
      refine ⟨_, hd, ?_⟩
      have : ¬ denoteU32 threshold < (denoteRule rules.val[index.val]).threshold := by
        simp only [denoteRule, UInt32.lt_iff_toNat_lt, denoteU32_toNat]
        exact hk
      simp [denoteOutcome, Chain.RuleSet.raiseThreshold, hget, this, hv]
  · refine ⟨_, raise_threshold_err rules index threshold (by omega), ?_⟩
    have : rules.val.length ≤ index.val := by simp only [Slice.length] at h; omega
    simp [denoteOutcome, denoteError, Chain.RuleSet.raiseThreshold, denoteRules, this]

/-! ## Adding a condition -/

/-- The rule `add_cond` needs: the rule at `index`, when there is one, holds
fewer than `Usize.max` conditions, so Aeneas's model of `Vec::push` can
append one more. -/
def CondRoom (rules : Slice rule_eval.rule.Rule) (index : Std.U32) : Prop :=
  ∀ r, rules.val[index.val]? = some r → r.conds.val.length < Usize.max

theorem add_cond_loop_eq (rules : Slice rule_eval.rule.Rule) (cond : rule_eval.rule.Cond)
    (index : Usize) (hroom : ∀ r, rules.val[index.val]? = some r → r.conds.val.length < Usize.max)
    (out : alloc.vec.Vec rule_eval.rule.Rule) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.attenuate.add_cond_loop rules cond index out i = ok out' ∧
      out'.val.map denoteRule = out.val.map denoteRule ++
        pushedFrom (fun j a => some (if j = index.val then
            (fun r : Chain.Rule => r.addCond (denoteCond cond)) (denoteRule a)
          else denoteRule a))
          (rules.val.drop i.val) i.val := by
  unfold rule_eval.attenuate.add_cond_loop
  refine loop_build rules.val _ denoteRule _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
    by_cases hii : i = index
    · subst hii
      have hr : rules.val[i.val]? = some rules.val[i.val] := List.getElem?_eq_getElem hi
      obtain ⟨conds', hc, hcv⟩ := push_eq rules.val[i.val].conds cond (hroom _ hr)
      obtain ⟨out', hp, hval⟩ := push_eq out { rules.val[i.val] with conds := conds' }
        (room_of_lt rules out i hi hout)
      refine ⟨out', j, hj', ?_, ?_⟩
      · simp [hval, denoteRule, Chain.Rule.addCond, hcv]
      · simp [rule_eval.attenuate.add_cond_loop.body, hi, index_usize_eq _ _ hi, rule_copy_eq,
          cond_copy_eq, hc, hp, hj]
    · have hv : i.val ≠ index.val := fun h => hii (usize_val_eq_iff.mp h)
      obtain ⟨out', hp, hval⟩ := push_eq out rules.val[i.val] (room_of_lt rules out i hi hout)
      refine ⟨out', j, hj', by simp [hval, hv], ?_⟩
      simp [rule_eval.attenuate.add_cond_loop.body, hi, hii, index_usize_eq _ _ hi,
        rule_copy_eq, hp, hj]
  · intro out i hi
    have : ¬ i.val < rules.length := by simp only [Slice.length]; omega
    simp [rule_eval.attenuate.add_cond_loop.body, this]

theorem add_cond_ok (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (cond : rule_eval.rule.Cond) (h : index.val < rules.length) (hroom : CondRoom rules index) :
    ∃ out, rule_eval.attenuate.add_cond rules index cond = ok (.Ok out) ∧
      denoteRules out.val =
        (denoteRules rules.val).set index.val
          ((denoteRule rules.val[index.val]).addCond (denoteCond cond)) := by
  obtain ⟨out, hl, hv⟩ := add_cond_loop_eq rules cond (UScalar.cast .Usize index)
    (fun r hr => hroom r (by simpa using hr)) (alloc.vec.Vec.new rule_eval.rule.Rule) 0#usize
    (by simp)
  refine ⟨out, ?_, ?_⟩
  · have : ¬ rules.length ≤ index.val := by omega
    simp [rule_eval.attenuate.add_cond, lift, this, hl]
  · have h0 : (0#usize).val = 0 := by simp
    simp only [vec_new_val, List.map_nil, List.nil_append, cast_usize_val, h0,
      List.drop_zero] at hv
    have key := pushedFrom_set denoteRule
      (fun r : Chain.Rule => r.addCond (denoteCond cond)) rules.val index.val h
    beta_reduce at key
    rw [show denoteRules out.val = out.val.map denoteRule from rfl, hv, key]
    rfl

theorem add_cond_err (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (cond : rule_eval.rule.Cond) (h : rules.length ≤ index.val) :
    rule_eval.attenuate.add_cond rules index cond =
      ok (.Err rule_eval.attenuate.AttenuationError.NoSuchRule) := by
  simp [rule_eval.attenuate.add_cond, lift, h]

/-- The extracted `add_cond` returns `ok` on every input satisfying
`CondRoom`, and its outcome is `RuleSet.addCond` of the denotations. -/
theorem add_cond_eq (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (cond : rule_eval.rule.Cond) (hroom : CondRoom rules index) :
    ∃ res, rule_eval.attenuate.add_cond rules index cond = ok res ∧
      denoteOutcome res =
        (denoteRules rules.val).addCond (denoteU32 index) (denoteCond cond) := by
  by_cases h : index.val < rules.length
  · obtain ⟨out, hd, hv⟩ := add_cond_ok rules index cond h hroom
    refine ⟨_, hd, ?_⟩
    have : index.val < rules.val.length := h
    simp only [denoteRules] at hv
    simp [denoteOutcome, Chain.RuleSet.addCond, Chain.RuleSet.modifyRule, denoteRules, hv, this]
  · refine ⟨_, add_cond_err rules index cond (by omega), ?_⟩
    have : rules.val.length ≤ index.val := by simp only [Slice.length] at h; omega
    simp [denoteOutcome, denoteError, Chain.RuleSet.addCond, Chain.RuleSet.modifyRule,
      denoteRules, this]

/-- `CondRoom` is exact: on a rule that already holds `Usize.max` conditions,
the extracted `add_cond` fails. -/
theorem add_cond_full (rules : Slice rule_eval.rule.Rule) (index : Std.U32)
    (cond : rule_eval.rule.Cond) {r : rule_eval.rule.Rule}
    (hr : rules.val[index.val]? = some r) (hfull : r.conds.val.length = Usize.max) :
    rule_eval.attenuate.add_cond rules index cond = fail .maximumSizeExceeded := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hr
  have hloop : rule_eval.attenuate.add_cond_loop rules cond (UScalar.cast .Usize index)
      (alloc.vec.Vec.new rule_eval.rule.Rule) 0#usize = fail .maximumSizeExceeded := by
    unfold rule_eval.attenuate.add_cond_loop
    refine loop_build_fail rules.val index.val _ _ ?_ ?_ _ _ (by simp) (by simp)
    · intro out i hn hout
      have hi : i.val < rules.length := by simp only [Slice.length]; omega
      have hii : i ≠ UScalar.cast .Usize index := by
        intro h
        rw [← usize_val_eq_iff, cast_usize_val] at h
        omega
      obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
      obtain ⟨out', hp, hval⟩ := push_eq out rules.val[i.val] (room_of_lt rules out i hi hout)
      refine ⟨out', j, hj', by simp [hval], ?_⟩
      simp [rule_eval.attenuate.add_cond_loop.body, hi, hii, index_usize_eq _ _ hi,
        rule_copy_eq, hp, hj]
    · intro out i hn hout
      have hi : i.val < rules.length := by simp only [Slice.length]; omega
      have hii : i = UScalar.cast .Usize index := by
        rw [← usize_val_eq_iff, cast_usize_val]
        exact hn
      have hri : rules.val[i.val] = r := by simp only [hn]; exact hget
      simp [rule_eval.attenuate.add_cond_loop.body, hi, hii.symm, index_usize_eq _ _ hi,
        rule_copy_eq, cond_copy_eq, hri, push_full _ _ hfull]
  have : ¬ rules.length ≤ index.val := by simp only [Slice.length]; omega
  simp [rule_eval.attenuate.add_cond, lift, this, hloop]

end RuleCore.Equiv
