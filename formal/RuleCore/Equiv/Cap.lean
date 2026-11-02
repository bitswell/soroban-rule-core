import RuleCore.Equiv.DenoteCap
import RuleCore.Equiv.Attenuation
import RuleCore.Theorems.Cap

/-!
# Caps: the extracted check agrees with the model

Each theorem says that an extracted function of the `cap` module returns `ok`
on every input, so it neither fails nor diverges, and that the value it returns
is the model's on the denoted inputs:

* `params_valid_eq`: `params_valid params` is `Params.valid` of the denotation;
* `empty_record_eq`: `empty_record` denotes `Record.empty`;
* `before_newest_eq`: the clock check is `beforeNewest`;
* `evict_loop_eq`: the eviction loop from position `i` is `evict` of the
  entries from `i` on, and stops within the history;
* `entries_from_eq`, `record_copy_eq`: the copies return the same entries;
* `check_spend_eq`: `check_spend record limit period now amount` is
  `Params.check` of the denotations.

`checked_add_eq`, `checked_sub_eq` and `saturating_sub_val` relate the
library's `i128::checked_add`, `i128::checked_sub` and `u32::saturating_sub`
to the model's `addI128`, `subI128` and truncated subtraction.

No bound is stated. `entries_from` pushes one entry per position of the slice
it copies, and `check_spend` pushes the new entry only after checking that
fewer than `MAX_HISTORY_ENTRIES` entries are kept, so every `Vec::push` has
room.
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std Result ControlFlow

/-! ## Scalars -/

theorem i128_min_eq : I128.min = Cap.i128Min := by
  rw [I128.min_def]
  simp [I128.numBits, Cap.i128Min]

theorem i128_max_eq : I128.max = Cap.i128Max := by
  rw [I128.max_def]
  simp [I128.numBits, Cap.i128Max]

theorem checked_add_eq (x y : Std.I128) :
    (I128.checked_add x y).map (·.val) = Cap.addI128 x.val y.val := by
  have h := I128.checked_add_bv_spec x y
  rw [i128_min_eq, i128_max_eq] at h
  simp only [I128.checked_add]
  cases hc : core.num.checked_add_IScalar x y with
  | none =>
    rw [hc] at h
    simp only [Option.map_none, Cap.addI128, h, ↓reduceIte]
  | some z =>
    rw [hc] at h
    simp [Cap.addI128, h.1, h.2.1, h.2.2.1]

theorem checked_sub_eq (x y : Std.I128) :
    (I128.checked_sub x y).map (·.val) = Cap.subI128 x.val y.val := by
  have h := I128.checked_sub_bv_spec x y
  rw [i128_min_eq, i128_max_eq] at h
  simp only [I128.checked_sub]
  cases hc : core.num.checked_sub_IScalar x y with
  | none =>
    rw [hc] at h
    simp only [Option.map_none, Cap.subI128, h, ↓reduceIte]
  | some z =>
    rw [hc] at h
    simp [Cap.subI128, h.1, h.2.1, h.2.2.1]

theorem saturating_sub_val (x y : Std.U32) :
    (core.num.U32.saturating_sub x y).val = x.val - y.val := by
  simp only [core.num.U32.saturating_sub, UScalar.saturating_sub, UScalar.val, BitVec.toNat_ofNat]
  have := x.hBounds
  apply Nat.mod_eq_of_lt
  simp only [UScalar.val] at this
  omega

/-! ## Parameters and the empty record -/

theorem params_valid_eq (params : rule_eval.cap.CapParams) :
    rule_eval.cap.params_valid params = ok (denoteParams params).valid := by
  simp only [rule_eval.cap.params_valid, denoteParams, Cap.Params.valid]
  by_cases h : (0 : Int) < params.limit.val
  · have : params.limit > 0#i128 := by simpa using h
    by_cases hp : 0 < params.period.val <;> simp [this, h, hp]
  · have : ¬ params.limit > 0#i128 := by simpa using h
    simp [this, h]

theorem empty_record_eq :
    ∃ r, rule_eval.cap.empty_record = ok r ∧ denoteRecord r = Cap.Record.empty :=
  ⟨_, rfl, by simp [denoteRecord, Cap.Record.empty]⟩

/-! ## The clock check -/

theorem before_newest_eq (history : Slice rule_eval.cap.SpendEntry) (now : Std.U32) :
    rule_eval.cap.before_newest history now =
      ok (Cap.beforeNewest (history.val.map denoteEntry) now.val) := by
  unfold rule_eval.cap.before_newest
  rcases List.eq_nil_or_concat history.val with hn | ⟨l, b, hc⟩
  · have : Slice.len history = 0#usize := by
      apply UScalar.eq_of_val_eq
      simp [hn]
    simp [this, hn]
  · rw [List.concat_eq_append] at hc
    have hlen : history.length = l.length + 1 := by simp [Slice.length, hc]
    have hne : Slice.len history ≠ 0#usize := by
      intro h
      have := congrArg UScalar.val h
      simp [hlen] at this
    have hsub := UScalar.sub_spec (x := Slice.len history) (y := 1#usize) (by simp [hlen])
    revert hsub
    cases hres : Slice.len history - 1#usize with
    | ret j =>
      intro hj
      have hj' : j.val = l.length := by simpa [Slice.len_val, hlen] using hj
      have hidx : j.val < history.length := by omega
      have hb : history.val[j.val]'hidx = b := by simp [hc, hj']
      simp only [hne, ↓reduceIte, hres, bind_ok, index_usize_eq _ _ hidx, hb]
      simp [hc, denoteEntry]
    | vis e k => intro hj; simp at hj
    | div => intro hj; simp at hj

/-! ## Eviction -/

/-- What the extracted `evict` returned, read against the history it walked:
the entries from `kept_from` on with the evicted total, or the overflow. -/
def evictedOf (h : List rule_eval.cap.SpendEntry) :
    rule_eval.cap.Eviction → Except Cap.CapError (List Cap.Entry × Int)
  | .Stopped keptFrom removed => .ok ((h.drop keptFrom.val).map denoteEntry, removed.val)
  | .Overflow => .error .overflow

theorem checked_add_none {x y : Std.I128} (h : I128.checked_add x y = none) :
    Cap.addI128 x.val y.val = none := by
  rw [← checked_add_eq, h]
  rfl

theorem checked_add_some {x y z : Std.I128} (h : I128.checked_add x y = some z) :
    Cap.addI128 x.val y.val = some z.val := by
  rw [← checked_add_eq, h]
  rfl

theorem checked_sub_none {x y : Std.I128} (h : I128.checked_sub x y = none) :
    Cap.subI128 x.val y.val = none := by
  rw [← checked_sub_eq, h]
  rfl

theorem checked_sub_some {x y z : Std.I128} (h : I128.checked_sub x y = some z) :
    Cap.subI128 x.val y.val = some z.val := by
  rw [← checked_sub_eq, h]
  rfl

theorem evict_body_stop (history : Slice rule_eval.cap.SpendEntry) (cutoff : Std.U32)
    (removed : Std.I128) (i : Usize) (hlt : i.val < history.length)
    (hc : cutoff.val < history.val[i.val].ledger.val) :
    rule_eval.cap.evict_loop.body history cutoff removed i =
      ok (done (.Stopped i removed)) := by
  have hgt : history.val[i.val].ledger > cutoff := by simpa using hc
  simp only [rule_eval.cap.evict_loop.body, slice_len_lt, hlt, ↓reduceIte, index_usize_eq _ _ hlt,
    bind_ok, hgt]

theorem evict_body_overflow (history : Slice rule_eval.cap.SpendEntry) (cutoff : Std.U32)
    (removed : Std.I128) (i : Usize) (hlt : i.val < history.length)
    (hc : ¬ cutoff.val < history.val[i.val].ledger.val)
    (hca : I128.checked_add removed history.val[i.val].amount = none) :
    rule_eval.cap.evict_loop.body history cutoff removed i =
      ok (done .Overflow) := by
  have hgt : ¬ history.val[i.val].ledger > cutoff := by simpa using hc
  simp only [rule_eval.cap.evict_loop.body, slice_len_lt, hlt, ↓reduceIte, index_usize_eq _ _ hlt,
    bind_ok, hgt, lift, hca]

theorem evict_body_next (history : Slice rule_eval.cap.SpendEntry) (cutoff : Std.U32)
    (removed : Std.I128) (i j : Usize) (hlt : i.val < history.length)
    (hc : ¬ cutoff.val < history.val[i.val].ledger.val) {sum : Std.I128}
    (hca : I128.checked_add removed history.val[i.val].amount = some sum)
    (hj : i + 1#usize = ok j) :
    rule_eval.cap.evict_loop.body history cutoff removed i = ok (cont (sum, j)) := by
  have hgt : ¬ history.val[i.val].ledger > cutoff := by simpa using hc
  simp only [rule_eval.cap.evict_loop.body, slice_len_lt, hlt, ↓reduceIte, index_usize_eq _ _ hlt,
    bind_ok, hgt, lift, hca, hj]

theorem evict_body_end (history : Slice rule_eval.cap.SpendEntry) (cutoff : Std.U32)
    (removed : Std.I128) (i : Usize) (hge : ¬ i.val < history.length) :
    rule_eval.cap.evict_loop.body history cutoff removed i =
      ok (done (.Stopped i removed)) := by
  simp [rule_eval.cap.evict_loop.body, hge]

/-- The eviction loop, from position `i` with `removed` evicted so far, returns
the model's eviction of the entries from `i` on, and stops at a position
within the history. -/
theorem evict_loop_eq (history : Slice rule_eval.cap.SpendEntry) (cutoff : Std.U32)
    (removed : Std.I128) (i : Usize) (hi : i.val ≤ history.length) :
    ∃ res, rule_eval.cap.evict_loop history cutoff removed i = ok res ∧
      evictedOf history.val res =
        Cap.evict cutoff.val ((history.val.drop i.val).map denoteEntry) removed.val ∧
      (∀ k r, res = .Stopped k r → k.val ≤ history.length) := by
  unfold rule_eval.cap.evict_loop
  rw [loop]
  dsimp only
  by_cases hlt : i.val < history.length
  · have hdrop : (history.val.drop i.val).map denoteEntry =
        denoteEntry history.val[i.val] :: (history.val.drop (i.val + 1)).map denoteEntry := by
      rw [List.drop_eq_getElem_cons hlt, List.map_cons]
    by_cases hc : cutoff.val < history.val[i.val].ledger.val
    · refine ⟨.Stopped i removed, ?_, ?_, ?_⟩
      · rw [evict_body_stop history cutoff removed i hlt hc, bind_ok]
      · show Except.ok ((history.val.drop i.val).map denoteEntry, removed.val) = _
        rw [hdrop]
        have : cutoff.val < (denoteEntry history.val[i.val]).ledger := hc
        simp only [Cap.evict, this, ↓reduceIte]
      · intro k r hev
        cases hev
        exact Nat.le_of_lt hlt
    · cases hca : I128.checked_add removed history.val[i.val].amount with
      | none =>
        refine ⟨.Overflow, ?_, ?_, ?_⟩
        · rw [evict_body_overflow history cutoff removed i hlt hc hca, bind_ok]
        · rw [hdrop]
          have : ¬ cutoff.val < (denoteEntry history.val[i.val]).ledger := hc
          simp only [evictedOf, Cap.evict, ↓reduceIte, denoteEntry, hc,
            checked_add_none hca]
        · intro k r hev
          cases hev
      | some sum =>
        obtain ⟨j, hj, hj'⟩ := incr_eq history i hlt
        obtain ⟨res, hres, hden, hbound⟩ :=
          evict_loop_eq history cutoff sum j (by omega)
        unfold rule_eval.cap.evict_loop at hres
        refine ⟨res, ?_, ?_, hbound⟩
        · rw [evict_body_next history cutoff removed i j hlt hc hca hj, bind_ok]
          exact hres
        · rw [hden, hdrop, hj']
          have : ¬ cutoff.val < (denoteEntry history.val[i.val]).ledger := hc
          simp only [Cap.evict, ↓reduceIte, denoteEntry, hc, checked_add_some hca]
  · have hnd : history.val.drop i.val = [] :=
      List.drop_of_length_le (by simp only [Slice.length] at hi hlt; omega)
    refine ⟨.Stopped i removed, ?_, ?_, ?_⟩
    · rw [evict_body_end history cutoff removed i hlt, bind_ok]
    · simp [evictedOf, Cap.evict, hnd]
    · intro k r hev
      cases hev
      exact hi
termination_by history.length - i.val
decreasing_by omega

/-! ## Copies -/

theorem entry_copy_eq (e : rule_eval.cap.SpendEntry) : rule_eval.cap.entry_copy e = ok e := rfl

theorem entries_from_loop_eq (s : Slice rule_eval.cap.SpendEntry)
    (out : alloc.vec.Vec rule_eval.cap.SpendEntry) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.cap.entries_from_loop s out i = ok out' ∧
      out'.val.map id = out.val.map id ++
        pushedFrom (fun _ a => some (id a)) (s.val.drop i.val) i.val := by
  unfold rule_eval.cap.entries_from_loop
  refine loop_build s.val (fun _ a => some (id a)) id _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨out', hp, hv⟩ := push_eq out s.val[i.val] (room_of_lt s out i hi hout)
    obtain ⟨j, hj, hj'⟩ := incr_eq s i hi
    refine ⟨out', j, hj', by simp [hv], ?_⟩
    simp [rule_eval.cap.entries_from_loop.body, hi, index_usize_eq _ _ hi, entry_copy_eq, hp, hj]
  · intro out i hi
    have : ¬ i.val < s.length := by simp only [Slice.length]; omega
    simp [rule_eval.cap.entries_from_loop.body, this]

/-- `entries_from` returns the entries from position `start` on. -/
theorem entries_from_eq (s : Slice rule_eval.cap.SpendEntry) (start : Usize) :
    ∃ v, rule_eval.cap.entries_from s start = ok v ∧ v.val = s.val.drop start.val := by
  obtain ⟨out, h, hv⟩ := entries_from_loop_eq s (alloc.vec.Vec.new rule_eval.cap.SpendEntry) start
    (by simp)
  refine ⟨out, h, ?_⟩
  simpa [pushedFrom_map] using hv

theorem record_copy_eq (record : rule_eval.cap.SpendRecord) :
    rule_eval.cap.record_copy record = ok record := by
  obtain ⟨v, h, hv⟩ := entries_from_eq (alloc.vec.Vec.deref record.history) 0#usize
  simp only [rule_eval.cap.record_copy, h, bind_ok]
  have : v = record.history := vec_eq_of_val (by simpa using hv)
  rw [this]

/-! ## The check -/

theorem max_history_val : rule_eval.cap.MAX_HISTORY_ENTRIES.val = Cap.maxHistory := by
  simp [rule_eval.cap.MAX_HISTORY_ENTRIES, Cap.maxHistory]

theorem max_history_lt_usize : Cap.maxHistory < Usize.max := by
  have : U32.max ≤ Usize.max := by scalar_tac
  have h32 : U32.max = 4294967295 := by simp [U32.max, U32.numBits]
  simp only [Cap.maxHistory]
  omega

theorem denoteRecord_history (record : rule_eval.cap.SpendRecord) :
    (denoteRecord record).history = record.history.val.map denoteEntry := rfl

theorem denoteRecord_total (record : rule_eval.cap.SpendRecord) :
    (denoteRecord record).total = record.total.val := rfl

/-- On every input, the extracted `check_spend` returns `ok` of the model's
check on the denotations: it never panics and never diverges. -/
theorem check_spend_eq (record : rule_eval.cap.SpendRecord) (limit : Std.I128)
    (period now : Std.U32) (amount : Std.I128) :
    ∃ res, rule_eval.cap.check_spend record limit period now amount = ok res ∧
      denoteSpend res =
        (⟨limit.val, period.val⟩ : Cap.Params).check (denoteRecord record) now.val amount.val := by
  unfold rule_eval.cap.check_spend
  by_cases hneg : amount < 0#i128
  · have h : amount.val < 0 := by simpa using hneg
    refine ⟨.Err .NegativeAmount, by simp only [hneg, ↓reduceIte], ?_⟩
    simp [denoteSpend, denoteCapError, Cap.Params.check, h]
  have hneg' : ¬ amount.val < 0 := by simpa using hneg
  by_cases hz : amount = 0#i128
  · have h : amount.val = 0 := by simp [hz]
    refine ⟨.Ok record, ?_, ?_⟩
    · simp only [hneg, ↓reduceIte]
      simp only [hz, ↓reduceIte, record_copy_eq, bind_ok]
    simp [denoteSpend, Cap.Params.check, h]
  have hz' : amount.val ≠ 0 := fun h => hz (IScalar.eq_of_val_eq (by simpa using h))
  simp only [hneg, hz, ↓reduceIte, before_newest_eq, vec_deref_val, bind_ok]
  simp only [Cap.Params.check, hneg', hz', ↓reduceIte, denoteRecord_history, denoteRecord_total]
  by_cases hb : Cap.beforeNewest (record.history.val.map denoteEntry) now.val = true
  · simp only [hb, ↓reduceIte]
    refine ⟨.Err .LedgerBeforeNewest, rfl, ?_⟩
    simp [denoteSpend, denoteCapError]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, lift, bind_ok]
    obtain ⟨res, hres, hden, hbound⟩ := evict_loop_eq (alloc.vec.Vec.deref record.history)
      (core.num.U32.saturating_sub now period) 0#i128 0#usize (by simp)
    simp only [vec_deref_val, saturating_sub_val] at hden hbound
    simp only [rule_eval.cap.evict, hres, bind_ok]
    have hzero : (0#i128 : Std.I128).val = 0 := by simp
    have hzero' : (0#usize : Usize).val = 0 := by simp
    rw [hzero, hzero', List.drop_zero] at hden
    cases res with
    | Overflow =>
      simp only [evictedOf] at hden
      refine ⟨.Err .Overflow, rfl, ?_⟩
      rw [← hden]
      rfl
    | Stopped keptFrom removed =>
      simp only [evictedOf] at hden
      rw [← hden]
      have hkept := hbound keptFrom removed rfl
      simp only
      cases hcs : I128.checked_sub record.total removed with
      | none =>
        refine ⟨.Err .Overflow, by simp, ?_⟩
        simp [checked_sub_none hcs, denoteSpend, denoteCapError]
      | some remaining =>
        cases hca : I128.checked_add remaining amount with
        | none =>
          refine ⟨.Err .Overflow, by simp [hca], ?_⟩
          simp [checked_sub_some hcs, checked_add_none hca, denoteSpend, denoteCapError]
        | some total =>
          simp only [hca, checked_sub_some hcs]
          simp only [checked_add_some hca]
          by_cases hlim : total > limit
          · have hl : limit.val < total.val := by simpa using hlim
            refine ⟨.Err .LimitExceeded, by simp [hlim], ?_⟩
            simp [hl, denoteSpend, denoteCapError]
          · have hl : ¬ limit.val < total.val := by simpa using hlim
            simp only [hlim, ↓reduceIte, hl]
            have hlen : (alloc.vec.Vec.len record.history).val = record.history.val.length := by
              simp [alloc.vec.Vec.len]
            have hsub := UScalar.sub_spec (x := alloc.vec.Vec.len record.history)
              (y := keptFrom) (by simp only [hlen]; simpa [Slice.length] using hkept)
            revert hsub
            cases hd : alloc.vec.Vec.len record.history - keptFrom with
            | ret d =>
              intro hdv
              have hdv' : d.val = record.history.val.length - keptFrom.val := by
                simp only [hlen] at hdv
                simp at hdv
                exact hdv.1
              have hklen : ((record.history.val.drop keptFrom.val).map denoteEntry).length =
                  d.val := by simp [hdv']
              by_cases hfull : d >= rule_eval.cap.MAX_HISTORY_ENTRIES
              · have hf : Cap.maxHistory ≤ d.val := by
                  simpa [max_history_val] using hfull
                refine ⟨.Err .HistoryFull, by simp only [bind_ok, hfull, ↓reduceIte], ?_⟩
                have hf2 : Cap.maxHistory ≤ record.history.val.length - keptFrom.val :=
                  hdv' ▸ hf
                simp [hf2, denoteSpend, denoteCapError]
              · have hf : ¬ Cap.maxHistory ≤ d.val := by
                  simpa [max_history_val] using hfull
                obtain ⟨v, hv, hvv⟩ := entries_from_eq (alloc.vec.Vec.deref record.history)
                  keptFrom
                simp only [vec_deref_val] at hvv
                have hroom : v.val.length < Usize.max := by
                  have := max_history_lt_usize
                  rw [hvv]
                  simp only [List.length_drop]
                  omega
                obtain ⟨v', hp, hpv⟩ := push_eq v ({ ledger := now, amount } : rule_eval.cap.SpendEntry)
                  hroom
                refine ⟨.Ok { history := v', total },
                  by simp only [bind_ok, hfull, ↓reduceIte, hv, hp], ?_⟩
                have hf2 : ¬ Cap.maxHistory ≤ record.history.val.length - keptFrom.val :=
                  hdv' ▸ hf
                simp [hf2, denoteSpend, denoteRecord, hpv, hvv, denoteEntry]
            | vis e k => intro h; simp at h
            | div => intro h; simp at h

end RuleCore.Equiv
