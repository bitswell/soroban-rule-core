import RuleCore.Model.Cap

/-!
# Spending caps: theorems

About one check (`Params.check`):

* `check_negative`, `check_zero`: a negative amount is refused, and a zero
  amount passes and returns the record unchanged, whatever its total;
* `check_ledgerBeforeNewest_iff`: the clock check refuses a positive spend
  exactly when `now` is earlier than the ledger of the newest recorded entry,
  and `beforeNewest_eq_false_iff` reads that, on a history in ledger order, as
  some entry being after `now`;
* `check_valid`: on a valid record the check keeps the entries after the
  cutoff `now - period` and refuses with `overflow`, `limitExceeded` or
  `historyFull` exactly when the kept total plus the amount does not fit in an
  `i128`, exceeds the limit, or when the kept entries already number
  `maxHistory`;
* `step_of_error`, `run_cons_of_error`: a refused call leaves the record as it
  was.

About runs (`Params.run`, `Params.recorded`), from the empty record unless
stated:

* `check_preserves_valid`, `run_valid`: the check keeps a record valid;
* `window_le_limit`: window safety, for every ledger `t`, the recorded spends
  in the window eviction leaves at `t` sum to at most the limit;
* `period_le_limit_of_pos`: every window of `period` consecutive ledgers
  starting at ledger 1 or later holds at most the limit;
* `period_le_limit`: when every call is at ledger 1 or later, every window of
  `period` consecutive ledgers does;
* `period_ledger_zero`: without that rule the window from ledger 0 can hold
  twice the limit, because the cutoff saturates to 0 and evicts entries at
  ledger 0;
* `window_le_limit_of_valid`: from any valid record, every window holding a
  spend the run recorded holds at most the limit, so a cap installed over an
  existing record bounds every window holding a spend made under it;
* `run_history`, `run_total`, `run_eq_window`: the refinement, the stored
  history is the recorded spends eviction left at the last recorded spend's
  ledger, followed by that spend, and its total is their sum; with a nonzero
  period and that spend at ledger 1 or later, the history is exactly the
  recorded spends in the window at its ledger;
* `run_history_length_le`: a record never holds more than `maxHistory`
  entries;
* `Params.accepts_of_narrower`, `accepts_of_limit_le`, `accepts_of_period_le`,
  `capAccepts_of_capNarrower`: narrowing is trace inclusion, every run a
  narrower cap (a lower limit, a longer period, or a cap where there was none)
  accepts from a valid record, the wider one accepts; `check_of_narrower_suffix`
  is its single step, from records whose histories are suffixes of each other.

None of these assumes anything about the ledgers the calls are made at: the
clock check refuses every positive spend made earlier than the newest recorded
one.
-/

namespace RuleCore.Cap

/-! ## Checked arithmetic -/

theorem i128Min_neg : i128Min < 0 := by decide

theorem i128Max_pos : 0 < i128Max := by decide

theorem addI128_eq_some {a b : Int} (h₁ : i128Min ≤ a + b) (h₂ : a + b ≤ i128Max) :
    addI128 a b = some (a + b) := by
  simp [addI128, h₁, h₂]

theorem addI128_eq_none {a b : Int} (h : i128Max < a + b) : addI128 a b = none := by
  simp only [addI128, ite_eq_right_iff, reduceCtorEq, imp_false, not_and, Int.not_le]
  intro _
  exact h

theorem subI128_eq_some {a b : Int} (h₁ : i128Min ≤ a - b) (h₂ : a - b ≤ i128Max) :
    subI128 a b = some (a - b) := by
  simp [subI128, h₁, h₂]

/-! ## Sums -/

@[simp] theorem amountSum_nil : amountSum [] = 0 := rfl

@[simp] theorem amountSum_cons (e : Entry) (es : List Entry) :
    amountSum (e :: es) = e.amount + amountSum es := by
  simp [amountSum]

@[simp] theorem amountSum_append (as bs : List Entry) :
    amountSum (as ++ bs) = amountSum as + amountSum bs := by
  simp [amountSum]

theorem amountSum_nonneg {es : List Entry} (h : ∀ e ∈ es, 0 < e.amount) : 0 ≤ amountSum es := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [amountSum_cons]
    have := h e (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    omega

theorem amountSum_filter_le {es : List Entry} (h : ∀ e ∈ es, 0 < e.amount) (q : Entry → Bool) :
    amountSum (es.filter q) ≤ amountSum es := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := h e (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    by_cases hq : q e = true <;> simp [hq] <;> omega

/-! ## Eviction -/

theorem evict_eq (cutoff : Nat) :
    ∀ (h : List Entry) (removed : Int), (∀ e ∈ h, 0 < e.amount) → 0 ≤ removed →
      removed + amountSum h ≤ i128Max →
      evict cutoff h removed =
        .ok (h.dropWhile (fun e => decide (e.ledger ≤ cutoff)),
          removed + amountSum (h.takeWhile (fun e => decide (e.ledger ≤ cutoff))))
  | [], removed, _, _, _ => by simp [evict]
  | e :: h, removed, hpos, hr, hmax => by
    have he := hpos e (by simp)
    have hh : ∀ x ∈ h, 0 < x.amount := fun x hx => hpos x (by simp [hx])
    have hs := amountSum_nonneg hh
    simp only [amountSum_cons] at hmax
    by_cases hc : cutoff < e.ledger
    · simp [evict, hc, Nat.not_le.mpr hc]
    · have hadd : addI128 removed e.amount = some (removed + e.amount) :=
        addI128_eq_some (by have := i128Min_neg; omega) (by omega)
      have hle : e.ledger ≤ cutoff := Nat.le_of_not_lt hc
      simp only [evict, hc, ↓reduceIte, hadd]
      rw [evict_eq cutoff h (removed + e.amount) hh (by omega) (by omega)]
      simp [hle, Int.add_assoc]

/-- On a list in ledger order, the entries from the first one after `cutoff` on
are the entries after `cutoff`. -/
theorem dropWhile_eq_filter (cutoff : Nat) :
    ∀ (h : List Entry), h.Pairwise (fun a b => a.ledger ≤ b.ledger) →
      h.dropWhile (fun e => decide (e.ledger ≤ cutoff)) = h.filter (fun e => decide (cutoff < e.ledger))
  | [], _ => rfl
  | e :: h, hs => by
    rw [List.pairwise_cons] at hs
    by_cases hc : e.ledger ≤ cutoff
    · simp only [List.dropWhile_cons, hc, decide_true, List.filter_cons, Nat.not_lt.mpr hc,
        decide_false]
      exact dropWhile_eq_filter cutoff h hs.2
    · have hk : ∀ x ∈ h, cutoff < x.ledger := fun x hx => by have := hs.1 x hx; omega
      simp only [List.dropWhile_cons, hc, decide_false, List.filter_cons, Nat.lt_of_not_le hc,
        decide_true, ↓reduceIte, Bool.false_eq_true]
      congr 1
      exact (List.filter_eq_self.mpr (fun x hx => decide_eq_true (hk x hx))).symm

/-! ## The newest entry -/

@[simp] theorem beforeNewest_nil (now : Nat) : beforeNewest [] now = false := rfl

@[simp] theorem beforeNewest_concat (h : List Entry) (e : Entry) (now : Nat) :
    beforeNewest (h ++ [e]) now = decide (now < e.ledger) := by
  simp [beforeNewest]

/-- On a history in ledger order, `now` is not before the newest entry exactly
when no entry's ledger is after `now`. -/
theorem beforeNewest_eq_false_iff {h : List Entry}
    (hs : h.Pairwise (fun a b => a.ledger ≤ b.ledger)) (now : Nat) :
    beforeNewest h now = false ↔ ∀ e ∈ h, e.ledger ≤ now := by
  rcases List.eq_nil_or_concat h with rfl | ⟨l, b, rfl⟩
  · simp
  · rw [List.concat_eq_append] at hs ⊢
    rw [List.pairwise_append] at hs
    simp only [beforeNewest_concat, decide_eq_false_iff_not, Nat.not_lt, List.mem_append,
      List.mem_singleton]
    constructor
    · rintro hb e (he | rfl)
      · exact Nat.le_trans (hs.2.2 e he b (by simp)) hb
      · exact hb
    · intro hall
      exact hall b (Or.inr rfl)

/-! ## The check on a valid record -/

/-- On a valid record, a positive spend that passes the clock check keeps the
entries after the cutoff `now - period`, and is refused when their total plus
the amount does not fit in an `i128`, exceeds the limit, or when they already
number `maxHistory`. -/
theorem check_valid {p : Params} {r : Record} (hr : r.Valid) {now : Nat} {amount : Int}
    (ha : 0 < amount) (hn : beforeNewest r.history now = false) :
    p.check r now amount =
      let kept := r.history.filter (fun e => decide (now - p.period < e.ledger))
      if i128Max < amountSum kept + amount then .error .overflow
      else if p.limit < amountSum kept + amount then .error .limitExceeded
      else if maxHistory ≤ kept.length then .error .historyFull
      else .ok ⟨kept ++ [⟨now, amount⟩], amountSum kept + amount⟩ := by
  have hsum := hr.total_eq
  have hle := hr.total_le
  have hev := evict_eq (now - p.period) r.history 0 hr.pos (Int.le_refl 0) (by omega)
  have hsplit := List.takeWhile_append_dropWhile (p := fun e => decide (e.ledger ≤ now - p.period))
    (l := r.history)
  have hdrop := dropWhile_eq_filter (now - p.period) r.history hr.sorted
  rw [hdrop] at hev hsplit
  have hkpos : ∀ e ∈ r.history.filter (fun e => decide (now - p.period < e.ledger)),
      0 < e.amount := fun e he => hr.pos e (List.mem_filter.mp he).1
  have htpos : ∀ e ∈ r.history.takeWhile (fun e => decide (e.ledger ≤ now - p.period)),
      0 < e.amount := fun e he => hr.pos e ((List.takeWhile_sublist _).subset he)
  simp only [Params.check, Int.not_lt.mpr (Int.le_of_lt ha), ↓reduceIte, Int.ne_of_gt ha, hn,
    Bool.false_eq_true, hev]
  generalize r.history.filter (fun e => decide (now - p.period < e.ledger)) = kept at *
  generalize r.history.takeWhile (fun e => decide (e.ledger ≤ now - p.period)) = taken at *
  have hsum' : r.total = amountSum taken + amountSum kept := by
    rw [hsum, ← amountSum_append, hsplit]
  have hk0 := amountSum_nonneg hkpos
  have ht0 := amountSum_nonneg htpos
  have hmin := i128Min_neg
  have hsub : subI128 r.total (0 + amountSum taken) = some (amountSum kept) := by
    rw [subI128_eq_some (by omega) (by omega)]
    congr 1
    omega
  simp only [hsub]
  by_cases hover : i128Max < amountSum kept + amount
  · simp [addI128_eq_none hover, hover]
  · rw [addI128_eq_some (by omega) (by omega)]
    simp [hover]

/-! ## Outcomes of one check -/

theorem check_negative (p : Params) (r : Record) (now : Nat) {amount : Int} (h : amount < 0) :
    p.check r now amount = .error .negativeAmount := by
  simp [Params.check, h]

theorem check_zero (p : Params) (r : Record) (now : Nat) : p.check r now 0 = .ok r := by
  simp [Params.check]

theorem evict_error {cutoff : Nat} :
    ∀ {h : List Entry} {removed : Int} {e : CapError},
      evict cutoff h removed = .error e → e = .overflow
  | [], _, _, h => by simp [evict] at h
  | x :: xs, removed, e, h => by
    unfold evict at h
    split at h
    · simp at h
    · split at h
      · exact evict_error h
      · simpa using h.symm

/-- The clock check: a positive spend is refused with `ledgerBeforeNewest`
exactly when `now` is earlier than the ledger of the newest recorded entry. -/
theorem check_ledgerBeforeNewest_iff (p : Params) (r : Record) (now : Nat) {amount : Int}
    (ha : 0 < amount) :
    p.check r now amount = .error .ledgerBeforeNewest ↔ beforeNewest r.history now = true := by
  constructor
  · intro h
    cases hb : beforeNewest r.history now
    · simp only [Params.check, Int.not_lt.mpr (Int.le_of_lt ha), ↓reduceIte, Int.ne_of_gt ha, hb,
        Bool.false_eq_true] at h
      split at h
      · have := evict_error (by assumption)
        simp_all
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · split at h <;> simp at h
    · rfl
  · intro h
    simp [Params.check, Int.not_lt.mpr (Int.le_of_lt ha), Int.ne_of_gt ha, h]

/-- A refused call leaves the record as it was. -/
theorem step_of_error {p : Params} {r : Record} {k : Call} {e : CapError}
    (h : p.check r k.now k.amount = .error e) : p.step r k = r := by
  simp [Params.step, h]

/-- A refused call changes nothing in the rest of the run. -/
theorem run_cons_of_error {p : Params} {r : Record} {k : Call} {e : CapError} (ks : List Call)
    (h : p.check r k.now k.amount = .error e) :
    p.run r (k :: ks) = p.run r ks ∧ p.recorded r (k :: ks) = p.recorded r ks := by
  simp [Params.run, List.foldl_cons, step_of_error h, Params.recorded, h]

/-! ## Valid records -/

@[simp] theorem Record.empty_history : Record.empty.history = [] := rfl

theorem Record.empty_valid : Record.empty.Valid where
  sorted := List.Pairwise.nil
  pos := by simp [Record.empty]
  total_eq := rfl
  total_le := Int.le_of_lt i128Max_pos

/-- What an accepted positive spend does to a valid record: it passed the clock
check, the new history is the entries after the cutoff followed by the new
entry, and the new total is their sum, within the limit and an `i128`. -/
theorem check_pos_ok {p : Params} {r r' : Record} (hr : r.Valid) {now : Nat} {amount : Int}
    (ha : 0 < amount) (h : p.check r now amount = .ok r') :
    beforeNewest r.history now = false ∧
      r'.history = r.history.filter (fun e => decide (now - p.period < e.ledger)) ++ [⟨now, amount⟩] ∧
      r'.total = amountSum r'.history ∧ r'.total ≤ p.limit ∧ r'.total ≤ i128Max ∧
      (r.history.filter (fun e => decide (now - p.period < e.ledger))).length < maxHistory := by
  cases hb : beforeNewest r.history now
  · rw [check_valid hr ha hb] at h
    simp only at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          subst h
          refine ⟨rfl, rfl, by simp, by dsimp only; omega, by dsimp only; omega, by omega⟩
  · have := (check_ledgerBeforeNewest_iff p r now ha).mpr hb
    simp [this] at h

theorem check_preserves_valid {p : Params} {r r' : Record} (hr : r.Valid) {now : Nat}
    {amount : Int} (h : p.check r now amount = .ok r') : r'.Valid := by
  rcases Int.lt_trichotomy amount 0 with hn | rfl | ha
  · simp [check_negative p r now hn] at h
  · simp only [check_zero, Except.ok.injEq] at h
    exact h ▸ hr
  · obtain ⟨hb, hh, ht, -, hle, -⟩ := check_pos_ok hr ha h
    have hall := (beforeNewest_eq_false_iff hr.sorted now).mp hb
    refine ⟨?_, ?_, ht, hle⟩
    · rw [hh, List.pairwise_append]
      refine ⟨hr.sorted.sublist List.filter_sublist, by simp, ?_⟩
      intro a ha' b hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact hall a (List.mem_filter.mp ha').1
    · rw [hh]
      intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hr.pos e (List.mem_filter.mp he).1
      · exact ha

theorem run_valid (p : Params) : ∀ (calls : List Call) {r : Record}, r.Valid → (p.run r calls).Valid
  | [], _, hr => hr
  | k :: ks, r, hr => by
    simp only [Params.run, List.foldl_cons]
    apply run_valid p ks
    unfold Params.step
    split
    · exact check_preserves_valid hr (by assumption)
    · exact hr

/-! ## What a run keeps -/

/-- What a run keeps, for `hist` the entries a record started with followed by
every entry the run has recorded since: the record is valid; no entry of
`hist` is after a ledger that passes the clock check; and at every such ledger,
the window holds the same entries of `hist` as of the record. -/
structure RunInv (p : Params) (r : Record) (hist : List Entry) : Prop where
  valid : r.Valid
  le : ∀ x ∈ hist, ∀ t, beforeNewest r.history t = false → x.ledger ≤ t
  window : ∀ t, beforeNewest r.history t = false →
    hist.filter (p.inWindow t) = r.history.filter (p.inWindow t)

theorem RunInv.start {p : Params} {r : Record} (hr : r.Valid) : RunInv p r r.history where
  valid := hr
  le := fun x hx t ht => (beforeNewest_eq_false_iff hr.sorted t).mp ht x hx
  window := fun _ _ => rfl

/-- Filtering by a window at `t ≥ now` keeps only entries after the cutoff
`now - period`. -/
theorem filter_cutoff_window (p : Params) (h : List Entry) {now t : Nat} (ht : now ≤ t) :
    (h.filter (fun x => decide (now - p.period < x.ledger))).filter (p.inWindow t) =
      h.filter (p.inWindow t) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  unfold Params.inWindow
  by_cases h1 : t - p.period < x.ledger
  · have : now - p.period < x.ledger := Nat.lt_of_le_of_lt (Nat.sub_le_sub_right ht _) h1
    simp [h1, this]
  · simp [h1]

/-- Filtering entries no later than `t` by the window at `t` is filtering by
the cutoff `t - period`. -/
theorem filter_window_eq_cutoff (p : Params) {h : List Entry} {t : Nat}
    (hle : ∀ x ∈ h, x.ledger ≤ t) :
    h.filter (p.inWindow t) = h.filter (fun x => decide (t - p.period < x.ledger)) := by
  apply List.filter_congr
  intro x hx
  simp [Params.inWindow, hle x hx]

/-- One accepted positive spend: the invariant carries over with the new entry
appended; the new history is the entries of `hist` after the cutoff followed by
the new entry; and every window holding the new entry sums to at most the
limit. -/
theorem RunInv.step_pos {p : Params} {r r' : Record} {hist : List Entry} {now : Nat} {amount : Int}
    (hi : RunInv p r hist) (ha : 0 < amount) (h : p.check r now amount = .ok r') :
    RunInv p r' (hist ++ [⟨now, amount⟩]) ∧
      r'.history = hist.filter (fun x => decide (now - p.period < x.ledger)) ++ [⟨now, amount⟩] ∧
      (∀ t, p.inWindow t ⟨now, amount⟩ = true →
        amountSum ((hist ++ [Entry.mk now amount]).filter (p.inWindow t)) ≤ p.limit) := by
  obtain ⟨hb, hh, ht, hlim, -, -⟩ := check_pos_ok hi.valid ha h
  have hr := hi.valid
  have hall_r := (beforeNewest_eq_false_iff hr.sorted now).mp hb
  have hall_h : ∀ x ∈ hist, x.ledger ≤ now := fun x hx => hi.le x hx now hb
  -- A ledger at or after `now` passes the clock check on the old record.
  have hb_t : ∀ t, now ≤ t → beforeNewest r.history t = false := fun t hnt =>
    (beforeNewest_eq_false_iff hr.sorted t).mpr (fun x hx => Nat.le_trans (hall_r x hx) hnt)
  -- It passes on the new record exactly when it is at or after `now`.
  have hb' : ∀ t, beforeNewest r'.history t = false ↔ now ≤ t := by
    intro t
    rw [hh, beforeNewest_concat]
    simp
  have hwin : ∀ t, now ≤ t →
      hist.filter (p.inWindow t) =
        (r.history.filter (fun e => decide (now - p.period < e.ledger))).filter (p.inWindow t) := by
    intro t hnt
    rw [hi.window t (hb_t t hnt), filter_cutoff_window p _ hnt]
  have hkept : hist.filter (fun x => decide (now - p.period < x.ledger)) =
      r.history.filter (fun e => decide (now - p.period < e.ledger)) := by
    rw [← filter_window_eq_cutoff p hall_h, hwin now (Nat.le_refl _),
      filter_cutoff_window p _ (Nat.le_refl _), filter_window_eq_cutoff p hall_r]
  refine ⟨RunInv.mk (check_preserves_valid hr h) ?_ ?_, by rw [hh, hkept], ?_⟩
  · intro x hx t ht'
    have hnt := (hb' t).mp ht'
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Nat.le_trans (hall_h x hx) hnt
    · exact hnt
  · intro t ht'
    have hnt := (hb' t).mp ht'
    rw [List.filter_append, hwin t hnt, hh, List.filter_append]
  · intro t hwt
    have hnt : now ≤ t := by
      simp only [Params.inWindow, Bool.and_eq_true, decide_eq_true_eq] at hwt
      exact hwt.2
    have hkpos : ∀ e ∈ r.history.filter (fun e => decide (now - p.period < e.ledger)),
        0 < e.amount := fun e he => hr.pos e (List.mem_filter.mp he).1
    rw [List.filter_append, hwin t hnt, amountSum_append]
    have h1 := amountSum_filter_le hkpos (p.inWindow t)
    have h2 : amountSum ([⟨now, amount⟩].filter (p.inWindow t)) = amount := by
      simp [hwt]
    rw [ht, hh, amountSum_append] at hlim
    simp only [amountSum_cons, amountSum_nil, Int.add_zero] at hlim
    omega

@[simp] theorem run_nil (p : Params) (r : Record) : p.run r [] = r := rfl

theorem run_cons (p : Params) (r : Record) (k : Call) (ks : List Call) :
    p.run r (k :: ks) = p.run (p.step r k) ks := rfl

@[simp] theorem recorded_nil (p : Params) (r : Record) : p.recorded r [] = [] := rfl

/-- A whole run from `r`, with `hist` the entries `r` started from and `new`
the entries recorded before: the invariant holds at the end with every
recorded entry appended; every window holding a recorded entry sums to at most
the limit; a run that records nothing leaves the record as it was; and the
final history is the entries eviction left at the last recorded entry's
ledger, followed by that entry. -/
theorem run_spec (p : Params) : ∀ (calls : List Call) (r : Record) (hist new : List Entry),
    RunInv p r hist →
    (∀ t, (∃ x ∈ new, p.inWindow t x = true) → amountSum (hist.filter (p.inWindow t)) ≤ p.limit) →
    RunInv p (p.run r calls) (hist ++ p.recorded r calls) ∧
      (∀ t, (∃ x ∈ new ++ p.recorded r calls, p.inWindow t x = true) →
        amountSum ((hist ++ p.recorded r calls).filter (p.inWindow t)) ≤ p.limit) ∧
      (p.recorded r calls = [] → p.run r calls = r) ∧
      (∀ A e, p.recorded r calls = A ++ [e] →
        (p.run r calls).history =
          (hist ++ A).filter (fun x => decide (e.ledger - p.period < x.ledger)) ++ [e])
  | [], r, hist, new, hi, hd => by
    refine ⟨by simpa using hi, by simpa using hd, fun _ => rfl, ?_⟩
    intro A e h
    simp at h
  | k :: ks, r, hist, new, hi, hd => by
    rw [run_cons]
    unfold Params.recorded
    cases hc : p.check r k.now k.amount with
    | error e =>
      simp only [Params.step, hc]
      exact run_spec p ks r hist new hi hd
    | ok r' =>
      simp only [Params.step, hc]
      by_cases ha : 0 < k.amount
      · obtain ⟨hi', hh, hw⟩ := hi.step_pos ha hc
        have hd' : ∀ t, (∃ x ∈ new ++ [Entry.mk k.now k.amount], p.inWindow t x = true) →
            amountSum ((hist ++ [Entry.mk k.now k.amount]).filter (p.inWindow t)) ≤ p.limit := by
          intro t ⟨x, hx, hxt⟩
          by_cases hwe : p.inWindow t ⟨k.now, k.amount⟩ = true
          · exact hw t hwe
          · have hx' : x ∈ new := by
              simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | rfl
              · exact hx
              · exact absurd hxt hwe
            rw [List.filter_append]
            simp only [List.filter_cons, hwe, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
              List.append_nil]
            exact hd t ⟨x, hx', hxt⟩
        obtain ⟨h1, h2, h3, h4⟩ := run_spec p ks r' (hist ++ [⟨k.now, k.amount⟩])
          (new ++ [⟨k.now, k.amount⟩]) hi' hd'
        simp only [ha, ↓reduceIte, List.singleton_append]
        refine ⟨by simpa using h1, by simpa using h2, fun h => by simp at h, ?_⟩
        intro A e he
        rcases List.eq_nil_or_concat (p.recorded r' ks) with hn | ⟨A', e', hc'⟩
        · rw [hn] at he
          have he0 : ([] : List Entry) ++ [Entry.mk k.now k.amount] = A ++ [e] := by simpa using he
          obtain ⟨rfl, he'⟩ := List.append_inj' he0 (by simp)
          simp only [List.cons.injEq, and_true] at he'
          subst he'
          rw [h3 hn, hh]
          simp
        · rw [List.concat_eq_append] at hc'
          rw [hc'] at he
          have he0 : (Entry.mk k.now k.amount :: A') ++ [e'] = A ++ [e] := by simpa using he
          obtain ⟨rfl, he'⟩ := List.append_inj' he0 (by simp)
          simp only [List.cons.injEq, and_true] at he'
          subst he'
          rw [h4 A' e' hc']
          simp
      · have hz : k.amount = 0 := by
          rcases Int.lt_trichotomy k.amount 0 with hn | hz | hp
          · simp [check_negative p r k.now hn] at hc
          · exact hz
          · exact absurd hp ha
        have hr' : r' = r := by
          rw [hz, check_zero] at hc
          exact (Except.ok.inj hc).symm
        subst hr'
        simp only [ha, ↓reduceIte, List.nil_append]
        exact run_spec p ks r' hist new hi hd

/-- Every recorded entry is a call of the run. -/
theorem mem_recorded (p : Params) : ∀ {calls : List Call} {r : Record} {x : Entry},
    x ∈ p.recorded r calls → ∃ k ∈ calls, x = ⟨k.now, k.amount⟩
  | [], _, _, h => by simp at h
  | k :: ks, r, x, h => by
    unfold Params.recorded at h
    split at h
    · simp only [List.mem_append] at h
      rcases h with h | h
      · split at h
        · simp only [List.mem_singleton] at h
          exact ⟨k, by simp, h⟩
        · simp at h
      · obtain ⟨k', hk', rfl⟩ := mem_recorded p h
        exact ⟨k', by simp [hk'], rfl⟩
    · obtain ⟨k', hk', rfl⟩ := mem_recorded p h
      exact ⟨k', by simp [hk'], rfl⟩

/-! ## Window safety -/

/-- From a valid record, every window holding a spend the run recorded sums,
over the record's entries and the recorded ones, to at most the limit. So a
cap installed over an existing record (a lowered limit, say) bounds every
window holding a spend made under it. -/
theorem window_le_limit_of_valid (p : Params) {r : Record} (hr : r.Valid) (calls : List Call)
    (t : Nat) (h : ∃ x ∈ p.recorded r calls, p.inWindow t x = true) :
    amountSum ((r.history ++ p.recorded r calls).filter (p.inWindow t)) ≤ p.limit :=
  (run_spec p calls r r.history [] (RunInv.start hr) (by simp)).2.1 t (by simpa using h)

/-- Window safety: from the empty record, the recorded spends in the window
that eviction leaves at any ledger `t` sum to at most the limit. -/
theorem window_le_limit (p : Params) (hl : 0 ≤ p.limit) (calls : List Call) (t : Nat) :
    amountSum ((p.recorded .empty calls).filter (p.inWindow t)) ≤ p.limit := by
  by_cases h : ∃ x ∈ p.recorded .empty calls, p.inWindow t x = true
  · simpa [Record.empty] using window_le_limit_of_valid p Record.empty_valid calls t h
  · have : (p.recorded .empty calls).filter (p.inWindow t) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx hxt
      exact h ⟨x, hx, hxt⟩
    simp [this, hl]

/-- The `period` consecutive ledgers from `s` are the window eviction leaves at
`s + period - 1`, for every entry when `s` is at least 1, and for entries at
ledger 1 or later when `s` is 0. -/
theorem inPeriodFrom_eq_inWindow (p : Params) (hp : 0 < p.period) {s : Nat} {e : Entry}
    (h : 0 < s ∨ 0 < e.ledger) :
    p.inPeriodFrom s e = p.inWindow (s + p.period - 1) e := by
  rw [Bool.eq_iff_iff]
  simp only [Params.inPeriodFrom, Params.inWindow, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem filter_inPeriodFrom_period_zero (p : Params) (hp : p.period = 0) (s : Nat)
    (es : List Entry) : es.filter (p.inPeriodFrom s) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x _
  simp only [Params.inPeriodFrom, hp, Nat.add_zero, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- Every window of `period` consecutive ledgers starting at ledger 1 or later
holds recorded spends summing to at most the limit. -/
theorem period_le_limit_of_pos (p : Params) (hl : 0 ≤ p.limit) (calls : List Call) {s : Nat}
    (hs : 0 < s) :
    amountSum ((p.recorded .empty calls).filter (p.inPeriodFrom s)) ≤ p.limit := by
  rcases Nat.eq_zero_or_pos p.period with hp | hp
  · simp [filter_inPeriodFrom_period_zero p hp, hl]
  · rw [List.filter_congr (fun x _ => inPeriodFrom_eq_inWindow p hp (Or.inl hs))]
    exact window_le_limit p hl calls _

/-- When every call is at ledger 1 or later, every window of `period`
consecutive ledgers holds recorded spends summing to at most the limit.
Stellar's ledgers start at 1. -/
theorem period_le_limit (p : Params) (hl : 0 ≤ p.limit) (calls : List Call)
    (h1 : ∀ k ∈ calls, 0 < k.now) (s : Nat) :
    amountSum ((p.recorded .empty calls).filter (p.inPeriodFrom s)) ≤ p.limit := by
  rcases Nat.eq_zero_or_pos p.period with hp | hp
  · simp [filter_inPeriodFrom_period_zero p hp, hl]
  · rw [List.filter_congr (fun x hx => inPeriodFrom_eq_inWindow p hp (Or.inr (by
      obtain ⟨k, hk, rfl⟩ := mem_recorded p hx
      exact h1 k hk)))]
    exact window_le_limit p hl calls _

/-- At ledger 0 the cutoff saturates to 0 and evicts entries at ledger 0, so
each spend at ledger 0 is checked alone: two spends of the whole limit at
ledger 0 are both recorded, and the window of `period` ledgers from 0 holds
twice the limit. -/
theorem period_ledger_zero :
    (⟨100, 10⟩ : Params).valid = true ∧
      (⟨100, 10⟩ : Params).recorded .empty [⟨0, 100⟩, ⟨0, 100⟩] = [⟨0, 100⟩, ⟨0, 100⟩] ∧
      amountSum (((⟨100, 10⟩ : Params).recorded .empty [⟨0, 100⟩, ⟨0, 100⟩]).filter
        ((⟨100, 10⟩ : Params).inPeriodFrom 0)) = 200 := by
  decide

/-! ## The record is the recorded spends in the window -/

/-- A run that records nothing leaves the record as it was. -/
theorem run_eq_of_recorded_nil (p : Params) {r : Record} (hr : r.Valid) (calls : List Call)
    (h : p.recorded r calls = []) : p.run r calls = r :=
  (run_spec p calls r r.history [] (RunInv.start hr) (by simp)).2.2.1 h

/-- After a run from a valid record, the history is the entries eviction left
at the ledger of the last recorded spend, of the record's entries and the
spends recorded before it, followed by that spend. -/
theorem run_history (p : Params) {r : Record} (hr : r.Valid) (calls : List Call)
    {A : List Entry} {e : Entry} (h : p.recorded r calls = A ++ [e]) :
    (p.run r calls).history =
      (r.history ++ A).filter (fun x => decide (e.ledger - p.period < x.ledger)) ++ [e] :=
  (run_spec p calls r r.history [] (RunInv.start hr) (by simp)).2.2.2 A e h

/-- After a run from a valid record, the total is the sum of the history. -/
theorem run_total (p : Params) {r : Record} (hr : r.Valid) (calls : List Call) :
    (p.run r calls).total = amountSum (p.run r calls).history :=
  (run_valid p calls hr).total_eq

/-- The refinement: from the empty record, with a nonzero period and the last
recorded spend at ledger 1 or later, the stored history is exactly the
recorded spends in the window at that spend's ledger, and the stored total is
their sum. -/
theorem run_eq_window (p : Params) (hp : 0 < p.period) (calls : List Call) {A : List Entry}
    {e : Entry} (h : p.recorded .empty calls = A ++ [e]) (he : 0 < e.ledger) :
    (p.run .empty calls).history = (p.recorded .empty calls).filter (p.inWindow e.ledger) ∧
      (p.run .empty calls).total = amountSum ((p.recorded .empty calls).filter (p.inWindow e.ledger)) := by
  have hh := run_history p Record.empty_valid calls h
  simp only [Record.empty_history, List.nil_append] at hh
  have hi := (run_spec p calls .empty [] [] (RunInv.start Record.empty_valid) (by simp)).1
  simp only [List.nil_append] at hi
  have hb : beforeNewest (p.run .empty calls).history e.ledger = false := by
    rw [hh, beforeNewest_concat]
    simp
  have hle : ∀ x ∈ A, x.ledger ≤ e.ledger := fun x hx =>
    hi.le x (by rw [h]; simp [hx]) e.ledger hb
  have hwe : p.inWindow e.ledger e = true := by
    simp only [Params.inWindow, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hhist : (p.run .empty calls).history = (p.recorded .empty calls).filter (p.inWindow e.ledger) := by
    rw [hh, h, List.filter_append, filter_window_eq_cutoff p hle]
    simp [hwe]
  refine ⟨hhist, ?_⟩
  rw [run_total p Record.empty_valid calls, hhist]

/-- A record never holds more than `maxHistory` entries. -/
theorem run_history_length_le (p : Params) {r : Record} (hr : r.Valid)
    (hlen : r.history.length ≤ maxHistory) :
    ∀ calls : List Call, (p.run r calls).history.length ≤ maxHistory := by
  intro calls
  induction calls generalizing r with
  | nil => exact hlen
  | cons k ks ih =>
    rw [run_cons]
    unfold Params.step
    split
    · rename_i r' hc
      apply ih (check_preserves_valid hr hc)
      rcases Int.lt_trichotomy k.amount 0 with hn | hz | hpos
      · simp [check_negative p r k.now hn] at hc
      · rw [hz, check_zero] at hc
        obtain rfl := Except.ok.inj hc
        exact hlen
      · obtain ⟨-, hh, -, -, -, hl⟩ := check_pos_ok hr hpos hc
        rw [hh, List.length_append]
        simp only [List.length_singleton]
        omega
    · exact ih hr hlen

/-! ## Narrowing is trace inclusion -/

theorem Params.narrower_refl (p : Params) : p.narrower p :=
  ⟨Int.le_refl _, Nat.le_refl _⟩

theorem Params.narrower_trans {c b a : Params} (h₁ : c.narrower b) (h₂ : b.narrower a) :
    c.narrower a :=
  ⟨Int.le_trans h₁.1 h₂.1, Nat.le_trans h₂.2 h₁.2⟩

theorem runAll_nil (p : Params) (r : Record) : p.runAll r [] = .ok r := rfl

theorem runAll_cons (p : Params) (r : Record) (k : Call) (ks : List Call) :
    p.runAll r (k :: ks) =
      match p.check r k.now k.amount with
      | .ok r' => p.runAll r' ks
      | .error e => .error e := by
  simp only [Params.runAll, List.foldlM_cons]
  cases p.check r k.now k.amount <;> rfl

theorem accepts_cons_iff (p : Params) (r : Record) (k : Call) (ks : List Call) :
    p.Accepts r (k :: ks) ↔ ∃ r', p.check r k.now k.amount = .ok r' ∧ p.Accepts r' ks := by
  simp only [Params.Accepts, runAll_cons]
  cases p.check r k.now k.amount <;> simp

/-- On a history in ledger order, a later cutoff keeps a suffix of what an
earlier one keeps. -/
theorem filter_cutoff_suffix {c₁ c₂ : Nat} (hc : c₁ ≤ c₂) :
    ∀ (h : List Entry), h.Pairwise (fun a b => a.ledger ≤ b.ledger) →
      h.filter (fun x => decide (c₂ < x.ledger)) <:+ h.filter (fun x => decide (c₁ < x.ledger))
  | [], _ => List.suffix_refl _
  | e :: h, hs => by
    rw [List.pairwise_cons] at hs
    have ih := filter_cutoff_suffix hc h hs.2
    by_cases h₁ : c₁ < e.ledger
    · by_cases h₂ : c₂ < e.ledger
      · have hk : ∀ c, c < e.ledger → h.filter (fun x => decide (c < x.ledger)) = h :=
          fun c hce => List.filter_eq_self.mpr (fun x hx => decide_eq_true
            (Nat.lt_of_lt_of_le hce (hs.1 x hx)))
        simp only [List.filter_cons, h₁, h₂, decide_true, ↓reduceIte, hk c₁ h₁, hk c₂ h₂]
        exact List.suffix_refl _
      · simp only [List.filter_cons, h₁, h₂, decide_true, decide_false, ↓reduceIte,
          Bool.false_eq_true]
        exact ih.trans (List.suffix_cons _ _)
    · have h₂ : ¬ c₂ < e.ledger := fun h' => h₁ (Nat.lt_of_le_of_lt hc h')
      simp only [List.filter_cons, h₁, h₂, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih

theorem amountSum_suffix_le {as bs : List Entry} (h : as <:+ bs) (hpos : ∀ e ∈ bs, 0 < e.amount) :
    amountSum as ≤ amountSum bs := by
  obtain ⟨t, rfl⟩ := h
  have : 0 ≤ amountSum t := amountSum_nonneg (fun e he => hpos e (by simp [he]))
  simp only [amountSum_append]
  omega

/-- One check under a narrower cap: when the narrower cap `q` accepts a spend
from `rq`, the wider cap `p` accepts it from any valid `rp` whose history is a
suffix of `rq`'s, and its history stays a suffix of the one `q` leaves. -/
theorem check_of_narrower_suffix {q p : Params} (hqp : q.narrower p) {rq rp rq' : Record}
    (hq : rq.Valid) (hp : rp.Valid) (hs : rp.history <:+ rq.history) {now : Nat} {amount : Int}
    (hcq : q.check rq now amount = .ok rq') :
    ∃ rp', p.check rp now amount = .ok rp' ∧ rp'.history <:+ rq'.history := by
  rcases Int.lt_trichotomy amount 0 with hn | hz | hpos
  · simp [check_negative q rq now hn] at hcq
  · rw [hz, check_zero] at hcq ⊢
    obtain rfl := Except.ok.inj hcq
    exact ⟨rp, rfl, hs⟩
  · obtain ⟨hbq, hhq, htq, hlq, hmq, hlenq⟩ := check_pos_ok hq hpos hcq
    have hbp : beforeNewest rp.history now = false := by
      rw [beforeNewest_eq_false_iff hp.sorted]
      exact fun x hx => (beforeNewest_eq_false_iff hq.sorted now).mp hbq x (hs.subset hx)
    have hsuf : rp.history.filter (fun x => decide (now - p.period < x.ledger)) <:+
        rq.history.filter (fun x => decide (now - q.period < x.ledger)) :=
      (filter_cutoff_suffix (Nat.sub_le_sub_left hqp.2 _) rp.history hp.sorted).trans
        (hs.filter _)
    have hkpos : ∀ e ∈ rq.history.filter (fun x => decide (now - q.period < x.ledger)),
        0 < e.amount := fun e he => hq.pos e (List.mem_filter.mp he).1
    have hsum := amountSum_suffix_le hsuf hkpos
    have hlen := hsuf.length_le
    rw [htq, hhq, amountSum_append] at hlq hmq
    simp only [amountSum_cons, amountSum_nil, Int.add_zero] at hlq hmq
    have hl := hqp.1
    have hcp : p.check rp now amount =
        .ok ⟨rp.history.filter (fun x => decide (now - p.period < x.ledger)) ++
            [⟨now, amount⟩],
          amountSum (rp.history.filter (fun x => decide (now - p.period < x.ledger))) +
            amount⟩ := by
      rw [check_valid hp hpos hbp]
      simp only [show ¬ i128Max < amountSum (rp.history.filter
          (fun x => decide (now - p.period < x.ledger))) + amount by omega,
        show ¬ p.limit < amountSum (rp.history.filter
          (fun x => decide (now - p.period < x.ledger))) + amount by omega,
        show ¬ maxHistory ≤ (rp.history.filter
          (fun x => decide (now - p.period < x.ledger))).length by omega, ↓reduceIte]
    refine ⟨_, hcp, ?_⟩
    rw [hhq]
    obtain ⟨t, ht⟩ := hsuf
    exact ⟨t, by rw [← ht, List.append_assoc]⟩

theorem accepts_of_narrower_suffix {q p : Params} (hqp : q.narrower p) :
    ∀ (calls : List Call) (rq rp : Record), rq.Valid → rp.Valid → rp.history <:+ rq.history →
      q.Accepts rq calls → p.Accepts rp calls
  | [], _, rp, _, _, _, _ => ⟨rp, rfl⟩
  | k :: ks, rq, rp, hq, hp, hs, ha => by
    rw [accepts_cons_iff] at ha ⊢
    obtain ⟨rq', hcq, ha'⟩ := ha
    obtain ⟨rp', hcp, hs'⟩ := check_of_narrower_suffix hqp hq hp hs hcq
    exact ⟨rp', hcp, accepts_of_narrower_suffix hqp ks rq' rp' (check_preserves_valid hq hcq)
      (check_preserves_valid hp hcp) hs' ha'⟩

/-- Narrowing is trace inclusion: every run a narrower cap accepts from a
valid record, the wider cap accepts too. -/
theorem Params.accepts_of_narrower {q p : Params} (h : q.narrower p) {r : Record} (hr : r.Valid)
    {calls : List Call} (ha : q.Accepts r calls) : p.Accepts r calls :=
  accepts_of_narrower_suffix h calls r r hr hr (List.suffix_refl _) ha

/-- Lowering the limit narrows: every run accepted under the lower limit is
accepted under the higher one. -/
theorem accepts_of_limit_le {p : Params} {limit : Int} (h : limit ≤ p.limit) {r : Record}
    (hr : r.Valid) {calls : List Call} (ha : (⟨limit, p.period⟩ : Params).Accepts r calls) :
    p.Accepts r calls :=
  Params.accepts_of_narrower (q := ⟨limit, p.period⟩) (p := p) ⟨h, Nat.le_refl _⟩ hr ha

/-- Lengthening the period narrows: every run accepted under the longer period
is accepted under the shorter one. -/
theorem accepts_of_period_le {p : Params} {period : Nat} (h : p.period ≤ period) {r : Record}
    (hr : r.Valid) {calls : List Call} (ha : (⟨p.limit, period⟩ : Params).Accepts r calls) :
    p.Accepts r calls :=
  Params.accepts_of_narrower (q := ⟨p.limit, period⟩) (p := p) ⟨Int.le_refl _, h⟩ hr ha

/-- Adding a cap or narrowing one is trace inclusion: every run the narrower
cap accepts, the wider one accepts, and a rule without a cap accepts every
run. -/
theorem capAccepts_of_capNarrower {q p : Option Params} (h : capNarrower q p) {r : Record}
    (hr : r.Valid) {calls : List Call} (ha : capAccepts q r calls) : capAccepts p r calls := by
  match q, p, h with
  | _, none, _ => trivial
  | some _, some _, h => exact Params.accepts_of_narrower h hr ha

end RuleCore.Cap
