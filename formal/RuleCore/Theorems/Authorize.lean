import RuleCore.Model.Authorize
import RuleCore.Theorems.Attenuation
import RuleCore.Theorems.Cap

/-!
# Authorization: theorems

One authorization (`RuleSet.authorize`):

* `RuleSet.authorize_eq_ok_iff`: what an accepted authorization is, pass by
  pass;
* `RuleSet.authorize_chosen`: every context is allowed by the rule chosen for
  it, under the authorization's signers;
* `RuleSet.authorize_allowsAll`: so the rule set allows the whole batch under
  them; the stateful check is sound with respect to `allowsAll`;
* `RuleSet.authorize_length`: the records keep one record per rule;
* `RuleSet.step_of_error`: a refused authorization leaves the records as they
  were, the charges of its earlier contexts included.

Runs from records holding one record per rule (`RuleSet.run`), for a rule `j`
with cap `k`:

* `RuleSet.run_get`: the stored record of `j` is the cap check's own run
  (`Cap.Params.run`) over the calls the run charges to `j`;
* `RuleSet.run_get_of_cap_none`: a rule without a cap keeps its record;
* `RuleSet.spent_eq_recorded`: the spends recorded there are the ones the cap
  check records over those calls.

From empty records (`RuleSet.emptyRecords`), carrying the cap theorems of
`RuleCore.Theorems.Cap` over:

* `RuleSet.window_le_limit`: window safety, the spends a run records for `j`
  in the window eviction leaves at any ledger sum to at most the limit;
* `RuleSet.period_le_limit_of_pos`, `RuleSet.period_le_limit`: every window of
  `period` consecutive ledgers starting at ledger 1 or later holds at most the
  limit, and so does every window when every authorization is at ledger 1 or
  later;
* `RuleSet.run_eq_window`: the stored record of `j` is exactly the spends in
  the window at its last spend's ledger, with their sum as total;
* `RuleSet.run_history_length_le`: it never holds more than `Cap.maxHistory`
  entries.

Narrowing as trace inclusion (`RuleSet.TraceNarrower`):

* `RuleSet.Refines.traceNarrower`: a rule set whose every rule, renumbered by
  a one-to-one `f`, allows no more than its counterpart and carries a cap at
  least as narrow (`RuleSet.Refines`) accepts no run the other does not;
* `RuleSet.attenuate_refines`, `RuleSet.attenuateAll_refines`: each of the
  eight steps, and every list of them, refines along `Attenuation.source` and
  `Attenuation.chainSource`;
* `RuleSet.attenuate_traceNarrower`, `RuleSet.attenuateAll_traceNarrower`: so
  each step, and every chain of steps, is narrowing as trace inclusion, each
  side holding its own records from empty, with the choices renumbered by the
  map `dropRule` induces (`Attenuation.source_dropRule`,
  `Attenuation.source_eq_of_ne_dropRule`);
* `RuleSet.TraceNarrower.refl`, `RuleSet.TraceNarrower.trans`: trace inclusion
  is reflexive and composes, with the renumberings composed;
* `RuleSet.attenuate_capsValid`, `RuleSet.attenuateAll_capsValid`: the steps
  keep every cap valid.

None of these assumes anything about the ledgers the authorizations are made
at, except `period_le_limit`, which takes the stated rule that ledgers start
at 1.
-/

namespace RuleCore

variable {Ctx Sig : Type}

/-! ## The monad -/

theorem forM_except_ok_iff {α ε : Type} (f : α → Except ε Unit) :
    ∀ (l : List α), l.forM f = .ok () ↔ ∀ x ∈ l, f x = .ok ()
  | [] => by simp [List.forM, pure, Except.pure]
  | a :: l => by
    unfold List.forM
    cases h : f a with
    | error e => simp [h, bind, Except.bind]
    | ok u =>
      cases u
      simp only [bind, Except.bind, List.mem_cons, forall_eq_or_imp, h, true_and]
      exact forM_except_ok_iff f l

theorem foldlM_except_cons {α β ε : Type} (f : β → α → Except ε β) (b : β) (a : α)
    (l : List α) :
    (a :: l).foldlM f b = match f b a with
      | .ok b' => l.foldlM f b'
      | .error e => .error e := by
  rw [List.foldlM_cons]
  cases f b a <;> rfl

theorem foldlM_except_append {α β ε : Type} (f : β → α → Except ε β) :
    ∀ (l₁ l₂ : List α) (b : β), (l₁ ++ l₂).foldlM f b =
      match l₁.foldlM f b with
      | .ok b' => l₂.foldlM f b'
      | .error e => .error e
  | [], l₂, b => by simp only [List.nil_append, List.foldlM_nil]; rfl
  | a :: l₁, l₂, b => by
    rw [List.cons_append, foldlM_except_cons, foldlM_except_cons]
    cases f b a with
    | ok b' => exact foldlM_except_append f l₁ l₂ b'
    | error e => rfl

/-! ## One authorization -/

theorem Authorization.map_fst_chosen {a : Authorization Ctx Sig}
    (h : a.choices.length = a.contexts.length) : a.chosen.map Prod.fst = a.contexts :=
  List.map_fst_zip (Nat.le_of_eq h.symm)

theorem Authorization.length_chosen {a : Authorization Ctx Sig}
    (h : a.choices.length = a.contexts.length) : a.chosen.length = a.contexts.length := by
  simp [Authorization.chosen, List.length_zip, h]

section

variable [DecidableEq Sig]

theorem RuleSet.checkChoice_ok_iff (rs : RuleSet Ctx Sig) (auth : List Sig) (x : Ctx × Nat) :
    rs.checkChoice auth x = .ok () ↔ ∃ r, rs.rules[x.2]? = some r ∧ r.allows x.1 auth = true := by
  unfold RuleSet.checkChoice
  split <;> rename_i h
  · split <;> rename_i ha
    · simp [h, ha]
    · simp [h, ha]
  · simp [h]

/-- An accepted authorization, pass by pass: its choices and records have the
right lengths, every chosen rule exists and allows its context, and the
charges in context order build the new records. -/
theorem RuleSet.authorize_eq_ok_iff (rs : RuleSet Ctx Sig) (records records' : List Cap.Record)
    (a : Authorization Ctx Sig) :
    rs.authorize records a = .ok records' ↔
      a.choices.length = a.contexts.length ∧ records.length = rs.rules.length ∧
        (∀ x ∈ a.chosen, rs.checkChoice a.auth x = .ok ()) ∧
        a.chosen.foldlM (rs.charge a.now) records = .ok records' := by
  unfold RuleSet.authorize
  by_cases hc : a.choices.length = a.contexts.length
  · by_cases hr : records.length = rs.rules.length
    · simp only [hc, hr, ne_eq, not_true_eq_false, ↓reduceIte, true_and]
      rw [← forM_except_ok_iff]
      cases hf : a.chosen.forM (rs.checkChoice a.auth) with
      | error e => simp [bind, Except.bind]
      | ok u =>
        cases u
        simp [bind, Except.bind]
    · simp [hc, hr]
  · simp [hc]

/-- Every context of an accepted authorization is allowed by the rule chosen
for it, under the authorization's signers. -/
theorem RuleSet.authorize_chosen {rs : RuleSet Ctx Sig} {records records' : List Cap.Record}
    {a : Authorization Ctx Sig} (h : rs.authorize records a = .ok records') :
    ∀ x ∈ a.chosen, ∃ r, rs.rules[x.2]? = some r ∧ r.allows x.1 a.auth = true := by
  obtain ⟨-, -, hk, -⟩ := (rs.authorize_eq_ok_iff records records' a).mp h
  exact fun x hx => (rs.checkChoice_ok_iff a.auth x).mp (hk x hx)

/-- Soundness of the stateful check: a rule set that accepts an authorization
allows its whole batch under its signers. -/
theorem RuleSet.authorize_allowsAll {rs : RuleSet Ctx Sig} {records records' : List Cap.Record}
    {a : Authorization Ctx Sig} (h : rs.authorize records a = .ok records') :
    rs.allowsAll a.contexts a.auth = true := by
  obtain ⟨hc, -, -, -⟩ := (rs.authorize_eq_ok_iff records records' a).mp h
  rw [RuleSet.allowsAll_iff]
  intro c hcm
  rw [← Authorization.map_fst_chosen hc, List.mem_map] at hcm
  obtain ⟨x, hx, rfl⟩ := hcm
  obtain ⟨r, hr, ha⟩ := RuleSet.authorize_chosen h x hx
  exact (RuleSet.allows_iff rs x.1 a.auth).mpr ⟨r, List.mem_of_getElem? hr, ha⟩

end

theorem RuleSet.charge_length {rs : RuleSet Ctx Sig} {now : Nat}
    {records records' : List Cap.Record} {x : Ctx × Nat}
    (h : rs.charge now records x = .ok records') : records'.length = records.length := by
  unfold RuleSet.charge at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · cases h
            simp
          · cases h
        · cases h
      · cases h
    · cases h
      rfl
  · cases h

theorem RuleSet.foldlM_charge_length {rs : RuleSet Ctx Sig} {now : Nat} :
    ∀ (l : List (Ctx × Nat)) (records records' : List Cap.Record),
      l.foldlM (rs.charge now) records = .ok records' → records'.length = records.length
  | [], records, records', h => by
    simp only [List.foldlM_nil] at h
    cases h
    rfl
  | x :: l, records, records', h => by
    rw [foldlM_except_cons] at h
    cases hc : rs.charge now records x with
    | error e => rw [hc] at h; cases h
    | ok r₁ =>
      rw [hc] at h
      rw [RuleSet.foldlM_charge_length l r₁ records' h, RuleSet.charge_length hc]

section

variable [DecidableEq Sig]

/-- An accepted authorization keeps one record per rule. -/
theorem RuleSet.authorize_length {rs : RuleSet Ctx Sig} {records records' : List Cap.Record}
    {a : Authorization Ctx Sig} (h : rs.authorize records a = .ok records') :
    records'.length = rs.rules.length := by
  obtain ⟨-, hr, -, hf⟩ := (rs.authorize_eq_ok_iff records records' a).mp h
  rw [RuleSet.foldlM_charge_length _ _ _ hf, hr]

/-- A refused authorization leaves the records as they were. -/
theorem RuleSet.step_of_error {rs : RuleSet Ctx Sig} {records : List Cap.Record}
    {a : Authorization Ctx Sig} {e : Refusal} (h : rs.authorize records a = .error e) :
    rs.step records a = records := by
  simp [RuleSet.step, h]

end

/-! ## Runs of the cap check -/

namespace Cap

theorem run_of_runAll {p : Params} :
    ∀ {calls : List Call} {r r' : Record}, p.runAll r calls = .ok r' → p.run r calls = r'
  | [], r, r', h => by
    simp only [runAll_nil] at h
    cases h
    rfl
  | k :: ks, r, r', h => by
    rw [runAll_cons] at h
    rw [run_cons]
    cases hc : p.check r k.now k.amount with
    | error e => rw [hc] at h; cases h
    | ok r₁ =>
      rw [hc] at h
      simp only [Params.step, hc]
      exact run_of_runAll h

/-- A run the check accepts call by call records exactly its positive calls. -/
theorem recorded_of_runAll {p : Params} :
    ∀ {calls : List Call} {r r' : Record}, p.runAll r calls = .ok r' →
      p.recorded r calls =
        (calls.filter (fun x => decide (0 < x.amount))).map fun x => ⟨x.now, x.amount⟩
  | [], _, _, _ => rfl
  | k :: ks, r, r', h => by
    rw [runAll_cons] at h
    unfold Params.recorded
    cases hc : p.check r k.now k.amount with
    | error e => rw [hc] at h; cases h
    | ok r₁ =>
      rw [hc] at h
      simp only [recorded_of_runAll h, List.filter_cons]
      by_cases ha : 0 < k.amount <;> simp [ha]

theorem runAll_append (p : Params) (A B : List Call) (r : Record) :
    p.runAll r (A ++ B) = match p.runAll r A with
      | .ok r' => p.runAll r' B
      | .error e => .error e := by
  simp only [Params.runAll]
  rw [foldlM_except_append]
  cases List.foldlM (fun r k => p.check r k.now k.amount) r A <;> rfl

theorem run_append (p : Params) (A B : List Call) (r : Record) :
    p.run r (A ++ B) = p.run (p.run r A) B :=
  List.foldl_append

end Cap

/-! ## Charging one rule -/

section

variable {rs : RuleSet Ctx Sig} {now : Nat}

/-- A charge touches at most the record of the context's chosen rule. -/
theorem RuleSet.charge_get_ne {records records' : List Cap.Record} {x : Ctx × Nat}
    (h : rs.charge now records x = .ok records') {i : Nat} (hi : i ≠ x.2) :
    records'[i]? = records[i]? := by
  unfold RuleSet.charge at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · cases h
            exact List.getElem?_set_ne (Ne.symm hi)
          · cases h
        · cases h
      · cases h
    · cases h
      rfl
  · cases h

/-- A charge to a rule with a cap: the context names an amount, and the check
accepts it from the rule's record and leaves the record the charge stores. -/
theorem RuleSet.charge_get_capped {records records' : List Cap.Record} {x : Ctx × Nat}
    {r : Rule Ctx Sig} {k : RuleCap Ctx} (hr : rs.rules[x.2]? = some r) (hk : r.cap = some k)
    (h : rs.charge now records x = .ok records') :
    ∃ amount rec rec', k.amount x.1 = some amount ∧ records[x.2]? = some rec ∧
      k.params.check rec now amount = .ok rec' ∧ records' = records.set x.2 rec' := by
  unfold RuleSet.charge at h
  rw [hr] at h
  simp only [hk] at h
  split at h
  · rename_i amount ha
    split at h
    · rename_i rec hrec
      split at h
      · rename_i rec' hc
        cases h
        exact ⟨amount, rec, rec', ha, hrec, hc, rfl⟩
      · cases h
    · cases h
  · cases h

/-- A charge to a rule without a cap changes nothing. -/
theorem RuleSet.charge_of_cap_none {records records' : List Cap.Record} {x : Ctx × Nat}
    {r : Rule Ctx Sig} (hr : rs.rules[x.2]? = some r) (hk : r.cap = none)
    (h : rs.charge now records x = .ok records') : records' = records := by
  unfold RuleSet.charge at h
  rw [hr] at h
  simp only [hk] at h
  cases h
  rfl

/-- The calls a list of contexts and choices charges to rule `j` under cap `k`
at ledger `now`. -/
def chargesOf (now : Nat) (k : RuleCap Ctx) (j : Nat) (l : List (Ctx × Nat)) : List Cap.Call :=
  l.filterMap fun x => if x.2 = j then (k.amount x.1).map (⟨now, ·⟩) else none

theorem Authorization.charges_eq (a : Authorization Ctx Sig) (k : RuleCap Ctx) (j : Nat) :
    a.charges k j = chargesOf a.now k j a.chosen := rfl

/-- Charging every context of `l` in order runs the cap check of rule `j` over
the calls `l` charges to it, from its record. -/
theorem RuleSet.foldlM_charge_get {j : Nat} {r : Rule Ctx Sig} {k : RuleCap Ctx}
    (hr : rs.rules[j]? = some r) (hk : r.cap = some k) :
    ∀ (l : List (Ctx × Nat)) (records records' : List Cap.Record) (rec : Cap.Record),
      records[j]? = some rec → l.foldlM (rs.charge now) records = .ok records' →
      ∃ rec', records'[j]? = some rec' ∧ k.params.runAll rec (chargesOf now k j l) = .ok rec'
  | [], records, records', rec, hrec, h => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨rec, hrec, rfl⟩
  | x :: l, records, records', rec, hrec, h => by
    rw [foldlM_except_cons] at h
    cases hc : rs.charge now records x with
    | error e => rw [hc] at h; cases h
    | ok r₁ =>
      rw [hc] at h
      by_cases hx : x.2 = j
      · obtain ⟨amount, rec₀, rec₁, ha, hrec₀, hck, rfl⟩ :=
          RuleSet.charge_get_capped (hx ▸ hr) hk hc
        rw [hx, hrec] at hrec₀
        cases hrec₀
        have hr₁ : (records.set x.2 rec₁)[j]? = some rec₁ := by
          rw [hx, List.getElem?_set_self]
          exact (List.getElem?_eq_some_iff.mp hrec).1
        obtain ⟨rec', hrec', hrun⟩ := RuleSet.foldlM_charge_get hr hk l _ records' rec₁ hr₁ h
        refine ⟨rec', hrec', ?_⟩
        simp only [chargesOf, List.filterMap_cons, hx, ↓reduceIte, ha, Option.map_some]
        rw [Cap.runAll_cons, hck]
        exact hrun
      · have hr₁ : r₁[j]? = some rec := by
          rw [RuleSet.charge_get_ne hc (Ne.symm hx)]
          exact hrec
        obtain ⟨rec', hrec', hrun⟩ := RuleSet.foldlM_charge_get hr hk l r₁ records' rec hr₁ h
        refine ⟨rec', hrec', ?_⟩
        simpa [chargesOf, List.filterMap_cons, hx] using hrun

/-- Charging every context of `l` leaves the record of a rule without a cap as
it was. -/
theorem RuleSet.foldlM_charge_get_of_cap_none {j : Nat} {r : Rule Ctx Sig}
    (hr : rs.rules[j]? = some r) (hk : r.cap = none) :
    ∀ (l : List (Ctx × Nat)) (records records' : List Cap.Record),
      l.foldlM (rs.charge now) records = .ok records' → records'[j]? = records[j]?
  | [], records, records', h => by
    simp only [List.foldlM_nil] at h
    cases h
    rfl
  | x :: l, records, records', h => by
    rw [foldlM_except_cons] at h
    cases hc : rs.charge now records x with
    | error e => rw [hc] at h; cases h
    | ok r₁ =>
      rw [hc] at h
      rw [RuleSet.foldlM_charge_get_of_cap_none hr hk l r₁ records' h]
      by_cases hx : x.2 = j
      · rw [RuleSet.charge_of_cap_none (hx ▸ hr) hk hc]
      · exact RuleSet.charge_get_ne hc (Ne.symm hx)

end

/-! ## Runs -/

section

variable [DecidableEq Sig] {rs : RuleSet Ctx Sig}

theorem RuleSet.run_nil (records : List Cap.Record) : rs.run records [] = records := rfl

theorem RuleSet.run_cons (records : List Cap.Record) (a : Authorization Ctx Sig)
    (as : List (Authorization Ctx Sig)) : rs.run records (a :: as) = rs.run (rs.step records a) as :=
  rfl

/-- The stored record of rule `j` after a run is the cap check's own run over
the calls the run charges to `j`, from the record it started with. -/
theorem RuleSet.run_get {j : Nat} {r : Rule Ctx Sig} {k : RuleCap Ctx}
    (hr : rs.rules[j]? = some r) (hk : r.cap = some k) :
    ∀ (as : List (Authorization Ctx Sig)) (records : List Cap.Record) (rec : Cap.Record),
      records.length = rs.rules.length → records[j]? = some rec →
      (rs.run records as)[j]? = some (k.params.run rec (rs.charged k j records as))
  | [], _, rec, _, hrec => by simpa [RuleSet.run_nil, RuleSet.charged] using hrec
  | a :: as, records, rec, hlen, hrec => by
    rw [RuleSet.run_cons]
    unfold RuleSet.charged
    cases ha : rs.authorize records a with
    | error e =>
      simp only [RuleSet.step, ha]
      exact RuleSet.run_get hr hk as records rec hlen hrec
    | ok records' =>
      simp only [RuleSet.step, ha]
      obtain ⟨-, -, -, hf⟩ := (rs.authorize_eq_ok_iff records records' a).mp ha
      obtain ⟨rec₁, hrec₁, hrun⟩ := RuleSet.foldlM_charge_get hr hk _ _ _ rec hrec hf
      rw [RuleSet.run_get hr hk as records' rec₁ (RuleSet.authorize_length ha) hrec₁,
        Authorization.charges_eq, Cap.run_append, Cap.run_of_runAll hrun]

/-- The calls a run charges to a rule with a cap are accepted by its cap check,
call by call, from the record it started with. -/
theorem RuleSet.runAll_charged {j : Nat} {r : Rule Ctx Sig} {k : RuleCap Ctx}
    (hr : rs.rules[j]? = some r) (hk : r.cap = some k) :
    ∀ (as : List (Authorization Ctx Sig)) (records : List Cap.Record) (rec : Cap.Record),
      records.length = rs.rules.length → records[j]? = some rec →
      ∃ rec', k.params.runAll rec (rs.charged k j records as) = .ok rec'
  | [], _, rec, _, _ => ⟨rec, rfl⟩
  | a :: as, records, rec, hlen, hrec => by
    unfold RuleSet.charged
    cases ha : rs.authorize records a with
    | error e => exact RuleSet.runAll_charged hr hk as records rec hlen hrec
    | ok records' =>
      obtain ⟨-, -, -, hf⟩ := (rs.authorize_eq_ok_iff records records' a).mp ha
      obtain ⟨rec₁, hrec₁, hrun⟩ := RuleSet.foldlM_charge_get hr hk _ _ _ rec hrec hf
      obtain ⟨rec', hrun'⟩ :=
        RuleSet.runAll_charged hr hk as records' rec₁ (RuleSet.authorize_length ha) hrec₁
      refine ⟨rec', ?_⟩
      simp only
      rw [Cap.runAll_append, Authorization.charges_eq, hrun]
      exact hrun'

/-- The spends a run records for a rule with a cap are the ones its cap check
records over the calls the run charges there. -/
theorem RuleSet.spent_eq_recorded {j : Nat} {r : Rule Ctx Sig} {k : RuleCap Ctx}
    (hr : rs.rules[j]? = some r) (hk : r.cap = some k) (as : List (Authorization Ctx Sig))
    {records : List Cap.Record} {rec : Cap.Record} (hlen : records.length = rs.rules.length)
    (hrec : records[j]? = some rec) :
    rs.spent k j records as = k.params.recorded rec (rs.charged k j records as) := by
  obtain ⟨rec', hrun⟩ := RuleSet.runAll_charged hr hk as records rec hlen hrec
  rw [Cap.recorded_of_runAll hrun]
  rfl

/-- A rule without a cap keeps its record through every run. -/
theorem RuleSet.run_get_of_cap_none {j : Nat} {r : Rule Ctx Sig}
    (hr : rs.rules[j]? = some r) (hk : r.cap = none) :
    ∀ (as : List (Authorization Ctx Sig)) (records : List Cap.Record),
      (rs.run records as)[j]? = records[j]?
  | [], _ => rfl
  | a :: as, records => by
    rw [RuleSet.run_cons, RuleSet.run_get_of_cap_none hr hk as]
    cases ha : rs.authorize records a with
    | error e => simp only [RuleSet.step, ha]
    | ok records' =>
      simp only [RuleSet.step, ha]
      obtain ⟨-, -, -, hf⟩ := (rs.authorize_eq_ok_iff records records' a).mp ha
      exact RuleSet.foldlM_charge_get_of_cap_none hr hk _ _ _ hf

/-- Every call a run charges is made at the ledger of one of its
authorizations. -/
theorem RuleSet.mem_charged {k : RuleCap Ctx} {j : Nat} :
    ∀ {as : List (Authorization Ctx Sig)} {records : List Cap.Record} {x : Cap.Call},
      x ∈ rs.charged k j records as → ∃ a ∈ as, x.now = a.now
  | [], _, _, h => by simp [RuleSet.charged] at h
  | a :: as, records, x, h => by
    unfold RuleSet.charged at h
    split at h
    · rcases List.mem_append.mp h with h | h
      · simp only [Authorization.charges, List.mem_filterMap] at h
        obtain ⟨y, -, hy⟩ := h
        split at hy
        · obtain ⟨amount, -, rfl⟩ := Option.map_eq_some_iff.mp hy
          exact ⟨a, by simp, rfl⟩
        · cases hy
      · obtain ⟨a', ha', he⟩ := RuleSet.mem_charged h
        exact ⟨a', by simp [ha'], he⟩
    · obtain ⟨a', ha', he⟩ := RuleSet.mem_charged h
      exact ⟨a', by simp [ha'], he⟩

omit [DecidableEq Sig] in
theorem RuleSet.emptyRecords_length (rs : RuleSet Ctx Sig) :
    rs.emptyRecords.length = rs.rules.length := by
  simp [RuleSet.emptyRecords]

omit [DecidableEq Sig] in
theorem RuleSet.emptyRecords_get {rs : RuleSet Ctx Sig} {j : Nat} {r : Rule Ctx Sig}
    (hr : rs.rules[j]? = some r) : rs.emptyRecords[j]? = some .empty := by
  simp [RuleSet.emptyRecords, hr]

/-! ## Window safety -/

/-- Window safety: from empty records, the spends a run records for a rule with
a cap, in the window eviction leaves at any ledger `t`, sum to at most the
cap's limit. -/
theorem RuleSet.window_le_limit (rs : RuleSet Ctx Sig) {j : Nat} {r : Rule Ctx Sig}
    {k : RuleCap Ctx} (hr : rs.rules[j]? = some r) (hk : r.cap = some k)
    (hl : 0 ≤ k.params.limit) (as : List (Authorization Ctx Sig)) (t : Nat) :
    Cap.amountSum ((rs.spent k j rs.emptyRecords as).filter (k.params.inWindow t)) ≤
      k.params.limit := by
  rw [RuleSet.spent_eq_recorded hr hk as rs.emptyRecords_length (RuleSet.emptyRecords_get hr)]
  exact Cap.window_le_limit k.params hl _ t

/-- From empty records, every window of `period` consecutive ledgers starting
at ledger 1 or later holds spends of a capped rule summing to at most its
limit. -/
theorem RuleSet.period_le_limit_of_pos (rs : RuleSet Ctx Sig) {j : Nat} {r : Rule Ctx Sig}
    {k : RuleCap Ctx} (hr : rs.rules[j]? = some r) (hk : r.cap = some k)
    (hl : 0 ≤ k.params.limit) (as : List (Authorization Ctx Sig)) {s : Nat} (hs : 0 < s) :
    Cap.amountSum ((rs.spent k j rs.emptyRecords as).filter (k.params.inPeriodFrom s)) ≤
      k.params.limit := by
  rw [RuleSet.spent_eq_recorded hr hk as rs.emptyRecords_length (RuleSet.emptyRecords_get hr)]
  exact Cap.period_le_limit_of_pos k.params hl _ hs

/-- From empty records, when every authorization is at ledger 1 or later,
every window of `period` consecutive ledgers holds spends of a capped rule
summing to at most its limit. -/
theorem RuleSet.period_le_limit (rs : RuleSet Ctx Sig) {j : Nat} {r : Rule Ctx Sig}
    {k : RuleCap Ctx} (hr : rs.rules[j]? = some r) (hk : r.cap = some k)
    (hl : 0 ≤ k.params.limit) (as : List (Authorization Ctx Sig)) (h1 : ∀ a ∈ as, 0 < a.now)
    (s : Nat) :
    Cap.amountSum ((rs.spent k j rs.emptyRecords as).filter (k.params.inPeriodFrom s)) ≤
      k.params.limit := by
  rw [RuleSet.spent_eq_recorded hr hk as rs.emptyRecords_length (RuleSet.emptyRecords_get hr)]
  refine Cap.period_le_limit k.params hl _ (fun x hx => ?_) s
  obtain ⟨a, ha, he⟩ := RuleSet.mem_charged hx
  rw [he]
  exact h1 a ha

/-- From empty records, with a nonzero period and the last spend at ledger 1
or later, the stored record of a capped rule is exactly the spends the run
recorded there in the window at that spend's ledger, and its total is their
sum. -/
theorem RuleSet.run_eq_window (rs : RuleSet Ctx Sig) {j : Nat} {r : Rule Ctx Sig}
    {k : RuleCap Ctx} (hr : rs.rules[j]? = some r) (hk : r.cap = some k)
    (hp : 0 < k.params.period) (as : List (Authorization Ctx Sig)) {A : List Cap.Entry}
    {e : Cap.Entry} (h : rs.spent k j rs.emptyRecords as = A ++ [e]) (he : 0 < e.ledger) :
    ∃ rec, (rs.run rs.emptyRecords as)[j]? = some rec ∧
      rec.history = (rs.spent k j rs.emptyRecords as).filter (k.params.inWindow e.ledger) ∧
      rec.total = Cap.amountSum rec.history := by
  have hs := RuleSet.spent_eq_recorded hr hk as rs.emptyRecords_length (RuleSet.emptyRecords_get hr)
  rw [hs] at h ⊢
  obtain ⟨hh, ht⟩ := Cap.run_eq_window k.params hp _ h he
  refine ⟨_, RuleSet.run_get hr hk as _ _ rs.emptyRecords_length (RuleSet.emptyRecords_get hr),
    hh, ?_⟩
  rw [ht, hh]

/-- From empty records, the stored record of a capped rule never holds more
than `Cap.maxHistory` entries. -/
theorem RuleSet.run_history_length_le (rs : RuleSet Ctx Sig) {j : Nat} {r : Rule Ctx Sig}
    {k : RuleCap Ctx} (hr : rs.rules[j]? = some r) (hk : r.cap = some k)
    (as : List (Authorization Ctx Sig)) :
    ∃ rec, (rs.run rs.emptyRecords as)[j]? = some rec ∧ rec.history.length ≤ Cap.maxHistory :=
  ⟨_, RuleSet.run_get hr hk as _ _ rs.emptyRecords_length (RuleSet.emptyRecords_get hr),
    Cap.run_history_length_le k.params Cap.Record.empty_valid (by simp [Cap.Record.empty]) _⟩

end

/-! ## Narrowing as trace inclusion -/

/-- Narrower on a rule's cap, reading amounts: any cap is narrower than none,
and one cap is narrower than another when it reads the same amount from every
context, its limit is at most the other's and its period at least the
other's. -/
def RuleCap.NarrowerOpt : Option (RuleCap Ctx) → Option (RuleCap Ctx) → Prop
  | _, none => True
  | none, some _ => False
  | some q, some p => q.amount = p.amount ∧ q.params.narrower p.params

theorem RuleCap.NarrowerOpt.refl : ∀ k : Option (RuleCap Ctx), RuleCap.NarrowerOpt k k
  | none => trivial
  | some p => ⟨rfl, Cap.Params.narrower_refl p.params⟩

theorem RuleCap.NarrowerOpt.trans :
    ∀ {c b a : Option (RuleCap Ctx)}, RuleCap.NarrowerOpt c b → RuleCap.NarrowerOpt b a →
      RuleCap.NarrowerOpt c a
  | _, _, none, _, _ => trivial
  | none, none, some _, _, h => h.elim
  | none, some _, some _, h, _ => h.elim
  | some _, none, some _, _, h => h.elim
  | some _, some _, some _, h₁, h₂ => ⟨h₁.1.trans h₂.1, Cap.Params.narrower_trans h₁.2 h₂.2⟩

section

variable [DecidableEq Sig]

/-- `r'` refines `r`: it allows no context, under any signers, that `r` does
not, and carries a cap at least as narrow. -/
def Rule.Refines (r' r : Rule Ctx Sig) : Prop :=
  (∀ c auth, r'.allows c auth = true → r.allows c auth = true) ∧
    RuleCap.NarrowerOpt r'.cap r.cap

theorem Rule.Refines.refl (r : Rule Ctx Sig) : r.Refines r :=
  ⟨fun _ _ h => h, RuleCap.NarrowerOpt.refl r.cap⟩

theorem Rule.Refines.trans {r'' r' r : Rule Ctx Sig} (h₁ : r''.Refines r') (h₂ : r'.Refines r) :
    r''.Refines r :=
  ⟨fun c auth h => h₂.1 c auth (h₁.1 c auth h), h₁.2.trans h₂.2⟩

/-- `rs'` refines `rs` along `f`: `f` sends the rules of `rs'` one to one to
rules of `rs`, and each rule refines its image. -/
def RuleSet.Refines (rs' rs : RuleSet Ctx Sig) (f : Nat → Nat) : Prop :=
  (∀ i j, i < rs'.rules.length → j < rs'.rules.length → f i = f j → i = j) ∧
    ∀ j r', rs'.rules[j]? = some r' → ∃ r, rs.rules[f j]? = some r ∧ r'.Refines r

theorem RuleSet.Refines.refl (rs : RuleSet Ctx Sig) : rs.Refines rs fun j => j :=
  ⟨fun _ _ _ _ h => h, fun _ r' h => ⟨r', h, Rule.Refines.refl r'⟩⟩

theorem RuleSet.Refines.trans {rs'' rs' rs : RuleSet Ctx Sig} {g f : Nat → Nat}
    (h₁ : rs''.Refines rs' g) (h₂ : rs'.Refines rs f) : rs''.Refines rs fun j => f (g j) := by
  refine ⟨fun i j hi hj he => ?_, fun j r'' hr'' => ?_⟩
  · obtain ⟨ri, hri, -⟩ := h₁.2 i _ (List.getElem?_eq_getElem hi)
    obtain ⟨rj, hrj, -⟩ := h₁.2 j _ (List.getElem?_eq_getElem hj)
    exact h₁.1 i j hi hj (h₂.1 _ _ (List.getElem?_eq_some_iff.mp hri).1
      (List.getElem?_eq_some_iff.mp hrj).1 he)
  · obtain ⟨r', hr', hR₁⟩ := h₁.2 j r'' hr''
    obtain ⟨r, hr, hR₂⟩ := h₂.2 _ r' hr'
    exact ⟨r, hr, hR₁.trans hR₂⟩

/-- Replacing one rule by a rule that refines it refines, keeping every
index. -/
theorem RuleSet.Refines.set {rs : RuleSet Ctx Sig} {i : Nat} {r r' : Rule Ctx Sig}
    (hr : rs.rules[i]? = some r) (h : r'.Refines r) :
    (RuleSet.ofRules (rs.rules.set i r') : RuleSet Ctx Sig).Refines rs fun j => j := by
  refine ⟨fun _ _ _ _ he => he, fun j r'' hr'' => ?_⟩
  simp only [RuleSet.rules_ofRules] at hr''
  by_cases hj : i = j
  · subst hj
    have hi : i < rs.rules.length := (List.getElem?_eq_some_iff.mp hr).1
    rw [List.getElem?_set_self hi, Option.some.injEq] at hr''
    subst hr''
    exact ⟨r, hr, h⟩
  · rw [List.getElem?_set_ne hj] at hr''
    exact ⟨r'', hr'', Rule.Refines.refl r''⟩

/-- What the records of `rs'` and `rs` keep along `f` while both accept the same
run: one record per rule each, and for each rule of `rs'` with a cap whose
image has one too, both records are valid and the history of the image's is a
suffix of the other's. -/
structure RuleSet.RecordsRel (rs' rs : RuleSet Ctx Sig) (f : Nat → Nat)
    (recs' recs : List Cap.Record) : Prop where
  narrowLen : recs'.length = rs'.rules.length
  wideLen : recs.length = rs.rules.length
  rel : ∀ j r' r q p, rs'.rules[j]? = some r' → rs.rules[f j]? = some r → r'.cap = some q →
    r.cap = some p → ∃ rq rp, recs'[j]? = some rq ∧ recs[f j]? = some rp ∧ rq.Valid ∧
      rp.Valid ∧ rp.history <:+ rq.history

omit [DecidableEq Sig] in
theorem RuleSet.RecordsRel.empty (rs' rs : RuleSet Ctx Sig) (f : Nat → Nat) :
    RuleSet.RecordsRel rs' rs f rs'.emptyRecords rs.emptyRecords where
  narrowLen := rs'.emptyRecords_length
  wideLen := rs.emptyRecords_length
  rel := fun _ _ _ _ _ hr' hr _ _ =>
    ⟨_, _, RuleSet.emptyRecords_get hr', RuleSet.emptyRecords_get hr, Cap.Record.empty_valid,
      Cap.Record.empty_valid, List.suffix_refl _⟩

/-- One charge: what `rs'` charges, `rs` charges to the image of the chosen
rule, and the records keep their relation. -/
theorem RuleSet.Refines.charge {rs' rs : RuleSet Ctx Sig} {f : Nat → Nat}
    (hR : rs'.Refines rs f) {now : Nat} {recs' recs recs'' : List Cap.Record} {x : Ctx × Nat}
    (hrel : RuleSet.RecordsRel rs' rs f recs' recs) (h : rs'.charge now recs' x = .ok recs'') :
    ∃ recsN, rs.charge now recs (x.1, f x.2) = .ok recsN ∧
      RuleSet.RecordsRel rs' rs f recs'' recsN := by
  cases hr' : rs'.rules[x.2]? with
  | none => simp [RuleSet.charge, hr'] at h
  | some r' =>
    obtain ⟨r, hr, hRr⟩ := hR.2 x.2 r' hr'
    have hx' : x.2 < rs'.rules.length := (List.getElem?_eq_some_iff.mp hr').1
    cases hq : r'.cap with
    | none =>
      have hp : r.cap = none := by
        have := hRr.2
        rw [hq] at this
        cases hc : r.cap with
        | none => rfl
        | some _ => rw [hc] at this; exact this.elim
      rw [RuleSet.charge_of_cap_none hr' hq h]
      refine ⟨recs, ?_, hrel⟩
      simp [RuleSet.charge, hr, hp]
    | some q =>
      obtain ⟨amount, rq, rq', hamount, hrq, hcq, rfl⟩ := RuleSet.charge_get_capped hr' hq h
      have hlen'' : (recs'.set x.2 rq').length = rs'.rules.length := by simp [hrel.narrowLen]
      have hne : ∀ j, rs'.rules[j]? ≠ none → j ≠ x.2 → f j ≠ f x.2 := fun j hj hjx he =>
        hjx (hR.1 j x.2 (by
          rcases hjs : rs'.rules[j]? with _ | _
          · exact absurd hjs hj
          · exact (List.getElem?_eq_some_iff.mp hjs).1) hx' he)
      cases hp : r.cap with
      | none =>
        refine ⟨recs, by simp [RuleSet.charge, hr, hp], ⟨hlen'', hrel.wideLen, ?_⟩⟩
        intro j r₁' r₁ q₁ p₁ hj hj' hq₁ hp₁
        by_cases hjx : j = x.2
        · subst hjx
          rw [hr] at hj'
          cases hj'
          rw [hp] at hp₁
          cases hp₁
        · obtain ⟨a, b, ha, hb, hva, hvb, hs⟩ := hrel.rel j r₁' r₁ q₁ p₁ hj hj' hq₁ hp₁
          exact ⟨a, b, by rw [List.getElem?_set_ne (Ne.symm hjx)]; exact ha, hb, hva, hvb, hs⟩
      | some p =>
        have hnar := hRr.2
        rw [hq, hp] at hnar
        obtain ⟨hamt, hqp⟩ := hnar
        obtain ⟨rq₀, rp, hrq₀, hrp, hvq, hvp, hs⟩ := hrel.rel x.2 r' r q p hr' hr hq hp
        rw [hrq] at hrq₀
        cases hrq₀
        obtain ⟨rp', hcp, hs'⟩ := Cap.check_of_narrower_suffix hqp hvq hvp hs hcq
        have hrpm : (recs.set (f x.2) rp')[f x.2]? = some rp' := by
          rw [List.getElem?_set_self]
          exact (List.getElem?_eq_some_iff.mp hrp).1
        refine ⟨recs.set (f x.2) rp', ?_, ⟨hlen'', by simp [hrel.wideLen], ?_⟩⟩
        · have hpa : p.amount x.1 = some amount := by rw [← hamt]; exact hamount
          simp [RuleSet.charge, hr, hp, hpa, hrp, hcp]
        · intro j r₁' r₁ q₁ p₁ hj hj' hq₁ hp₁
          by_cases hjx : j = x.2
          · subst hjx
            refine ⟨rq', rp', ?_, hrpm, Cap.check_preserves_valid hvq hcq,
              Cap.check_preserves_valid hvp hcp, hs'⟩
            rw [List.getElem?_set_self]
            exact (List.getElem?_eq_some_iff.mp hrq).1
          · have hfj : f j ≠ f x.2 := hne j (by rw [hj]; simp) hjx
            obtain ⟨a, b, ha, hb, hva, hvb, hsab⟩ := hrel.rel j r₁' r₁ q₁ p₁ hj hj' hq₁ hp₁
            exact ⟨a, b, by rw [List.getElem?_set_ne (Ne.symm hjx)]; exact ha,
              by rw [List.getElem?_set_ne (Ne.symm hfj)]; exact hb, hva, hvb, hsab⟩

theorem RuleSet.Refines.foldlM_charge {rs' rs : RuleSet Ctx Sig} {f : Nat → Nat}
    (hR : rs'.Refines rs f) {now : Nat} :
    ∀ (l : List (Ctx × Nat)) (recs' recs recs'' : List Cap.Record),
      RuleSet.RecordsRel rs' rs f recs' recs → l.foldlM (rs'.charge now) recs' = .ok recs'' →
      ∃ recsN, (l.map fun x => (x.1, f x.2)).foldlM (rs.charge now) recs = .ok recsN ∧
        RuleSet.RecordsRel rs' rs f recs'' recsN
  | [], recs', recs, recs'', hrel, h => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨recs, rfl, hrel⟩
  | x :: l, recs', recs, recs'', hrel, h => by
    rw [foldlM_except_cons] at h
    cases hc : rs'.charge now recs' x with
    | error e => rw [hc] at h; cases h
    | ok r₁ =>
      rw [hc] at h
      obtain ⟨recs₁, hc₁, hrel₁⟩ := hR.charge hrel hc
      obtain ⟨recsN, hN, hrelN⟩ := hR.foldlM_charge l r₁ recs₁ recs'' hrel₁ h
      refine ⟨recsN, ?_, hrelN⟩
      rw [List.map_cons, foldlM_except_cons, hc₁]
      exact hN

omit [DecidableEq Sig] in
theorem Authorization.chosen_renumber (a : Authorization Ctx Sig) (f : Nat → Nat) :
    (a.renumber f).chosen = a.chosen.map fun x => (x.1, f x.2) := by
  simp only [Authorization.chosen, Authorization.renumber, List.zip_map_right]
  rfl

/-- One authorization: what `rs'` accepts, `rs` accepts with the choices
renumbered, and the records keep their relation. -/
theorem RuleSet.Refines.authorize {rs' rs : RuleSet Ctx Sig} {f : Nat → Nat}
    (hR : rs'.Refines rs f) {recs' recs recs'' : List Cap.Record} {a : Authorization Ctx Sig}
    (hrel : RuleSet.RecordsRel rs' rs f recs' recs) (h : rs'.authorize recs' a = .ok recs'') :
    ∃ recsN, rs.authorize recs (a.renumber f) = .ok recsN ∧
      RuleSet.RecordsRel rs' rs f recs'' recsN := by
  obtain ⟨hc, -, hk, hf⟩ := (rs'.authorize_eq_ok_iff recs' recs'' a).mp h
  obtain ⟨recsN, hN, hrelN⟩ := hR.foldlM_charge _ _ _ _ hrel hf
  refine ⟨recsN, (rs.authorize_eq_ok_iff recs recsN _).mpr ⟨?_, hrel.wideLen, ?_, ?_⟩, hrelN⟩
  · simpa [Authorization.renumber] using hc
  · rw [Authorization.chosen_renumber]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨r', hr', ha⟩ := (rs'.checkChoice_ok_iff a.auth x).mp (hk x hx)
    obtain ⟨r, hr, hRr⟩ := hR.2 x.2 r' hr'
    exact (rs.checkChoice_ok_iff a.auth _).mpr ⟨r, hr, hRr.1 x.1 a.auth ha⟩
  · rw [Authorization.chosen_renumber]
    exact hN

theorem RuleSet.Refines.authorizeAll {rs' rs : RuleSet Ctx Sig} {f : Nat → Nat}
    (hR : rs'.Refines rs f) :
    ∀ (as : List (Authorization Ctx Sig)) (recs' recs recs'' : List Cap.Record),
      RuleSet.RecordsRel rs' rs f recs' recs → rs'.authorizeAll recs' as = .ok recs'' →
      ∃ recsN, rs.authorizeAll recs (as.map (·.renumber f)) = .ok recsN
  | [], _, recs, _, _, _ => ⟨recs, rfl⟩
  | a :: as, recs', recs, recs'', hrel, h => by
    simp only [RuleSet.authorizeAll] at h ⊢
    rw [foldlM_except_cons] at h
    cases ha : rs'.authorize recs' a with
    | error e => rw [ha] at h; cases h
    | ok r₁ =>
      rw [ha] at h
      obtain ⟨recs₁, ha₁, hrel₁⟩ := hR.authorize hrel ha
      rw [List.map_cons, foldlM_except_cons, ha₁]
      exact hR.authorizeAll as r₁ recs₁ recs'' hrel₁ h

/-- Refining is narrowing as trace inclusion: every run of authorizations a
refining rule set accepts from its empty records, the refined one accepts from
its own, with the choices renumbered. -/
theorem RuleSet.Refines.traceNarrower {rs' rs : RuleSet Ctx Sig} {f : Nat → Nat}
    (hR : rs'.Refines rs f) : rs'.TraceNarrower rs f := by
  intro as ⟨recs'', h⟩
  exact hR.authorizeAll as _ _ _ (RuleSet.RecordsRel.empty rs' rs f) h

omit [DecidableEq Sig] in
theorem Authorization.renumber_renumber (a : Authorization Ctx Sig) (g f : Nat → Nat) :
    (a.renumber g).renumber f = a.renumber fun j => f (g j) := by
  simp [Authorization.renumber, List.map_map, Function.comp_def]

theorem RuleSet.TraceNarrower.refl (rs : RuleSet Ctx Sig) : rs.TraceNarrower rs fun j => j := by
  intro as h
  have : as.map (·.renumber fun j => j) = as := by
    simp [Authorization.renumber]
  rw [this]
  exact h

/-- Trace inclusion composes, with the renumberings composed. -/
theorem RuleSet.TraceNarrower.trans {rs'' rs' rs : RuleSet Ctx Sig} {g f : Nat → Nat}
    (h₁ : rs''.TraceNarrower rs' g) (h₂ : rs'.TraceNarrower rs f) :
    rs''.TraceNarrower rs fun j => f (g j) := by
  intro as h
  have := h₂ _ (h₁ as h)
  rw [List.map_map] at this
  have he : ((·.renumber f) ∘ (·.renumber g) : Authorization Ctx Sig → Authorization Ctx Sig) =
      (·.renumber fun j => f (g j)) := by
    funext a
    exact Authorization.renumber_renumber a g f
  rw [he] at this
  exact this

/-! ### Each step refines -/

theorem Rule.refines_addCond (r : Rule Ctx Sig) (p : Ctx → Bool) : (r.addCond p).Refines r :=
  ⟨fun _ _ h => Rule.allows_of_allows_addCond h, RuleCap.NarrowerOpt.refl r.cap⟩

theorem Rule.refines_restrictScope (r : Rule Ctx Sig) (s : Ctx → Bool) :
    (r.restrictScope s).Refines r :=
  ⟨fun _ _ h => Rule.allows_of_allows_restrictScope h, RuleCap.NarrowerOpt.refl r.cap⟩

theorem Rule.refines_removeSigners (r : Rule Ctx Sig) (ss : List Sig) :
    (r.removeSigners ss).Refines r :=
  ⟨fun _ _ h => Rule.allows_of_allows_removeSigners h, RuleCap.NarrowerOpt.refl r.cap⟩

theorem RuleSet.modifyRule_refines {rs rs' : RuleSet Ctx Sig} {i : Nat}
    {f : Rule Ctx Sig → Rule Ctx Sig} (hf : ∀ r, (f r).Refines r)
    (h : rs.modifyRule i f = .ok rs') : rs'.Refines rs fun j => j := by
  unfold RuleSet.modifyRule at h
  split at h
  · rename_i r hr
    cases h
    exact RuleSet.Refines.set hr (hf r)
  · cases h

theorem RuleSet.dropRule_refines {rs rs' : RuleSet Ctx Sig} {i : Nat}
    (h : rs.dropRule i = .ok rs') : rs'.Refines rs fun j => if j < i then j else j + 1 := by
  unfold RuleSet.dropRule at h
  split at h
  · cases h
    refine ⟨fun a b _ _ he => ?_, fun j r' hr' => ⟨r', ?_, Rule.Refines.refl r'⟩⟩
    · dsimp only at he
      split at he <;> split at he <;> omega
    · simp only [RuleSet.rules_ofRules, List.getElem?_eraseIdx] at hr'
      by_cases hj : j < i
      · simp only [hj, ↓reduceIte] at hr' ⊢
        exact hr'
      · simp only [hj, ↓reduceIte] at hr' ⊢
        exact hr'
  · cases h

theorem RuleSet.raiseThreshold_refines {rs rs' : RuleSet Ctx Sig} {i k : Nat}
    (h : rs.raiseThreshold i k = .ok rs') : rs'.Refines rs fun j => j := by
  unfold RuleSet.raiseThreshold at h
  split at h
  · rename_i r hr
    split at h
    · cases h
    · rename_i hk
      cases h
      exact RuleSet.Refines.set hr
        ⟨fun _ _ hc => Rule.allows_of_allows_threshold_le (Nat.le_of_not_lt hk) hc,
          RuleCap.NarrowerOpt.refl r.cap⟩
  · cases h

theorem RuleSet.addCap_refines {rs rs' : RuleSet Ctx Sig} {i : Nat} {k : RuleCap Ctx}
    (h : rs.addCap i k = .ok rs') : rs'.Refines rs fun j => j := by
  unfold RuleSet.addCap at h
  split at h
  · rename_i r hr
    split at h
    · cases h
    · rename_i hc
      split at h
      · cases h
        exact RuleSet.Refines.set hr ⟨fun _ _ hc => hc, by simp [RuleCap.NarrowerOpt, hc]⟩
      · cases h
  · cases h

theorem RuleSet.lowerCapLimit_refines {rs rs' : RuleSet Ctx Sig} {i : Nat} {limit : Int}
    (h : rs.lowerCapLimit i limit = .ok rs') : rs'.Refines rs fun j => j := by
  unfold RuleSet.lowerCapLimit at h
  split at h
  · rename_i r hr
    split at h
    · rename_i k hc
      split at h
      · cases h
      · rename_i hl
        split at h
        · cases h
        · cases h
          refine RuleSet.Refines.set hr ⟨fun _ _ hc => hc, ?_⟩
          show RuleCap.NarrowerOpt (some (k.withLimit limit)) r.cap
          rw [hc]
          exact ⟨rfl, Int.not_lt.mp hl, Nat.le_refl _⟩
    · cases h
  · cases h

theorem RuleSet.lengthenCapPeriod_refines {rs rs' : RuleSet Ctx Sig} {i period : Nat}
    (h : rs.lengthenCapPeriod i period = .ok rs') : rs'.Refines rs fun j => j := by
  unfold RuleSet.lengthenCapPeriod at h
  split at h
  · rename_i r hr
    split at h
    · rename_i k hc
      split at h
      · cases h
      · rename_i hp
        cases h
        refine RuleSet.Refines.set hr ⟨fun _ _ hc => hc, ?_⟩
        show RuleCap.NarrowerOpt (some (k.withPeriod period)) r.cap
        rw [hc]
        exact ⟨rfl, Int.le_refl _, Nat.le_of_not_lt hp⟩
    · cases h
  · cases h

/-- Each of the eight steps refines along the renumbering it induces. -/
theorem RuleSet.attenuate_refines {rs rs' : RuleSet Ctx Sig} {a : Attenuation Ctx Sig}
    (h : rs.attenuate a = .ok rs') : rs'.Refines rs a.source := by
  cases a with
  | dropRule i => exact RuleSet.dropRule_refines h
  | addCond i p => exact RuleSet.modifyRule_refines (fun r => r.refines_addCond p) h
  | restrictScope i s => exact RuleSet.modifyRule_refines (fun r => r.refines_restrictScope s) h
  | removeSigners i ss => exact RuleSet.modifyRule_refines (fun r => r.refines_removeSigners ss) h
  | raiseThreshold i k => exact RuleSet.raiseThreshold_refines h
  | addCap i k => exact RuleSet.addCap_refines h
  | lowerCapLimit i limit => exact RuleSet.lowerCapLimit_refines h
  | lengthenCapPeriod i period => exact RuleSet.lengthenCapPeriod_refines h

/-- Every list of steps refines along the renumbering it induces. -/
theorem RuleSet.attenuateAll_refines :
    ∀ {steps : List (Attenuation Ctx Sig)} {root rs : RuleSet Ctx Sig},
      root.attenuateAll steps = .ok rs → rs.Refines root (Attenuation.chainSource steps)
  | [], root, rs, h => by
    simp only [RuleSet.attenuateAll, List.foldlM_nil] at h
    cases h
    exact RuleSet.Refines.refl root
  | a :: steps, root, rs, h => by
    simp only [RuleSet.attenuateAll] at h
    rw [foldlM_except_cons] at h
    cases ha : root.attenuate a with
    | error e => rw [ha] at h; cases h
    | ok rs₁ =>
      rw [ha] at h
      exact (RuleSet.attenuateAll_refines (root := rs₁) h).trans (RuleSet.attenuate_refines ha)

/-- Each step is narrowing as trace inclusion: every run of authorizations the
new rule set accepts from its empty records, the old one accepts from its own,
with each choice `j` renumbered to `a.source j`. -/
theorem RuleSet.attenuate_traceNarrower {rs rs' : RuleSet Ctx Sig} {a : Attenuation Ctx Sig}
    (h : rs.attenuate a = .ok rs') : rs'.TraceNarrower rs a.source :=
  (RuleSet.attenuate_refines h).traceNarrower

/-- Every chain of steps is narrowing as trace inclusion: every run the rule set
at its end accepts from its empty records, the root accepts from its own, with
each choice `j` renumbered to `Attenuation.chainSource steps j`. -/
theorem RuleSet.attenuateAll_traceNarrower {root rs : RuleSet Ctx Sig}
    {steps : List (Attenuation Ctx Sig)} (h : root.attenuateAll steps = .ok rs) :
    rs.TraceNarrower root (Attenuation.chainSource steps) :=
  (RuleSet.attenuateAll_refines h).traceNarrower

omit [DecidableEq Sig] in
/-- The renumbering of every step but `dropRule` keeps each index. -/
theorem Attenuation.source_eq_of_ne_dropRule {a : Attenuation Ctx Sig}
    (h : ∀ i, a ≠ .dropRule i) (j : Nat) : a.source j = j := by
  cases a with
  | dropRule i => exact absurd rfl (h i)
  | _ => rfl

omit [DecidableEq Sig] in
/-- `dropRule i` moves each rule after `i` down by one. -/
theorem Attenuation.source_dropRule (i j : Nat) :
    (Attenuation.dropRule (Ctx := Ctx) (Sig := Sig) i).source j = if j < i then j else j + 1 :=
  rfl

/-! ### Steps keep caps valid -/

omit [DecidableEq Sig] in
theorem RuleSet.capsValid_set {rs : RuleSet Ctx Sig} (hv : rs.capsValid) {i : Nat}
    {r' : Rule Ctx Sig} (h : ∀ k, r'.cap = some k → k.params.valid = true) :
    (RuleSet.ofRules (rs.rules.set i r') : RuleSet Ctx Sig).capsValid := by
  intro r hr k hk
  rcases List.mem_or_eq_of_mem_set hr with hmem | rfl
  · exact hv r hmem k hk
  · exact h k hk

/-- Each step keeps every cap valid. -/
theorem RuleSet.attenuate_capsValid {rs rs' : RuleSet Ctx Sig} {a : Attenuation Ctx Sig}
    (hv : rs.capsValid) (h : rs.attenuate a = .ok rs') : rs'.capsValid := by
  have hkeep : ∀ {i : Nat} {f : Rule Ctx Sig → Rule Ctx Sig}, (∀ r, (f r).cap = r.cap) →
      rs.modifyRule i f = .ok rs' → rs'.capsValid := by
    intro i f hf hm
    unfold RuleSet.modifyRule at hm
    split at hm
    · rename_i r hr
      cases hm
      exact RuleSet.capsValid_set hv fun k hk =>
        hv r (List.mem_of_getElem? hr) k ((hf r) ▸ hk)
    · cases hm
  cases a with
  | dropRule i =>
    simp only [RuleSet.attenuate, RuleSet.dropRule] at h
    split at h
    · cases h
      exact fun r hr => hv r (List.mem_of_mem_eraseIdx hr)
    · cases h
  | addCond i p => exact hkeep (f := (·.addCond p)) (fun _ => rfl) h
  | restrictScope i s => exact hkeep (f := (·.restrictScope s)) (fun _ => rfl) h
  | removeSigners i ss => exact hkeep (f := (·.removeSigners ss)) (fun _ => rfl) h
  | raiseThreshold i k =>
    simp only [RuleSet.attenuate, RuleSet.raiseThreshold] at h
    split at h
    · rename_i r hr
      split at h
      · cases h
      · cases h
        exact RuleSet.capsValid_set hv fun k hk => hv r (List.mem_of_getElem? hr) k hk
    · cases h
  | addCap i k =>
    simp only [RuleSet.attenuate, RuleSet.addCap] at h
    split at h
    · split at h
      · cases h
      · split at h
        · rename_i hk
          cases h
          exact RuleSet.capsValid_set hv fun k' hk' => by
            simp only [Option.some.injEq] at hk'
            exact hk' ▸ hk
        · cases h
    · cases h
  | lowerCapLimit i limit =>
    simp only [RuleSet.attenuate, RuleSet.lowerCapLimit] at h
    split at h
    · rename_i r hr
      split at h
      · rename_i k hc
        split at h
        · cases h
        · split at h
          · cases h
          · rename_i hz
            cases h
            refine RuleSet.capsValid_set hv fun k' hk' => ?_
            simp only [Option.some.injEq] at hk'
            subst hk'
            have hk := hv r (List.mem_of_getElem? hr) k hc
            simp only [Cap.Params.valid, Bool.and_eq_true, decide_eq_true_eq] at hk ⊢
            exact ⟨by simp only [RuleCap.withLimit]; omega, hk.2⟩
      · cases h
    · cases h
  | lengthenCapPeriod i period =>
    simp only [RuleSet.attenuate, RuleSet.lengthenCapPeriod] at h
    split at h
    · rename_i r hr
      split at h
      · rename_i k hc
        split at h
        · cases h
        · rename_i hp
          cases h
          refine RuleSet.capsValid_set hv fun k' hk' => ?_
          simp only [Option.some.injEq] at hk'
          subst hk'
          have hk := hv r (List.mem_of_getElem? hr) k hc
          simp only [Cap.Params.valid, Bool.and_eq_true, decide_eq_true_eq] at hk ⊢
          exact ⟨hk.1, by simp only [RuleCap.withPeriod]; omega⟩
      · cases h
    · cases h

/-- Every list of steps keeps every cap valid. -/
theorem RuleSet.attenuateAll_capsValid :
    ∀ {steps : List (Attenuation Ctx Sig)} {root rs : RuleSet Ctx Sig},
      root.capsValid → root.attenuateAll steps = .ok rs → rs.capsValid
  | [], root, rs, hv, h => by
    simp only [RuleSet.attenuateAll, List.foldlM_nil] at h
    cases h
    exact hv
  | a :: steps, root, rs, hv, h => by
    simp only [RuleSet.attenuateAll] at h
    rw [foldlM_except_cons] at h
    cases ha : root.attenuate a with
    | error e => rw [ha] at h; cases h
    | ok rs₁ =>
      rw [ha] at h
      exact RuleSet.attenuateAll_capsValid (root := rs₁) (RuleSet.attenuate_capsValid hv ha) h

end

end RuleCore
