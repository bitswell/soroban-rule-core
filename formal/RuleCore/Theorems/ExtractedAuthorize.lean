import RuleCore.Equiv.Authorize
import RuleCore.Theorems.Extracted
import RuleCore.Theorems.ExtractedCap

/-!
# Theorems on the extracted authorization

The theorems of `RuleCore.Theorems.Authorize`, carried over to the Lean
translation of `crates/rule-eval` through `authorize_eq` and the equivalence
theorems of the attenuation steps.

One authorization:

* `authorize_allows_all`: an `authorize` that returned `Ok` means the
  extracted `allows_all` accepts the same contexts under the same signers; the
  stateful check is sound with respect to the view without caps, time or
  generation.
* `authorize_valid_until`: it chose no rule whose last ledger is before `now`.
* `authorize_generation`, `authorize_not_chosen_of_stale`,
  `authorize_contexts_nil_of_stale`: it chose no rule issued under a generation
  other than `generation`, so a rule issued under `g` authorizes nothing once
  the generation is not `g`, and a rule set issued under `g` accepts only an
  empty batch.
* `authorize_signers`: every authenticated signer is a signer of a chosen
  rule.

Runs (`runAuthorizations`, which keeps the records after a refusal as a
contract shell does when it stores what `authorize` returns only on `Ok`):

* `runAuthorizations_eq`: a run returns `ok` of records denoting the model's
  run on the denoted authorizations, so it never panics and never diverges;
* `runAuthorizations_of_err`: a refused authorization leaves the records as
  they were;
* `runAuthorizations_window`: from empty records (`emptyRecords`), the stored
  record of a capped rule denotes exactly the spends the run recorded there in
  the window at its last spend's ledger, with their sum as total, when the
  period is nonzero and that ledger is 1 or later;
* `runAuthorizations_window_le_limit`: in every window, the spends a run
  records for a capped rule with a non-negative limit sum to at most it;
* `runAuthorizations_length_le`: that record never holds more than
  `MAX_HISTORY_ENTRIES` entries.

Narrowing as trace inclusion (`TraceNarrower`: every run of authorizations the
narrower rule set accepts from its empty records, the wider one accepts from its
own with each choice `j` renumbered to `f j`; `Renumbered` relates the two
runs):

* `traceNarrower_of_denote`: the model's trace inclusion on the denotations
  gives it on the extracted `authorize`;
* `StepAlong.traceNarrower`: each of the ten extracted steps, along the
  renumbering it induces (`drop_rule` at `index` moves every rule after
  `index` down by one; every other step keeps each index), through the chain
  step it denotes (`StepAlong.denote_step`);
* `DerivesAlong.traceNarrower`: every chain of extracted steps, along the
  composed renumbering.

Generations:

* `StepAlong.generation`, `DerivesAlong.generation`,
  `DerivesAlong.generation_eq`: no extracted step changes a rule's
  generation, so a rule set derived from a root issued under `g` is issued
  under `g`.

A renumbered choice is a `u32`, so a renumbered run exists only when every
renumbered index fits one; for a rule set of more than `2^32` rules, a run
choosing a rule past index `2^32 - 2` after a `drop_rule` has no renumbered
counterpart, and `TraceNarrower` says nothing about it.
-/

namespace RuleCore.Extracted

open Aeneas Aeneas.Std Result RuleCore.Equiv

/-! ## One authorization -/

/-- Soundness of the extracted stateful check: an `authorize` that returned
`Ok` means the extracted `allows_all` accepts the same contexts under the same
authenticated signers. -/
theorem authorize_allows_all {rules : Slice rule_eval.rule.Rule}
    {records : Slice rule_eval.cap.SpendRecord} {contexts : Slice rule_eval.context.Context}
    {choices : Slice Std.U32} {authenticated : Slice rule_eval.signer.Signer} {now : Std.U32}
    {generation : Std.U64} {out : alloc.vec.Vec rule_eval.cap.SpendRecord}
    (h : rule_eval.authorize.authorize rules records contexts choices authenticated now
      generation = ok (.Ok out)) :
    rule_eval.rule_set.allows_all rules contexts authenticated = ok true := by
  obtain ⟨res, hres, hd⟩ := authorize_eq rules records contexts choices authenticated now
    generation
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  rw [allows_all_eq]
  simp only [denoteAuthorized] at hd
  exact congrArg ok (Chain.RuleSet.authorize_allowsAll hd.symm)

/-! ## Runs -/

/-- One authorization's arguments, as Rust values. -/
structure AuthCall where
  contexts : Slice rule_eval.context.Context
  choices : Slice Std.U32
  authenticated : Slice rule_eval.signer.Signer
  now : Std.U32
  generation : Std.U64

/-- An authorization's arguments, as the chain vocabulary's authorization. -/
def AuthCall.denote (a : AuthCall) : Chain.Authorization :=
  denoteAuthorization a.contexts a.choices a.authenticated a.now a.generation

/-- A run of the extracted `authorize` from `records`: each authorization's
records, or the same records when it is refused. -/
def runAuthorizations (rules : Slice rule_eval.rule.Rule)
    (records : alloc.vec.Vec rule_eval.cap.SpendRecord) :
    List AuthCall → Result (alloc.vec.Vec rule_eval.cap.SpendRecord)
  | [] => ok records
  | a :: auths => do
    let res ← rule_eval.authorize.authorize rules (alloc.vec.Vec.deref records) a.contexts
      a.choices a.authenticated a.now a.generation
    match res with
    | .Ok records' => runAuthorizations rules records' auths
    | .Err _ => runAuthorizations rules records auths

/-- Every authorization of a run, in order, failing with the first refusal. -/
def authorizeAll (rules : Slice rule_eval.rule.Rule)
    (records : alloc.vec.Vec rule_eval.cap.SpendRecord) :
    List AuthCall →
      Result (core.result.Result (alloc.vec.Vec rule_eval.cap.SpendRecord)
        rule_eval.authorize.Refusal)
  | [] => ok (.Ok records)
  | a :: auths => do
    let res ← rule_eval.authorize.authorize rules (alloc.vec.Vec.deref records) a.contexts
      a.choices a.authenticated a.now a.generation
    match res with
    | .Ok records' => authorizeAll rules records' auths
    | .Err e => ok (.Err e)

/-- `rules` accepts every authorization of `as`, in order, from `records`. -/
def Accepts (rules : Slice rule_eval.rule.Rule) (records : alloc.vec.Vec rule_eval.cap.SpendRecord)
    (auths : List AuthCall) : Prop :=
  ∃ out, authorizeAll rules records auths = ok (.Ok out)

/-- One empty record per rule of `rules`. -/
def emptyRecords (rules : Slice rule_eval.rule.Rule) : alloc.vec.Vec rule_eval.cap.SpendRecord :=
  ⟨Slice.from (rules.val.map fun _ => ⟨alloc.vec.Vec.new rule_eval.cap.SpendEntry, 0#i128⟩)
    (by simp)⟩

theorem emptyRecords_denote (rules : Slice rule_eval.rule.Rule) :
    (emptyRecords rules).val.map denoteRecord = (denoteRules rules.val).emptyRecords := by
  simp only [emptyRecords, alloc.vec.Vec.val, Slice.from_val, List.map_map,
    Chain.RuleSet.emptyRecords, denoteRules]
  apply List.map_congr_left
  intro x _
  simp [denoteRecord, Cap.Record.empty]

theorem emptyRecords_denote_rules (rules : Slice rule_eval.rule.Rule) :
    (emptyRecords rules).val.map denoteRecord = (denoteRules rules.val).denote.emptyRecords := by
  rw [Chain.RuleSet.emptyRecords_denote, emptyRecords_denote]

/-- On every input, a run of the extracted `authorize` returns `ok` of records
whose denotation is the model's run on the denoted authorizations. -/
theorem runAuthorizations_eq (rules : Slice rule_eval.rule.Rule) :
    ∀ (auths : List AuthCall) (records : alloc.vec.Vec rule_eval.cap.SpendRecord),
      ∃ out, runAuthorizations rules records auths = ok out ∧
        out.val.map denoteRecord =
          (denoteRules rules.val).denote.run (records.val.map denoteRecord)
            (auths.map fun a => a.denote.denote)
  | [], records => ⟨records, rfl, rfl⟩
  | a :: auths, records => by
    obtain ⟨res, hres, hd⟩ := authorize_eq rules (alloc.vec.Vec.deref records) a.contexts
      a.choices a.authenticated a.now a.generation
    simp only [vec_deref_val] at hd
    simp only [runAuthorizations, hres, bind_ok, List.map_cons, RuleSet.run_cons, RuleSet.step]
    have hm : (denoteRules rules.val).denote.authorize (records.val.map denoteRecord)
        a.denote.denote = denoteAuthorized res := hd.symm
    rw [hm]
    cases res with
    | Ok r' => exact runAuthorizations_eq rules auths r'
    | Err e => exact runAuthorizations_eq rules auths records

/-- A refused authorization leaves the records as they were. -/
theorem runAuthorizations_of_err {rules : Slice rule_eval.rule.Rule}
    {records : alloc.vec.Vec rule_eval.cap.SpendRecord} {a : AuthCall} {auths : List AuthCall}
    {e : rule_eval.authorize.Refusal}
    (h : rule_eval.authorize.authorize rules (alloc.vec.Vec.deref records) a.contexts a.choices
      a.authenticated a.now a.generation = ok (.Err e)) :
    runAuthorizations rules records (a :: auths) = runAuthorizations rules records auths := by
  simp [runAuthorizations, h]

/-- On every input, the extracted run of `authorizeAll` returns `ok` of the
model's on the denoted authorizations. -/
theorem authorizeAll_eq (rules : Slice rule_eval.rule.Rule) :
    ∀ (auths : List AuthCall) (records : alloc.vec.Vec rule_eval.cap.SpendRecord),
      ∃ res, authorizeAll rules records auths = ok res ∧
        denoteAuthorized res =
          (denoteRules rules.val).denote.authorizeAll (records.val.map denoteRecord)
            (auths.map fun a => a.denote.denote)
  | [], records => ⟨.Ok records, rfl, rfl⟩
  | a :: auths, records => by
    obtain ⟨res, hres, hd⟩ := authorize_eq rules (alloc.vec.Vec.deref records) a.contexts
      a.choices a.authenticated a.now a.generation
    simp only [vec_deref_val] at hd
    simp only [authorizeAll, hres, bind_ok, List.map_cons, RuleSet.authorizeAll,
      List.foldlM_cons]
    have hm : (denoteRules rules.val).denote.authorize (records.val.map denoteRecord)
        a.denote.denote = denoteAuthorized res := hd.symm
    rw [hm]
    cases res with
    | Ok r' => exact authorizeAll_eq rules auths r'
    | Err e => exact ⟨.Err e, rfl, rfl⟩

theorem accepts_iff (rules : Slice rule_eval.rule.Rule)
    (records : alloc.vec.Vec rule_eval.cap.SpendRecord) (auths : List AuthCall) :
    Accepts rules records auths ↔
      (denoteRules rules.val).denote.Accepts (records.val.map denoteRecord)
        (auths.map fun a => a.denote.denote) := by
  obtain ⟨res, hres, hd⟩ := authorizeAll_eq rules auths records
  constructor
  · rintro ⟨out, hout⟩
    obtain rfl := Result.ok_injective (hout.symm.trans hres)
    exact ⟨_, hd.symm⟩
  · rintro ⟨recs, hrecs⟩
    rw [hrecs] at hd
    cases res with
    | Ok out => exact ⟨out, hres⟩
    | Err e => simp [denoteAuthorized] at hd

/-! ## Window safety -/

theorem emptyRecords_length (rules : Slice rule_eval.rule.Rule) :
    ((emptyRecords rules).val.map denoteRecord).length = rules.val.length := by
  simp [emptyRecords, alloc.vec.Vec.val, Slice.from_val]

/-- From empty records, with a nonzero period and the last spend at ledger 1 or
later, the stored record of a rule with a cap denotes exactly the spends the
run recorded there in the window at that spend's ledger, and its total is their
sum. -/
theorem runAuthorizations_window (rules : Slice rule_eval.rule.Rule) {j : Nat}
    {r : rule_eval.rule.Rule} {c : rule_eval.rule.Cap} (hr : rules.val[j]? = some r)
    (hc : r.cap = some c) (hp : 0 < c.period.val) (auths : List AuthCall) {A : List Cap.Entry}
    {e : Cap.Entry}
    (h : (denoteRules rules.val).denote.spent (denoteCap c).denote j
      (denoteRules rules.val).denote.emptyRecords (auths.map fun a => a.denote.denote) = A ++ [e])
    (he : 0 < e.ledger) :
    ∃ out rec, runAuthorizations rules (emptyRecords rules) auths = ok out ∧
      out.val[j]? = some rec ∧
      (denoteRecord rec).history =
        ((denoteRules rules.val).denote.spent (denoteCap c).denote j
          (denoteRules rules.val).denote.emptyRecords (auths.map fun a => a.denote.denote)).filter
          ((denoteCap c).denote.params.inWindow e.ledger) ∧
      (denoteRecord rec).total = Cap.amountSum (denoteRecord rec).history := by
  obtain ⟨out, hout, hd⟩ := runAuthorizations_eq rules auths (emptyRecords rules)
  rw [emptyRecords_denote_rules] at hd
  have hrd : (denoteRules rules.val).denote.rules[j]? = some (denoteRule r).denote := by
    rw [denoteRules_rules_get, hr]
    rfl
  have hcd : (denoteRule r).denote.cap = some (denoteCap c).denote := by
    simp [denoteRule_denote_cap, hc]
  obtain ⟨rec, hrec, hh, ht⟩ := RuleSet.run_eq_window _ hrd hcd hp _ h he
  rw [← hd, List.getElem?_map] at hrec
  cases hj : out.val[j]? with
  | none => rw [hj] at hrec; cases hrec
  | some x =>
    rw [hj] at hrec
    simp only [Option.map_some, Option.some.injEq] at hrec
    subst hrec
    exact ⟨out, x, hout, hj, hh, ht⟩

/-- Window safety on the extracted run: from empty records, the spends a run
records for a rule with a cap of non-negative limit, in the window eviction
leaves at any ledger `t`, sum to at most the limit. -/
theorem runAuthorizations_window_le_limit (rules : Slice rule_eval.rule.Rule) {j : Nat}
    {r : rule_eval.rule.Rule} {c : rule_eval.rule.Cap} (hr : rules.val[j]? = some r)
    (hc : r.cap = some c) (hl : 0 ≤ c.limit.val) (auths : List AuthCall) (t : Nat) :
    Cap.amountSum (((denoteRules rules.val).denote.spent (denoteCap c).denote j
        (denoteRules rules.val).denote.emptyRecords (auths.map fun a => a.denote.denote)).filter
        ((denoteCap c).denote.params.inWindow t)) ≤ c.limit.val := by
  have hrd : (denoteRules rules.val).denote.rules[j]? = some (denoteRule r).denote := by
    rw [denoteRules_rules_get, hr]
    rfl
  have hcd : (denoteRule r).denote.cap = some (denoteCap c).denote := by
    simp [denoteRule_denote_cap, hc]
  exact RuleSet.window_le_limit _ hrd hcd hl _ t

/-- The stored record of a rule with a cap never holds more than
`MAX_HISTORY_ENTRIES` entries, from empty records. -/
theorem runAuthorizations_length_le (rules : Slice rule_eval.rule.Rule) {j : Nat}
    {r : rule_eval.rule.Rule} {c : rule_eval.rule.Cap} (hr : rules.val[j]? = some r)
    (hc : r.cap = some c) (auths : List AuthCall) :
    ∃ out rec, runAuthorizations rules (emptyRecords rules) auths = ok out ∧
      out.val[j]? = some rec ∧ rec.history.val.length ≤ rule_eval.cap.MAX_HISTORY_ENTRIES.val := by
  obtain ⟨out, hout, hd⟩ := runAuthorizations_eq rules auths (emptyRecords rules)
  rw [emptyRecords_denote_rules] at hd
  have hrd : (denoteRules rules.val).denote.rules[j]? = some (denoteRule r).denote := by
    rw [denoteRules_rules_get, hr]
    rfl
  have hcd : (denoteRule r).denote.cap = some (denoteCap c).denote := by
    simp [denoteRule_denote_cap, hc]
  obtain ⟨rec, hrec, hlen⟩ := RuleSet.run_history_length_le _ hrd hcd (auths.map fun a => a.denote.denote)
  rw [← hd, List.getElem?_map] at hrec
  cases hj : out.val[j]? with
  | none => rw [hj] at hrec; cases hrec
  | some x =>
    rw [hj] at hrec
    simp only [Option.map_some, Option.some.injEq] at hrec
    subst hrec
    refine ⟨out, x, hout, hj, ?_⟩
    simpa [denoteRecord, max_history_val] using hlen

/-! ## Narrowing as trace inclusion -/

/-- `b` is `a` with each choice `j` renumbered to `f j`. -/
def Renumbered (f : Nat → Nat) (a b : AuthCall) : Prop :=
  b.contexts = a.contexts ∧ b.authenticated = a.authenticated ∧ b.now = a.now ∧
    b.generation = a.generation ∧ b.choices.val.map (·.val) = a.choices.val.map fun x => f x.val

/-- `rules'` is narrower than `rules` as trace inclusion along `f` on the
extracted `authorize`: every run of authorizations `rules'` accepts from its
empty records, `rules` accepts from its own, with each choice `j` renumbered to
`f j`. -/
def TraceNarrower (rules' rules : Slice rule_eval.rule.Rule) (f : Nat → Nat) : Prop :=
  ∀ auths auths', List.Forall₂ (Renumbered f) auths auths' → Accepts rules' (emptyRecords rules') auths →
    Accepts rules (emptyRecords rules) auths'

theorem renumbered_denote {f : Nat → Nat} {a b : AuthCall} (h : Renumbered f a b) :
    a.denote.denote.renumber f = b.denote.denote := by
  obtain ⟨hc, ha, hn, hg, hch⟩ := h
  simp only [AuthCall.denote, denoteAuthorization, Chain.Authorization.denote,
    Authorization.renumber, hc, ha, hn, hg, List.map_map, Function.comp_def, denoteU32_toNat]
  congr 1
  exact hch.symm

theorem renumbered_map {f : Nat → Nat} :
    ∀ {auths auths' : List AuthCall}, List.Forall₂ (Renumbered f) auths auths' →
      (auths.map fun a => a.denote.denote).map (·.renumber f) = auths'.map fun b => b.denote.denote
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, renumbered_denote h, renumbered_map hs]

/-- The model's trace inclusion on the denotations gives trace inclusion on the
extracted `authorize`. -/
theorem traceNarrower_of_denote {rules' rules : Slice rule_eval.rule.Rule} {f : Nat → Nat}
    (h : (denoteRules rules'.val).TraceNarrower (denoteRules rules.val) f) :
    TraceNarrower rules' rules f := by
  intro auths auths' hab ha
  rw [accepts_iff, emptyRecords_denote_rules] at ha ⊢
  rw [← renumbered_map hab]
  exact h _ ha

/-- One extracted attenuation step that returned `Ok`, along the renumbering it
induces: `drop_rule` at `index` sends `j` to `j` below `index` and to `j + 1`
from it on; every other step sends `j` to `j`. -/
inductive StepAlong (rs : Slice rule_eval.rule.Rule) :
    Slice rule_eval.rule.Rule → (Nat → Nat) → Prop where
  | dropRule (index : Std.U32) {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.drop_rule rs index = ok (.Ok out) →
        StepAlong rs (alloc.vec.Vec.deref out) fun j => if j < index.val then j else j + 1
  | addCond (index : Std.U32) (cond : rule_eval.rule.Cond)
      {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.add_cond rs index cond = ok (.Ok out) →
        StepAlong rs (alloc.vec.Vec.deref out) fun j => j
  | removeFunctions (index : Std.U32) (functions : Slice (alloc.vec.Vec Std.U8))
      {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.remove_functions rs index functions = ok (.Ok out) →
        StepAlong rs (alloc.vec.Vec.deref out) fun j => j
  | restrictFunctions (index : Std.U32) (functions : Slice (alloc.vec.Vec Std.U8))
      {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.restrict_functions rs index functions = ok (.Ok out) →
        StepAlong rs (alloc.vec.Vec.deref out) fun j => j
  | removeSigners (index : Std.U32) (signers : Slice rule_eval.signer.Signer)
      {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.remove_signers rs index signers = ok (.Ok out) →
        StepAlong rs (alloc.vec.Vec.deref out) fun j => j
  | raiseThreshold (index threshold : Std.U32) {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.raise_threshold rs index threshold = ok (.Ok out) →
        StepAlong rs (alloc.vec.Vec.deref out) fun j => j
  | addCap (index : Std.U32) (new_cap : rule_eval.rule.Cap)
      {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.add_cap rs index new_cap = ok (.Ok out) →
        StepAlong rs (alloc.vec.Vec.deref out) fun j => j
  | lowerCapLimit (index : Std.U32) (limit : Std.I128) {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.lower_cap_limit rs index limit = ok (.Ok out) →
        StepAlong rs (alloc.vec.Vec.deref out) fun j => j
  | lengthenCapPeriod (index period : Std.U32) {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.lengthen_cap_period rs index period = ok (.Ok out) →
        StepAlong rs (alloc.vec.Vec.deref out) fun j => j
  | lowerValidUntil (index valid_until : Std.U32) {out : alloc.vec.Vec rule_eval.rule.Rule} :
      rule_eval.attenuate.lower_valid_until rs index valid_until = ok (.Ok out) →
        StepAlong rs (alloc.vec.Vec.deref out) fun j => j

/-- `DerivesAlong root rs f`: `rs` is reachable from `root` by zero or more
extracted attenuation steps, and `f` is the composed renumbering: the rule at
index `j` of `rs` comes from the rule at index `f j` of `root`. -/
inductive DerivesAlong (root : Slice rule_eval.rule.Rule) :
    Slice rule_eval.rule.Rule → (Nat → Nat) → Prop where
  | refl : DerivesAlong root root fun j => j
  | step {rs rs' : Slice rule_eval.rule.Rule} {f g : Nat → Nat} :
      DerivesAlong root rs f → StepAlong rs rs' g → DerivesAlong root rs' fun j => f (g j)

/-- Each extracted step is the chain step it denotes, on the denotations, and
its renumbering is that step's. -/
theorem StepAlong.denote_step {rs rs' : Slice rule_eval.rule.Rule} {f : Nat → Nat} :
    StepAlong rs rs' f → ∃ a : Chain.Attenuation,
      (denoteRules rs.val).attenuate a = .ok (denoteRules rs'.val) ∧ a.denote.source = f
  | .dropRule index h => by
    obtain ⟨res, hres, hd⟩ := drop_rule_eq rs index
    obtain rfl := Result.ok_injective (h.symm.trans hres)
    rw [vec_deref_val]
    exact ⟨.dropRule (denoteU32 index), hd.symm, rfl⟩
  | .addCond index cond h => by
    obtain ⟨res, hres, hd⟩ := add_cond_eq rs index cond (add_cond_room h)
    obtain rfl := Result.ok_injective (h.symm.trans hres)
    rw [vec_deref_val]
    exact ⟨.addCond (denoteU32 index) (denoteCond cond), hd.symm, rfl⟩
  | .removeFunctions index functions h => by
    obtain ⟨res, hres, hd⟩ := remove_functions_eq rs index functions (remove_functions_room h)
    obtain rfl := Result.ok_injective (h.symm.trans hres)
    rw [vec_deref_val]
    exact ⟨.removeFunctions (denoteU32 index) (functions.val.map denoteBytes), hd.symm, rfl⟩
  | .restrictFunctions index functions h => by
    obtain ⟨res, hres, hd⟩ := restrict_functions_eq rs index functions
    obtain rfl := Result.ok_injective (h.symm.trans hres)
    rw [vec_deref_val]
    exact ⟨.restrictFunctions (denoteU32 index) (functions.val.map denoteBytes), hd.symm, rfl⟩
  | .removeSigners index signers h => by
    obtain ⟨res, hres, hd⟩ := remove_signers_eq rs index signers
    obtain rfl := Result.ok_injective (h.symm.trans hres)
    rw [vec_deref_val]
    exact ⟨.removeSigners (denoteU32 index) (denoteSigners signers.val), hd.symm, rfl⟩
  | .raiseThreshold index threshold h => by
    obtain ⟨res, hres, hd⟩ := raise_threshold_eq rs index threshold
    obtain rfl := Result.ok_injective (h.symm.trans hres)
    rw [vec_deref_val]
    exact ⟨.raiseThreshold (denoteU32 index) (denoteU32 threshold), hd.symm, rfl⟩
  | .addCap index new_cap h => by
    obtain ⟨res, hres, hd⟩ := add_cap_eq rs index new_cap
    obtain rfl := Result.ok_injective (h.symm.trans hres)
    rw [vec_deref_val]
    exact ⟨.addCap (denoteU32 index) (denoteCap new_cap), hd.symm, rfl⟩
  | .lowerCapLimit index limit h => by
    obtain ⟨res, hres, hd⟩ := lower_cap_limit_eq rs index limit
    obtain rfl := Result.ok_injective (h.symm.trans hres)
    rw [vec_deref_val]
    exact ⟨.lowerCapLimit (denoteU32 index) limit.bv, hd.symm, rfl⟩
  | .lengthenCapPeriod index period h => by
    obtain ⟨res, hres, hd⟩ := lengthen_cap_period_eq rs index period
    obtain rfl := Result.ok_injective (h.symm.trans hres)
    rw [vec_deref_val]
    exact ⟨.lengthenCapPeriod (denoteU32 index) (denoteU32 period), hd.symm, rfl⟩
  | .lowerValidUntil index valid_until h => by
    obtain ⟨res, hres, hd⟩ := lower_valid_until_eq rs index valid_until
    obtain rfl := Result.ok_injective (h.symm.trans hres)
    rw [vec_deref_val]
    exact ⟨.lowerValidUntil (denoteU32 index) (denoteU32 valid_until), hd.symm, rfl⟩

/-- The model's trace inclusion of one extracted step, on the denotations. -/
theorem StepAlong.denote_traceNarrower {rs rs' : Slice rule_eval.rule.Rule} {f : Nat → Nat}
    (h : StepAlong rs rs' f) : (denoteRules rs'.val).TraceNarrower (denoteRules rs.val) f := by
  obtain ⟨a, ha, rfl⟩ := h.denote_step
  exact Chain.RuleSet.attenuate_traceNarrower ha

/-- Each extracted step is narrowing as trace inclusion, along the renumbering
it induces. -/
theorem StepAlong.traceNarrower {rs rs' : Slice rule_eval.rule.Rule} {f : Nat → Nat}
    (h : StepAlong rs rs' f) : TraceNarrower rs' rs f :=
  traceNarrower_of_denote h.denote_traceNarrower

/-- Every chain of extracted steps is narrowing as trace inclusion, along the
composed renumbering. -/
theorem DerivesAlong.traceNarrower {root rs : Slice rule_eval.rule.Rule} {f : Nat → Nat}
    (h : DerivesAlong root rs f) : TraceNarrower rs root f := by
  suffices hd : (denoteRules rs.val).TraceNarrower (denoteRules root.val) f from
    traceNarrower_of_denote hd
  induction h with
  | refl => exact RuleSet.TraceNarrower.refl _
  | step _ hs ih => exact RuleSet.TraceNarrower.trans hs.denote_traceNarrower ih

/-- A chain of extracted steps is also a `Derives`. -/
theorem DerivesAlong.derives {root rs : Slice rule_eval.rule.Rule} {f : Nat → Nat}
    (h : DerivesAlong root rs f) : Derives root rs := by
  induction h with
  | refl => exact .refl
  | step _ hs ih =>
    refine .step ih ?_
    cases hs with
    | dropRule index h => exact .dropRule index h
    | addCond index cond h => exact .addCond index cond h
    | removeFunctions index functions h => exact .removeFunctions index functions h
    | restrictFunctions index functions h => exact .restrictFunctions index functions h
    | removeSigners index signers h => exact .removeSigners index signers h
    | raiseThreshold index threshold h => exact .raiseThreshold index threshold h
    | addCap index new_cap h => exact .addCap index new_cap h
    | lowerCapLimit index limit h => exact .lowerCapLimit index limit h
    | lengthenCapPeriod index period h => exact .lengthenCapPeriod index period h
    | lowerValidUntil index valid_until h => exact .lowerValidUntil index valid_until h

/-! ## Generations -/

/-- No extracted step changes a rule's generation: the rule at index `j` after
a step carries the generation of the rule at index `f j` before it. -/
theorem StepAlong.generation {rs rs' : Slice rule_eval.rule.Rule} {f : Nat → Nat}
    (h : StepAlong rs rs' f) {j : Nat} {r' : rule_eval.rule.Rule} (hj : rs'.val[j]? = some r') :
    ∃ r, rs.val[f j]? = some r ∧ r'.generation = r.generation := by
  obtain ⟨a, ha, rfl⟩ := h.denote_step
  obtain ⟨r, hr, hg⟩ := Chain.RuleSet.attenuate_generation ha (j := j) (r' := denoteRule r')
    (by simp [denoteRules, hj])
  simp only [denoteRules, List.getElem?_map] at hr
  cases hr₀ : rs.val[a.denote.source j]? with
  | none => rw [hr₀] at hr; cases hr
  | some r₀ =>
    rw [hr₀] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    subst hr
    refine ⟨r₀, rfl, ?_⟩
    simp only [denoteRule] at hg
    exact Option.map_injective denoteU64_injective hg

/-- Along a chain of extracted steps, the rule at index `j` carries the
generation of the root rule at index `f j`. -/
theorem DerivesAlong.generation {root rs : Slice rule_eval.rule.Rule} {f : Nat → Nat}
    (h : DerivesAlong root rs f) :
    ∀ {j : Nat} {r' : rule_eval.rule.Rule}, rs.val[j]? = some r' →
      ∃ r, root.val[f j]? = some r ∧ r'.generation = r.generation := by
  induction h with
  | refl => exact fun hj => ⟨_, hj, rfl⟩
  | step _ hs ih =>
    intro j r' hj
    obtain ⟨r₁, hr₁, hg₁⟩ := hs.generation hj
    obtain ⟨r, hr, hg⟩ := ih hr₁
    exact ⟨r, hr, hg₁.trans hg⟩

/-- A rule set derived by extracted steps from a root every rule of which was
issued under `g` has every rule issued under `g`. -/
theorem DerivesAlong.generation_eq {root rs : Slice rule_eval.rule.Rule} {f : Nat → Nat}
    (h : DerivesAlong root rs f) {g : Std.U64} (hall : ∀ r ∈ root.val, r.generation = some g) :
    ∀ r ∈ rs.val, r.generation = some g := by
  intro r' hr'
  obtain ⟨j, hj, hjr⟩ := List.getElem_of_mem hr'
  obtain ⟨r, hr, hg⟩ := h.generation (List.getElem?_eq_some_iff.mpr ⟨hj, hjr⟩)
  rw [hg]
  exact hall r (List.mem_of_getElem? hr)

/-! ## Expiry, generation and signers of one authorization -/

theorem denoteRules_get (rules : Slice rule_eval.rule.Rule) (k : Std.U32) :
    (denoteRules rules.val)[(denoteU32 k).toNat]? = rules.val[k.val]?.map denoteRule := by
  simp [denoteRules, List.getElem?_map]

/-- Expiry: an `authorize` that returned `Ok` chose no rule whose last ledger is
before `now`. -/
theorem authorize_valid_until {rules : Slice rule_eval.rule.Rule}
    {records : Slice rule_eval.cap.SpendRecord} {contexts : Slice rule_eval.context.Context}
    {choices : Slice Std.U32} {authenticated : Slice rule_eval.signer.Signer} {now : Std.U32}
    {generation : Std.U64} {out : alloc.vec.Vec rule_eval.cap.SpendRecord}
    (h : rule_eval.authorize.authorize rules records contexts choices authenticated now
      generation = ok (.Ok out))
    {k : Std.U32} (hk : k ∈ choices.val) {r : rule_eval.rule.Rule}
    (hr : rules.val[k.val]? = some r) {last : Std.U32} (hl : r.valid_until = some last) :
    now.val ≤ last.val := by
  obtain ⟨res, hres, hd⟩ := authorize_eq rules records contexts choices authenticated now
    generation
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  simp only [denoteAuthorized] at hd
  have := Chain.RuleSet.authorize_validUntil hd.symm (j := denoteU32 k)
    (by simpa [denoteAuthorization] using List.mem_map_of_mem (f := denoteU32) hk)
    (r := denoteRule r) (by rw [denoteRules_get, hr]; rfl) (last := denoteU32 last)
    (by simp [denoteRule, hl])
  simpa [denoteAuthorization, UInt32.le_iff_toNat_le] using this

/-- Generation: an `authorize` that returned `Ok` chose no rule issued under a
generation other than `generation`. -/
theorem authorize_generation {rules : Slice rule_eval.rule.Rule}
    {records : Slice rule_eval.cap.SpendRecord} {contexts : Slice rule_eval.context.Context}
    {choices : Slice Std.U32} {authenticated : Slice rule_eval.signer.Signer} {now : Std.U32}
    {generation : Std.U64} {out : alloc.vec.Vec rule_eval.cap.SpendRecord}
    (h : rule_eval.authorize.authorize rules records contexts choices authenticated now
      generation = ok (.Ok out))
    {k : Std.U32} (hk : k ∈ choices.val) {r : rule_eval.rule.Rule}
    (hr : rules.val[k.val]? = some r) {g : Std.U64} (hg : r.generation = some g) :
    g = generation := by
  obtain ⟨res, hres, hd⟩ := authorize_eq rules records contexts choices authenticated now
    generation
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  simp only [denoteAuthorized] at hd
  have := Chain.RuleSet.authorize_generation hd.symm (j := denoteU32 k)
    (by simpa [denoteAuthorization] using List.mem_map_of_mem (f := denoteU32) hk)
    (r := denoteRule r) (by rw [denoteRules_get, hr]; rfl) (g := denoteU64 g)
    (by simp [denoteRule, hg])
  exact denoteU64_injective (by simpa [denoteAuthorization] using this)

/-- Once the current generation is not `g`, a rule issued under `g` authorizes
nothing: no `authorize` that returned `Ok` chose it. -/
theorem authorize_not_chosen_of_stale {rules : Slice rule_eval.rule.Rule}
    {records : Slice rule_eval.cap.SpendRecord} {contexts : Slice rule_eval.context.Context}
    {choices : Slice Std.U32} {authenticated : Slice rule_eval.signer.Signer} {now : Std.U32}
    {generation : Std.U64} {out : alloc.vec.Vec rule_eval.cap.SpendRecord}
    (h : rule_eval.authorize.authorize rules records contexts choices authenticated now
      generation = ok (.Ok out))
    {k : Std.U32} {r : rule_eval.rule.Rule} (hr : rules.val[k.val]? = some r) {g : Std.U64}
    (hg : r.generation = some g) (hne : g ≠ generation) : k ∉ choices.val :=
  fun hk => hne (authorize_generation h hk hr hg)

/-- A rule set every rule of which was issued under `g` accepts, once the
current generation is not `g`, only an authorization with no contexts. -/
theorem authorize_contexts_nil_of_stale {rules : Slice rule_eval.rule.Rule}
    {records : Slice rule_eval.cap.SpendRecord} {contexts : Slice rule_eval.context.Context}
    {choices : Slice Std.U32} {authenticated : Slice rule_eval.signer.Signer} {now : Std.U32}
    {generation : Std.U64} {out : alloc.vec.Vec rule_eval.cap.SpendRecord}
    (h : rule_eval.authorize.authorize rules records contexts choices authenticated now
      generation = ok (.Ok out))
    {g : Std.U64} (hall : ∀ r ∈ rules.val, r.generation = some g) (hne : g ≠ generation) :
    contexts.val = [] := by
  obtain ⟨res, hres, hd⟩ := authorize_eq rules records contexts choices authenticated now
    generation
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  simp only [denoteAuthorized] at hd
  have := Chain.RuleSet.authorize_contexts_nil_of_stale hd.symm (g := denoteU64 g)
    (by
      intro r hr
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      simp [denoteRule, hall r₀ hr₀])
    (fun he => hne (denoteU64_injective he))
  simpa [denoteAuthorization] using this

/-- Signers: every signer an `authorize` that returned `Ok` authenticated is,
by `signer_in`, a signer of some rule it chose. -/
theorem authorize_signers {rules : Slice rule_eval.rule.Rule}
    {records : Slice rule_eval.cap.SpendRecord} {contexts : Slice rule_eval.context.Context}
    {choices : Slice Std.U32} {authenticated : Slice rule_eval.signer.Signer} {now : Std.U32}
    {generation : Std.U64} {out : alloc.vec.Vec rule_eval.cap.SpendRecord}
    (h : rule_eval.authorize.authorize rules records contexts choices authenticated now
      generation = ok (.Ok out)) :
    ∀ s ∈ authenticated.val, ∃ k ∈ choices.val, ∃ r, rules.val[k.val]? = some r ∧
      rule_eval.signer.signer_in s (alloc.vec.Vec.deref r.signers) = ok true := by
  obtain ⟨res, hres, hd⟩ := authorize_eq rules records contexts choices authenticated now
    generation
  obtain rfl := Result.ok_injective (h.symm.trans hres)
  simp only [denoteAuthorized] at hd
  intro s hs
  obtain ⟨j, hj, r', hr', hsr⟩ := Chain.RuleSet.authorize_signers hd.symm (denoteSigner s)
    (by simpa [denoteAuthorization, denoteSigners] using List.mem_map_of_mem (f := denoteSigner) hs)
  simp only [denoteAuthorization, List.mem_map] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  rw [denoteRules_get] at hr'
  cases hr₀ : rules.val[k.val]? with
  | none => rw [hr₀] at hr'; cases hr'
  | some r₀ =>
    rw [hr₀] at hr'
    simp only [Option.map_some, Option.some.injEq] at hr'
    subst hr'
    refine ⟨k, hk, r₀, hr₀, ?_⟩
    rw [signer_in_eq, vec_deref_val]
    exact congrArg ok (decide_eq_true hsr)

end RuleCore.Extracted
