import RuleCore.Equiv.Cap

/-!
# Theorems on the extracted cap check

`runSpends` runs the extracted `check_spend` over a list of calls, keeping the
record unchanged on a refusal, as a contract shell does when it stores what
`check_spend` returns only on `Ok`. `runSpends_eq` proves that it returns `ok`
of a record whose denotation is the model's `Params.run`, so every theorem of
`RuleCore.Theorems.Cap` about the stored record holds of the record the Rust
code computes:

* `runSpends_window`: from the empty record, with a nonzero period and the last
  recorded spend at ledger 1 or later, the stored history denotes exactly the
  recorded spends in the window at that spend's ledger, and the stored total
  is their sum;
* `runSpends_length_le`: the stored history never holds more than
  `MAX_HISTORY_ENTRIES` entries.

The remaining theorems state single outcomes on the extracted function alone:
a negative amount is refused (`check_spend_negative`), a zero amount returns
the record unchanged (`check_spend_zero`), and a positive spend earlier than
the newest recorded ledger is refused (`check_spend_before_newest`).
-/

namespace RuleCore.Extracted

open Aeneas Aeneas.Std Result RuleCore.Equiv

/-- A call of a run, as Rust values: the current ledger and the amount. -/
def callOf (k : Std.U32 × Std.I128) : Cap.Call := ⟨k.1.val, k.2.val⟩

/-- A run of the extracted check from `record`: each call's checked record, or
the same record when the check refuses. -/
def runSpends (record : rule_eval.cap.SpendRecord) (limit : Std.I128) (period : Std.U32) :
    List (Std.U32 × Std.I128) → Result rule_eval.cap.SpendRecord
  | [] => ok record
  | k :: ks => do
    let res ← rule_eval.cap.check_spend record limit period k.1 k.2
    match res with
    | .Ok r' => runSpends r' limit period ks
    | .Err _ => runSpends record limit period ks

/-- On every input, a run of the extracted check returns `ok` of a record whose
denotation is the model's run on the denoted calls. -/
theorem runSpends_eq (limit : Std.I128) (period : Std.U32) :
    ∀ (calls : List (Std.U32 × Std.I128)) (record : rule_eval.cap.SpendRecord),
      ∃ r', runSpends record limit period calls = ok r' ∧
        denoteRecord r' =
          (⟨limit.val, period.val⟩ : Cap.Params).run (denoteRecord record) (calls.map callOf)
  | [], record => ⟨record, rfl, rfl⟩
  | k :: ks, record => by
    obtain ⟨res, hres, hden⟩ := check_spend_eq record limit period k.1 k.2
    simp only [runSpends, hres, bind_ok, List.map_cons, Cap.run_cons, Cap.Params.step, callOf]
    cases res with
    | Ok r' =>
      simp only [denoteSpend] at hden
      rw [← hden]
      exact runSpends_eq limit period ks r'
    | Err e =>
      simp only [denoteSpend] at hden
      rw [← hden]
      exact runSpends_eq limit period ks record

/-- The empty record denotes the model's empty record. -/
theorem empty_record_denote :
    ∃ r, rule_eval.cap.empty_record = ok r ∧ denoteRecord r = Cap.Record.empty :=
  empty_record_eq

/-- From the empty record, with a nonzero period and the last recorded spend at
ledger 1 or later, the record the extracted check stores denotes exactly the
recorded spends in the window at that spend's ledger, and its total is their
sum. -/
theorem runSpends_window (limit : Std.I128) (period : Std.U32) (hp : 0 < period.val)
    (calls : List (Std.U32 × Std.I128)) {A : List Cap.Entry} {e : Cap.Entry}
    (h : (⟨limit.val, period.val⟩ : Cap.Params).recorded .empty (calls.map callOf) = A ++ [e])
    (he : 0 < e.ledger) :
    ∃ empty r', rule_eval.cap.empty_record = ok empty ∧ runSpends empty limit period calls = ok r' ∧
      (denoteRecord r').history =
        ((⟨limit.val, period.val⟩ : Cap.Params).recorded .empty (calls.map callOf)).filter
          ((⟨limit.val, period.val⟩ : Cap.Params).inWindow e.ledger) ∧
      (denoteRecord r').total = Cap.amountSum (denoteRecord r').history := by
  obtain ⟨empty, he0, hd0⟩ := empty_record_eq
  obtain ⟨r', hr, hd⟩ := runSpends_eq limit period calls empty
  rw [hd0] at hd
  obtain ⟨hh, ht⟩ := Cap.run_eq_window _ hp _ h he
  refine ⟨empty, r', he0, hr, by rw [hd, hh], by rw [hd, ht, hh]⟩

/-- The record the extracted check stores never holds more than
`MAX_HISTORY_ENTRIES` entries, from the empty record. -/
theorem runSpends_length_le (limit : Std.I128) (period : Std.U32)
    (calls : List (Std.U32 × Std.I128)) :
    ∃ empty r', rule_eval.cap.empty_record = ok empty ∧ runSpends empty limit period calls = ok r' ∧
      r'.history.val.length ≤ rule_eval.cap.MAX_HISTORY_ENTRIES.val := by
  obtain ⟨empty, he0, hd0⟩ := empty_record_eq
  obtain ⟨r', hr, hd⟩ := runSpends_eq limit period calls empty
  rw [hd0] at hd
  refine ⟨empty, r', he0, hr, ?_⟩
  have := Cap.run_history_length_le ⟨limit.val, period.val⟩ Cap.Record.empty_valid (by simp)
    (calls.map callOf)
  rw [← hd] at this
  simpa [denoteRecord, max_history_val] using this

/-- A negative amount is refused. -/
theorem check_spend_negative (record : rule_eval.cap.SpendRecord) (limit : Std.I128)
    (period now : Std.U32) {amount : Std.I128} (h : amount.val < 0) :
    rule_eval.cap.check_spend record limit period now amount = ok (.Err .NegativeAmount) := by
  have : amount < 0#i128 := by simpa using h
  simp [rule_eval.cap.check_spend, this]

/-- A zero amount returns the record unchanged. -/
theorem check_spend_zero (record : rule_eval.cap.SpendRecord) (limit : Std.I128)
    (period now : Std.U32) :
    rule_eval.cap.check_spend record limit period now 0#i128 = ok (.Ok record) := by
  simp [rule_eval.cap.check_spend, record_copy_eq]

/-- A positive spend at a ledger earlier than that of the last recorded entry
is refused. -/
theorem check_spend_before_newest (record : rule_eval.cap.SpendRecord) (limit : Std.I128)
    (period now : Std.U32) {amount : Std.I128} (ha : 0 < amount.val)
    {l : List rule_eval.cap.SpendEntry} {last : rule_eval.cap.SpendEntry}
    (hh : record.history.val = l ++ [last]) (hn : now.val < last.ledger.val) :
    rule_eval.cap.check_spend record limit period now amount =
      ok (.Err .LedgerBeforeNewest) := by
  obtain ⟨res, hres, hden⟩ := check_spend_eq record limit period now amount
  have hb : Cap.beforeNewest (denoteRecord record).history now.val = true := by
    simp [denoteRecord, hh, denoteEntry, hn]
  have hm := (Cap.check_ledgerBeforeNewest_iff ⟨limit.val, period.val⟩ (denoteRecord record)
    now.val ha).mpr hb
  rw [hm] at hden
  rw [hres]
  cases res with
  | Ok r => simp [denoteSpend] at hden
  | Err e =>
    simp only [denoteSpend, Except.error.injEq] at hden
    have : e = .LedgerBeforeNewest := denoteCapError_injective (by simpa [denoteCapError] using hden)
    rw [this]

end RuleCore.Extracted
