import RuleCore.Model.Cap
import RuleCore.Extracted.RuleEval

/-!
# Denotation of the extracted cap types

The functions below map the types Aeneas generates for the `cap` module of
`crates/rule-eval` to the model of `RuleCore/Model/Cap.lean`. Like the maps in
`RuleCore/Equiv/Denote.lean`, they are part of the specification, and each is
structural:

* a `u32` (a ledger or a period) is its value, a natural number, and an `i128`
  (an amount, a total or a limit) is its value, an integer;
* `SpendEntry`, `SpendRecord` and `CapParams` map each field to the field of
  the same name, and the history vector to the list of its entries'
  denotations;
* `CapError` maps each constructor to the constructor of the same name, and a
  Rust `Result` of `check_spend` is the `Except` with the denoted payload.

Every denotation is injective (`denoteEntry_injective`,
`denoteRecord_injective`, `denoteParams_injective`, `denoteCapError_injective`,
`denoteSpend_injective`).
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std

def denoteEntry (e : rule_eval.cap.SpendEntry) : Cap.Entry :=
  ⟨e.ledger.val, e.amount.val⟩

def denoteRecord (r : rule_eval.cap.SpendRecord) : Cap.Record :=
  ⟨r.history.val.map denoteEntry, r.total.val⟩

def denoteParams (p : rule_eval.cap.CapParams) : Cap.Params :=
  ⟨p.limit.val, p.period.val⟩

def denoteCapError : rule_eval.cap.CapError → Cap.CapError
  | .NegativeAmount => .negativeAmount
  | .LedgerBeforeNewest => .ledgerBeforeNewest
  | .Overflow => .overflow
  | .LimitExceeded => .limitExceeded
  | .HistoryFull => .historyFull

/-- What `check_spend` returned, as the model's outcome. -/
def denoteSpend :
    core.result.Result rule_eval.cap.SpendRecord rule_eval.cap.CapError →
      Except Cap.CapError Cap.Record
  | .Ok r => .ok (denoteRecord r)
  | .Err e => .error (denoteCapError e)

/-! ## Injectivity -/

theorem u32_val_injective : Function.Injective (fun x : Std.U32 => x.val) :=
  fun _ _ h => UScalar.eq_of_val_eq h

theorem i128_val_injective : Function.Injective (fun x : Std.I128 => x.val) :=
  fun _ _ h => IScalar.eq_of_val_eq h

theorem denoteEntry_injective : Function.Injective denoteEntry := by
  intro a b h
  simp only [denoteEntry, Cap.Entry.mk.injEq] at h
  cases a
  cases b
  simp only [rule_eval.cap.SpendEntry.mk.injEq]
  exact ⟨u32_val_injective h.1, i128_val_injective h.2⟩

theorem denoteRecord_injective : Function.Injective denoteRecord := by
  intro a b h
  simp only [denoteRecord, Cap.Record.mk.injEq] at h
  cases a
  cases b
  simp only [rule_eval.cap.SpendRecord.mk.injEq]
  exact ⟨alloc.vec.Vec.ext _ _ ((List.map_injective_iff.mpr denoteEntry_injective).eq_iff.mp h.1),
    i128_val_injective h.2⟩

theorem denoteParams_injective : Function.Injective denoteParams := by
  intro a b h
  simp only [denoteParams, Cap.Params.mk.injEq] at h
  cases a
  cases b
  simp only [rule_eval.cap.CapParams.mk.injEq]
  exact ⟨i128_val_injective h.1, u32_val_injective h.2⟩

theorem denoteCapError_injective : Function.Injective denoteCapError := by
  intro a b h
  cases a <;> cases b <;> first | rfl | simp [denoteCapError] at h

theorem denoteSpend_injective : Function.Injective denoteSpend := by
  intro a b h
  cases a with
  | Ok r =>
    cases b with
    | Ok r' =>
      simp only [denoteSpend, Except.ok.injEq] at h
      rw [denoteRecord_injective h]
    | Err e => simp [denoteSpend] at h
  | Err e =>
    cases b with
    | Ok r => simp [denoteSpend] at h
    | Err e' =>
      simp only [denoteSpend, Except.error.injEq] at h
      rw [denoteCapError_injective h]

end RuleCore.Equiv
