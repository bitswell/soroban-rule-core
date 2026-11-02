import RuleCore.Vocab.Bytes

/-!
# Byte strings: theorems

* `Bytes.eq_iff`: byte strings are equal exactly when they have the same length
  and the same byte at every index.
* `Bytes.append_ne_self`: a byte string is never equal to a proper extension
  of itself.
-/

namespace RuleCore

/-- Byte strings are equal exactly when they have the same length and the same
byte at every index. -/
theorem Bytes.eq_iff (a b : Bytes) :
    a = b ↔
      a.length = b.length ∧ ∀ (i : Nat) (ha : i < a.length) (hb : i < b.length), a[i] = b[i] :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ _ => rfl⟩, fun ⟨hl, h⟩ => List.ext_getElem hl h⟩

theorem Bytes.append_ne_self {a ext : Bytes} (h : ext ≠ []) : a ++ ext ≠ a := by
  intro e
  have := congrArg List.length e
  simp only [List.length_append] at this
  exact h (List.eq_nil_of_length_eq_zero (by omega))

end RuleCore
