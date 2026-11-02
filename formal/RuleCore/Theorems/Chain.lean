import RuleCore.Vocab.Chain
import RuleCore.Theorems.Attenuation
import RuleCore.Theorems.Bytes

/-!
# Chain vocabulary: theorems

Evaluation:

* `Rule.allows_call_iff`, `Rule.allows_iff`, `RuleSet.allows_iff`,
  `RuleSet.allowsAll_iff`: what each verdict means in the vocabulary's terms.

Contract creation:

* `Rule.allows_create`, `RuleSet.allows_create`: no rule and no rule set
  allows a contract creation.
* `RuleSet.allowsAll_false_of_create_mem`: a batch containing a creation is
  denied.

Arguments:

* `Cond.argEq_holds_iff`, `Cond.argI128AtMost_holds_iff`: what each condition
  means.
* `Cond.holds_false_of_length_le`: a condition on a missing argument is false.
* `Val.ne_of_kind_ne`: values of different constructors are never equal.
* `Cond.argEq_kind`: `argEq` holds only for an argument of the same constructor.
* `Cond.argEq_false_of_kind_ne`, `Cond.argEq_bytes_false_of_other`: an argument
  of another constructor fails `argEq`, whatever its payload.

Byte strings (with `RuleCore.Bytes.eq_iff`):

* `Rule.contract_eq_of_allows`: a rule allows only calls to exactly its
  contract and exactly one of its functions.
* `Rule.allows_false_of_functions_nil`: a rule with an empty function list
  allows nothing.
* `Rule.allows_extension_false`, `Rule.allows_prefix_false`: a call to a
  proper extension or a proper prefix of the rule's contract id is denied.

Attenuation:

* `RuleSet.rules_denote`: a rule set denotes the list of its rules' denotations.
* `Rule.denote_addCond`, `Rule.denote_removeFunctions`,
  `RuleSet.denote_modifyRule`, `RuleSet.denote_dropRule`,
  `RuleSet.denote_addCond`, `RuleSet.denote_removeFunctions`,
  `RuleSet.denote_attenuate`: each chain step denotes the generic step of the
  same kind.
* `RuleSet.dropRule_narrower`, `RuleSet.addCond_narrower`,
  `RuleSet.removeFunctions_narrower`, `RuleSet.attenuate_narrower`: each step
  yields a narrower rule set.
* `RuleSet.narrower_refl`, `RuleSet.narrower_trans`: `narrower` is a preorder.
* `RuleSet.Derives.narrower`, `RuleSet.attenuateAll_derives`,
  `RuleSet.attenuateAll_narrower`: any chain of steps stays inside its root.
* `RuleSet.allowsAll_of_narrower`: a narrower rule set allows a batch only if
  its ancestor does.
* `Rule.mem_removeFunctions`: removing `fs` keeps exactly the functions not in
  `fs`.
* `RuleSet.dropRule_eq_error_iff`, `RuleSet.addCond_eq_error_iff`,
  `RuleSet.removeFunctions_eq_error_iff`, `RuleSet.modifyRule_eq_error_iff`: a
  step is refused with `noSuchRule` exactly when its index is not below the
  number of rules.
-/

namespace RuleCore.Chain

/-! ## Evaluation -/

theorem Rule.allows_call_iff (r : Rule) (contract function : Bytes) (args : List Val) :
    r.allows (.call contract function args) = true ↔
      contract = r.contract ∧ function ∈ r.functions ∧
        ∀ cond ∈ r.conds, cond.holds args = true := by
  simp [Rule.allows, Rule.denote, RuleCore.Rule.allows, Rule.scope, Cond.denote, and_assoc]

theorem Rule.allows_iff (r : Rule) (c : Context) :
    r.allows c = true ↔
      ∃ function args, c = .call r.contract function args ∧ function ∈ r.functions ∧
        ∀ cond ∈ r.conds, cond.holds args = true := by
  cases c with
  | call contract function args =>
    rw [Rule.allows_call_iff]
    constructor
    · rintro ⟨rfl, hf, hc⟩
      exact ⟨function, args, rfl, hf, hc⟩
    · rintro ⟨function', args', h, hf, hc⟩
      cases h
      exact ⟨rfl, hf, hc⟩
  | create wasmHash =>
    simp [Rule.allows, Rule.denote, RuleCore.Rule.allows, Rule.scope]

@[simp] theorem RuleSet.rules_denote (rs : RuleSet) : rs.denote.rules = rs.map Rule.denote := rfl

theorem RuleSet.allows_iff (rs : RuleSet) (c : Context) :
    rs.allows c = true ↔ ∃ r ∈ rs, r.allows c = true := by
  rw [RuleSet.allows, RuleCore.RuleSet.allows_iff, RuleSet.rules_denote]
  constructor
  · rintro ⟨_, hm, h⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    exact ⟨r, hr, h⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r.denote, List.mem_map_of_mem hr, h⟩

theorem RuleSet.allowsAll_iff (rs : RuleSet) (cs : List Context) :
    rs.allowsAll cs = true ↔ ∀ c ∈ cs, rs.allows c = true :=
  RuleCore.RuleSet.allowsAll_iff _ _

/-! ## Contract creation -/

@[simp] theorem Rule.allows_create (r : Rule) (wasmHash : Bytes) :
    r.allows (.create wasmHash) = false := rfl

/-- No rule set allows a contract creation. -/
@[simp] theorem RuleSet.allows_create (rs : RuleSet) (wasmHash : Bytes) :
    rs.allows (.create wasmHash) = false := by
  cases h : rs.allows (.create wasmHash)
  · rfl
  · obtain ⟨r, _, hr⟩ := (RuleSet.allows_iff _ _).mp h
    simp at hr

/-- A batch containing a contract creation is denied. -/
theorem RuleSet.allowsAll_false_of_create_mem (rs : RuleSet) {cs : List Context}
    {wasmHash : Bytes} (h : .create wasmHash ∈ cs) : rs.allowsAll cs = false := by
  cases hall : rs.allowsAll cs
  · rfl
  · have := (RuleSet.allowsAll_iff _ _).mp hall _ h
    simp at this

/-! ## Arguments -/

/-- The index of the argument a condition reads. -/
def Cond.index : Cond → UInt32
  | .argEq i _ => i
  | .argI128AtMost i _ => i

theorem Cond.argEq_holds_iff (i : UInt32) (val : Val) (args : List Val) :
    (Cond.argEq i val).holds args = true ↔ args[i.toNat]? = some val := by
  simp [Cond.holds]

theorem Cond.argI128AtMost_holds_iff (i : UInt32) (n : I128) (args : List Val) :
    (Cond.argI128AtMost i n).holds args = true ↔
      ∃ v, args[i.toNat]? = some (.i128 v) ∧ v.toInt ≤ n.toInt := by
  simp only [Cond.holds]
  split <;> simp_all

/-- A condition on an argument the call does not have is false. -/
theorem Cond.holds_false_of_length_le (cond : Cond) {args : List Val}
    (h : args.length ≤ cond.index.toNat) : cond.holds args = false := by
  cases cond with
  | argEq i val =>
    simp only [Cond.index] at h
    simp [Cond.holds, List.getElem?_eq_none h]
  | argI128AtMost i n =>
    simp only [Cond.index] at h
    simp [Cond.holds, List.getElem?_eq_none h]

/-- Values of different constructors are never equal. -/
theorem Val.ne_of_kind_ne {v w : Val} (h : v.kind ≠ w.kind) : v ≠ w :=
  fun e => h (e ▸ rfl)

/-- `argEq i val` holds only for an argument with `val`'s constructor. -/
theorem Cond.argEq_kind {i : UInt32} {val : Val} {args : List Val}
    (h : (Cond.argEq i val).holds args = true) :
    ∃ w, args[i.toNat]? = some w ∧ w.kind = val.kind :=
  ⟨val, (Cond.argEq_holds_iff i val args).mp h, rfl⟩

/-- An argument of another constructor fails `argEq`, whatever its payload. -/
theorem Cond.argEq_false_of_kind_ne {i : UInt32} {val w : Val} {args : List Val}
    (hw : args[i.toNat]? = some w) (hk : w.kind ≠ val.kind) :
    (Cond.argEq i val).holds args = false := by
  cases h : (Cond.argEq i val).holds args
  · rfl
  · obtain ⟨w', hw', hk'⟩ := Cond.argEq_kind h
    rw [hw] at hw'
    cases hw'
    exact absurd hk' hk

/-- An unmodelled argument never satisfies a `bytes` condition, even when its
XDR is exactly the condition's bytes. -/
theorem Cond.argEq_bytes_false_of_other {i : UInt32} {b xdr : Bytes} {args : List Val}
    (hw : args[i.toNat]? = some (.other xdr)) :
    (Cond.argEq i (.bytes b)).holds args = false :=
  Cond.argEq_false_of_kind_ne hw (by simp [Val.kind])

/-! ## Byte strings -/

/-- A rule allows only calls to exactly its contract and exactly one of its
functions. -/
theorem Rule.contract_eq_of_allows {r : Rule} {contract function : Bytes} {args : List Val}
    (h : r.allows (.call contract function args) = true) :
    contract = r.contract ∧ function ∈ r.functions :=
  let ⟨hc, hf, _⟩ := (Rule.allows_call_iff r contract function args).mp h
  ⟨hc, hf⟩

/-- A rule with an empty function list allows nothing. -/
theorem Rule.allows_false_of_functions_nil {r : Rule} (h : r.functions = []) (c : Context) :
    r.allows c = false := by
  cases ha : r.allows c
  · rfl
  · obtain ⟨_, _, _, hf, _⟩ := (Rule.allows_iff r c).mp ha
    simp [h] at hf

/-- No prefix match: a call to a proper extension of the rule's contract id is
denied. -/
theorem Rule.allows_extension_false (r : Rule) {ext : Bytes} (h : ext ≠ [])
    (function : Bytes) (args : List Val) :
    r.allows (.call (r.contract ++ ext) function args) = false := by
  cases ha : r.allows (.call (r.contract ++ ext) function args)
  · rfl
  · exact absurd (Rule.contract_eq_of_allows ha).1 (Bytes.append_ne_self h)

/-- A call to a proper prefix of the rule's contract id is denied. -/
theorem Rule.allows_prefix_false (r : Rule) {contract ext : Bytes}
    (hp : contract ++ ext = r.contract) (h : ext ≠ []) (function : Bytes) (args : List Val) :
    r.allows (.call contract function args) = false := by
  cases ha : r.allows (.call contract function args)
  · rfl
  · have hc := (Rule.contract_eq_of_allows ha).1
    rw [hc] at hp
    exact absurd hp (Bytes.append_ne_self h)

/-! ## Attenuation: denotation -/

private theorem map_eraseIdx {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.eraseIdx i).map f = (l.map f).eraseIdx i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: l, i + 1 => by simp [map_eraseIdx f l i]

theorem Rule.denote_addCond (r : Rule) (cond : Cond) :
    (r.addCond cond).denote = r.denote.addCond cond.denote := by
  simp only [Rule.denote, RuleCore.Rule.addCond, RuleCore.Rule.mk.injEq]
  refine ⟨?_, by simp [Rule.addCond]⟩
  funext c
  cases c <;> rfl

theorem Rule.mem_removeFunctions (r : Rule) (fs : List Bytes) (f : Bytes) :
    f ∈ (r.removeFunctions fs).functions ↔ f ∈ r.functions ∧ f ∉ fs := by
  simp [Rule.removeFunctions]

theorem Rule.denote_removeFunctions (r : Rule) (fs : List Bytes) :
    (r.removeFunctions fs).denote = r.denote.restrictScope (notCalling fs) := by
  simp only [Rule.denote, RuleCore.Rule.restrictScope, RuleCore.Rule.mk.injEq]
  refine ⟨?_, rfl⟩
  funext c
  cases c with
  | call contract function args =>
    simp [Rule.scope, notCalling, Rule.removeFunctions, Bool.and_assoc]
  | create wasmHash => rfl

theorem RuleSet.denote_modifyRule (rs : RuleSet) (i : Nat) (f : Rule → Rule)
    (g : RuleCore.Rule Context → RuleCore.Rule Context) (hfg : ∀ r, (f r).denote = g r.denote) :
    (rs.modifyRule i f).map RuleSet.denote = rs.denote.modifyRule i g := by
  unfold RuleSet.modifyRule RuleCore.RuleSet.modifyRule
  simp only [RuleSet.rules_denote, List.getElem?_map]
  cases h : rs[i]? with
  | none => rfl
  | some r =>
    simp [Except.map, RuleSet.denote, List.map_set, hfg]

theorem RuleSet.denote_dropRule (rs : RuleSet) (i : UInt32) :
    (rs.dropRule i).map RuleSet.denote = rs.denote.dropRule i.toNat := by
  unfold RuleSet.dropRule RuleCore.RuleSet.dropRule
  simp only [RuleSet.rules_denote, List.length_map]
  split
  · simp [Except.map, RuleSet.denote, map_eraseIdx]
  · rfl

theorem RuleSet.denote_addCond (rs : RuleSet) (i : UInt32) (cond : Cond) :
    (rs.addCond i cond).map RuleSet.denote = rs.denote.addCond i.toNat cond.denote :=
  RuleSet.denote_modifyRule rs i.toNat _ _ (fun r => Rule.denote_addCond r cond)

theorem RuleSet.denote_removeFunctions (rs : RuleSet) (i : UInt32) (fs : List Bytes) :
    (rs.removeFunctions i fs).map RuleSet.denote =
      rs.denote.restrictScope i.toNat (notCalling fs) :=
  RuleSet.denote_modifyRule rs i.toNat _ _ (fun r => Rule.denote_removeFunctions r fs)

theorem RuleSet.denote_attenuate (rs : RuleSet) (a : Attenuation) :
    (rs.attenuate a).map RuleSet.denote = rs.denote.attenuate a.denote := by
  cases a with
  | dropRule i => exact RuleSet.denote_dropRule rs i
  | addCond i cond => exact RuleSet.denote_addCond rs i cond
  | removeFunctions i fs => exact RuleSet.denote_removeFunctions rs i fs

/-! ## Attenuation: narrowing -/

theorem RuleSet.narrower_refl (rs : RuleSet) : rs.narrower rs :=
  RuleCore.RuleSet.narrower_refl _

theorem RuleSet.narrower_trans {rs'' rs' rs : RuleSet} :
    rs''.narrower rs' → rs'.narrower rs → rs''.narrower rs :=
  RuleCore.RuleSet.narrower_trans

theorem RuleSet.attenuate_narrower {rs rs' : RuleSet} {a : Attenuation}
    (h : rs.attenuate a = .ok rs') : rs'.narrower rs := by
  have hd := RuleSet.denote_attenuate rs a
  rw [h] at hd
  exact RuleCore.RuleSet.attenuate_narrower hd.symm

theorem RuleSet.dropRule_narrower {rs rs' : RuleSet} {i : UInt32}
    (h : rs.dropRule i = .ok rs') : rs'.narrower rs :=
  RuleSet.attenuate_narrower (a := .dropRule i) h

theorem RuleSet.addCond_narrower {rs rs' : RuleSet} {i : UInt32} {cond : Cond}
    (h : rs.addCond i cond = .ok rs') : rs'.narrower rs :=
  RuleSet.attenuate_narrower (a := .addCond i cond) h

theorem RuleSet.removeFunctions_narrower {rs rs' : RuleSet} {i : UInt32} {fs : List Bytes}
    (h : rs.removeFunctions i fs = .ok rs') : rs'.narrower rs :=
  RuleSet.attenuate_narrower (a := .removeFunctions i fs) h

/-- Every rule set derived from a root by attenuation steps stays inside the
root. -/
theorem RuleSet.Derives.narrower {root rs : RuleSet} (h : RuleSet.Derives root rs) :
    rs.narrower root := by
  induction h with
  | refl => exact RuleSet.narrower_refl root
  | step a _ ha ih => exact RuleSet.narrower_trans (RuleSet.attenuate_narrower ha) ih

theorem RuleSet.attenuateAll_derives {root rs : RuleSet} {steps : List Attenuation}
    (h : root.attenuateAll steps = .ok rs) : RuleSet.Derives root rs := by
  suffices ∀ (steps : List Attenuation) (rs₀ : RuleSet),
      RuleSet.Derives root rs₀ → steps.foldlM RuleSet.attenuate rs₀ = .ok rs →
      RuleSet.Derives root rs from
    this steps root .refl h
  intro steps
  induction steps with
  | nil =>
    intro rs₀ h₀ h
    simp only [List.foldlM_nil] at h
    cases h
    exact h₀
  | cons a steps ih =>
    intro rs₀ h₀ h
    rw [List.foldlM_cons] at h
    cases ha : rs₀.attenuate a with
    | error e => rw [ha] at h; cases h
    | ok rs₁ =>
      rw [ha] at h
      exact ih rs₁ (.step a h₀ ha) h

theorem RuleSet.attenuateAll_narrower {root rs : RuleSet} {steps : List Attenuation}
    (h : root.attenuateAll steps = .ok rs) : rs.narrower root :=
  (RuleSet.attenuateAll_derives h).narrower

/-- A narrower rule set allows a batch only if its ancestor does. -/
theorem RuleSet.allowsAll_of_narrower {rs' rs : RuleSet} (h : rs'.narrower rs)
    (cs : List Context) : rs'.allowsAll cs = true → rs.allowsAll cs = true :=
  RuleCore.RuleSet.allowsAll_of_narrower h cs

/-! ## Attenuation: failure -/

theorem RuleSet.modifyRule_eq_error_iff (rs : RuleSet) (i : Nat) (f : Rule → Rule) :
    rs.modifyRule i f = .error .noSuchRule ↔ rs.length ≤ i := by
  unfold RuleSet.modifyRule
  split <;> rename_i h
  · simp only [reduceCtorEq, false_iff, Nat.not_le]
    exact (List.getElem?_eq_some_iff.mp h).1
  · simp only [true_iff]
    exact List.getElem?_eq_none_iff.mp h

theorem RuleSet.dropRule_eq_error_iff (rs : RuleSet) (i : UInt32) :
    rs.dropRule i = .error .noSuchRule ↔ rs.length ≤ i.toNat := by
  unfold RuleSet.dropRule
  split <;> simp_all

theorem RuleSet.addCond_eq_error_iff (rs : RuleSet) (i : UInt32) (cond : Cond) :
    rs.addCond i cond = .error .noSuchRule ↔ rs.length ≤ i.toNat :=
  RuleSet.modifyRule_eq_error_iff rs i.toNat _

theorem RuleSet.removeFunctions_eq_error_iff (rs : RuleSet) (i : UInt32) (fs : List Bytes) :
    rs.removeFunctions i fs = .error .noSuchRule ↔ rs.length ≤ i.toNat :=
  RuleSet.modifyRule_eq_error_iff rs i.toNat _

end RuleCore.Chain
