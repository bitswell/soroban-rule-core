import RuleCore.Model.Budget

/-!
# Budgets on the delegation tree: theorems

About one spend (`Tree.spend`):

* `spend_ok_charges`, `spend_ok_unchanged`, `spend_ok_length`,
  `spend_ok_parentOf`, `spend_ok_allowance`: a successful spend at `i` adds the
  amount to the spent amount of `i` and of every ancestor, and changes nothing
  else: no other node, no node's parent or allowance, and not the number of
  nodes;
* `spend_overdrawn`: the node an `overdrawn` refusal names is on the
  spender's chain and cannot take the amount, and every node before it on the
  chain, counting from the spender, can: it is the first that would be
  overdrawn;
* `spend_accepts_iff`, `spend_error_overdrawn`: on a well-formed tree, a spend
  of a non-negative amount at an existing node succeeds exactly when every node
  on its chain can take the amount, and is otherwise refused as `overdrawn`, so
  it refuses only what it must;
* `spend_ok_iff`: a successful spend is a well-formed tree, an existing node, a
  non-negative amount and a walk that reaches the root;
* `step_of_error`, `run_cons_of_error`: a refused operation leaves the tree as
  it was.

About delegation and refills:

* `delegate_ok_iff`: a successful delegation appends exactly the new child,
  with nothing spent, at the next index, whatever its allowance and its
  parent's;
* `refill_ok_iff`: a successful refill raises exactly one node's allowance by
  the amount.

Invariants, each preserved by every operation and every run:

* `spend_valid`, `delegate_valid`, `refill_valid`, `run_valid`: the tree
  stays well formed;
* `spend_withinAllowance`, `delegate_withinAllowance`,
  `refill_withinAllowance`, `run_withinAllowance`: every node's spent amount
  stays within its allowance.

Runs (`Tree.run`):

* `run_extends`: a run never removes a node or changes an existing node's
  parent;
* `spent_run`, `spentUnder_eq_spent`: after any run, each node's spent amount is
  its spent amount before the run (nothing, for a node the run appended) plus
  the total successfully spent at or under it;
* `spentUnder_le_allowance`: budget safety. For every run of spends,
  delegations and refills from a well-formed tree with nothing spent, the total
  successfully spent at or under any node is that node's spent amount and
  never exceeds its allowance. Nothing relates allowances to each other:
  children's allowances may sum to more than their parent's.
-/

namespace RuleCore.Budget

open RuleCore.Cap (addI128 i128Min i128Max)

namespace Tree

/-! ## Well-formed trees -/

theorem validFrom_iff : ∀ (t : Tree) (k : Nat),
    t.validFrom k = true ↔ ∀ (i : Nat) (h : i < t.length), t[i].valid (k + i) = true
  | [], _ => by simp [validFrom]
  | n :: t, k => by
    rw [validFrom, Bool.and_eq_true, validFrom_iff t (k + 1)]
    constructor
    · rintro ⟨hn, ht⟩ i hi
      cases i with
      | zero => simpa using hn
      | succ i =>
        have := ht i (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    · intro h
      refine ⟨by have := h 0 (by simp); simpa using this, fun i hi => ?_⟩
      have := h (i + 1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem valid_iff {t : Tree} :
    t.valid = true ↔ ∀ (i : Nat) (h : i < t.length), t[i].valid i = true := by
  rw [valid, validFrom_iff]
  simp

theorem node_valid_iff {i : Nat} {n : Node} :
    n.valid i = true ↔ (∀ p, n.parent = some p → p < i) ∧ 0 ≤ n.allowance ∧ 0 ≤ n.spent := by
  unfold Node.valid
  cases n.parent <;> simp [and_assoc]

theorem lt_length_of_getElem? {t : Tree} {i : Nat} {n : Node} (h : t[i]? = some n) :
    i < t.length :=
  (List.getElem?_eq_some_iff.mp h).1

theorem getElem_of_getElem? {t : Tree} {i : Nat} {n : Node} (h : t[i]? = some n) :
    t[i]'(lt_length_of_getElem? h) = n :=
  (List.getElem?_eq_some_iff.mp h).2

/-- On a well-formed tree, a node's parent index is below its own. -/
theorem parent_lt {t : Tree} (hv : t.valid = true) {i p : Nat} (h : t.parentOf i = some p) :
    p < i := by
  unfold parentOf at h
  cases hi : t[i]? with
  | none => simp [hi] at h
  | some n =>
    simp only [hi, Option.bind_some] at h
    have := valid_iff.mp hv i (lt_length_of_getElem? hi)
    rw [getElem_of_getElem? hi] at this
    exact (node_valid_iff.mp this).1 p h

/-- On a well-formed tree, a node's allowance and spent amount are not
negative. -/
theorem nonneg_of_valid {t : Tree} (hv : t.valid = true) {i : Nat} {n : Node}
    (h : t[i]? = some n) : 0 ≤ n.allowance ∧ 0 ≤ n.spent := by
  have := valid_iff.mp hv i (lt_length_of_getElem? h)
  rw [getElem_of_getElem? h] at this
  exact (node_valid_iff.mp this).2

/-! ## The chain -/

theorem within_root {t : Tree} {i a : Nat} (h : t.parentOf i = none) :
    t.Within i a ↔ a = i := by
  constructor
  · intro w
    cases w with
    | self => rfl
    | up hp _ => rw [h] at hp; cases hp
  · rintro rfl
    exact .self _

theorem within_step {t : Tree} {i p a : Nat} (h : t.parentOf i = some p) :
    t.Within i a ↔ a = i ∨ t.Within p a := by
  constructor
  · intro w
    cases w with
    | self => exact .inl rfl
    | up hp w =>
      rw [h] at hp
      cases hp
      exact .inr w
  · rintro (rfl | w)
    · exact .self _
    · exact .up h w

/-- On a well-formed tree, a node's ancestors have smaller indices. -/
theorem le_of_within {t : Tree} (hv : t.valid = true) {i a : Nat} (w : t.Within i a) : a ≤ i := by
  induction w with
  | self => exact Nat.le_refl _
  | up hp _ ih => exact Nat.le_trans ih (Nat.le_of_lt (parent_lt hv hp))

theorem within_antisymm {t : Tree} (hv : t.valid = true) {i a : Nat} (w : t.Within i a)
    (w' : t.Within a i) : a = i :=
  Nat.le_antisymm (le_of_within hv w) (le_of_within hv w')

theorem within_trans {t : Tree} {i a b : Nat} (w : t.Within i a) (w' : t.Within a b) :
    t.Within i b := by
  induction w with
  | self => exact w'
  | up hp _ ih => exact .up hp (ih w')

/-! ## The walk -/

theorem walk_succ (t : Tree) (x : Int) (fuel i : Nat) :
    t.walk x (fuel + 1) i =
      match t[i]? with
      | none => .error .malformed
      | some n =>
        if !n.fits x then .error (.overdrawn i)
        else
          match n.parent with
          | none => .ok [i]
          | some p => if p < i then (t.walk x fuel p).map (i :: ·) else .error .malformed := rfl

/-- What a successful walk returns: the walked nodes, each in the tree and able
to take the amount, are exactly the spender and its ancestors. -/
theorem mem_walk {t : Tree} {x : Int} :
    ∀ {fuel i path}, t.walk x fuel i = .ok path → ∀ a, a ∈ path ↔ t.Within i a
  | 0, _, _, h => by simp [walk] at h
  | fuel + 1, i, path, h => by
    intro a
    rw [walk_succ] at h
    cases hi : t[i]? with
    | none => simp [hi] at h
    | some n =>
      have hpi : t.parentOf i = n.parent := by simp [parentOf, hi]
      simp only [hi] at h
      split at h
      · simp at h
      · cases hp : n.parent with
        | none =>
          simp only [hp, Except.ok.injEq] at h
          subst h
          rw [within_root (hpi.trans hp)]
          simp
        | some p =>
          simp only [hp] at h
          split at h
          · cases hw : t.walk x fuel p with
            | error e => simp [hw, Except.map] at h
            | ok rest =>
              simp only [hw, Except.map, Except.ok.injEq] at h
              subst h
              rw [within_step (hpi.trans hp), List.mem_cons, mem_walk hw a]
          · simp at h

/-- Every node a successful walk returns is in the tree and can take the
amount. -/
theorem walk_fits {t : Tree} {x : Int} :
    ∀ {fuel i path}, t.walk x fuel i = .ok path →
      ∀ a ∈ path, ∃ n, t[a]? = some n ∧ n.fits x = true
  | 0, _, _, h => by simp [walk] at h
  | fuel + 1, i, path, h => by
    intro a ha
    rw [walk_succ] at h
    cases hi : t[i]? with
    | none => simp [hi] at h
    | some n =>
      simp only [hi] at h
      split at h
      · simp at h
      · rename_i hf
        have hf' : n.fits x = true := by simpa using hf
        cases hp : n.parent with
        | none =>
          simp only [hp, Except.ok.injEq] at h
          subst h
          rw [List.mem_singleton.mp ha]
          exact ⟨n, hi, hf'⟩
        | some p =>
          simp only [hp] at h
          split at h
          · cases hw : t.walk x fuel p with
            | error e => simp [hw, Except.map] at h
            | ok rest =>
              simp only [hw, Except.map, Except.ok.injEq] at h
              subst h
              rcases List.mem_cons.mp ha with rfl | ha
              · exact ⟨n, hi, hf'⟩
              · exact walk_fits hw a ha
          · simp at h

/-- The node an `overdrawn` walk names is on the spender's chain and cannot
take the amount, and every node before it on the chain can. -/
theorem walk_overdrawn {t : Tree} (hv : t.valid = true) {x : Int} :
    ∀ {fuel i j}, t.walk x fuel i = .error (.overdrawn j) →
      t.Within i j ∧ (∃ n, t[j]? = some n ∧ n.fits x = false) ∧
        ∀ b, t.Within i b → t.Within b j → b ≠ j → ∃ m, t[b]? = some m ∧ m.fits x = true
  | 0, _, _, h => by simp [walk] at h
  | fuel + 1, i, j, h => by
    rw [walk_succ] at h
    cases hi : t[i]? with
    | none => simp [hi] at h
    | some n =>
      have hpi : t.parentOf i = n.parent := by simp [parentOf, hi]
      simp only [hi] at h
      split at h
      · rename_i hf
        simp only [Except.error.injEq, BudgetError.overdrawn.injEq] at h
        subst h
        refine ⟨.self _, ⟨n, hi, by simpa using hf⟩, fun b w w' hb => ?_⟩
        exact absurd (within_antisymm hv w w') hb
      · rename_i hf
        have hf' : n.fits x = true := by simpa using hf
        cases hp : n.parent with
        | none => simp [hp] at h
        | some p =>
          simp only [hp] at h
          split at h
          · cases hw : t.walk x fuel p with
            | ok rest => simp [hw, Except.map] at h
            | error e =>
              simp only [hw, Except.map, Except.error.injEq] at h
              subst h
              obtain ⟨wj, hj, first⟩ := walk_overdrawn hv hw
              refine ⟨.up (hpi.trans hp) wj, hj, fun b w w' hb => ?_⟩
              rcases (within_step (hpi.trans hp)).mp w with rfl | w
              · exact ⟨n, hi, hf'⟩
              · exact first b w w' hb
          · simp at h

/-- On a well-formed tree, the walk from an existing node with enough fuel
refuses only as `overdrawn`, and succeeds when every node on the chain can take
the amount. -/
theorem walk_total {t : Tree} (hv : t.valid = true) {x : Int} :
    ∀ {fuel i}, i < t.length → i < fuel →
      (∀ a, t.Within i a → ∃ n, t[a]? = some n ∧ n.fits x = true) →
      ∃ path, t.walk x fuel i = .ok path
  | 0, _, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, i, hi, hfuel, hall => by
    rw [walk_succ]
    obtain ⟨n, hn, hfits⟩ := hall i (.self i)
    have hpi : t.parentOf i = n.parent := by simp [parentOf, hn]
    simp only [hn, hfits, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hp : n.parent with
    | none => exact ⟨[i], rfl⟩
    | some p =>
      have hlt : p < i := parent_lt hv (hpi.trans hp)
      simp only [hlt, ↓reduceIte]
      obtain ⟨rest, hw⟩ := walk_total hv (fuel := fuel) (i := p) (by omega) (by omega)
        (fun a w => hall a (.up (hpi.trans hp) w))
      exact ⟨i :: rest, by rw [hw]; rfl⟩

/-- On a well-formed tree, the walk from an existing node with enough fuel
never refuses as anything but `overdrawn`. -/
theorem walk_error {t : Tree} (hv : t.valid = true) {x : Int} :
    ∀ {fuel i e}, i < t.length → i < fuel → t.walk x fuel i = .error e →
      ∃ j, e = .overdrawn j
  | 0, _, _, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, i, e, hi, hfuel, h => by
    rw [walk_succ] at h
    cases hn : t[i]? with
    | none => simp [List.getElem?_eq_getElem hi] at hn
    | some n =>
      have hpi : t.parentOf i = n.parent := by simp [parentOf, hn]
      simp only [hn] at h
      split at h
      · simp only [Except.error.injEq] at h
        exact ⟨i, h.symm⟩
      · cases hp : n.parent with
        | none => simp [hp] at h
        | some p =>
          have hlt : p < i := parent_lt hv (hpi.trans hp)
          simp only [hp, hlt, ↓reduceIte] at h
          cases hw : t.walk x fuel p with
          | ok rest => simp [hw, Except.map] at h
          | error e' =>
            simp only [hw, Except.map, Except.error.injEq] at h
            subst h
            exact walk_error hv (by omega) (by omega) hw

/-! ## Charging -/

theorem length_charge (t : Tree) (path : List Nat) (x : Int) :
    (t.charge path x).length = t.length := by
  simp [charge]

theorem getElem?_charge (t : Tree) (path : List Nat) (x : Int) (j : Nat) :
    (t.charge path x)[j]? =
      t[j]?.map (fun n => if j ∈ path then { n with spent := n.spent + x } else n) := by
  simp [charge, List.getElem?_mapIdx]

theorem parentOf_charge (t : Tree) (path : List Nat) (x : Int) :
    (t.charge path x).parentOf = t.parentOf := by
  funext j
  unfold parentOf
  rw [getElem?_charge]
  cases t[j]? with
  | none => rfl
  | some n => by_cases hj : j ∈ path <;> simp [hj]

theorem fits_iff {n : Node} {x : Int} :
    n.fits x = true ↔ i128Min ≤ n.spent + x ∧ n.spent + x ≤ i128Max ∧ n.spent + x ≤ n.allowance := by
  unfold Node.fits addI128
  by_cases h : i128Min ≤ n.spent + x ∧ n.spent + x ≤ i128Max
  · simp [h]
  · simp only [h, ↓reduceIte, Bool.false_eq_true, false_iff]
    intro h'
    exact h ⟨h'.1, h'.2.1⟩

/-! ## Spends -/

theorem spend_ok_iff {t t' : Tree} {i : Nat} {x : Int} :
    t.spend i x = .ok t' ↔
      t.valid = true ∧ i < t.length ∧ 0 ≤ x ∧
        ∃ path, t.walk x t.length i = .ok path ∧ t' = t.charge path x := by
  unfold spend
  by_cases hv : t.valid = true
  · by_cases hi : t.length ≤ i
    · simp [hv, hi]; intro h; omega
    · by_cases hx : x < 0
      · simp [hv, hi, hx]; intro _ h; omega
      · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi, hx, true_and]
        refine ⟨fun h => ?_, fun ⟨_, _, path, hw, ht⟩ => ?_⟩
        · cases hw : t.walk x t.length i with
          | error e => simp [hw, Except.map] at h
          | ok path =>
            simp only [hw, Except.map, Except.ok.injEq] at h
            exact ⟨by omega, by omega, path, rfl, h.symm⟩
        · rw [hw, ht]
          rfl
  · simp [hv]

/-- A successful spend charges the spender and every ancestor by the amount. -/
theorem spend_ok_charges {t t' : Tree} {i a : Nat} {x : Int} (h : t.spend i x = .ok t')
    (w : t.Within i a) :
    ∃ n, t[a]? = some n ∧ t'[a]? = some { n with spent := n.spent + x } := by
  obtain ⟨-, -, -, path, hw, rfl⟩ := spend_ok_iff.mp h
  have ha : a ∈ path := (mem_walk hw a).mpr w
  obtain ⟨n, hn, -⟩ := walk_fits hw a ha
  exact ⟨n, hn, by rw [getElem?_charge, hn]; simp [ha]⟩

/-- A successful spend changes no node off the spender's chain. -/
theorem spend_ok_unchanged {t t' : Tree} {i a : Nat} {x : Int} (h : t.spend i x = .ok t')
    (w : ¬ t.Within i a) : t'[a]? = t[a]? := by
  obtain ⟨-, -, -, path, hw, rfl⟩ := spend_ok_iff.mp h
  have ha : a ∉ path := fun ha => w ((mem_walk hw a).mp ha)
  rw [getElem?_charge]
  cases t[a]? <;> simp [ha]

/-- A successful spend adds or removes no node. -/
theorem spend_ok_length {t t' : Tree} {i : Nat} {x : Int} (h : t.spend i x = .ok t') :
    t'.length = t.length := by
  obtain ⟨-, -, -, path, -, rfl⟩ := spend_ok_iff.mp h
  exact length_charge t path x

/-- A successful spend changes no node's parent. -/
theorem spend_ok_parentOf {t t' : Tree} {i : Nat} {x : Int} (h : t.spend i x = .ok t') :
    t'.parentOf = t.parentOf := by
  obtain ⟨-, -, -, path, -, rfl⟩ := spend_ok_iff.mp h
  exact parentOf_charge t path x

/-- A successful spend changes no node's allowance. -/
theorem spend_ok_allowance {t t' : Tree} {i : Nat} {x : Int} (h : t.spend i x = .ok t')
    (a : Nat) : t'[a]?.map (·.allowance) = t[a]?.map (·.allowance) := by
  obtain ⟨-, -, -, path, -, rfl⟩ := spend_ok_iff.mp h
  rw [getElem?_charge]
  cases t[a]? with
  | none => rfl
  | some n => by_cases ha : a ∈ path <;> simp [ha]

/-- The node an `overdrawn` refusal names, the target of a refill request, is on
the spender's chain and cannot take the amount, and every node before it on the
chain, counting from the spender, can. -/
theorem spend_overdrawn {t : Tree} {i j : Nat} {x : Int}
    (h : t.spend i x = .error (.overdrawn j)) :
    t.Within i j ∧ (∃ n, t[j]? = some n ∧ n.fits x = false) ∧
      ∀ b, t.Within i b → t.Within b j → b ≠ j → ∃ m, t[b]? = some m ∧ m.fits x = true := by
  unfold spend at h
  by_cases hv : t.valid = true
  · by_cases hi : t.length ≤ i
    · simp [hv, hi] at h
    · by_cases hx : x < 0
      · simp [hv, hi, hx] at h
      · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi, hx] at h
        cases hw : t.walk x t.length i with
        | ok path => simp [hw, Except.map] at h
        | error e =>
          simp only [hw, Except.map, Except.error.injEq] at h
          subst h
          exact walk_overdrawn hv hw
  · simp [hv] at h

/-- On a well-formed tree, a spend of a non-negative amount at an existing node
succeeds exactly when every node on its chain can take the amount. -/
theorem spend_accepts_iff {t : Tree} {i : Nat} {x : Int} (hv : t.valid = true)
    (hi : i < t.length) (hx : 0 ≤ x) :
    (∃ t', t.spend i x = .ok t') ↔ ∀ a, t.Within i a → ∃ n, t[a]? = some n ∧ n.fits x = true := by
  constructor
  · rintro ⟨t', h⟩ a w
    obtain ⟨-, -, -, path, hw, -⟩ := spend_ok_iff.mp h
    exact walk_fits hw a ((mem_walk hw a).mpr w)
  · intro hall
    obtain ⟨path, hw⟩ := walk_total hv hi hi hall
    exact ⟨t.charge path x, spend_ok_iff.mpr ⟨hv, hi, hx, path, hw, rfl⟩⟩

/-- On a well-formed tree, a spend of a non-negative amount at an existing node
is refused only as `overdrawn`. -/
theorem spend_error_overdrawn {t : Tree} {i : Nat} {x : Int} {e : BudgetError}
    (hv : t.valid = true) (hi : i < t.length) (hx : 0 ≤ x) (h : t.spend i x = .error e) :
    ∃ j, e = .overdrawn j := by
  unfold spend at h
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.not_le.mpr hi,
    Int.not_lt.mpr hx] at h
  cases hw : t.walk x t.length i with
  | ok path => simp [hw, Except.map] at h
  | error e' =>
    simp only [hw, Except.map, Except.error.injEq] at h
    subst h
    exact walk_error hv hi hi hw

/-! ## Delegation and refills -/

/-- A successful delegation appends exactly the new child, with nothing spent,
at the next index. Nothing compares the allowance with the parent's. -/
theorem delegate_ok_iff {t t' : Tree} {p : Nat} {x : Int} :
    t.delegate p x = .ok t' ↔
      t.valid = true ∧ p < t.length ∧ 0 ≤ x ∧ t.length < maxNodes ∧
        t' = t ++ [⟨some p, x, 0⟩] := by
  unfold delegate
  by_cases hv : t.valid = true
  · by_cases hp : t.length ≤ p
    · simp [hv, hp]; intro h; omega
    · by_cases hx : x < 0
      · simp [hv, hp, hx]; intro _ h; omega
      · by_cases hf : maxNodes ≤ t.length
        · simp [hv, hp, hx, hf]; intro _ _ h; omega
        · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp, hx, hf,
            Except.ok.injEq, true_and]
          constructor
          · intro h; exact ⟨by omega, by omega, by omega, h.symm⟩
          · intro h; exact h.2.2.2.symm
  · simp [hv]

/-- A successful refill raises exactly one node's allowance by the amount. -/
theorem refill_ok_iff {t t' : Tree} {i : Nat} {x : Int} :
    t.refill i x = .ok t' ↔
      t.valid = true ∧ ∃ n, t[i]? = some n ∧ 0 ≤ x ∧ n.allowance + x ≤ i128Max ∧
        t' = t.set i { n with allowance := n.allowance + x } := by
  unfold refill
  by_cases hv : t.valid = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, true_and]
    cases hi : t[i]? with
    | none => simp
    | some n =>
      have hn := (nonneg_of_valid hv hi).1
      by_cases hx : x < 0
      · simp [hx]; intro h; omega
      · simp only [hx, ↓reduceIte, Option.some.injEq, exists_eq_left']
        unfold addI128
        have hmin : i128Min ≤ n.allowance + x := by
          have : i128Min < 0 := by decide
          omega
        by_cases hmax : n.allowance + x ≤ i128Max
        · simp only [hmin, hmax, and_self, ↓reduceIte, Except.ok.injEq, true_and]
          exact ⟨fun h => ⟨by omega, h.symm⟩, fun h => h.2.symm⟩
        · simp [hmax]
  · simp [hv]

/-! ## Invariants -/

theorem valid_set {t : Tree} (hv : t.valid = true) {i : Nat} {n : Node} (hn : n.valid i = true) :
    Tree.valid (t.set i n) = true := by
  rw [valid_iff] at hv ⊢
  intro j hj
  rw [List.length_set] at hj
  rw [List.getElem_set]
  split
  · subst_vars; exact hn
  · exact hv j hj

theorem spend_valid {t t' : Tree} {i : Nat} {x : Int} (h : t.spend i x = .ok t') :
    t'.valid = true := by
  obtain ⟨hv, -, hx, path, -, rfl⟩ := spend_ok_iff.mp h
  rw [valid_iff] at hv ⊢
  intro j hj
  rw [length_charge] at hj
  have hvj := node_valid_iff.mp (hv j hj)
  rw [node_valid_iff]
  simp only [charge, List.getElem_mapIdx]
  split
  · exact ⟨hvj.1, hvj.2.1, by dsimp only; have := hvj.2.2; omega⟩
  · exact hvj

theorem delegate_valid {t t' : Tree} {p : Nat} {x : Int} (h : t.delegate p x = .ok t') :
    t'.valid = true := by
  obtain ⟨hv, hp, hx, -, rfl⟩ := delegate_ok_iff.mp h
  rw [valid_iff] at hv ⊢
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  rw [List.getElem_append]
  split
  · exact hv j (by omega)
  · have hj' : j = t.length := by omega
    subst hj'
    simp only [Nat.sub_self, List.getElem_singleton]
    rw [node_valid_iff]
    exact ⟨fun q hq => by simp only [Option.some.injEq] at hq; omega, hx, Int.le_refl 0⟩

theorem refill_valid {t t' : Tree} {i : Nat} {x : Int} (h : t.refill i x = .ok t') :
    t'.valid = true := by
  obtain ⟨hv, n, hn, hx, -, rfl⟩ := refill_ok_iff.mp h
  apply valid_set hv
  have := valid_iff.mp hv i (lt_length_of_getElem? hn)
  rw [getElem_of_getElem? hn, node_valid_iff] at this
  rw [node_valid_iff]
  exact ⟨this.1, by dsimp only; have := this.2.1; omega, this.2.2⟩

theorem apply_valid {t t' : Tree} {op : Op} (h : op.apply t = .ok t') : t'.valid = true := by
  cases op with
  | spend i x => exact spend_valid h
  | delegate p x => exact delegate_valid h
  | refill i x => exact refill_valid h

theorem withinAllowance_iff {t : Tree} :
    t.WithinAllowance ↔ ∀ (a : Nat) (n : Node), t[a]? = some n → n.spent ≤ n.allowance := by
  constructor
  · intro h a n hn
    exact h n (List.mem_of_getElem? hn)
  · intro h n hn
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hn
    exact h a _ (List.getElem?_eq_getElem ha)

theorem spend_withinAllowance {t t' : Tree} {i : Nat} {x : Int} (hw : t.WithinAllowance)
    (h : t.spend i x = .ok t') : t'.WithinAllowance := by
  rw [withinAllowance_iff] at hw ⊢
  intro a n' hn'
  obtain ⟨-, -, -, path, hpath, rfl⟩ := spend_ok_iff.mp h
  rw [getElem?_charge] at hn'
  cases hn : t[a]? with
  | none => simp [hn] at hn'
  | some n =>
    simp only [hn, Option.map_some, Option.some.injEq] at hn'
    by_cases ha : a ∈ path
    · simp only [ha, ↓reduceIte] at hn'
      subst hn'
      obtain ⟨m, hm, hf⟩ := walk_fits hpath a ha
      rw [hn, Option.some.injEq] at hm
      subst hm
      exact (fits_iff.mp hf).2.2
    · simp only [ha, ↓reduceIte] at hn'
      subst hn'
      exact hw a n hn

theorem delegate_withinAllowance {t t' : Tree} {p : Nat} {x : Int} (hw : t.WithinAllowance)
    (h : t.delegate p x = .ok t') : t'.WithinAllowance := by
  obtain ⟨-, -, hx, -, rfl⟩ := delegate_ok_iff.mp h
  intro n hn
  rcases List.mem_append.mp hn with hn | hn
  · exact hw n hn
  · rw [List.mem_singleton.mp hn]
    exact hx

theorem refill_withinAllowance {t t' : Tree} {i : Nat} {x : Int} (hw : t.WithinAllowance)
    (h : t.refill i x = .ok t') : t'.WithinAllowance := by
  obtain ⟨-, n, hn, hx, -, rfl⟩ := refill_ok_iff.mp h
  rw [withinAllowance_iff] at hw ⊢
  intro a m hm
  rw [List.getElem?_set] at hm
  split at hm
  · rename_i hia
    subst hia
    simp only [lt_length_of_getElem? hn, ↓reduceIte, Option.some.injEq] at hm
    subst hm
    have := hw _ n hn
    simp only
    omega
  · exact hw a m hm

theorem apply_withinAllowance {t t' : Tree} {op : Op} (hw : t.WithinAllowance)
    (h : op.apply t = .ok t') : t'.WithinAllowance := by
  cases op with
  | spend i x => exact spend_withinAllowance hw h
  | delegate p x => exact delegate_withinAllowance hw h
  | refill i x => exact refill_withinAllowance hw h

/-! ## Runs -/

/-- A refused operation leaves the tree as it was. -/
theorem step_of_error {t : Tree} {op : Op} {e : BudgetError} (h : op.apply t = .error e) :
    t.step op = t := by
  simp [step, h]

theorem logged_of_error {t : Tree} {op : Op} {e : BudgetError} (h : op.apply t = .error e) :
    op.logged t = [] := by
  cases op with
  | spend i x =>
    simp only [Op.apply] at h
    simp [Op.logged, h]
  | delegate p x => rfl
  | refill i x => rfl

/-- A run continues from a refused operation as if it had not been made. -/
theorem run_cons_of_error {t : Tree} {op : Op} {e : BudgetError} (ops : List Op)
    (h : op.apply t = .error e) : t.run (op :: ops) = t.run ops := by
  simp [run, step_of_error h, logged_of_error h]

theorem step_valid {t : Tree} (hv : t.valid = true) (op : Op) : (t.step op).valid = true := by
  unfold step
  split
  · rename_i t' h; exact apply_valid h
  · exact hv

theorem step_withinAllowance {t : Tree} (hw : t.WithinAllowance) (op : Op) :
    (t.step op).WithinAllowance := by
  unfold step
  split
  · rename_i t' h; exact apply_withinAllowance hw h
  · exact hw

theorem run_valid {t : Tree} (hv : t.valid = true) (ops : List Op) :
    (t.run ops).1.valid = true := by
  induction ops generalizing t with
  | nil => exact hv
  | cons op ops ih => exact ih (step_valid hv op)

theorem run_withinAllowance {t : Tree} (hw : t.WithinAllowance) (ops : List Op) :
    (t.run ops).1.WithinAllowance := by
  induction ops generalizing t with
  | nil => exact hw
  | cons op ops ih => exact ih (step_withinAllowance hw op)

theorem step_extends (t : Tree) (op : Op) :
    t.length ≤ (t.step op).length ∧ ∀ j < t.length, (t.step op).parentOf j = t.parentOf j := by
  unfold step
  split
  · rename_i t' h
    cases op with
    | spend i x =>
      exact ⟨by rw [spend_ok_length h]; exact Nat.le_refl _,
        fun j _ => by rw [spend_ok_parentOf h]⟩
    | delegate p x =>
      obtain ⟨-, -, -, -, rfl⟩ := delegate_ok_iff.mp h
      refine ⟨by simp, fun j hj => ?_⟩
      simp [parentOf, List.getElem?_append_left hj]
    | refill i x =>
      obtain ⟨-, n, hn, -, -, rfl⟩ := refill_ok_iff.mp h
      refine ⟨by simp, fun j _ => ?_⟩
      unfold parentOf
      rw [List.getElem?_set]
      split
      · rename_i hij
        subst hij
        simp [lt_length_of_getElem? hn, getElem_of_getElem? hn]
      · rfl
  · exact ⟨Nat.le_refl _, fun _ _ => rfl⟩

/-- A run never removes a node or changes an existing node's parent. -/
theorem run_extends (t : Tree) (ops : List Op) :
    t.length ≤ (t.run ops).1.length ∧ ∀ j < t.length, (t.run ops).1.parentOf j = t.parentOf j := by
  induction ops generalizing t with
  | nil => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | cons op ops ih =>
    obtain ⟨hlen, hpar⟩ := step_extends t op
    obtain ⟨hlen', hpar'⟩ := ih (t.step op)
    exact ⟨Nat.le_trans hlen hlen', fun j hj => (hpar' j (Nat.lt_of_lt_of_le hj hlen)).trans
      (hpar j hj)⟩

/-- A successful walk fixes its chain in every tree that keeps the walked
tree's parents: there too, the nodes at or above `i` are exactly the walk's
path. -/
theorem within_of_walk {t t'' : Tree} {x : Int}
    (hext : ∀ j < t.length, t''.parentOf j = t.parentOf j) :
    ∀ {fuel i path}, t.walk x fuel i = .ok path → ∀ a, t''.Within i a ↔ a ∈ path
  | 0, _, _, h => by simp [walk] at h
  | fuel + 1, i, path, h => by
    intro a
    rw [walk_succ] at h
    cases hi : t[i]? with
    | none => simp [hi] at h
    | some n =>
      have hpi : t''.parentOf i = n.parent := by
        rw [hext i (lt_length_of_getElem? hi)]
        simp [parentOf, hi]
      simp only [hi] at h
      split at h
      · simp at h
      · cases hp : n.parent with
        | none =>
          simp only [hp, Except.ok.injEq] at h
          subst h
          rw [within_root (hpi.trans hp)]
          simp
        | some p =>
          simp only [hp] at h
          split at h
          · cases hw : t.walk x fuel p with
            | error e => simp [hw, Except.map] at h
            | ok rest =>
              simp only [hw, Except.map, Except.ok.injEq] at h
              subst h
              rw [within_step (hpi.trans hp), List.mem_cons, within_of_walk hext hw a]
          · simp at h

theorem spentUnder_append (t : Tree) (l l' : List (Nat × Int)) (a : Nat) :
    spentUnder t (l ++ l') a = spentUnder t l a + spentUnder t l' a := by
  simp [spentUnder, List.filter_append, List.sum_append]

theorem spentUnder_nil (t : Tree) (a : Nat) : spentUnder t [] a = 0 := rfl

theorem spentUnder_single (t : Tree) (i : Nat) (x : Int) (a : Nat) :
    open Classical in
    spentUnder t [(i, x)] a = if t.Within i a then x else 0 := by
  unfold spentUnder
  by_cases w : t.Within i a <;> simp [w]

/-- What one operation does to node `a`'s spent amount: a successful spend at or
under `a`, in every tree that keeps the current parents, adds its amount, and
nothing else changes it. A node the operation appends starts from nothing. -/
theorem step_spent (t t'' : Tree) (op : Op) (a : Nat)
    (hext : ∀ j < t.length, t''.parentOf j = t.parentOf j) :
    ((t.step op)[a]?.map (·.spent)).getD 0 =
      (t[a]?.map (·.spent)).getD 0 + spentUnder t'' (op.logged t) a := by
  cases op with
  | spend i x =>
    cases h : t.spend i x with
    | error e =>
      have he : (Op.spend i x).apply t = .error e := h
      rw [step_of_error he, logged_of_error he, spentUnder_nil, Int.add_zero]
    | ok t' =>
      have hs : t.step (.spend i x) = t' := by simp [step, Op.apply, h]
      have hl : (Op.spend i x).logged t = [(i, x)] := by simp [Op.logged, h]
      rw [hs, hl, spentUnder_single]
      obtain ⟨-, -, -, path, hw, -⟩ := spend_ok_iff.mp h
      have hwin : t''.Within i a ↔ t.Within i a := by
        rw [within_of_walk hext hw a, mem_walk hw a]
      by_cases w : t.Within i a
      · obtain ⟨n, hn, hn'⟩ := spend_ok_charges h w
        simp [hn, hn', hwin.mpr w]
      · simp only [spend_ok_unchanged h w, show ¬ t''.Within i a from fun w' => w (hwin.mp w'),
          ↓reduceIte, Int.add_zero]
  | delegate p x =>
    rw [show (Op.delegate p x).logged t = [] from rfl, spentUnder_nil, Int.add_zero]
    unfold step
    split
    · rename_i t' h
      obtain ⟨-, -, -, -, rfl⟩ := delegate_ok_iff.mp h
      rw [List.getElem?_append]
      split
      · rfl
      · rename_i ha
        rw [List.getElem?_eq_none (Nat.le_of_not_lt ha)]
        cases hk : a - t.length with
        | zero => simp
        | succ k => simp
    · rfl
  | refill i x =>
    rw [show (Op.refill i x).logged t = [] from rfl, spentUnder_nil, Int.add_zero]
    unfold step
    split
    · rename_i t' h
      obtain ⟨-, n, hn, -, -, rfl⟩ := refill_ok_iff.mp h
      rw [List.getElem?_set]
      split
      · rename_i hia
        subst hia
        simp [lt_length_of_getElem? hn, getElem_of_getElem? hn]
      · rfl
    · rfl

/-- After any run, each node's spent amount is its spent amount before the run
(nothing, for a node the run appended) plus the total successfully spent at or
under it. -/
theorem spent_run (t : Tree) (ops : List Op) (a : Nat) {n : Node}
    (ha : (t.run ops).1[a]? = some n) :
    n.spent = (t[a]?.map (·.spent)).getD 0 + spentUnder (t.run ops).1 (t.run ops).2 a := by
  induction ops generalizing t with
  | nil => simp [run, spentUnder] at ha ⊢; simp [ha]
  | cons op ops ih =>
    have ih' := ih (t.step op) ha
    have hext : ∀ j < t.length, ((t.step op).run ops).1.parentOf j = t.parentOf j := by
      intro j hj
      obtain ⟨hlen, hpar⟩ := step_extends t op
      exact ((run_extends (t.step op) ops).2 j (Nat.lt_of_lt_of_le hj hlen)).trans (hpar j hj)
    show n.spent = _ + spentUnder ((t.step op).run ops).1 (op.logged t ++ ((t.step op).run ops).2) a
    rw [ih', spentUnder_append, step_spent t _ op a hext, Int.add_assoc]

/-- From a tree with nothing spent, after any run, the total successfully spent
at or under each node is that node's spent amount. -/
theorem spentUnder_eq_spent {t : Tree} (h0 : ∀ n ∈ t, n.spent = 0) (ops : List Op) {a : Nat}
    {n : Node} (ha : (t.run ops).1[a]? = some n) :
    spentUnder (t.run ops).1 (t.run ops).2 a = n.spent := by
  have hz : (t[a]?.map (·.spent)).getD 0 = 0 := by
    cases hl : t[a]? with
    | none => rfl
    | some m => simp [h0 m (List.mem_of_getElem? hl)]
  rw [spent_run t ops a ha, hz, Int.zero_add]

/-- Budget safety over any run: from a well-formed tree with nothing spent,
after any sequence of spends, delegations and refills, the total successfully
spent at or under each node never exceeds that node's allowance, however much
its children's allowances oversubscribe it. -/
theorem spentUnder_le_allowance {t : Tree} (hv : t.valid = true) (h0 : ∀ n ∈ t, n.spent = 0)
    (ops : List Op) {a : Nat} {n : Node} (ha : (t.run ops).1[a]? = some n) :
    spentUnder (t.run ops).1 (t.run ops).2 a ≤ n.allowance := by
  have hw : t.WithinAllowance := fun m hm => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    rw [h0 _ hm]
    exact (nonneg_of_valid hv (List.getElem?_eq_getElem hj)).1
  rw [spentUnder_eq_spent h0 ops ha]
  exact withinAllowance_iff.mp (run_withinAllowance hw ops) a n ha

end Tree

/-! ## Examples

A root with allowance 10 delegates allowance 8 to each of two children, 16 in
all. The first child spends 8; the second child's spend of 3 is refused at the
root, which has 2 left, and its spend of 2 succeeds, charging the second child
and the root.

The first child then delegates allowance 20, more than its own 8, to node 3.
After the owner refills the root by 5, node 3's spend of 1 is still refused,
as `overdrawn 1`: the first child is the nearest node on its chain that cannot
take it. A spend of 0 succeeds and is logged. -/

private def siblings : Tree :=
  [⟨none, 10, 0⟩, ⟨some 0, 8, 0⟩, ⟨some 0, 8, 0⟩]

example : (siblings.spend 1 8 >>= (·.spend 2 3)) = .error (.overdrawn 0) := rfl

example : (siblings.spend 1 8 >>= (·.spend 2 2)) =
    .ok [⟨none, 10, 10⟩, ⟨some 0, 8, 8⟩, ⟨some 0, 8, 2⟩] := rfl

example :
    siblings.run [.spend 1 8, .delegate 1 20, .refill 0 5, .spend 3 1, .spend 3 0] =
      ([⟨none, 15, 8⟩, ⟨some 0, 8, 8⟩, ⟨some 0, 8, 0⟩, ⟨some 1, 20, 0⟩], [(1, 8), (3, 0)]) := by
  decide

example : siblings.spend 3 1 = .error (.noSuchNode 3) := rfl

example : Tree.spend [⟨some 0, 1, 0⟩] 0 0 = .error .malformed := rfl

end RuleCore.Budget
