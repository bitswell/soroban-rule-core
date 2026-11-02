import RuleCore.Extracted.RuleEval

/-!
# Loops of the extracted evaluator

Aeneas translates each `while i < s.len()` loop of `crates/rule-eval` to
`loop body x`, where `loop` is Aeneas's `partial_fixpoint` combinator and
`body` returns `cont x'` to go round again or `done b` to exit. `loop` is not
total by construction, so a theorem `loop body x = ok b` is a proof that the
loop neither fails nor diverges.

Every loop in the evaluator is one of four shapes over a list `l` (the
elements of the slice it walks):

* `loop_any`: exit with `true` at the first element satisfying `p`, with
  `false` at the end;
* `loop_all`: exit with `false` at the first element not satisfying `p`, with
  `true` at the end;
* `loop_build`: push at most one value per element onto a vector `out` and
  exit with `out` at the end. `pushedFrom g l k` is what it pushes, where
  `g k a` is the value pushed for the element `a` at position `k`, if any;
* `loop_count`: add one to a counter for each element satisfying `p` at its
  position and exit with the counter at the end. `countFrom p l k` is what it
  adds. The counter grows at most once per element, so it stays at most the
  loop's position and its increment cannot overflow.

Each takes, as hypotheses, what one round of the body returns, and concludes
what the whole loop returns, by induction on the number of elements left.
`loop_build_fail` gives the other outcome: a round that fails fails the loop.

`push_eq` is the one rule the vectors need: Aeneas's model of `Vec::push`
succeeds while the vector holds fewer than `Usize.max` elements and fails
otherwise. A building loop pushes at most one value per element of a slice,
and a slice holds at most `Usize.max` elements, so its pushes succeed.
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std Result ControlFlow

/-! ## Primitive operations -/

theorem index_usize_eq {α : Type} (s : Slice α) (i : Usize) (h : i.val < s.length) :
    Slice.index_usize s i = ok s.val[i.val] := by
  simp [Slice.index_usize, h]

/-- The loop counter's `i + 1` succeeds: `i` indexes a slice, whose length is at
most `Usize.max`. -/
theorem incr_eq {α : Type} (s : Slice α) (i : Usize) (h : i.val < s.length) :
    ∃ j : Usize, i + 1#usize = ok j ∧ j.val = i.val + 1 := by
  have hmax : i.val + (1#usize).val ≤ UScalar.max .Usize := by
    have := s.property
    simp only [Slice.length] at h
    rw [UScalar.max_USize_eq]
    simp
    omega
  have := UScalar.add_spec (ty := .Usize) hmax
  revert this
  cases (i + 1#usize) with
  | ret r => intro hr; exact ⟨r, rfl, by simpa using hr⟩
  | vis e k => intro hr; simp at hr
  | div => intro hr; simp at hr

/-- A counter that is at most a position of a slice can be incremented: it is
below `Usize.max`. -/
theorem incr_eq_of_le {α : Type} (s : Slice α) (n i : Usize) (h : i.val < s.length)
    (hn : n.val ≤ i.val) : ∃ m : Usize, n + 1#usize = ok m ∧ m.val = n.val + 1 := by
  have hmax : n.val + (1#usize).val ≤ UScalar.max .Usize := by
    have := s.property
    simp only [Slice.length] at h
    rw [UScalar.max_USize_eq]
    simp
    omega
  have := UScalar.add_spec (ty := .Usize) hmax
  revert this
  cases (n + 1#usize) with
  | ret r => intro hr; exact ⟨r, rfl, by simpa using hr⟩
  | vis e k => intro hr; simp at hr
  | div => intro hr; simp at hr

@[simp] theorem slice_len_lt {α : Type} (s : Slice α) (i : Usize) :
    (i < Slice.len s) = (i.val < s.length) := by
  apply propext
  show i.val < (Slice.len s).val ↔ _
  rw [Slice.len_val]

@[simp] theorem vec_deref_val {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]

@[simp] theorem vec_new_val (α : Type) : (alloc.vec.Vec.new α).val = [] := by
  simp [alloc.vec.Vec.new]

/-- `Vec::push` succeeds while the vector holds fewer than `Usize.max`
elements. -/
theorem push_eq {α : Type} (v : alloc.vec.Vec α) (y : α) (h : v.val.length < Usize.max) :
    ∃ v' : alloc.vec.Vec α, v.push y = ok v' ∧ v'.val = v.val ++ [y] := by
  have := alloc.vec.Vec.push_spec v y h
  revert this
  cases v.push y with
  | ret r => intro hr; exact ⟨r, rfl, by simpa using hr⟩
  | vis e k => intro hr; simp at hr
  | div => intro hr; simp at hr

/-- `Vec::push` fails on a vector that already holds `Usize.max` elements. -/
theorem push_full {α : Type} (v : alloc.vec.Vec α) (y : α) (h : v.val.length = Usize.max) :
    v.push y = fail .maximumSizeExceeded := by
  unfold alloc.vec.Vec.push
  have hu : U32.max ≤ Usize.max := by scalar_tac
  have hc : (decide (v.val.length + 1 ≤ U32.max) || decide (v.val.length + 1 ≤ Usize.max)) =
      false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  simp only [hc, Bool.false_eq_true, ↓reduceDIte]

/-! ## Scans -/

theorem loop_any {α : Type} (l : List α) (p : α → Bool)
    (body : Usize → Result (ControlFlow Usize Bool))
    (hlt : ∀ (i : Usize) (h : i.val < l.length), ∃ j : Usize, j.val = i.val + 1 ∧
      body i = ok (if p l[i.val] then done true else cont j))
    (hge : ∀ i : Usize, l.length ≤ i.val → body i = ok (done false))
    (i : Usize) :
    loop body i = ok ((l.drop i.val).any p) := by
  rw [loop]
  by_cases hi : i.val < l.length
  · obtain ⟨j, hj, hb⟩ := hlt i hi
    rw [hb, bind_ok, List.drop_eq_getElem_cons hi, List.any_cons]
    cases p l[i.val]
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      rw [loop_any l p body hlt hge j, hj]
    · simp
  · rw [hge i (Nat.le_of_not_lt hi), bind_ok, List.drop_of_length_le (Nat.le_of_not_lt hi)]
    rfl
termination_by l.length - i.val
decreasing_by omega

theorem loop_all {α : Type} (l : List α) (p : α → Bool)
    (body : Usize → Result (ControlFlow Usize Bool))
    (hlt : ∀ (i : Usize) (h : i.val < l.length), ∃ j : Usize, j.val = i.val + 1 ∧
      body i = ok (if p l[i.val] then cont j else done false))
    (hge : ∀ i : Usize, l.length ≤ i.val → body i = ok (done true))
    (i : Usize) :
    loop body i = ok ((l.drop i.val).all p) := by
  rw [loop]
  by_cases hi : i.val < l.length
  · obtain ⟨j, hj, hb⟩ := hlt i hi
    rw [hb, bind_ok, List.drop_eq_getElem_cons hi, List.all_cons]
    cases p l[i.val]
    · simp
    · simp only [↓reduceIte, Bool.true_and]
      rw [loop_all l p body hlt hge j, hj]
  · rw [hge i (Nat.le_of_not_lt hi), bind_ok, List.drop_of_length_le (Nat.le_of_not_lt hi)]
    rfl
termination_by l.length - i.val
decreasing_by omega

/-! ## Building a vector -/

/-- What a building loop pushes for the elements of `l`, the first of them at
position `k`: `g j a` for the element `a` at position `j`, when it is some
value. -/
def pushedFrom {α β : Type} (g : Nat → α → Option β) : List α → Nat → List β
  | [], _ => []
  | a :: l, k => (g k a).toList ++ pushedFrom g l (k + 1)

/-- A loop that, at each position `i` below the length of `l`, pushes the
values `d` maps to `g i l[i]`, and exits with its vector at the end. `d` reads
the pushed values (a denotation, or `id`); the vector holds at most one value
per position read so far. -/
theorem loop_build {α β γ : Type} (l : List α) (g : Nat → α → Option γ) (d : β → γ)
    (body : alloc.vec.Vec β × Usize →
      Result (ControlFlow (alloc.vec.Vec β × Usize) (alloc.vec.Vec β)))
    (hlt : ∀ (out : alloc.vec.Vec β) (i : Usize) (h : i.val < l.length),
      out.val.length ≤ i.val →
      ∃ (out' : alloc.vec.Vec β) (j : Usize), j.val = i.val + 1 ∧
        out'.val.map d = out.val.map d ++ (g i.val l[i.val]).toList ∧
        body (out, i) = ok (cont (out', j)))
    (hge : ∀ (out : alloc.vec.Vec β) (i : Usize), l.length ≤ i.val →
      body (out, i) = ok (done out))
    (out : alloc.vec.Vec β) (i : Usize) (hout : out.val.length ≤ i.val) :
    ∃ out', loop body (out, i) = ok out' ∧
      out'.val.map d = out.val.map d ++ pushedFrom g (l.drop i.val) i.val := by
  rw [loop]
  by_cases hi : i.val < l.length
  · obtain ⟨out', j, hj, hval, hb⟩ := hlt out i hi hout
    have hout' : out'.val.length ≤ j.val := by
      have := congrArg List.length hval
      simp only [List.length_map, List.length_append] at this
      have : (g i.val l[i.val]).toList.length ≤ 1 := by cases g i.val l[i.val] <;> simp
      omega
    obtain ⟨out'', hloop, hval'⟩ := loop_build l g d body hlt hge out' j hout'
    refine ⟨out'', ?_, ?_⟩
    · rw [hb, bind_ok]
      exact hloop
    · rw [hval', hval, hj, List.drop_eq_getElem_cons hi, pushedFrom, List.append_assoc]
  · refine ⟨out, ?_, ?_⟩
    · rw [hge out i (Nat.le_of_not_lt hi), bind_ok]
    · rw [List.drop_of_length_le (Nat.le_of_not_lt hi)]
      simp [pushedFrom]
termination_by l.length - i.val
decreasing_by omega

/-- A building loop whose round at position `n` fails fails with the same
error, provided every earlier round goes round again. -/
theorem loop_build_fail {α β : Type} (l : List α) (n : Nat) (e : Error)
    (body : alloc.vec.Vec β × Usize →
      Result (ControlFlow (alloc.vec.Vec β × Usize) (alloc.vec.Vec β)))
    (hlt : ∀ (out : alloc.vec.Vec β) (i : Usize), i.val < n →
      out.val.length ≤ i.val →
      ∃ (out' : alloc.vec.Vec β) (j : Usize), j.val = i.val + 1 ∧
        out'.val.length ≤ out.val.length + 1 ∧ body (out, i) = ok (cont (out', j)))
    (heq : ∀ (out : alloc.vec.Vec β) (i : Usize), i.val = n →
      out.val.length ≤ i.val → body (out, i) = fail e)
    (out : alloc.vec.Vec β) (i : Usize) (hout : out.val.length ≤ i.val) (hi : i.val ≤ n) :
    loop body (out, i) = fail e := by
  rw [loop]
  by_cases hn : i.val < n
  · obtain ⟨out', j, hj, hlen, hb⟩ := hlt out i hn hout
    rw [hb, bind_ok]
    exact loop_build_fail l n e body hlt heq out' j (by omega) (by omega)
  · rw [heq out i (by omega) hout, bind_fail]
termination_by n - i.val
decreasing_by omega

/-! ## Counting -/

/-- How many elements of `l`, the first of them at position `k`, satisfy `p`
at their position: `p j a` for the element `a` at position `j`. -/
def countFrom {α : Type} (p : Nat → α → Bool) : List α → Nat → Nat
  | [], _ => 0
  | a :: l, k => (if p k a then 1 else 0) + countFrom p l (k + 1)

/-- A loop that, at each position `i` below the length of `l`, adds one to its
counter when `p i l[i]` holds, and exits with the counter at the end. -/
theorem loop_count {α : Type} (l : List α) (p : Nat → α → Bool)
    (body : Usize × Usize → Result (ControlFlow (Usize × Usize) Usize))
    (hlt : ∀ (n i : Usize) (h : i.val < l.length), n.val ≤ i.val →
      ∃ (n' j : Usize), j.val = i.val + 1 ∧
        n'.val = n.val + (if p i.val l[i.val] then 1 else 0) ∧ body (n, i) = ok (cont (n', j)))
    (hge : ∀ n i : Usize, l.length ≤ i.val → body (n, i) = ok (done n))
    (n i : Usize) (hn : n.val ≤ i.val) :
    ∃ n', loop body (n, i) = ok n' ∧ n'.val = n.val + countFrom p (l.drop i.val) i.val := by
  rw [loop]
  by_cases hi : i.val < l.length
  · obtain ⟨n', j, hj, hval, hb⟩ := hlt n i hi hn
    have hn' : n'.val ≤ j.val := by
      have : (if p i.val l[i.val] then 1 else 0) ≤ 1 := by split <;> simp
      omega
    obtain ⟨n'', hloop, hval'⟩ := loop_count l p body hlt hge n' j hn'
    refine ⟨n'', ?_, ?_⟩
    · rw [hb, bind_ok]
      exact hloop
    · rw [hval', hval, hj, List.drop_eq_getElem_cons hi, countFrom, Nat.add_assoc]
  · refine ⟨n, ?_, ?_⟩
    · rw [hge n i (Nat.le_of_not_lt hi), bind_ok]
    · rw [List.drop_of_length_le (Nat.le_of_not_lt hi)]
      simp [countFrom]
termination_by l.length - i.val
decreasing_by omega

theorem countFrom_map {α β : Type} (f : α → β) (p : Nat → β → Bool) :
    ∀ (l : List α) (k : Nat), countFrom p (l.map f) k = countFrom (fun j a => p j (f a)) l k
  | [], _ => rfl
  | a :: l, k => by simp [countFrom, countFrom_map f p l (k + 1)]

/-- Counting each element of `l` at its first position, when it satisfies `q`,
counts the elements of `l.eraseDups` that satisfy `q`: from position `k` on,
the count adds to what `l.take k` already holds. -/
theorem countFrom_first_from {α : Type} [DecidableEq α] (l : List α) (q : α → Bool) (k : Nat)
    (hk : k ≤ l.length) :
    ((l.take k).eraseDups.filter q).length +
        countFrom (fun j a => !decide (a ∈ l.take j) && q a) (l.drop k) k =
      (l.eraseDups.filter q).length := by
  by_cases hlt : k < l.length
  · have ih := countFrom_first_from l q (k + 1) hlt
    rw [List.drop_eq_getElem_cons hlt, countFrom, ← ih, List.take_add_one, List.getElem?_eq_getElem hlt,
      Option.toList_some, List.eraseDups_append]
    by_cases hm : l[k] ∈ l.take k
    · have : [l[k]].removeAll (l.take k) = [] := by simp [List.removeAll, hm]
      simp [this, hm]
    · have : [l[k]].removeAll (l.take k) = [l[k]] := by simp [List.removeAll, hm]
      have hs : [l[k]].eraseDups = [l[k]] := rfl
      rw [this, hs, List.filter_append, List.length_append]
      cases hq : q l[k]
      · simp [hm, hq]
      · simp [hm, hq]
        omega
  · have hk' : k = l.length := by omega
    subst hk'
    simp [countFrom]
termination_by l.length - k

theorem countFrom_first {α : Type} [DecidableEq α] (l : List α) (q : α → Bool) :
    countFrom (fun j a => !decide (a ∈ l.take j) && q a) l 0 = (l.eraseDups.filter q).length := by
  have := countFrom_first_from l q 0 (Nat.zero_le _)
  simpa using this

/-! ## What a building loop pushes -/

theorem pushedFrom_map_of {α γ : Type} (f : α → γ) (g : Nat → α → Option γ) :
    ∀ (l : List α) (k : Nat), (∀ j a, k ≤ j → g j a = some (f a)) →
      pushedFrom g l k = l.map f
  | [], _, _ => rfl
  | a :: l, k, hg => by
    rw [pushedFrom, hg k a (Nat.le_refl k), pushedFrom_map_of f g l (k + 1)
      (fun j a h => hg j a (by omega))]
    rfl

/-- Pushing a value for every element maps the list. -/
theorem pushedFrom_map {α γ : Type} (f : α → γ) (l : List α) (k : Nat) :
    pushedFrom (fun _ a => some (f a)) l k = l.map f :=
  pushedFrom_map_of f _ l k (fun _ _ _ => rfl)

/-- Pushing a value for the elements satisfying `p` filters the list. -/
theorem pushedFrom_filter {α γ : Type} (p : α → Bool) (f : α → γ) :
    ∀ (l : List α) (k : Nat),
      pushedFrom (fun _ a => if p a then some (f a) else none) l k = (l.filter p).map f
  | [], _ => rfl
  | a :: l, k => by
    rw [pushedFrom, pushedFrom_filter p f l (k + 1), List.filter_cons]
    cases p a <;> simp

/-- Pushing a value for every element but the one at position `k + n` erases
that element. -/
theorem pushedFrom_eraseIdx_from {α γ : Type} (f : α → γ) :
    ∀ (l : List α) (k n : Nat),
      pushedFrom (fun j a => if j = k + n then none else some (f a)) l k =
        (l.map f).eraseIdx n
  | [], _, _ => rfl
  | a :: l, k, 0 => by
    rw [pushedFrom, pushedFrom_map_of f _ l (k + 1) (fun j a h => by simp; omega)]
    simp
  | a :: l, k, n + 1 => by
    rw [pushedFrom, show k + (n + 1) = (k + 1) + n by omega, pushedFrom_eraseIdx_from f l (k + 1) n]
    simp [show k ≠ k + 1 + n by omega]

/-- Pushing `h` of the value for the element at position `k + n`, and the value
itself for every other element, sets that position. -/
theorem pushedFrom_set_from {α γ : Type} (f : α → γ) (h : γ → γ) :
    ∀ (l : List α) (k n : Nat) (hn : n < l.length),
      pushedFrom (fun j a => some (if j = k + n then h (f a) else f a)) l k =
        (l.map f).set n (h (f l[n]))
  | [], _, _, hn => by simp at hn
  | a :: l, k, 0, _ => by
    rw [pushedFrom, pushedFrom_map_of f _ l (k + 1) (fun j a h => by simp; omega)]
    simp
  | a :: l, k, n + 1, hn => by
    rw [pushedFrom, show k + (n + 1) = (k + 1) + n by omega,
      pushedFrom_set_from f h l (k + 1) n (by simpa using hn)]
    simp [show k ≠ k + 1 + n by omega]

theorem pushedFrom_eraseIdx {α γ : Type} (f : α → γ) (l : List α) (n : Nat) :
    pushedFrom (fun j a => if j = n then none else some (f a)) l 0 = (l.map f).eraseIdx n := by
  rw [← pushedFrom_eraseIdx_from f l 0 n, Nat.zero_add]

theorem pushedFrom_set {α γ : Type} (f : α → γ) (h : γ → γ) (l : List α) (n : Nat)
    (hn : n < l.length) :
    pushedFrom (fun j a => some (if j = n then h (f a) else f a)) l 0 =
      (l.map f).set n (h (f l[n])) := by
  rw [← pushedFrom_set_from f h l 0 n hn, Nat.zero_add]

end RuleCore.Equiv
