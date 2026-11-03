import RuleCore.Equiv.DenoteBudget
import RuleCore.Equiv.Authorize
import RuleCore.Theorems.Budget

/-!
# Budgets: the extracted operations agree with the model

Each theorem says that an extracted function of the `budget` module returns
`ok` on every input, so it terminates and does not panic, and that the value it
returns denotes the model's result:

* `tree_valid_eq`: `tree_valid` is `Tree.valid`;
* `spend_eq`: `spend` returns the model's `Tree.spend`, the charged tree or the
  same refusal;
* `delegate_eq`: `delegate` returns the model's `Tree.delegate`;
* `refill_eq`: `refill` returns the model's `Tree.refill`.

None takes a hypothesis. The building blocks are `fits_eq` (Rust's
`checked_add` test is the model's `Node.fits`), `check_chain_loop_eq` (the
checking walk is the model's `Tree.walk`, with the steps left as fuel) and
`charged_loop_eq` (after a successful walk of `path`, the charging loop adds
the amount to exactly the nodes of `path`). The charging loop's `checked_add`
never fails there: the walk found that the same sum fits at each node it
visits. `delegate`'s `Vec::push` succeeds because it runs only on a tree of
fewer than `maxNodes` nodes, and `maxNodes` is below `Usize.max`
(`max_nodes_le_usize`).

A node index is a `u32` in Rust and a natural number in the model, and an
amount is an `i128` in Rust and an integer in the model. The denotation takes
each to its value, so the model's statements cover every Rust input; the model
also allows indices and amounts no Rust value denotes, about which the
equivalence says nothing.
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std Result ControlFlow
open RuleCore.Budget

theorem length_denoteTree (l : List rule_eval.budget.Node) :
    (denoteTree l).length = l.length := by
  simp [denoteTree]

theorem getElem?_denoteTree (l : List rule_eval.budget.Node) (i : Nat) :
    (denoteTree l)[i]? = l[i]?.map denoteNode := by
  simp [denoteTree]

theorem denoteTree_drop (l : List rule_eval.budget.Node) (i : Nat) :
    denoteTree (l.drop i) = (denoteTree l).drop i := by
  simp [denoteTree, List.map_drop]

/-! ## Well-formed trees -/

theorem node_valid_eq (n : rule_eval.budget.Node) (index : Usize) :
    rule_eval.budget.node_valid n index = ok ((denoteNode n).valid index.val) := by
  unfold rule_eval.budget.node_valid
  cases hp : n.parent with
  | none =>
    by_cases ha : (0 : Int) ≤ n.allowance.val
    · have ha' : n.allowance >= 0#i128 := by simpa using ha
      by_cases hs : (0 : Int) ≤ n.spent.val
      · have hs' : n.spent >= 0#i128 := by simpa using hs
        simp [Node.valid, denoteNode, hp, ha', ha, hs', hs]
      · have hs' : ¬ n.spent >= 0#i128 := by simpa using hs
        simp [Node.valid, denoteNode, hp, ha', ha, hs', hs]
    · have ha' : ¬ n.allowance >= 0#i128 := by simpa using ha
      simp [Node.valid, denoteNode, hp, ha', ha]
  | some p =>
    by_cases hlt : p.val < index.val
    · by_cases ha : (0 : Int) ≤ n.allowance.val
      · have ha' : n.allowance >= 0#i128 := by simpa using ha
        by_cases hs : (0 : Int) ≤ n.spent.val
        · have hs' : n.spent >= 0#i128 := by simpa using hs
          simp [Node.valid, denoteNode, hp, lift, hlt, ha', ha, hs', hs]
        · have hs' : ¬ n.spent >= 0#i128 := by simpa using hs
          simp [Node.valid, denoteNode, hp, lift, hlt, ha', ha, hs', hs]
      · have ha' : ¬ n.allowance >= 0#i128 := by simpa using ha
        simp [Node.valid, denoteNode, hp, lift, hlt, ha', ha]
    · simp [Node.valid, denoteNode, hp, lift, hlt]

theorem tree_valid_loop_eq (tree : Slice rule_eval.budget.Node) (i : Usize) :
    rule_eval.budget.tree_valid_loop tree i =
      ok (Tree.validFrom (denoteTree (tree.val.drop i.val)) i.val) := by
  unfold rule_eval.budget.tree_valid_loop
  rw [loop]
  by_cases hi : i.val < tree.length
  · have hiv : i.val < tree.val.length := hi
    rw [List.drop_eq_getElem_cons hiv]
    obtain ⟨j, hj, hj'⟩ := incr_eq tree i hi
    have ih := tree_valid_loop_eq tree j
    unfold rule_eval.budget.tree_valid_loop at ih
    have hr : Tree.validFrom (denoteTree (tree.val[i.val] :: tree.val.drop (i.val + 1))) i.val =
        ((denoteNode tree.val[i.val]).valid i.val &&
          Tree.validFrom (denoteTree (tree.val.drop (i.val + 1))) (i.val + 1)) := rfl
    rw [hr]
    cases hb : (denoteNode tree.val[i.val]).valid i.val with
    | false =>
      simp [rule_eval.budget.tree_valid_loop.body, hi, index_usize_eq _ _ hi, node_valid_eq, hb]
    | true =>
      have hbody : rule_eval.budget.tree_valid_loop.body tree i = ok (cont j) := by
        simp [rule_eval.budget.tree_valid_loop.body, hi, index_usize_eq _ _ hi, node_valid_eq, hb,
          hj]
      rw [hbody, bind_ok]
      dsimp only
      rw [ih, hj', Bool.true_and]
  · have hge : ¬ i < Slice.len tree := by simpa using hi
    simp only [rule_eval.budget.tree_valid_loop.body, hge, ↓reduceIte, bind_ok]
    rw [List.drop_of_length_le (Nat.le_of_not_lt hi)]
    rfl
termination_by tree.length - i.val
decreasing_by omega

theorem tree_valid_eq (tree : Slice rule_eval.budget.Node) :
    rule_eval.budget.tree_valid tree = ok (denoteTree tree.val).valid := by
  simp [rule_eval.budget.tree_valid, tree_valid_loop_eq, Tree.valid]

theorem fits_eq (n : rule_eval.budget.Node) (x : Std.I128) :
    rule_eval.budget.fits n x = ok ((denoteNode n).fits x.val) := by
  unfold rule_eval.budget.fits Node.fits
  cases hc : I128.checked_add n.spent x with
  | none => simp [lift, denoteNode, checked_add_none hc]
  | some z =>
    simp only [lift, bind_ok, denoteNode, checked_add_some hc, ok.injEq]
    exact decide_eq_decide.mpr Iff.rfl

/-! ## Walking the chain -/

/-- What `check_chain` returned, as the outcome of the model's walk with its
path dropped. -/
def denoteChain : core.result.Result Unit rule_eval.budget.BudgetError →
    Except Budget.BudgetError Unit
  | .Ok () => .ok ()
  | .Err e => .error (denoteBudgetError e)

theorem except_map_cons_unit {ε : Type} (e : Except ε (List Nat)) (i : Nat) :
    (e.map (i :: ·)).map (fun _ => ()) = e.map (fun _ => ()) := by
  cases e <;> rfl

/-- The walk of `check_chain` from `cur`, with `step` steps taken, is the
model's walk with the steps left as fuel. -/
theorem check_chain_loop_eq (tree : Slice rule_eval.budget.Node) (x : Std.I128) :
    ∀ (fuel : Nat) (cur : Std.U32) (step : Usize), step.val + fuel = tree.length →
      ∃ r, rule_eval.budget.check_chain_loop tree x cur step = ok r ∧
        denoteChain r = ((denoteTree tree.val).walk x.val fuel cur.val).map (fun _ => ())
  | 0, cur, step, h => by
    refine ⟨.Err .Malformed, ?_, rfl⟩
    unfold rule_eval.budget.check_chain_loop
    rw [loop]
    have : ¬ step < Slice.len tree := by simp only [slice_len_lt]; omega
    simp [rule_eval.budget.check_chain_loop.body, this]
  | fuel + 1, cur, step, h => by
    have hs : step.val < tree.length := by omega
    have hs' : step < Slice.len tree := by simpa using hs
    unfold rule_eval.budget.check_chain_loop
    rw [loop, Tree.walk_succ, getElem?_denoteTree]
    cases hn : tree.val[cur.val]? with
    | none =>
      refine ⟨.Err .Malformed, ?_, rfl⟩
      simp [rule_eval.budget.check_chain_loop.body, hs', lift, slice_get_eq, hn]
    | some n =>
      simp only [Option.map_some]
      cases hf : (denoteNode n).fits x.val with
      | false =>
        refine ⟨.Err (.Overdrawn cur), ?_, rfl⟩
        simp [rule_eval.budget.check_chain_loop.body, hs', lift, slice_get_eq, hn, fits_eq, hf]
      | true =>
        cases hp : n.parent with
        | none =>
          refine ⟨.Ok (), ?_, ?_⟩
          · simp [rule_eval.budget.check_chain_loop.body, hs', lift, slice_get_eq, hn, fits_eq, hf,
              hp]
          · simp [denoteNode, hp]
            rfl
        | some p =>
          by_cases hlt : p.val < cur.val
          · obtain ⟨j, hj, hj'⟩ := incr_eq tree step hs
            obtain ⟨r, hr, hd⟩ := check_chain_loop_eq tree x fuel p j (by omega)
            have hge : ¬ cur.val ≤ p.val := by omega
            have hb : rule_eval.budget.check_chain_loop.body tree x cur step = ok (cont (p, j)) := by
              simp [rule_eval.budget.check_chain_loop.body, hs', lift, slice_get_eq, hn, fits_eq,
                hf, hp, hge, hj]
            refine ⟨r, ?_, ?_⟩
            · rw [hb, bind_ok]
              dsimp only
              unfold rule_eval.budget.check_chain_loop at hr
              exact hr
            · simp only [denoteNode, hp, Option.map_some, hlt, ↓reduceIte, Bool.not_true,
                Bool.false_eq_true]
              rw [except_map_cons_unit, hd]
          · refine ⟨.Err .Malformed, ?_, ?_⟩
            · have hge : cur.val ≤ p.val := by omega
              simp [rule_eval.budget.check_chain_loop.body, hs', lift, slice_get_eq, hn, fits_eq,
                hf, hp, hge]
            · simp [denoteNode, hp, hlt]
              rfl

/-! ## Copying and charging -/

theorem node_copy_eq (n : rule_eval.budget.Node) : rule_eval.budget.node_copy n = ok n := rfl

theorem nodes_copy_loop_eq (s : Slice rule_eval.budget.Node)
    (out : alloc.vec.Vec rule_eval.budget.Node) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.budget.nodes_copy_loop s out i = ok out' ∧
      out'.val.map id = out.val.map id ++
        pushedFrom (fun _ a => some (id a)) (s.val.drop i.val) i.val := by
  unfold rule_eval.budget.nodes_copy_loop
  refine loop_build s.val (fun _ a => some (id a)) id _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨out', hp, hv⟩ := push_eq out s.val[i.val] (room_of_lt s out i hi hout)
    obtain ⟨j, hj, hj'⟩ := incr_eq s i hi
    refine ⟨out', j, hj', by simp [hv], ?_⟩
    simp [rule_eval.budget.nodes_copy_loop.body, hi, index_usize_eq _ _ hi, node_copy_eq, hp, hj]
  · intro out i hi
    have : ¬ i.val < s.length := by simp only [Slice.length]; omega
    simp [rule_eval.budget.nodes_copy_loop.body, this]

/-- The copy of a tree holds the same nodes. -/
theorem nodes_copy_eq (s : Slice rule_eval.budget.Node) :
    ∃ out, rule_eval.budget.nodes_copy s = ok out ∧ out.val = s.val := by
  obtain ⟨out, h, hv⟩ := nodes_copy_loop_eq s (alloc.vec.Vec.new rule_eval.budget.Node)
    0#usize (by simp)
  exact ⟨out, h, by simpa [pushedFrom_map] using hv⟩

theorem charge_nil (t : Tree) (x : Int) : t.charge [] x = t := by
  apply List.ext_getElem?
  intro j
  rw [Tree.getElem?_charge]
  cases t[j]? <;> simp

theorem charge_congr (t : Tree) (x : Int) {P Q : List Nat} (h : ∀ j, j ∈ P ↔ j ∈ Q) :
    t.charge P x = t.charge Q x := by
  apply List.ext_getElem?
  intro j
  rw [Tree.getElem?_charge, Tree.getElem?_charge]
  cases t[j]? <;> simp [h j]

/-- Charging one more node of a partly charged tree, from the node's value in
the uncharged tree, charges it. -/
theorem charge_set (t : Tree) (x : Int) (S : List Nat) {j : Nat} {n : Node} (hj : t[j]? = some n)
    (m : Node) (hm : (t.charge S x)[j]? = some m) :
    (t.charge S x).set j { m with spent := n.spent + x } = t.charge (j :: S) x := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_set, Tree.getElem?_charge, Tree.getElem?_charge]
  rw [Tree.getElem?_charge, hj] at hm
  by_cases hk : j = k
  · subst hk
    have hlt : j < (t.charge S x).length := by
      rw [Tree.length_charge]; exact Tree.lt_length_of_getElem? hj
    simp only [hlt, ↓reduceIte, hj, Option.map_some, List.mem_cons, true_or]
    simp only [Option.map_some, Option.some.injEq] at hm
    subst hm
    by_cases hS : j ∈ S <;> simp [hS]
  · simp only [hk, ↓reduceIte, List.mem_cons]
    have : ¬ k = j := fun h => hk h.symm
    simp [this]

theorem vec_val_set_opt (out : alloc.vec.Vec rule_eval.budget.Node) (i : Std.U32)
    (v : rule_eval.budget.Node) :
    (({ slice := out.slice.set_opt (UScalar.cast .Usize i) (some v) } :
      alloc.vec.Vec rule_eval.budget.Node)).val = out.val.set i.val v := by
  simp [alloc.vec.Vec.val, Slice.set_opt, list_set_opt_some]

/-- After a successful walk of `path`, the charging loop from the same node,
on a vector holding the tree with the nodes of `S` charged, returns the tree
with the nodes of `path` charged as well. -/
theorem charged_loop_eq (tree : Slice rule_eval.budget.Node) (x : Std.I128) :
    ∀ (fuel : Nat) (cur : Std.U32) (step : Usize) (out : alloc.vec.Vec rule_eval.budget.Node)
      (S path : List Nat),
      step.val + fuel = tree.length →
      denoteTree out.val = (denoteTree tree.val).charge S x.val →
      (denoteTree tree.val).walk x.val fuel cur.val = .ok path →
      ∃ out', rule_eval.budget.charged_loop tree x out cur step = ok (.Ok out') ∧
        denoteTree out'.val = (denoteTree tree.val).charge (path ++ S) x.val
  | 0, _, _, _, _, _, _, _, hw => by simp [Tree.walk] at hw
  | fuel + 1, cur, step, out, S, path, h, hout, hw => by
    have hs : step.val < tree.length := by omega
    have hs' : step < Slice.len tree := by simpa using hs
    rw [Tree.walk_succ, getElem?_denoteTree] at hw
    cases hn : tree.val[cur.val]? with
    | none => simp [hn] at hw
    | some n =>
      simp only [hn, Option.map_some] at hw
      split at hw
      · simp at hw
      · rename_i hf
        have hf' : (denoteNode n).fits x.val = true := by simpa using hf
        have hcur : cur.val < tree.val.length := (List.getElem?_eq_some_iff.mp hn).1
        have htn : (denoteTree tree.val)[cur.val]? = some (denoteNode n) := by
          rw [getElem?_denoteTree, hn]; rfl
        -- the charged amount fits in an `i128`
        cases hc : I128.checked_add n.spent x with
        | none =>
          have := checked_add_none hc
          simp [Node.fits, denoteNode, this] at hf'
        | some z =>
          have hz := checked_add_some hc
          have hzv : z.val = n.spent.val + x.val := by
            unfold Cap.addI128 at hz
            split at hz
            · simp only [Option.some.injEq] at hz; exact hz.symm
            · cases hz
          -- the vector holds the tree, so it has the node too
          have hlen : out.val.length = tree.val.length := by
            have := congrArg List.length hout
            rw [length_denoteTree, Tree.length_charge, length_denoteTree] at this
            exact this
          obtain ⟨m, hm⟩ : ∃ m, out.val[cur.val]? = some m :=
            ⟨out.val[cur.val], List.getElem?_eq_getElem (by omega)⟩
          have hm' : out.slice.val[cur.val]? = some m := hm
          have hmd : ((denoteTree tree.val).charge S x.val)[cur.val]? = some (denoteNode m) := by
            rw [← hout, getElem?_denoteTree, hm]; rfl
          let out1 : alloc.vec.Vec rule_eval.budget.Node :=
            { slice := out.slice.set_opt (UScalar.cast .Usize cur) (some { m with spent := z }) }
          have hout1 : denoteTree out1.val =
              (denoteTree tree.val).charge (cur.val :: S) x.val := by
            rw [vec_val_set_opt, denoteTree, List.map_set, ← denoteTree, hout]
            have := charge_set (denoteTree tree.val) x.val S htn (denoteNode m) hmd
            rw [← this]
            simp [denoteNode, hzv]
          unfold rule_eval.budget.charged_loop
          rw [loop]
          cases hp : n.parent with
          | none =>
            simp only [denoteNode, hp, Option.map_none, Except.ok.injEq] at hw
            subst hw
            refine ⟨out1, ?_, by simpa using hout1⟩
            simp [rule_eval.budget.charged_loop.body, hs', lift, slice_get_eq, hn, hc,
              alloc.vec.Vec.deref_mut, slice_get_mut_eq, hm', hp, out1]
          | some p =>
            simp only [denoteNode, hp, Option.map_some] at hw
            split at hw
            · rename_i hlt
              cases hrest : (denoteTree tree.val).walk x.val fuel p.val with
              | error e => simp [hrest, Except.map] at hw
              | ok rest =>
                simp only [hrest, Except.map, Except.ok.injEq] at hw
                subst hw
                obtain ⟨j, hj, hj'⟩ := incr_eq tree step hs
                obtain ⟨out', hl, hd⟩ :=
                  charged_loop_eq tree x fuel p j out1 (cur.val :: S) rest (by omega) hout1 hrest
                have hge : ¬ cur.val ≤ p.val := by omega
                have hb : rule_eval.budget.charged_loop.body tree x out cur step =
                    ok (cont (out1, p, j)) := by
                  simp [rule_eval.budget.charged_loop.body, hs', lift, slice_get_eq, hn, hc,
                    alloc.vec.Vec.deref_mut, slice_get_mut_eq, hm', hp, hge, hj, out1]
                refine ⟨out', ?_, ?_⟩
                · dsimp only
                  rw [hb, bind_ok]
                  dsimp only
                  unfold rule_eval.budget.charged_loop at hl
                  exact hl
                · rw [hd]
                  apply charge_congr
                  intro k
                  simp only [List.mem_append, List.mem_cons]
                  tauto
            · simp at hw

/-! ## Spends -/

/-- The extracted `spend` returns `ok` on every input, and its outcome is the
model's: the charged tree, or the same refusal. -/
theorem spend_eq (tree : Slice rule_eval.budget.Node) (node : Std.U32) (x : Std.I128) :
    ∃ r, rule_eval.budget.spend tree node x = ok r ∧
      denoteBudget r = (denoteTree tree.val).spend node.val x.val := by
  unfold rule_eval.budget.spend Tree.spend
  rw [tree_valid_eq]
  cases hv : (denoteTree tree.val).valid with
  | false => exact ⟨.Err .Malformed, by simp, rfl⟩
  | true =>
    have hlen : (denoteTree tree.val).length = tree.length := length_denoteTree _
    by_cases hi : tree.length ≤ node.val
    · refine ⟨.Err (.NoSuchNode node), ?_, ?_⟩
      · simp [lift, hi]
      · simp [hlen, hi]; rfl
    · by_cases hx : x.val < 0
      · refine ⟨.Err .NegativeAmount, ?_, ?_⟩
        · simp [lift, hi, hx]
        · simp [hlen, hi, hx]; rfl
      · obtain ⟨r, hr, hd⟩ := check_chain_loop_eq tree x tree.length node 0#usize (by simp)
        have hr' : rule_eval.budget.check_chain tree node x = ok r := hr
        simp only [lift, bind_ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlen, hi, hx]
        have hi' : ¬ Slice.len tree ≤ UScalar.cast .Usize node := by
          simp only [slice_len_le, cast_usize_val]; omega
        have hx' : ¬ x < 0#i128 := by simpa using hx
        cases hw : (denoteTree tree.val).walk x.val tree.length node.val with
        | error e =>
          rw [hw] at hd
          cases r with
          | Ok u => cases hd
          | Err e' =>
            refine ⟨.Err e', ?_, ?_⟩
            · simp [hi', hx', hr']
            · simp only [denoteChain, Except.map, Except.error.injEq] at hd
              simp [denoteBudget, Except.map, hd]
        | ok path =>
          rw [hw] at hd
          cases r with
          | Err e' => cases hd
          | Ok u =>
            obtain ⟨out, hc, hcv⟩ := nodes_copy_eq tree
            obtain ⟨out', hl, hd'⟩ := charged_loop_eq tree x tree.length node 0#usize out []
              path (by simp) (by rw [hcv, charge_nil]) hw
            refine ⟨.Ok out', ?_, ?_⟩
            · simp [hi', hx', hr', rule_eval.budget.charged, hc, hl]
            · simp [denoteBudget, Except.map, hd']

/-! ## Delegation -/

theorem max_nodes_eq : ∃ m, rule_eval.budget.MAX_NODES = ok m ∧ m.val = maxNodes := by
  refine ⟨UScalar.cast .Usize core.num.U32.MAX, by unfold rule_eval.budget.MAX_NODES; rfl, ?_⟩
  simp [core.num.U32.MAX, U32.rMax, maxNodes]

theorem max_nodes_le_usize : maxNodes ≤ Usize.max := by
  have : U32.max ≤ Usize.max := by scalar_tac
  have h32 : U32.max = 4294967295 := by simp [U32.max, U32.numBits]
  simp only [maxNodes]
  omega

/-- The extracted `delegate` returns `ok` on every input, and its outcome is
the model's: the tree with the new child appended, or the same refusal. -/
theorem delegate_eq (tree : Slice rule_eval.budget.Node) (parent : Std.U32) (x : Std.I128) :
    ∃ r, rule_eval.budget.delegate tree parent x = ok r ∧
      denoteBudget r = (denoteTree tree.val).delegate parent.val x.val := by
  unfold rule_eval.budget.delegate Tree.delegate
  rw [tree_valid_eq]
  cases hv : (denoteTree tree.val).valid with
  | false => exact ⟨.Err .Malformed, by simp, rfl⟩
  | true =>
    have hlen : (denoteTree tree.val).length = tree.length := length_denoteTree _
    by_cases hi : tree.length ≤ parent.val
    · refine ⟨.Err (.NoSuchNode parent), ?_, ?_⟩
      · simp [lift, hi]
      · simp [hlen, hi]; rfl
    · by_cases hx : x.val < 0
      · refine ⟨.Err .NegativeAmount, ?_, ?_⟩
        · simp [lift, hi, hx]
        · simp [hlen, hi, hx]; rfl
      · obtain ⟨m, hm, hmv⟩ := max_nodes_eq
        by_cases hf : maxNodes ≤ tree.length
        · refine ⟨.Err .TreeFull, ?_, ?_⟩
          · have : ¬ tree.val.length < m.val := by
              rw [hmv]; simp only [Slice.length] at hf; omega
            simp [lift, hi, hx, hm, this]
          · simp [hlen, hi, hx, hf]; rfl
        · have hf' : tree.val.length < m.val := by
            rw [hmv]; simp only [Slice.length] at hf; omega
          obtain ⟨out, hc, hcv⟩ := nodes_copy_eq tree
          obtain ⟨out', hp, hpv⟩ := push_eq out
            ({ parent := some parent, allowance := x, spent := 0#i128 } : rule_eval.budget.Node)
            (by rw [hcv]; have := max_nodes_le_usize; simp only [Slice.length] at hf; omega)
          refine ⟨.Ok out', ?_, ?_⟩
          · simp [lift, hi, hx, hm, hf', hc, hp]
          · simp only [denoteBudget, hlen, hi, hx, hf, ↓reduceIte, Bool.not_true,
              Bool.false_eq_true, Except.ok.injEq]
            rw [hpv, hcv]
            simp [denoteTree, denoteNode]

/-! ## Refills -/

theorem refill_loop_eq (tree : Slice rule_eval.budget.Node) (index : Usize) (a : Std.I128)
    (out : alloc.vec.Vec rule_eval.budget.Node) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.budget.refill_loop tree index a out i = ok out' ∧
      out'.val.map denoteNode = out.val.map denoteNode ++
        pushedFrom (fun j n => some (if j = index.val then
            (fun m : Budget.Node => { m with allowance := a.val }) (denoteNode n)
          else denoteNode n))
          (tree.val.drop i.val) i.val := by
  unfold rule_eval.budget.refill_loop
  refine loop_build tree.val _ denoteNode _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq tree i hi
    by_cases hii : i = index
    · subst hii
      obtain ⟨out', hp, hval⟩ := push_eq out { tree.val[i.val] with allowance := a }
        (room_of_lt tree out i hi hout)
      refine ⟨out', j, hj', by simp [hval, denoteNode], ?_⟩
      simp [rule_eval.budget.refill_loop.body, hi, index_usize_eq _ _ hi, node_copy_eq, hp, hj]
    · have hv : i.val ≠ index.val := fun h => hii (usize_val_eq_iff.mp h)
      obtain ⟨out', hp, hval⟩ := push_eq out tree.val[i.val] (room_of_lt tree out i hi hout)
      refine ⟨out', j, hj', by simp [hval, hv], ?_⟩
      simp [rule_eval.budget.refill_loop.body, hi, hii, index_usize_eq _ _ hi, node_copy_eq, hp, hj]
  · intro out i hi
    have : ¬ i.val < tree.length := by simp only [Slice.length]; omega
    simp [rule_eval.budget.refill_loop.body, this]

/-- The extracted `refill` returns `ok` on every input, and its outcome is the
model's: the tree with the raised allowance, or the same refusal. -/
theorem refill_eq (tree : Slice rule_eval.budget.Node) (node : Std.U32) (x : Std.I128) :
    ∃ r, rule_eval.budget.refill tree node x = ok r ∧
      denoteBudget r = (denoteTree tree.val).refill node.val x.val := by
  unfold rule_eval.budget.refill Tree.refill
  rw [tree_valid_eq]
  cases hv : (denoteTree tree.val).valid with
  | false => exact ⟨.Err .Malformed, by simp, rfl⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, getElem?_denoteTree]
    cases hn : tree.val[node.val]? with
    | none =>
      refine ⟨.Err (.NoSuchNode node), ?_, rfl⟩
      simp [lift, slice_get_eq, hn]
    | some n =>
      simp only [Option.map_some]
      by_cases hx : x.val < 0
      · refine ⟨.Err .NegativeAmount, ?_, ?_⟩
        · simp [lift, slice_get_eq, hn, hx]
        · simp [hx]; rfl
      · have hx' : ¬ x < 0#i128 := by simpa using hx
        cases hc : I128.checked_add n.allowance x with
        | none =>
          refine ⟨.Err .Overflow, ?_, ?_⟩
          · simp [lift, slice_get_eq, hn, hx', hc]
          · simp [denoteNode, hx, checked_add_none hc]; rfl
        | some a =>
          have hlt : node.val < tree.val.length := (List.getElem?_eq_some_iff.mp hn).1
          have hnode : tree.val[node.val] = n := (List.getElem?_eq_some_iff.mp hn).2
          obtain ⟨out, hl, hval⟩ := refill_loop_eq tree (UScalar.cast .Usize node) a
            (alloc.vec.Vec.new rule_eval.budget.Node) 0#usize (by simp)
          refine ⟨.Ok out, ?_, ?_⟩
          · simp [lift, slice_get_eq, hn, hx', hc, hl]
          · simp only [denoteNode, hx, ↓reduceIte, checked_add_some hc, denoteBudget,
              Except.ok.injEq]
            have h0 : (0#usize).val = 0 := by simp
            simp only [vec_new_val, List.map_nil, List.nil_append, cast_usize_val, h0,
              List.drop_zero] at hval
            have key := pushedFrom_set denoteNode
              (fun m : Budget.Node => { m with allowance := a.val }) tree.val node.val hlt
            beta_reduce at key
            rw [show denoteTree out.val = out.val.map denoteNode from rfl, hval, key, hnode]
            rfl

end RuleCore.Equiv
