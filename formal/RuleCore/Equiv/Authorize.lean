import RuleCore.Equiv.Cap
import RuleCore.Theorems.Chain

/-!
# Authorization: the extracted `check_auth` agrees with the model

The denotations below extend those of `RuleCore/Equiv/Denote.lean` and
`RuleCore/Equiv/DenoteCap.lean` to the `authorize` module, and are part of the
specification like them:

* each `Refusal` constructor is the constructor of the same name, and
  `Refusal::Cap(e)` is `Refusal.cap` of the denoted `CapError`;
* a Rust `Result` of `check_auth` is the `Except` with the denoted records, and
  one of the first pass (`check_choices`) the `Except` with the unit value;
* the arguments of `check_auth` (the contexts, the choices, the authenticated
  signers, the ledger and the generation) are the chain vocabulary's
  authorization of their denotations (`denoteAuthorization`).

Each theorem says that an extracted function returns `ok` on every input, so it
neither fails nor diverges, and that the value it returns is the model's on the
denoted inputs:

* `spend_amount_eq`: `spend_amount limits ctx` is the amount the denoted cap
  reads from the denoted context;
* `expired_eq`, `stale_eq`: `expired r now` and `stale r generation` are
  `Rule.expired` and `Rule.stale` of the denoted rule;
* `check_choices_loop_eq`: the first pass, from position `i`, is the model's
  `forM` of `checkChoice` over the contexts and choices from `i` on;
* `signer_chosen_eq`, `signers_chosen_eq`: the second pass is the model's
  `signerChosen` of each authenticated signer;
* `records_copy_eq`: the copy of the records returns the same records;
* `charge_all_loop_eq`: the second pass, from position `i`, is the model's
  `foldlM` of `charge` over the contexts and choices from `i` on;
* `check_auth_eq`: `check_auth rules records contexts choices authenticated now`
  is `Chain.RuleSet.checkAuth` of the denotations, every refusal included.

`get_mut` on the record vector is Aeneas's model of `<[T]>::get_mut` through
`Vec`'s `DerefMut`: it returns the element at the index, if any, and a function
that writes a new value back at that index. Every `Vec::push` of the record
copy has room, as in the copies of `RuleCore.Equiv.Attenuation`; no bound is
stated.
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std Result ControlFlow

def denoteRefusal : rule_eval.authorize.Refusal → Refusal
  | .ChoicesMismatch => .choicesMismatch
  | .RecordsMismatch => .recordsMismatch
  | .NoSuchRule => .noSuchRule
  | .Expired => .expired
  | .StaleGeneration => .staleGeneration
  | .NotAllowed => .notAllowed
  | .UnauthorizedSigner => .unauthorizedSigner
  | .NoAmount => .noAmount
  | .Cap e => .cap (denoteCapError e)

/-- What `check_auth` returned, as the model's outcome. -/
def denoteAuthorized :
    core.result.Result (alloc.vec.Vec rule_eval.cap.SpendRecord) rule_eval.authorize.Refusal →
      Except Refusal (List Cap.Record)
  | .Ok out => .ok (out.val.map denoteRecord)
  | .Err e => .error (denoteRefusal e)

/-- What the first pass returned, as the model's outcome. -/
def denoteChecked : core.result.Result Unit rule_eval.authorize.Refusal → Except Refusal Unit
  | .Ok () => .ok ()
  | .Err e => .error (denoteRefusal e)

/-- The arguments of `check_auth`, as the chain vocabulary's authorization. -/
def denoteAuthorization (contexts : Slice rule_eval.context.Context) (choices : Slice Std.U32)
    (authenticated : Slice rule_eval.signer.Signer) (now : Std.U32) (generation : Std.U64) :
    Chain.Authorization :=
  ⟨contexts.val.map denoteContext, choices.val.map denoteU32, denoteSigners authenticated.val,
    denoteU32 now, denoteU64 generation⟩

/-! ## Injectivity -/

theorem denoteRefusal_injective : Function.Injective denoteRefusal := by
  intro a b h
  cases a <;> cases b <;> simp only [denoteRefusal, reduceCtorEq, Refusal.cap.injEq] at h <;>
    first | rfl | rw [denoteCapError_injective h]

theorem denoteAuthorized_injective : Function.Injective denoteAuthorized := by
  intro a b h
  cases a with
  | Ok out =>
    cases b with
    | Ok out' =>
      simp only [denoteAuthorized, Except.ok.injEq] at h
      rw [vec_eq_of_val ((List.map_injective_iff.mpr denoteRecord_injective) h)]
    | Err e => simp [denoteAuthorized] at h
  | Err e =>
    cases b with
    | Ok out => simp [denoteAuthorized] at h
    | Err e' =>
      simp only [denoteAuthorized, Except.error.injEq] at h
      rw [denoteRefusal_injective h]

/-! ## The model, read on the denotations -/

@[simp] theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

@[simp] theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- The contexts of `check_auth`'s arguments with their chosen indices, as the
model's authorization lists them. -/
def chosenOf (contexts : Slice rule_eval.context.Context) (choices : Slice Std.U32) :
    List (Chain.Context × Nat) :=
  (contexts.val.map denoteContext).zip (choices.val.map (·.val))

theorem chosen_denoteAuthorization (contexts : Slice rule_eval.context.Context)
    (choices : Slice Std.U32) (authenticated : Slice rule_eval.signer.Signer) (now : Std.U32)
    (generation : Std.U64) :
    (denoteAuthorization contexts choices authenticated now generation).denote.chosen =
      chosenOf contexts choices := by
  simp [Authorization.chosen, Chain.Authorization.denote, denoteAuthorization, chosenOf,
    List.map_map, Function.comp_def]

theorem chosenOf_drop {contexts : Slice rule_eval.context.Context} {choices : Slice Std.U32}
    (hlen : choices.length = contexts.length) {i : Nat} (hi : i < contexts.length) :
    (chosenOf contexts choices).drop i =
      (denoteContext contexts.val[i], (choices.val[i]'(by simp only [Slice.length] at hlen hi; omega)).val) ::
        (chosenOf contexts choices).drop (i + 1) := by
  have hl : i < (chosenOf contexts choices).length := by
    simp only [chosenOf, List.length_zip, List.length_map]
    simp only [Slice.length] at hlen hi
    omega
  rw [List.drop_eq_getElem_cons hl]
  simp [chosenOf]

theorem chosenOf_drop_nil {contexts : Slice rule_eval.context.Context} {choices : Slice Std.U32}
    {i : Nat} (hi : contexts.length ≤ i) : (chosenOf contexts choices).drop i = [] := by
  apply List.drop_of_length_le
  simp only [chosenOf, List.length_zip, List.length_map]
  simp only [Slice.length] at hi
  omega

theorem denoteRules_rules_get (rules : Slice rule_eval.rule.Rule) (j : Nat) :
    (denoteRules rules.val).denote.rules[j]? = rules.val[j]?.map fun r => (denoteRule r).denote := by
  simp [Chain.RuleSet.denote, denoteRules, List.getElem?_map, Function.comp_def]

theorem denoteRule_denote_cap (r : rule_eval.rule.Rule) :
    (denoteRule r).denote.cap = r.cap.map fun c => (denoteCap c).denote := by
  cases h : r.cap <;> simp [Chain.Rule.denote, denoteRule, h]

theorem denoteCap_params (c : rule_eval.rule.Cap) :
    (denoteCap c).denote.params = ⟨c.limit.val, c.period.val⟩ := rfl

/-! ## The amount a context spends -/

theorem spend_amount_eq (limits : rule_eval.rule.Cap) (ctx : rule_eval.context.Context) :
    ∃ o, rule_eval.authorize.spend_amount limits ctx = ok o ∧
      o.map (·.val) = (denoteCap limits).amount (denoteContext ctx) := by
  cases ctx with
  | Create wasmHash => exact ⟨none, rfl, rfl⟩
  | Call contract function args =>
    simp only [rule_eval.authorize.spend_amount, lift, bind_ok, slice_get_eq, vec_deref_val,
      cast_usize_val, denoteContext, Chain.Cap.amount, denoteCap, denoteU32_toNat,
      List.getElem?_map]
    cases args.val[limits.amount_arg.val]? with
    | none => exact ⟨none, rfl, rfl⟩
    | some v =>
      cases v <;> simp [denoteVal]

/-! ## The first pass -/

@[simp] theorem denoteU64_toNat (x : Std.U64) : (denoteU64 x).toNat = x.val := rfl

theorem expired_eq (r : rule_eval.rule.Rule) (now : Std.U32) :
    rule_eval.authorize.expired r now = ok ((denoteRule r).denote.expired now.val) := by
  cases h : r.valid_until <;>
    simp [rule_eval.authorize.expired, Chain.Rule.denote, denoteRule, RuleCore.Rule.expired, h]

theorem stale_eq (r : rule_eval.rule.Rule) (generation : Std.U64) :
    rule_eval.authorize.stale r generation = ok ((denoteRule r).denote.stale generation.val) := by
  cases h : r.generation with
  | none => simp [rule_eval.authorize.stale, Chain.Rule.denote, denoteRule, RuleCore.Rule.stale, h]
  | some g =>
    simp only [rule_eval.authorize.stale, h, Chain.Rule.denote, denoteRule, RuleCore.Rule.stale,
      Option.map_some, denoteU64_toNat]
    by_cases he : g = generation
    · subst he
      simp
    · have hv : g.val ≠ generation.val := fun hv => he (UScalar.eq_of_val_eq hv)
      simp [he, hv]

theorem check_choices_loop_eq (rules : Slice rule_eval.rule.Rule)
    (contexts : Slice rule_eval.context.Context) (choices : Slice Std.U32)
    (authenticated : Slice rule_eval.signer.Signer) (now : Std.U32) (generation : Std.U64)
    (hlen : choices.length = contexts.length) (i : Usize) (hi : i.val ≤ contexts.length) :
    ∃ res, rule_eval.authorize.check_choices_loop rules contexts choices authenticated now
        generation i = ok res ∧
      denoteChecked res =
        ((chosenOf contexts choices).drop i.val).forM
          ((denoteRules rules.val).denote.checkChoice (denoteSigners authenticated.val) now.val
            generation.val (contexts.val.head?.map denoteContext)) := by
  unfold rule_eval.authorize.check_choices_loop
  rw [loop]
  by_cases hlt : i.val < contexts.length
  · have hc : i.val < choices.length := by omega
    have hcv : i.val < choices.val.length := hc
    rw [chosenOf_drop hlen hlt]
    have hget : choices.val[i.val]? = some choices.val[i.val] := List.getElem?_eq_getElem hcv
    cases hr : rules.val[choices.val[i.val].val]? with
    | none =>
      refine ⟨.Err .NoSuchRule, ?_, ?_⟩
      · simp [rule_eval.authorize.check_choices_loop.body, hlt, slice_get_eq, hget, lift, hr]
      · simp [denoteChecked, denoteRefusal, List.forM, RuleSet.checkChoice, denoteRules,
          List.getElem?_map, hr]
    | some r =>
      cases hexp : (denoteRule r).denote.expired now.val with
      | true =>
        refine ⟨.Err .Expired, ?_, ?_⟩
        · simp [rule_eval.authorize.check_choices_loop.body, hlt, slice_get_eq, hget, lift, hr,
            expired_eq, hexp]
        · simp [denoteChecked, denoteRefusal, List.forM, RuleSet.checkChoice, denoteRules,
            List.getElem?_map, hr, hexp]
      | false =>
        cases hst : (denoteRule r).denote.stale generation.val with
        | true =>
          refine ⟨.Err .StaleGeneration, ?_, ?_⟩
          · simp [rule_eval.authorize.check_choices_loop.body, hlt, slice_get_eq, hget, lift, hr,
              expired_eq, hexp, stale_eq, hst]
          · simp [denoteChecked, denoteRefusal, List.forM, RuleSet.checkChoice, denoteRules,
              List.getElem?_map, hr, hexp, hst]
        | false =>
          cases ha : (denoteRule r).allowsIn (contexts.val.head?.map denoteContext) (denoteContext contexts.val[i.val])
              (denoteSigners authenticated.val) with
          | false =>
            refine ⟨.Err .NotAllowed, ?_, ?_⟩
            · simp [rule_eval.authorize.check_choices_loop.body, hlt, slice_get_eq, hget, lift,
                hr, expired_eq, hexp, stale_eq, hst, index_usize_eq _ _ hlt, rule_allows_in_eq, entry_root_eq, ha]
            · have ha' : (denoteRule r).denote.allowsIn (contexts.val.head?.map denoteContext) (denoteContext contexts.val[i.val])
                  (denoteSigners authenticated.val) = false := ha
              simp [denoteChecked, denoteRefusal, List.forM, RuleSet.checkChoice,
                denoteRules, List.getElem?_map, hr, hexp, hst, ha']
          | true =>
            obtain ⟨j, hj, hj'⟩ := incr_eq contexts i hlt
            obtain ⟨res, hres, hden⟩ := check_choices_loop_eq rules contexts choices
              authenticated now generation hlen j (by omega)
            unfold rule_eval.authorize.check_choices_loop at hres
            refine ⟨res, ?_, ?_⟩
            · have hb : rule_eval.authorize.check_choices_loop.body rules contexts choices
                  authenticated now generation i = ok (cont j) := by
                simp [rule_eval.authorize.check_choices_loop.body, hlt, slice_get_eq, hget, lift,
                  hr, expired_eq, hexp, stale_eq, hst, index_usize_eq _ _ hlt, rule_allows_in_eq, entry_root_eq,
                  ha, hj]
              rw [hb, bind_ok]
              exact hres
            · have ha' : (denoteRule r).denote.allowsIn (contexts.val.head?.map denoteContext) (denoteContext contexts.val[i.val])
                  (denoteSigners authenticated.val) = true := ha
              rw [hden, hj']
              simp [List.forM, RuleSet.checkChoice, denoteRules, List.getElem?_map, hr, hexp, hst,
                ha']
  · refine ⟨.Ok (), ?_, ?_⟩
    · simp [rule_eval.authorize.check_choices_loop.body, hlt]
    · rw [chosenOf_drop_nil (by omega)]
      rfl
termination_by contexts.length - i.val
decreasing_by omega

/-! ## The second pass -/

/-- What `signer_chosen` reads for one choice: whether `s` is a signer of the
rule the choice names, if there is one. -/
def signerOfChoice (rules : Slice rule_eval.rule.Rule) (s : rule_eval.signer.Signer)
    (k : Std.U32) : Bool :=
  match rules.val[k.val]? with
  | some r => decide (denoteSigner s ∈ denoteSigners r.signers.val)
  | none => false

theorem signer_chosen_eq (s : rule_eval.signer.Signer) (rules : Slice rule_eval.rule.Rule)
    (choices : Slice Std.U32) :
    rule_eval.authorize.signer_chosen s rules choices =
      ok ((denoteRules rules.val).denote.signerChosen (choices.val.map (·.val))
        (denoteSigner s)) := by
  unfold rule_eval.authorize.signer_chosen rule_eval.authorize.signer_chosen_loop
  rw [loop_any choices.val (signerOfChoice rules s)]
  · have h0 : (0#usize).val = 0 := by simp
    rw [h0, List.drop_zero]
    congr 1
    simp only [RuleSet.signerChosen, List.any_map, Function.comp_def]
    congr 1
    funext k
    simp only [signerOfChoice, denoteRules_rules_get]
    cases rules.val[k.val]? <;> rfl
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq choices i hi
    refine ⟨j, hj', ?_⟩
    cases hr : rules.val[choices.val[i.val].val]? with
    | none =>
      simp [rule_eval.authorize.signer_chosen_loop.body, hi, index_usize_eq _ _ hi, lift,
        slice_get_eq, hr, signerOfChoice, hj]
    | some r =>
      cases hs : decide (denoteSigner s ∈ denoteSigners r.signers.val) with
      | false =>
        have hs' : denoteSigner s ∉ denoteSigners r.signers.val := by simpa using hs
        simp [rule_eval.authorize.signer_chosen_loop.body, hi, index_usize_eq _ _ hi, lift,
          slice_get_eq, hr, signerOfChoice, signer_in_eq, hs', hj]
      | true =>
        have hs' : denoteSigner s ∈ denoteSigners r.signers.val := by simpa using hs
        simp [rule_eval.authorize.signer_chosen_loop.body, hi, index_usize_eq _ _ hi, lift,
          slice_get_eq, hr, signerOfChoice, signer_in_eq, hs']
  · intro i hi
    have : ¬ i.val < choices.length := by simp only [Slice.length]; omega
    simp [rule_eval.authorize.signer_chosen_loop.body, this]

theorem signers_chosen_eq (authenticated : Slice rule_eval.signer.Signer)
    (rules : Slice rule_eval.rule.Rule) (choices : Slice Std.U32) :
    rule_eval.authorize.signers_chosen authenticated rules choices =
      ok ((denoteSigners authenticated.val).all
        ((denoteRules rules.val).denote.signerChosen (choices.val.map (·.val)))) := by
  unfold rule_eval.authorize.signers_chosen rule_eval.authorize.signers_chosen_loop
  rw [loop_all authenticated.val
    (fun a => (denoteRules rules.val).denote.signerChosen (choices.val.map (·.val))
      (denoteSigner a))]
  · simp [denoteSigners, List.all_map, Function.comp_def]
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq authenticated i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.authorize.signers_chosen_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, signer_chosen_eq, bind_ok, hj]
    cases (denoteRules rules.val).denote.signerChosen (choices.val.map (·.val))
      (denoteSigner authenticated.val[i.val]) <;> simp
  · intro i hi
    have : ¬ i.val < authenticated.length := by simp only [Slice.length]; omega
    simp [rule_eval.authorize.signers_chosen_loop.body, this]

/-! ## Copying the records -/

theorem records_copy_loop_eq (s : Slice rule_eval.cap.SpendRecord)
    (out : alloc.vec.Vec rule_eval.cap.SpendRecord) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.authorize.records_copy_loop s out i = ok out' ∧
      out'.val.map id = out.val.map id ++
        pushedFrom (fun _ a => some (id a)) (s.val.drop i.val) i.val := by
  unfold rule_eval.authorize.records_copy_loop
  refine loop_build s.val (fun _ a => some (id a)) id _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨out', hp, hv⟩ := push_eq out s.val[i.val] (room_of_lt s out i hi hout)
    obtain ⟨j, hj, hj'⟩ := incr_eq s i hi
    refine ⟨out', j, hj', by simp [hv], ?_⟩
    simp [rule_eval.authorize.records_copy_loop.body, hi, index_usize_eq _ _ hi, record_copy_eq,
      hp, hj]
  · intro out i hi
    have : ¬ i.val < s.length := by simp only [Slice.length]; omega
    simp [rule_eval.authorize.records_copy_loop.body, this]

/-- The copy of the records holds the same records. -/
theorem records_copy_eq (s : Slice rule_eval.cap.SpendRecord) :
    ∃ out, rule_eval.authorize.records_copy s = ok out ∧ out.val = s.val := by
  obtain ⟨out, h, hv⟩ := records_copy_loop_eq s (alloc.vec.Vec.new rule_eval.cap.SpendRecord)
    0#usize (by simp)
  exact ⟨out, h, by simpa [pushedFrom_map] using hv⟩

/-! ## The third pass -/

theorem list_set_opt_some {α : Type} :
    ∀ (l : List α) (i : Nat) (x : α), l.set_opt i (some x) = l.set i x
  | [], _, _ => rfl
  | _ :: _, 0, _ => by simp
  | hd :: tl, i + 1, x => by
    rw [List.set_opt_cons_nzero' hd tl (i + 1) (some x) (by omega)]
    simp [list_set_opt_some tl i x]

/-- `get_mut` returns the element at the index, if any, and writes a new value
back at that index. -/
theorem slice_get_mut_eq {α : Type} (s : Slice α) (i : Usize) :
    core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice α) s i =
      ok (s.val[i.val]?, s.set_opt i) := by
  simp [core.slice.Slice.get_mut]

theorem charge_all_loop_eq (rules : Slice rule_eval.rule.Rule)
    (contexts : Slice rule_eval.context.Context) (choices : Slice Std.U32) (now : Std.U32)
    (hlen : choices.length = contexts.length) (out : alloc.vec.Vec rule_eval.cap.SpendRecord)
    (i : Usize) (hi : i.val ≤ contexts.length) :
    ∃ res, rule_eval.authorize.charge_all_loop rules contexts choices now out i = ok res ∧
      denoteAuthorized res =
        ((chosenOf contexts choices).drop i.val).foldlM
          ((denoteRules rules.val).denote.charge now.val) (out.val.map denoteRecord) := by
  unfold rule_eval.authorize.charge_all_loop
  rw [loop]
  dsimp only
  by_cases hlt : i.val < contexts.length
  · have hc : i.val < choices.length := by omega
    have hcv : i.val < choices.val.length := hc
    rw [chosenOf_drop hlen hlt, foldlM_except_cons]
    have hget : choices.val[i.val]? = some choices.val[i.val] := List.getElem?_eq_getElem hcv
    obtain ⟨j, hj, hj'⟩ := incr_eq contexts i hlt
    cases hr : rules.val[choices.val[i.val].val]? with
    | none =>
      refine ⟨.Err .NoSuchRule, ?_, ?_⟩
      · simp [rule_eval.authorize.charge_all_loop.body, hlt, slice_get_eq, hget, lift, hr]
      · simp [denoteAuthorized, denoteRefusal, RuleSet.charge, denoteRules, List.getElem?_map, hr]
    | some r =>
      cases hcap : r.cap with
      | none =>
        obtain ⟨res, hres, hden⟩ :=
          charge_all_loop_eq rules contexts choices now hlen out j (by omega)
        unfold rule_eval.authorize.charge_all_loop at hres
        refine ⟨res, ?_, ?_⟩
        · have hb : rule_eval.authorize.charge_all_loop.body rules contexts choices now out i =
              ok (cont (out, j)) := by
            simp [rule_eval.authorize.charge_all_loop.body, hlt, slice_get_eq, hget, lift, hr,
              hcap, hj]
          rw [hb, bind_ok]
          exact hres
        · rw [hden, hj']
          simp [RuleSet.charge, denoteRules, List.getElem?_map, hr, denoteRule_denote_cap, hcap]
      | some limits =>
        obtain ⟨o, ho, hod⟩ := spend_amount_eq limits contexts.val[i.val]
        cases o with
        | none =>
          refine ⟨.Err .NoAmount, ?_, ?_⟩
          · simp [rule_eval.authorize.charge_all_loop.body, hlt, slice_get_eq, hget, lift, hr,
              hcap, index_usize_eq _ _ hlt, ho]
          · have hamt : (denoteCap limits).denote.amount (denoteContext contexts.val[i.val]) =
                none := by
              show (denoteCap limits).amount _ = none
              rw [← hod]
              rfl
            simp [denoteAuthorized, denoteRefusal, RuleSet.charge, denoteRules, List.getElem?_map, hr,
              denoteRule_denote_cap, hcap, hamt]
        | some amount =>
          have hamt : (denoteCap limits).denote.amount (denoteContext contexts.val[i.val]) =
              some amount.val := by
            show (denoteCap limits).amount _ = _
            rw [← hod]
            rfl
          have hsl : (alloc.vec.Vec.deref_mut out).1 = out.slice := rfl
          cases hrec : out.val[choices.val[i.val].val]? with
          | none =>
            refine ⟨.Err .RecordsMismatch, ?_, ?_⟩
            · have hrec' : out.slice.val[choices.val[i.val].val]? = none := hrec
              simp [rule_eval.authorize.charge_all_loop.body, hlt, slice_get_eq, hget, lift, hr,
                hcap, index_usize_eq _ _ hlt, ho, alloc.vec.Vec.deref_mut, slice_get_mut_eq, hrec']
            · simp [denoteAuthorized, denoteRefusal, RuleSet.charge, denoteRules, List.getElem?_map, hr,
                denoteRule_denote_cap, hcap, hamt, List.getElem?_map, hrec]
          | some record =>
            have hrec' : out.slice.val[choices.val[i.val].val]? = some record := hrec
            obtain ⟨sres, hs, hsd⟩ := check_spend_eq record limits.limit limits.period now amount
            cases sres with
            | Err e =>
              refine ⟨.Err (.Cap e), ?_, ?_⟩
              · simp [rule_eval.authorize.charge_all_loop.body, hlt, slice_get_eq, hget, lift, hr,
                  hcap, index_usize_eq _ _ hlt, ho, alloc.vec.Vec.deref_mut, slice_get_mut_eq, hrec', hs]
              · simp only [denoteSpend] at hsd
                simp [denoteAuthorized, denoteRefusal, RuleSet.charge, denoteRules, List.getElem?_map, hr,
                  denoteRule_denote_cap, hcap, hamt, List.getElem?_map, hrec, denoteCap_params,
                  ← hsd]
            | Ok next =>
              let out1 : alloc.vec.Vec rule_eval.cap.SpendRecord :=
                { slice := out.slice.set_opt (UScalar.cast .Usize choices.val[i.val]) (some next) }
              have hout1 : out1.val = out.val.set choices.val[i.val].val next := by
                simp [out1, alloc.vec.Vec.val, Slice.set_opt, list_set_opt_some]
              obtain ⟨res, hres, hden⟩ :=
                charge_all_loop_eq rules contexts choices now hlen out1 j (by omega)
              unfold rule_eval.authorize.charge_all_loop at hres
              refine ⟨res, ?_, ?_⟩
              · have hb : rule_eval.authorize.charge_all_loop.body rules contexts choices now out i =
                    ok (cont (out1, j)) := by
                  simp [rule_eval.authorize.charge_all_loop.body, hlt, slice_get_eq, hget, lift, hr,
                    hcap, index_usize_eq _ _ hlt, ho, alloc.vec.Vec.deref_mut, slice_get_mut_eq, hrec', hs, hj, out1]
                rw [hb, bind_ok]
                exact hres
              · simp only [denoteSpend] at hsd
                rw [hden, hj', hout1, List.map_set]
                simp [RuleSet.charge, denoteRules, List.getElem?_map, hr, denoteRule_denote_cap, hcap,
                  hamt, List.getElem?_map, hrec, denoteCap_params, ← hsd]
  · refine ⟨.Ok out, ?_, ?_⟩
    · simp [rule_eval.authorize.charge_all_loop.body, hlt]
    · rw [chosenOf_drop_nil (by omega)]
      rfl
termination_by contexts.length - i.val
decreasing_by all_goals omega

/-! ## Authorization -/

theorem slice_len_bne_any {α β : Type} (a : Slice α) (b : Slice β) :
    (Slice.len a != Slice.len b) = !decide (a.length = b.length) := by
  by_cases h : a.length = b.length
  · have : Slice.len a = Slice.len b := by
      apply UScalar.eq_of_val_eq
      simp [h]
    simp [this, h]
  · have : Slice.len a ≠ Slice.len b := by
      intro he
      have := congrArg UScalar.val he
      simp at this
      exact h this
    simp [this, h]

/-- On every input, the extracted `check_auth` returns `ok` of the model's
authorization on the denotations, every refusal included: it never panics and
never diverges. -/
theorem check_auth_eq (rules : Slice rule_eval.rule.Rule)
    (records : Slice rule_eval.cap.SpendRecord) (contexts : Slice rule_eval.context.Context)
    (choices : Slice Std.U32) (authenticated : Slice rule_eval.signer.Signer) (now : Std.U32)
    (generation : Std.U64) :
    ∃ res, rule_eval.authorize.check_auth rules records contexts choices authenticated now
        generation = ok res ∧
      denoteAuthorized res =
        (denoteRules rules.val).checkAuth (records.val.map denoteRecord)
          (denoteAuthorization contexts choices authenticated now generation) := by
  have hmodel : (denoteRules rules.val).checkAuth (records.val.map denoteRecord)
      (denoteAuthorization contexts choices authenticated now generation) =
      if choices.length ≠ contexts.length then .error .choicesMismatch
      else if records.length ≠ rules.length then .error .recordsMismatch
      else
        (chosenOf contexts choices).forM
            ((denoteRules rules.val).denote.checkChoice (denoteSigners authenticated.val) now.val
              generation.val (contexts.val.head?.map denoteContext)) >>=
          fun _ => (denoteRules rules.val).denote.checkSigners (denoteSigners authenticated.val)
              (choices.val.map (·.val)) >>=
            fun _ => (chosenOf contexts choices).foldlM
              ((denoteRules rules.val).denote.charge now.val) (records.val.map denoteRecord) := by
    simp only [Chain.RuleSet.checkAuth, RuleSet.checkAuth, chosen_denoteAuthorization]
    simp [Chain.Authorization.denote, denoteAuthorization, Chain.RuleSet.denote, denoteRules,
      Slice.length, List.map_map, Function.comp_def]
  rw [hmodel]
  unfold rule_eval.authorize.check_auth
  simp only [slice_len_bne_any]
  by_cases hc : choices.length = contexts.length
  · by_cases hr : records.length = rules.length
    · obtain ⟨res₁, h₁, hd₁⟩ := check_choices_loop_eq rules contexts choices authenticated now
        generation hc 0#usize (by simp)
      simp only [hc, hr, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq,
        not_true_eq_false, rule_eval.authorize.check_choices, h₁, bind_ok]
      have h0 : (0#usize).val = 0 := by simp
      rw [h0, List.drop_zero] at hd₁
      cases res₁ with
      | Err e =>
        refine ⟨.Err e, rfl, ?_⟩
        simp only [denoteChecked] at hd₁
        rw [← hd₁]
        rfl
      | Ok u =>
        cases u
        simp only [denoteChecked] at hd₁
        rw [← hd₁, except_ok_bind, signers_chosen_eq, bind_ok]
        cases hall : (denoteSigners authenticated.val).all
            ((denoteRules rules.val).denote.signerChosen (choices.val.map (·.val))) with
        | false =>
          refine ⟨.Err .UnauthorizedSigner, by simp, ?_⟩
          simp [RuleSet.checkSigners, hall, denoteAuthorized, denoteRefusal]
        | true =>
          have hcs : (denoteRules rules.val).denote.checkSigners (denoteSigners authenticated.val)
              (choices.val.map (·.val)) = .ok () := by
            simp [RuleSet.checkSigners, hall]
          rw [hcs, except_ok_bind]
          obtain ⟨out, hout, hv⟩ := records_copy_eq records
          obtain ⟨res, h, hd⟩ :=
            charge_all_loop_eq rules contexts choices now hc out 0#usize (by simp)
          refine ⟨res, ?_, ?_⟩
          · simp only [↓reduceIte, rule_eval.authorize.charge_all, hout, bind_ok]
            exact h
          · rw [hd, h0, List.drop_zero, hv]
    · simp [hc, hr, denoteAuthorized, denoteRefusal]
  · simp [hc, denoteAuthorized, denoteRefusal]

/-! ## Former names

The names these theorems had before the evaluator's entry point was renamed
`check_auth`, kept so that citations of them still resolve. -/

@[deprecated check_auth_eq (since := "2026-11-08")]
theorem authorize_eq : type_of% @check_auth_eq := @check_auth_eq

end RuleCore.Equiv
