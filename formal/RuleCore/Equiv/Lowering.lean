import RuleCore.Equiv.DenoteDocument
import RuleCore.Equiv.Attenuation
import RuleCore.Equiv.Cap

/-!
# Equivalence of the lowering

The translated lowering (`rule_eval.lowering` and `rule_eval.scoped` in
`RuleCore/Extracted/RuleEval.lean`) computes the model's lowering
(`RuleCore.Vocab.Lowering`) on the denotations of its inputs:

* `lower_eq`: on every document and account, the translated `lower` returns
  `ok` of rules denoting `Doc.lower`, under the stated rule `LowerRoom`;
* `lower_scoped_eq`: the translated `lower_scoped` returns `ok` of the result
  denoting `Doc.lowerScoped`, refusals included, under `LowerRoom`;
* `excluded_eq`: the translated `excluded` returns `ok` of byte strings
  denoting `Doc.excluded`.

`ok` rules out both a panic and divergence, so these also prove that the
lowering terminates and never panics. The steps are proven one by one: the
names `transfer` and `apply_doc` (`transfer_eq`, `apply_doc_eq`), the `u32` XDR
(`u32_xdr_eq`), signer resolution (`resolve_eq`, `named_eq`), the threshold
(`threshold_of_eq`), the contract (`contract_of_eq`), the functions
(`lower_functions_eq`), the conditions (`strings_within_eq`, `lower_pred_eq`,
`lower_args_eq`, `lower_conds_eq`), the cap and the last ledger (`lower_cap_eq`,
`last_ledger_eq`), one rule (`lower_rule_eq`), the rules (`lower_rules_eq`),
the recovery rule (`recovery_rule_eq`) and the excluded scopes
(`any_excluded_eq`).

`LowerRoom d` is the one stated rule: a document with a recovery
configuration has fewer than `Usize.max` rules, and each capped rule fewer than
`Usize.max` argument predicates, so the vector that holds them and one more
element fits Aeneas's model of `Vec`. `lower_full` proves the rule exact: on a
document with a recovery configuration and `Usize.max` rules, the translated
`lower` fails.
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std Result ControlFlow

/-! ## Names and encodings -/

theorem array_slice_val {α : Type} (n : Usize) (l : List α) (h : l.length = n.val) :
    (Array.to_slice (Array.make n l h)).val = l := by
  simp [Array.to_slice, Array.make_val]

theorem transfer_eq :
    ∃ v, rule_eval.lowering.transfer = ok v ∧ denoteBytes v = Document.transfer := by
  refine ⟨⟨Array.to_slice (Array.make 8#usize
    [116#u8, 114#u8, 97#u8, 110#u8, 115#u8, 102#u8, 101#u8, 114#u8])⟩, ?_, ?_⟩
  · simp only [rule_eval.lowering.transfer, lift, bind_ok, bytes_copy_eq]
  · simp only [denoteBytes, bytesOf, alloc.vec.Vec.val, array_slice_val]
    rfl

theorem apply_doc_eq :
    ∃ v, rule_eval.lowering.apply_doc = ok v ∧ denoteBytes v = Document.applyDoc := by
  refine ⟨⟨Array.to_slice (Array.make 9#usize
    [97#u8, 112#u8, 112#u8, 108#u8, 121#u8, 95#u8, 100#u8, 111#u8, 99#u8])⟩, ?_, ?_⟩
  · simp only [rule_eval.lowering.apply_doc, lift, bind_ok, bytes_copy_eq]
  · simp only [denoteBytes, bytesOf, alloc.vec.Vec.val, array_slice_val]
    rfl

/-- A byte of a `u32`, as a cast of its value modulo 256. -/
theorem byte_cast (z : Std.U32) : byte (UScalar.cast .U8 z) = UInt8.ofNat z.val := by
  apply UInt8.toNat_inj.mp
  simp only [byte, UInt8.toNat_ofBitVec]
  have := UScalar.cast_val_eq .U8 z
  simp only [UScalar.val] at this
  rw [this]
  rfl

theorem u32_div_eq (x y : Std.U32) (hy : y.val ≠ 0) :
    ∃ z, x / y = ok z ∧ z.val = x.val / y.val := by
  obtain ⟨z, hz, hv, -⟩ := UScalar.div_bv_spec x hy
  exact ⟨z, hz, hv⟩

theorem u32_rem_eq (x y : Std.U32) (hy : y.val ≠ 0) :
    ∃ z, x % y = ok z ∧ z.val = x.val % y.val := by
  have := UScalar.rem_bv_spec x hy
  revert this
  cases x % y with
  | ret r => intro hr; refine ⟨r, rfl, ?_⟩; simp at hr; exact hr.1
  | vis e k => intro hr; simp at hr
  | div => intro hr; simp at hr

/-- The translated `u32_xdr` returns the `ScVal` XDR of the value. -/
theorem u32_xdr_eq (v : Std.U32) :
    ∃ w, rule_eval.lowering.u32_xdr v = ok w ∧ denoteBytes w = Document.u32Xdr (denoteU32 v) := by
  have h1 : (16777216#u32 : Std.U32).val = 16777216 := rfl
  have h2 : (65536#u32 : Std.U32).val = 65536 := rfl
  have h3 : (256#u32 : Std.U32).val = 256 := rfl
  obtain ⟨a, ha, hav⟩ := u32_div_eq v 16777216#u32 (by rw [h1]; omega)
  obtain ⟨b, hb, hbv⟩ := u32_div_eq v 65536#u32 (by rw [h2]; omega)
  obtain ⟨b', hb', hb'v⟩ := u32_rem_eq b 256#u32 (by rw [h3]; omega)
  obtain ⟨c, hc, hcv⟩ := u32_div_eq v 256#u32 (by rw [h3]; omega)
  obtain ⟨c', hc', hc'v⟩ := u32_rem_eq c 256#u32 (by rw [h3]; omega)
  obtain ⟨e, he, hev⟩ := u32_rem_eq v 256#u32 (by rw [h3]; omega)
  rw [h1] at hav
  rw [h2] at hbv
  rw [h3] at hb'v hcv hc'v hev
  refine ⟨⟨Array.to_slice (Array.make 8#usize [0#u8, 0#u8, 0#u8, 3#u8, UScalar.cast .U8 a,
    UScalar.cast .U8 b', UScalar.cast .U8 c', UScalar.cast .U8 e])⟩, ?_, ?_⟩
  · simp only [rule_eval.lowering.u32_xdr, ha, hb, hb', hc, hc', he, bind_ok, lift,
      bytes_copy_eq]
  · simp only [denoteBytes, bytesOf, alloc.vec.Vec.val, array_slice_val, List.map_cons,
      List.map_nil, byte_cast, Document.u32Xdr, denoteU32_toNat, hav, hb'v, hbv, hc'v, hcv, hev]
    rfl


/-! ## Loops that find, and what a building loop pushes -/

/-- A loop that exits with `some (f a)` at the first element `a` satisfying
`p`, and with `none` at the end. -/
theorem loop_find {α β : Type} (l : List α) (p : α → Bool) (f : α → β)
    (body : Usize → Result (ControlFlow Usize (Option β)))
    (hlt : ∀ (i : Usize) (h : i.val < l.length), ∃ j : Usize, j.val = i.val + 1 ∧
      body i = ok (if p l[i.val] then done (some (f l[i.val])) else cont j))
    (hge : ∀ i : Usize, l.length ≤ i.val → body i = ok (done none))
    (i : Usize) :
    loop body i = ok (((l.drop i.val).find? p).map f) := by
  rw [loop]
  by_cases hi : i.val < l.length
  · obtain ⟨j, hj, hb⟩ := hlt i hi
    rw [hb, bind_ok, List.drop_eq_getElem_cons hi, List.find?_cons]
    cases hp : p l[i.val]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [loop_find l p f body hlt hge j, hj]
    · simp
  · rw [hge i (Nat.le_of_not_lt hi), bind_ok, List.drop_of_length_le (Nat.le_of_not_lt hi)]
    rfl
termination_by l.length - i.val
decreasing_by omega

theorem pushedFrom_filterMap {α γ : Type} (f : α → Option γ) :
    ∀ (l : List α) (k : Nat), pushedFrom (fun _ a => f a) l k = l.filterMap f
  | [], _ => rfl
  | a :: l, k => by
    rw [pushedFrom, pushedFrom_filterMap f l (k + 1), List.filterMap_cons]
    cases f a <;> rfl

theorem bytes_list_copy_eq (s : Slice (alloc.vec.Vec Std.U8)) :
    rule_eval.bytes.bytes_list_copy s = ok ⟨s⟩ := by
  obtain ⟨out, h, hv⟩ := bytes_list_copy_loop_eq s (alloc.vec.Vec.new _) 0#usize (by simp)
  rw [rule_eval.bytes.bytes_list_copy, h]
  congr 1
  exact vec_eq_of_val (show out.val = s.val by simpa [pushedFrom_map] using hv)

/-! ## Signers -/

/-- Whether a declared signer is declared under `id`. -/
def declaredAs (id : List Std.U8) (sd : rule_eval.document.SignerDecl) : Bool :=
  decide (sd.id.val = id)

theorem resolve_eq (id : Slice Std.U8) (signers : Slice rule_eval.document.SignerDecl) :
    rule_eval.lowering.resolve id signers =
      ok ((signers.val.find? (declaredAs id.val)).map (·.signer)) := by
  unfold rule_eval.lowering.resolve rule_eval.lowering.resolve_loop
  rw [loop_find signers.val (declaredAs id.val) (·.signer)]
  · simp
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq signers i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.lowering.resolve_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, bytes_eq_eq, vec_deref_val, hj, signer_copy_eq, declaredAs]
    by_cases he : signers.val[i.val].id.val = id.val <;> simp [he]
  · intro i hi
    have : ¬ i.val < signers.length := by simp only [Slice.length]; omega
    simp [rule_eval.lowering.resolve_loop.body, this]

theorem resolve_denote {d : Document.Doc} {signers : List rule_eval.document.SignerDecl}
    (hs : d.signers = signers.map denoteDecl) (id : List Std.U8) :
    ((signers.find? (declaredAs id)).map (·.signer)).map denoteSigner = d.resolve (bytesOf id) := by
  have hp : ((fun s : Document.SignerDecl => decide (s.id = bytesOf id)) ∘ denoteDecl) =
      declaredAs id := by
    funext sd
    simp only [Function.comp_apply, denoteDecl, denoteBytes, declaredAs, bytesOf_inj]
  rw [Document.Doc.resolve, hs, List.find?_map, hp, Option.map_map, Option.map_map]
  rfl

theorem named_loop_eq (ids : Slice (alloc.vec.Vec Std.U8))
    (signers : Slice rule_eval.document.SignerDecl) (out : alloc.vec.Vec rule_eval.signer.Signer)
    (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.lowering.named_loop ids signers out i = ok out' ∧
      out'.val.map denoteSigner = out.val.map denoteSigner ++
        pushedFrom (fun _ v => ((signers.val.find? (declaredAs v.val)).map (·.signer)).map
          denoteSigner) (ids.val.drop i.val) i.val := by
  unfold rule_eval.lowering.named_loop
  refine loop_build ids.val _ denoteSigner _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq ids i hi
    cases hr : (signers.val.find? (declaredAs ids.val[i.val].val)).map (·.signer) with
    | none =>
      refine ⟨out, j, hj', by simp, ?_⟩
      simp only [rule_eval.lowering.named_loop.body, slice_len_lt, hi, ↓reduceIte,
        index_usize_eq _ _ hi, resolve_eq, vec_deref_val, bind_ok, hr, hj]
    | some s₀ =>
      obtain ⟨out', hp, hv⟩ := push_eq out s₀ (room_of_lt ids out i hi hout)
      refine ⟨out', j, hj', by simp [hv], ?_⟩
      simp only [rule_eval.lowering.named_loop.body, slice_len_lt, hi, ↓reduceIte,
        index_usize_eq _ _ hi, resolve_eq, vec_deref_val, bind_ok, hr, hp, hj]
  · intro out i hi
    have : ¬ i.val < ids.length := by simp only [Slice.length]; omega
    simp [rule_eval.lowering.named_loop.body, this]

/-- The translated `named` returns the signers declared under the ids, as the
model's `Doc.named` does. -/
theorem named_eq {d : Document.Doc} {signers : Slice rule_eval.document.SignerDecl}
    (hs : d.signers = signers.val.map denoteDecl) (ids : Slice (alloc.vec.Vec Std.U8)) :
    ∃ out, rule_eval.lowering.named ids signers = ok out ∧
      out.val.map denoteSigner = (ids.val.map denoteBytes).filterMap d.resolve := by
  obtain ⟨out, h, hv⟩ := named_loop_eq ids signers (alloc.vec.Vec.new _) 0#usize (by simp)
  refine ⟨out, h, ?_⟩
  rw [hv, List.filterMap_map]
  simp only [vec_new_val, List.map_nil, List.nil_append]
  rw [pushedFrom_filterMap]
  congr 1
  funext v
  exact resolve_denote hs v.val

theorem principal_ids_eq (p : rule_eval.document.Principals) :
    ∃ s, rule_eval.lowering.principal_ids p = ok s ∧ s.val.map denoteBytes = (denotePrincipals p).ids := by
  cases p with
  | All ids =>
    exact ⟨alloc.vec.Vec.deref ids, by simp [rule_eval.lowering.principal_ids],
      by simp [denotePrincipals, Document.Principals.ids]⟩
  | Threshold ids m =>
    exact ⟨alloc.vec.Vec.deref ids, by simp [rule_eval.lowering.principal_ids],
      by simp [denotePrincipals, Document.Principals.ids]⟩

theorem denoteU32_eq_ofNat (x : Std.U32) : denoteU32 x = UInt32.ofNat x.val := by
  apply UInt32.toNat_inj.mp
  simp only [denoteU32_toNat, UInt32.toNat_ofNat']
  have : x.val ≤ 4294967295 := by scalar_tac
  omega

theorem threshold_of_eq (p : rule_eval.document.Principals) (count : Usize) :
    ∃ t, rule_eval.lowering.threshold_of p count = ok t ∧
      denoteU32 t = match denotePrincipals p with
        | .all _ => UInt32.ofNat (min count.val 4294967295)
        | .threshold _ m => m := by
  cases p with
  | Threshold ids m => exact ⟨m, rfl, rfl⟩
  | All ids =>
    have hmax : (UScalar.cast .Usize core.num.U32.MAX).val = 4294967295 := by
      rw [cast_usize_val]; rfl
    by_cases hc : count.val > 4294967295
    · refine ⟨core.num.U32.MAX, ?_, ?_⟩
      · simp only [rule_eval.lowering.threshold_of, lift, bind_ok]
        rw [ite_eq_left (by show (UScalar.cast .Usize core.num.U32.MAX).val < count.val; omega)]
      · simp only [denotePrincipals]
        rw [Nat.min_eq_right (by omega), denoteU32_eq_ofNat]
        rfl
    · refine ⟨UScalar.cast .U32 count, ?_, ?_⟩
      · simp only [rule_eval.lowering.threshold_of, lift, bind_ok]
        rw [ite_eq_right (by show ¬ (UScalar.cast .Usize core.num.U32.MAX).val < count.val; omega)]
      · simp only [denotePrincipals]
        rw [Nat.min_eq_left (by omega), denoteU32_eq_ofNat, UScalar.cast_val_eq]
        congr 1
        exact Nat.mod_eq_of_lt (by simp; omega)


/-! ## Contract and functions -/

theorem contract_of_eq (sc : rule_eval.document.Scope) (account : Slice Std.U8) :
    ∃ c, rule_eval.lowering.contract_of sc account = ok c ∧
      denoteBytes c = (denoteScope sc).contractOn (bytesOf account.val) := by
  cases sc with
  | Contract a => exact ⟨a, by simp [rule_eval.lowering.contract_of, bytes_copy_deref], rfl⟩
  | SelfAdmin => exact ⟨⟨account⟩, by simp [rule_eval.lowering.contract_of, bytes_copy_eq], rfl⟩

theorem covers_transfer_eq (fs : Option (alloc.vec.Vec (alloc.vec.Vec Std.U8))) :
    rule_eval.lowering.covers_transfer fs =
      ok (Document.coversTransfer (fs.map fun l => l.val.map denoteBytes)) := by
  cases fs with
  | none => rfl
  | some l =>
    obtain ⟨v, hv, hd⟩ := transfer_eq
    simp only [rule_eval.lowering.covers_transfer, hv, bind_ok, bytes_in_eq, vec_deref_val,
      Option.map_some, Document.coversTransfer]
    rw [any_bytes_eq_mem]
    simp only [denoteBytes] at hd
    rw [hd]

theorem lower_functions_eq (r : rule_eval.document.DocRule) :
    ∃ f, rule_eval.lowering.lower_functions r.functions r.cap = ok f ∧
      denoteFunctions f = (denoteDocRule r).lowerFunctions := by
  obtain ⟨v, hv, hd⟩ := transfer_eq
  rcases r with ⟨sc, p, fs, args, na, cap⟩
  cases cap with
  | none =>
    cases fs with
    | none =>
      exact ⟨.AnyExcept (alloc.vec.Vec.new _),
        by simp [rule_eval.lowering.lower_functions, rule_eval.lowering.listed_functions],
        by simp [denoteFunctions, denoteDocRule, Document.Rule.lowerFunctions]⟩
    | some l =>
      exact ⟨.Only l, by simp [rule_eval.lowering.lower_functions,
        rule_eval.lowering.listed_functions, bytes_list_copy_deref],
        by simp [denoteFunctions, denoteDocRule, Document.Rule.lowerFunctions]⟩
  | some k =>
    have hc := covers_transfer_eq fs
    cases hb : Document.coversTransfer (fs.map fun l => l.val.map denoteBytes) with
    | false =>
      refine ⟨.Only (alloc.vec.Vec.new _), ?_, ?_⟩
      · simp [rule_eval.lowering.lower_functions, rule_eval.lowering.capped_functions, hc, hb]
      · simp [denoteFunctions, denoteDocRule, Document.Rule.lowerFunctions, hb]
    | true =>
      obtain ⟨out, hp, hpv⟩ := push_eq (alloc.vec.Vec.new (alloc.vec.Vec Std.U8)) v
        (by simp; scalar_tac)
      refine ⟨.Only out, ?_, ?_⟩
      · simp [rule_eval.lowering.lower_functions, rule_eval.lowering.capped_functions, hc, hb,
          hv, hp]
      · simp only [denoteFunctions, denoteDocRule, Document.Rule.lowerFunctions, hb, ↓reduceIte,
          Option.map_some, hpv, vec_new_val, List.nil_append, List.map_cons, List.map_nil, hd]

/-! ## Conditions -/

theorem max_string_len_val : rule_eval.lowering.MAX_STRING_LEN.val = Document.maxStringLen := by
  simp [rule_eval.lowering.MAX_STRING_LEN, Document.maxStringLen]

theorem strings_within_loop_eq (values : Slice (alloc.vec.Vec Std.U8))
    (out : alloc.vec.Vec rule_eval.val.Val) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.lowering.strings_within_loop values out i = ok out' ∧
      out'.val.map denoteVal = out.val.map denoteVal ++
        pushedFrom (fun _ v => if decide (v.val.length ≤ Document.maxStringLen) then
            some (Chain.Val.string (denoteBytes v)) else none) (values.val.drop i.val) i.val := by
  unfold rule_eval.lowering.strings_within_loop
  refine loop_build values.val _ denoteVal _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq values i hi
    by_cases hl : values.val[i.val].val.length ≤ Document.maxStringLen
    · obtain ⟨out', hp, hv⟩ := push_eq out (.String values.val[i.val])
        (room_of_lt values out i hi hout)
      refine ⟨out', j, hj', by simp [hv, hl, denoteVal], ?_⟩
      have hle : alloc.vec.Vec.len values.val[i.val] ≤ rule_eval.lowering.MAX_STRING_LEN := by
        show (alloc.vec.Vec.len values.val[i.val]).val ≤ rule_eval.lowering.MAX_STRING_LEN.val
        rw [max_string_len_val]
        simpa [alloc.vec.Vec.len] using hl
      simp only [rule_eval.lowering.strings_within_loop.body, slice_len_lt, hi, ↓reduceIte,
        index_usize_eq _ _ hi, hle, bytes_copy_deref, bind_ok, hp, hj]
    · refine ⟨out, j, hj', by simp [hl], ?_⟩
      have hle : ¬ alloc.vec.Vec.len values.val[i.val] ≤ rule_eval.lowering.MAX_STRING_LEN := by
        show ¬ (alloc.vec.Vec.len values.val[i.val]).val ≤ rule_eval.lowering.MAX_STRING_LEN.val
        rw [max_string_len_val]
        simpa [alloc.vec.Vec.len] using hl
      simp only [rule_eval.lowering.strings_within_loop.body, slice_len_lt, hi, ↓reduceIte,
        index_usize_eq _ _ hi, hle, bind_ok, hj]
  · intro out i hi
    have : ¬ i.val < values.length := by simp only [Slice.length]; omega
    simp [rule_eval.lowering.strings_within_loop.body, this]

theorem filterMap_strings (l : List (alloc.vec.Vec Std.U8)) :
    l.filterMap (fun v => if decide (v.val.length ≤ Document.maxStringLen) then
        some (Chain.Val.string (denoteBytes v)) else none) =
      ((l.map denoteBytes).filter fun v => decide (v.length ≤ Document.maxStringLen)).map
        .string := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    have hlen : (denoteBytes v).length = v.val.length := by simp [denoteBytes, bytesOf]
    simp only [decide_eq_true_eq] at ih
    by_cases hv : v.val.length ≤ Document.maxStringLen
    · simp [hv, hlen, ih]
    · simp [hv, hlen, ih]

theorem strings_within_eq (values : Slice (alloc.vec.Vec Std.U8)) :
    ∃ out, rule_eval.lowering.strings_within values = ok out ∧
      out.val.map denoteVal =
        ((values.val.map denoteBytes).filter fun v => decide (v.length ≤ Document.maxStringLen)).map
          .string := by
  obtain ⟨out, h, hv⟩ := strings_within_loop_eq values (alloc.vec.Vec.new _) 0#usize (by simp)
  refine ⟨out, h, ?_⟩
  rw [hv]
  simp only [vec_new_val, List.map_nil, List.nil_append]
  rw [pushedFrom_filterMap, ← filterMap_strings]
  simp

theorem lower_pred_eq (index : Std.U32) (pred : rule_eval.document.Pred) (account : Slice Std.U8) :
    ∃ c, rule_eval.lowering.lower_pred index pred account = ok c ∧
      denoteCond c = (denotePred pred).lower (bytesOf account.val) (denoteU32 index) := by
  cases pred with
  | IsSelf =>
    exact ⟨.ArgEq index (.Address ⟨account⟩),
      by simp [rule_eval.lowering.lower_pred, bytes_copy_eq], rfl⟩
  | AddressEq a =>
    exact ⟨.ArgEq index (.Address a),
      by simp [rule_eval.lowering.lower_pred, bytes_copy_deref], rfl⟩
  | StringPrefix pre =>
    exact ⟨.ArgStrPrefix index pre,
      by simp [rule_eval.lowering.lower_pred, bytes_copy_deref], rfl⟩
  | U32Eq v =>
    obtain ⟨w, hw, hd⟩ := u32_xdr_eq v
    exact ⟨.ArgEq index (.Other w), by simp [rule_eval.lowering.lower_pred, hw],
      by simp [denoteCond, denoteVal, denotePred, Document.Pred.lower, hd]⟩
  | StringIn values =>
    obtain ⟨out, ho, hv⟩ := strings_within_eq (alloc.vec.Vec.deref values)
    refine ⟨.ArgIn index out, by simp [rule_eval.lowering.lower_pred, ho], ?_⟩
    simp only [vec_deref_val] at hv
    simp [denoteCond, denotePred, Document.Pred.lower, hv]

theorem lower_args_loop_eq (args : Slice rule_eval.document.ArgConstraint) (account : Slice Std.U8)
    (out : alloc.vec.Vec rule_eval.rule.Cond) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.lowering.lower_args_loop args account out i = ok out' ∧
      out'.val.map denoteCond = out.val.map denoteCond ++
        pushedFrom (fun _ c => some ((denoteArg c).lower (bytesOf account.val)))
          (args.val.drop i.val) i.val := by
  unfold rule_eval.lowering.lower_args_loop
  refine loop_build args.val _ denoteCond _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq args i hi
    obtain ⟨c, hc, hcd⟩ := lower_pred_eq args.val[i.val].index args.val[i.val].pred account
    obtain ⟨out', hp, hv⟩ := push_eq out c (room_of_lt args out i hi hout)
    refine ⟨out', j, hj', ?_, ?_⟩
    · simp [hv, hcd, Document.ArgConstraint.lower, denoteArg]
    · simp only [rule_eval.lowering.lower_args_loop.body, slice_len_lt, hi, ↓reduceIte,
        index_usize_eq _ _ hi, hc, bind_ok, hp, hj]
  · intro out i hi
    have : ¬ i.val < args.length := by simp only [Slice.length]; omega
    simp [rule_eval.lowering.lower_args_loop.body, this]

theorem lower_args_eq (args : Slice rule_eval.document.ArgConstraint) (account : Slice Std.U8) :
    ∃ out, rule_eval.lowering.lower_args args account = ok out ∧
      out.val.map denoteCond = (args.val.map denoteArg).map (Document.ArgConstraint.lower
        (bytesOf account.val)) := by
  obtain ⟨out, h, hv⟩ := lower_args_loop_eq args account (alloc.vec.Vec.new _) 0#usize (by simp)
  refine ⟨out, h, ?_⟩
  rw [hv]
  simp [pushedFrom_map, List.map_map, Function.comp_def]

theorem i128_max_bv : core.num.I128.MAX.bv = Document.i128Max := by
  simp [core.num.I128.MAX, Document.i128Max, IScalar.ofInt]
  rfl

theorem amount_arg_val : denoteU32 rule_eval.lowering.AMOUNT_ARG = Document.amountArg := by
  simp [rule_eval.lowering.AMOUNT_ARG, Document.amountArg]
  rfl

/-- What the stated rule needs of one document rule: a capped rule has fewer
than `Usize.max` argument predicates. -/
def ArgsRoom (r : rule_eval.document.DocRule) : Prop :=
  r.cap.isSome → ∀ cs, r.args = some cs → cs.val.length < Usize.max

theorem with_amount_eq (base : alloc.vec.Vec rule_eval.rule.Cond)
    (h : base.val.length < Usize.max) :
    ∃ out, rule_eval.lowering.with_amount base = ok out ∧
      out.val.map denoteCond = base.val.map denoteCond ++ [Document.amountCond] := by
  obtain ⟨out, hp, hv⟩ := push_eq base
    (.ArgI128AtMost rule_eval.lowering.AMOUNT_ARG core.num.I128.MAX) h
  refine ⟨out, hp, ?_⟩
  simp only [hv, List.map_append, List.map_cons, List.map_nil, denoteCond, i128_max_bv,
    amount_arg_val, Document.amountCond]

theorem lower_conds_eq (r : rule_eval.document.DocRule) (account : Slice Std.U8)
    (hroom : ArgsRoom r) :
    ∃ out, rule_eval.lowering.lower_conds r.args r.cap account = ok out ∧
      out.val.map denoteCond = (denoteDocRule r).lowerConds (bytesOf account.val) := by
  rcases r with ⟨sc, p, fs, args, na, cap⟩
  cases args with
  | none =>
    cases cap with
    | none =>
      exact ⟨alloc.vec.Vec.new _, by simp [rule_eval.lowering.lower_conds],
        by simp [denoteDocRule, Document.Rule.lowerConds]⟩
    | some k =>
      obtain ⟨out, hw, hv⟩ := with_amount_eq (alloc.vec.Vec.new _) (by simp; scalar_tac)
      exact ⟨out, by simp [rule_eval.lowering.lower_conds, hw],
        by simp [denoteDocRule, Document.Rule.lowerConds, hv]⟩
  | some cs =>
    obtain ⟨base, hb, hbv⟩ := lower_args_eq (alloc.vec.Vec.deref cs) account
    simp only [vec_deref_val] at hbv
    cases cap with
    | none =>
      exact ⟨base, by simp [rule_eval.lowering.lower_conds, hb],
        by simp [denoteDocRule, Document.Rule.lowerConds, hbv]⟩
    | some k =>
      have hl : base.val.length < Usize.max := by
        have := congrArg List.length hbv
        simp only [List.length_map] at this
        rw [this]
        exact hroom rfl cs rfl
      obtain ⟨out, hw, hv⟩ := with_amount_eq base hl
      exact ⟨out, by simp [rule_eval.lowering.lower_conds, hb, hw],
        by simp [denoteDocRule, Document.Rule.lowerConds, hv, hbv]⟩


/-! ## One rule -/

theorem lower_cap_eq (cap : Option rule_eval.document.DocCap) :
    ∃ c, rule_eval.lowering.lower_cap cap = ok c ∧
      c.map denoteCap = (cap.map denoteDocCap).map Document.Cap.lower := by
  cases cap with
  | none => exact ⟨none, rfl, rfl⟩
  | some k =>
    refine ⟨some ⟨k.limit, k.period_ledgers, rule_eval.lowering.AMOUNT_ARG⟩, rfl, ?_⟩
    simp only [Option.map_some, denoteCap, denoteDocCap, Document.Cap.lower, amount_arg_val]

theorem last_ledger_eq (na : Option Std.U32) :
    ∃ v, rule_eval.lowering.last_ledger na = ok v ∧
      v.map denoteU32 = (na.map denoteU32).map Document.lastLedger := by
  cases na with
  | none => exact ⟨none, rfl, rfl⟩
  | some x =>
    refine ⟨some (core.num.U32.saturating_sub x 1#u32), by simp [rule_eval.lowering.last_ledger,
      lift], ?_⟩
    simp only [Option.map_some, Option.some.injEq, Document.lastLedger, denoteU32_eq_ofNat,
      saturating_sub_val]
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by scalar_tac)]
    rfl

/-- The translated `lower_rule` returns the rule the model lowers the document
rule to, for a document whose declared signers are those `signers` denotes. -/
theorem lower_rule_eq {d : Document.Doc} {signers : Slice rule_eval.document.SignerDecl}
    (hs : d.signers = signers.val.map denoteDecl) (r : rule_eval.document.DocRule)
    (account : Slice Std.U8) (gen : Option Std.U64) (hroom : ArgsRoom r) :
    ∃ r', rule_eval.lowering.lower_rule r signers account gen = ok r' ∧
      denoteRule r' = d.lowerRule (bytesOf account.val) (gen.map denoteU64) (denoteDocRule r) := by
  obtain ⟨ids, hids, hidsv⟩ := principal_ids_eq r.principals
  obtain ⟨ss, hss, hssv⟩ := named_eq hs ids
  obtain ⟨t, ht, htv⟩ := threshold_of_eq r.principals (alloc.vec.Vec.len ss)
  obtain ⟨c, hc, hcv⟩ := contract_of_eq r.scope account
  obtain ⟨f, hf, hfv⟩ := lower_functions_eq r
  obtain ⟨cs, hcs, hcsv⟩ := lower_conds_eq r account hroom
  obtain ⟨k, hk, hkv⟩ := lower_cap_eq r.cap
  obtain ⟨v, hv, hvv⟩ := last_ledger_eq r.not_after_ledger
  refine ⟨{ contract := c, functions := f, conds := cs, signers := ss, threshold := t,
            cap := k, valid_until := v, generation := gen,
            auth_root := match r.scope with | .Contract _ => r.auth_root | .SelfAdmin => none }, ?_, ?_⟩
  · simp only [rule_eval.lowering.lower_rule, hids, hss, ht, hc, hf, hcs, hk, hv, bind_ok]
    cases r.scope <;> simp [auth_root_copy_eq]
  · have hnamed : ss.val.map denoteSigner = d.named (denoteDocRule r).principals := by
      rw [hssv, hidsv]
      rfl
    have hlen : (alloc.vec.Vec.len ss).val = (d.named (denoteDocRule r).principals).length := by
      rw [← hnamed, List.length_map]
      simp [alloc.vec.Vec.len]
    simp only [denoteRule, Document.Doc.lowerRule, denoteSigners, hcv, hfv, hcsv, hnamed, hkv,
      hvv]
    congr 1
    · rw [htv, hlen]
      simp only [denoteDocRule, Document.Doc.threshold]
      cases r.principals <;> rfl
    · simp only [Document.Rule.effectiveRoot, denoteDocRule, denoteScope]
      cases r.scope <;> rfl

theorem lower_rules_loop_eq {d : Document.Doc} {signers : Slice rule_eval.document.SignerDecl}
    (hs : d.signers = signers.val.map denoteDecl) (rules : Slice rule_eval.document.DocRule)
    (account : Slice Std.U8) (gen : Option Std.U64) (hroom : ∀ r ∈ rules.val, ArgsRoom r)
    (out : alloc.vec.Vec rule_eval.rule.Rule) (i : Usize) (h : out.val.length ≤ i.val) :
    ∃ out', rule_eval.lowering.lower_rules_loop rules signers account gen out i = ok out' ∧
      out'.val.map denoteRule = out.val.map denoteRule ++
        pushedFrom (fun _ r => some (d.lowerRule (bytesOf account.val) (gen.map denoteU64)
          (denoteDocRule r))) (rules.val.drop i.val) i.val := by
  unfold rule_eval.lowering.lower_rules_loop
  refine loop_build rules.val _ denoteRule _ ?_ ?_ out i h
  · intro out i hi hout
    obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
    obtain ⟨r', hr, hrv⟩ := lower_rule_eq hs rules.val[i.val] account gen
      (hroom _ (List.getElem_mem hi))
    obtain ⟨out', hp, hv⟩ := push_eq out r' (room_of_lt rules out i hi hout)
    refine ⟨out', j, hj', by simp [hv, hrv], ?_⟩
    simp only [rule_eval.lowering.lower_rules_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, hr, bind_ok, hp, hj]
  · intro out i hi
    have : ¬ i.val < rules.length := by simp only [Slice.length]; omega
    simp [rule_eval.lowering.lower_rules_loop.body, this]

theorem lower_rules_eq (doc : rule_eval.document.Doc) (account : Slice Std.U8)
    (gen : Option Std.U64) (hroom : ∀ r ∈ doc.rules.val, ArgsRoom r) :
    ∃ out, rule_eval.lowering.lower_rules (alloc.vec.Vec.deref doc.rules)
        (alloc.vec.Vec.deref doc.signers) account gen = ok out ∧
      denoteRules out.val = (denoteDoc doc).lowerRules (bytesOf account.val) (gen.map denoteU64) := by
  obtain ⟨out, h, hv⟩ := lower_rules_loop_eq (d := denoteDoc doc)
    (signers := alloc.vec.Vec.deref doc.signers) (by simp [denoteDoc])
    (alloc.vec.Vec.deref doc.rules) account gen (by simpa using hroom) (alloc.vec.Vec.new _)
    0#usize (by simp)
  refine ⟨out, h, ?_⟩
  rw [denoteRules, hv]
  simp [pushedFrom_map, Document.Doc.lowerRules, denoteDoc, List.map_map, Function.comp_def]

theorem recovery_rule_eq (account : Slice Std.U8) :
    ∃ r, rule_eval.lowering.recovery_rule account = ok r ∧
      denoteRule r = Document.recoveryRule (bytesOf account.val) := by
  obtain ⟨v, hv, hvd⟩ := apply_doc_eq
  refine ⟨{ contract := ⟨account⟩,
            functions := .Only ⟨Array.to_slice (Array.make 1#usize [v])⟩,
            conds := alloc.vec.Vec.new _, signers := alloc.vec.Vec.new _, threshold := 0#u32,
            cap := none, valid_until := none, generation := none, auth_root := none }, ?_, ?_⟩
  · simp only [rule_eval.lowering.recovery_rule, bytes_copy_eq, hv, lift, bind_ok,
      bytes_list_copy_eq]
  · simp only [denoteRule, Document.recoveryRule, denoteFunctions, alloc.vec.Vec.val,
      array_slice_val, List.map_cons, List.map_nil, hvd, denoteSigners]
    rfl

/-! ## The admin document -/

/-- The stated rule `LowerRoom`: a document with a recovery configuration has
fewer than `Usize.max` rules, and each capped rule fewer than `Usize.max`
argument predicates. -/
structure LowerRoom (doc : rule_eval.document.Doc) : Prop where
  rules : doc.recovery.isSome → doc.rules.val.length < Usize.max
  args : ∀ r ∈ doc.rules.val, ArgsRoom r

/-- The translated `lower` returns the rules the model lowers the admin
document to: it terminates, never panics, and computes `Doc.lower`. -/
theorem lower_eq (doc : rule_eval.document.Doc) (account : Slice Std.U8) (hroom : LowerRoom doc) :
    ∃ out, rule_eval.lowering.lower doc account = ok out ∧
      denoteRules out.val = (denoteDoc doc).lower (bytesOf account.val) := by
  obtain ⟨base, hb, hbv⟩ := lower_rules_eq doc account none hroom.args
  cases hrc : doc.recovery with
  | none =>
    refine ⟨base, ?_, ?_⟩
    · simp only [rule_eval.lowering.lower, hb, bind_ok, hrc]
    · rw [hbv]
      simp [Document.Doc.lower, Document.Doc.recoveryRules, denoteDoc, hrc]
  | some rc =>
    obtain ⟨r, hr, hrv⟩ := recovery_rule_eq account
    have hl : base.val.length < Usize.max := by
      have := congrArg List.length hbv
      simp only [denoteRules, List.length_map, Document.Doc.lowerRules, denoteDoc] at this
      rw [this]
      exact hroom.rules (by simp [hrc])
    obtain ⟨out, hp, hv⟩ := push_eq base r hl
    refine ⟨out, ?_, ?_⟩
    · simp only [rule_eval.lowering.lower, hb, bind_ok, hrc, rule_eval.lowering.with_recovery, hr,
        hp]
    · rw [denoteRules, hv, List.map_append, ← denoteRules, hbv]
      simp [Document.Doc.lower, Document.Doc.recoveryRules, denoteDoc, hrc, hrv]

/-- `LowerRoom` is exact for the rules: on a document with a recovery
configuration and `Usize.max` rules, each capped one with room for its
amount condition, the translated `lower` fails. -/
theorem lower_full (doc : rule_eval.document.Doc) (account : Slice Std.U8)
    (hrc : doc.recovery.isSome) (hlen : doc.rules.val.length = Usize.max)
    (hargs : ∀ r ∈ doc.rules.val, ArgsRoom r) :
    rule_eval.lowering.lower doc account = fail .maximumSizeExceeded := by
  obtain ⟨base, hb, hbv⟩ := lower_rules_eq doc account none hargs
  obtain ⟨r, hr, -⟩ := recovery_rule_eq account
  have hl : base.val.length = Usize.max := by
    have := congrArg List.length hbv
    simp only [denoteRules, List.length_map, Document.Doc.lowerRules, denoteDoc] at this
    rw [this, hlen]
  cases h : doc.recovery with
  | none => rw [h] at hrc; cases hrc
  | some rc =>
    simp only [rule_eval.lowering.lower, hb, bind_ok, h, rule_eval.lowering.with_recovery, hr]
    exact push_full base r hl

/-! ## Scoped documents -/

@[simp] theorem vec_deref_mk {α : Type} (v : alloc.vec.Vec α) :
    (⟨alloc.vec.Vec.deref v⟩ : alloc.vec.Vec α) = v :=
  (vec_mk_deref v).symm

@[simp] theorem vec_mk_val {α : Type} (s : Slice α) : (⟨s⟩ : alloc.vec.Vec α).val = s.val := rfl

theorem excluded_eq (admin : rule_eval.document.Doc) (account : Slice Std.U8) :
    ∃ out, rule_eval.scoped.excluded admin account = ok out ∧
      out.val.map denoteBytes = (denoteDoc admin).excluded (bytesOf account.val) := by
  obtain ⟨o1, h1, h1v⟩ := push_eq (alloc.vec.Vec.new (alloc.vec.Vec Std.U8)) ⟨account⟩
    (by simp; scalar_tac)
  cases hrc : admin.recovery with
  | none =>
    refine ⟨o1, ?_, ?_⟩
    · simp [rule_eval.scoped.excluded, bytes_copy_eq, h1, hrc]
    · simp [h1v, Document.Doc.excluded, denoteDoc, hrc, denoteBytes]
  | some rc =>
    obtain ⟨o2, h2, h2v⟩ := push_eq o1 rc.controller (by rw [h1v]; simp; scalar_tac)
    cases hz : rc.zk with
    | none =>
      refine ⟨o2, ?_, ?_⟩
      · simp only [rule_eval.scoped.excluded, bytes_copy_eq, vec_deref_mk, h1, h2, hrc, hz,
          bind_ok]
      · simp [h2v, h1v, Document.Doc.excluded, denoteDoc, hrc, denoteRecovery, hz, denoteBytes]
    | some z =>
      obtain ⟨o3, h3, h3v⟩ := push_eq o2 z.adapter (by rw [h2v, h1v]; simp; scalar_tac)
      obtain ⟨o4, h4, h4v⟩ := push_eq o3 z.pool (by rw [h3v, h2v, h1v]; simp; scalar_tac)
      refine ⟨o4, ?_, ?_⟩
      · simp only [rule_eval.scoped.excluded, bytes_copy_eq, vec_deref_mk, h1, h2, h3, h4,
          hrc, hz, bind_ok]
      · simp [h4v, h3v, h2v, h1v, Document.Doc.excluded, denoteDoc, hrc, denoteRecovery, hz,
          denoteZk, denoteBytes]

theorem scope_excluded_eq (sc : rule_eval.document.Scope) (account : Slice Std.U8)
    (ex : Slice (alloc.vec.Vec Std.U8)) :
    rule_eval.scoped.scope_excluded sc account ex =
      ok ((denoteScope sc).excludedBy (bytesOf account.val) (ex.val.map denoteBytes)) := by
  cases sc with
  | SelfAdmin => rfl
  | Contract a =>
    simp only [rule_eval.scoped.scope_excluded, bytes_eq_eq, vec_deref_val, bind_ok,
      bytes_in_eq, denoteScope, Document.Scope.excludedBy]
    rw [any_bytes_eq_mem]
    by_cases ha : a.val = account.val
    · simp [ha, denoteBytes]
    · simp [ha, denoteBytes, bytesOf_inj]

theorem any_excluded_eq (rules : Slice rule_eval.document.DocRule) (account : Slice Std.U8)
    (ex : Slice (alloc.vec.Vec Std.U8)) :
    rule_eval.scoped.any_excluded rules account ex =
      ok ((rules.val.map denoteDocRule).any fun r =>
        r.scope.excludedBy (bytesOf account.val) (ex.val.map denoteBytes)) := by
  unfold rule_eval.scoped.any_excluded rule_eval.scoped.any_excluded_loop
  rw [loop_any rules.val (fun r => (denoteScope r.scope).excludedBy (bytesOf account.val)
    (ex.val.map denoteBytes))]
  · simp [List.any_map, Function.comp_def, denoteDocRule]
  · intro i hi
    obtain ⟨j, hj, hj'⟩ := incr_eq rules i hi
    refine ⟨j, hj', ?_⟩
    simp only [rule_eval.scoped.any_excluded_loop.body, slice_len_lt, hi, ↓reduceIte,
      index_usize_eq _ _ hi, scope_excluded_eq, bind_ok, hj]
    cases (denoteScope rules.val[i.val].scope).excludedBy (bytesOf account.val)
      (ex.val.map denoteBytes) <;> rfl
  · intro i hi
    have : ¬ i.val < rules.length := by simp only [Slice.length]; omega
    simp [rule_eval.scoped.any_excluded_loop.body, this]

/-- The translated `lower_scoped` returns the model's scoped lowering, its
refusals included: it terminates, never panics, and computes
`Doc.lowerScoped`. -/
theorem lower_scoped_eq (doc : rule_eval.document.Doc) (account : Slice Std.U8)
    (ex : Slice (alloc.vec.Vec Std.U8)) (gen : Std.U64)
    (hroom : ∀ r ∈ doc.rules.val, ArgsRoom r) :
    ∃ res, rule_eval.scoped.lower_scoped doc account ex gen = ok res ∧
      denoteScoped res = (denoteDoc doc).lowerScoped (bytesOf account.val) (ex.val.map denoteBytes)
        (denoteU64 gen) := by
  cases hrc : doc.recovery with
  | some rc =>
    exact ⟨.Err .RecoveryConfigured, by simp [rule_eval.scoped.lower_scoped, hrc],
      by simp [denoteScoped, denoteScopeError, Document.Doc.lowerScoped, denoteDoc, hrc]⟩
  | none =>
    have hany := any_excluded_eq (alloc.vec.Vec.deref doc.rules) account ex
    simp only [vec_deref_val] at hany
    cases hb : (doc.rules.val.map denoteDocRule).any fun r =>
        r.scope.excludedBy (bytesOf account.val) (ex.val.map denoteBytes) with
    | true =>
      exact ⟨.Err .ExcludedScope, by simp [rule_eval.scoped.lower_scoped, hrc, hany, hb],
        by simp [denoteScoped, denoteScopeError, Document.Doc.lowerScoped, denoteDoc, hrc, hb]⟩
    | false =>
      obtain ⟨out, ho, hov⟩ := lower_rules_eq doc account (some gen) hroom
      exact ⟨.Ok out, by simp [rule_eval.scoped.lower_scoped, hrc, hany, hb, ho],
        by simp [denoteScoped, Document.Doc.lowerScoped, denoteDoc, hrc, hb, hov]⟩

end RuleCore.Equiv
