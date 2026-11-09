import RuleCore.Equiv.Lowering
import RuleCore.Theorems.ExtractedAuthorize
import RuleCore.Theorems.Scoped

/-!
# Theorems of the extracted lowering

The theorems of `RuleCore.Theorems.Lowering` and `RuleCore.Theorems.Scoped`,
stated on the translated Rust functions (`rule_eval.lowering.lower`,
`rule_eval.scoped.lower_scoped`, `rule_eval.scoped.excluded`, the translated
attenuation steps and `rule_eval.authorize.check_auth`), with documents and
contexts read through the denotations. Each rests on the equivalence theorems
of `RuleCore.Equiv.Lowering` and `RuleCore.Equiv`.

Compile soundness:

* `lower_allows`, `lower_allows_of_recovery_none`: the translated `allows` on
  the rules the translated `lower` returns gives the document's verdict, or the
  recovery rule's when the document configures recovery;
* `lower_check_auth`: the translated `check_auth` on those rules accepts exactly
  when the document accepts, with the recovery controller's check read as
  `applyDocCheck`, and returns the same records;
* `lower_scoped_allows`, `lower_scoped_check_auth`: the same for a scoped
  document the translated `lower_scoped` accepts, issued under its generation.

Exclusion and generation:

* `lower_scoped_allows_excluded`, `derives_allows_excluded`: no rule set the
  translated `lower_scoped` returns, nor any rule set the translated steps
  derive from it, allows a call to the account or to a contract of the
  excluded set;
* `lower_scoped_generation`, `lower_generation`: every scoped rule carries the
  generation it was issued under, and no admin rule carries one.

The chain:

* `chain`: anything the translated `check_auth` accepts under a grant the
  translated steps derive from the rules the translated `lower_scoped` returns,
  under the excluded set the translated `excluded` takes from the admin
  document, is allowed by the scoped document, touches neither the account nor
  a contract of the excluded set, and is made in the generation the document
  was issued under;
* `chain_trace`: every run the grant accepts from empty records, those rules
  accept from theirs, with each choice renumbered, and they accept exactly what
  the scoped document does.
-/

namespace RuleCore.Extracted

open Aeneas Aeneas.Std Result RuleCore.Equiv

/-- The admin document's verdict on the translated `lower`'s rules. -/
theorem lower_allows {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    (hv : (denoteDoc doc).Valid) (hroom : LowerRoom doc)
    {out : alloc.vec.Vec rule_eval.rule.Rule} (h : rule_eval.lowering.lower doc account = ok out)
    (c : rule_eval.context.Context) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows (alloc.vec.Vec.deref out) c authenticated =
      ok ((denoteDoc doc).allows (bytesOf account.val) (denoteContext c)
          (denoteSigners authenticated.val) ||
        match doc.recovery with
        | some _ => (Document.recoveryRule (bytesOf account.val)).allows (denoteContext c)
            (denoteSigners authenticated.val)
        | none => false) := by
  obtain ⟨out', h', hd⟩ := lower_eq doc account hroom
  obtain rfl := Result.ok_injective (h.symm.trans h')
  rw [allows_eq, vec_deref_val, hd, Document.Doc.lower_allows hv]
  cases hr : doc.recovery <;> simp [denoteDoc, hr]

/-- With no recovery configured, the translated `allows` on the translated
`lower`'s rules gives exactly the document's verdict. -/
theorem lower_allows_of_recovery_none {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    (hv : (denoteDoc doc).Valid) (hroom : LowerRoom doc) (hr : doc.recovery = none)
    {out : alloc.vec.Vec rule_eval.rule.Rule} (h : rule_eval.lowering.lower doc account = ok out)
    (c : rule_eval.context.Context) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows (alloc.vec.Vec.deref out) c authenticated =
      ok ((denoteDoc doc).allows (bytesOf account.val) (denoteContext c)
        (denoteSigners authenticated.val)) := by
  rw [lower_allows hv hroom h, hr, Bool.or_false]

/-- Compile soundness through the translated `check_auth`: on every
authorization, it accepts the translated `lower`'s rules exactly when the
document accepts, with the recovery controller's check read as
`applyDocCheck`, and returns records denoting the same ones. -/
theorem lower_check_auth {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    (hv : (denoteDoc doc).Valid) (hroom : LowerRoom doc)
    {out : alloc.vec.Vec rule_eval.rule.Rule} (h : rule_eval.lowering.lower doc account = ok out)
    (records : Slice rule_eval.cap.SpendRecord) (contexts : Slice rule_eval.context.Context)
    (choices : Slice Std.U32) (authenticated : Slice rule_eval.signer.Signer) (now : Std.U32)
    (generation : Std.U64) :
    ∃ res, rule_eval.authorize.check_auth (alloc.vec.Vec.deref out) records contexts choices
        authenticated now generation = ok res ∧
      (denoteAuthorized res).toOption =
        (denoteDoc doc).checkAuth (bytesOf account.val) Document.applyDocCheck none
          (records.val.map denoteRecord)
          (denoteAuthorization contexts choices authenticated now generation) := by
  obtain ⟨out', h', hd⟩ := lower_eq doc account hroom
  obtain rfl := Result.ok_injective (h.symm.trans h')
  obtain ⟨res, hres, hdr⟩ := check_auth_eq (alloc.vec.Vec.deref out) records contexts choices
    authenticated now generation
  refine ⟨res, hres, ?_⟩
  rw [hdr, vec_deref_val, hd, Document.Doc.lower_checkAuth hv]

/-- A scoped document's verdict on the translated `lower_scoped`'s rules. -/
theorem lower_scoped_allows {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    {ex : Slice (alloc.vec.Vec Std.U8)} {gen : Std.U64} (hv : (denoteDoc doc).Valid)
    (hroom : ∀ r ∈ doc.rules.val, ArgsRoom r) {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.scoped.lower_scoped doc account ex gen = ok (.Ok out))
    (c : rule_eval.context.Context) (authenticated : Slice rule_eval.signer.Signer) :
    rule_eval.rule_set.allows (alloc.vec.Vec.deref out) c authenticated =
      ok ((denoteDoc doc).allows (bytesOf account.val) (denoteContext c)
        (denoteSigners authenticated.val)) := by
  obtain ⟨res, h', hd⟩ := lower_scoped_eq doc account ex gen hroom
  obtain rfl := Result.ok_injective (h.symm.trans h')
  simp only [denoteScoped] at hd
  rw [allows_eq, vec_deref_val, Document.Doc.lowerScoped_allows hv hd.symm]

/-- Compile soundness for scoped documents through the translated
`check_auth`, with the same records. -/
theorem lower_scoped_check_auth {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    {ex : Slice (alloc.vec.Vec Std.U8)} {gen : Std.U64} (hv : (denoteDoc doc).Valid)
    (hroom : ∀ r ∈ doc.rules.val, ArgsRoom r) {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.scoped.lower_scoped doc account ex gen = ok (.Ok out))
    (records : Slice rule_eval.cap.SpendRecord) (contexts : Slice rule_eval.context.Context)
    (choices : Slice Std.U32) (authenticated : Slice rule_eval.signer.Signer) (now : Std.U32)
    (generation : Std.U64) (ctl : Chain.Context → List Chain.Signer → Bool) :
    ∃ res, rule_eval.authorize.check_auth (alloc.vec.Vec.deref out) records contexts choices
        authenticated now generation = ok res ∧
      (denoteAuthorized res).toOption =
        (denoteDoc doc).checkAuth (bytesOf account.val) ctl (some (denoteU64 gen))
          (records.val.map denoteRecord)
          (denoteAuthorization contexts choices authenticated now generation) := by
  obtain ⟨res', h', hd⟩ := lower_scoped_eq doc account ex gen hroom
  obtain rfl := Result.ok_injective (h.symm.trans h')
  simp only [denoteScoped] at hd
  obtain ⟨res, hres, hdr⟩ := check_auth_eq (alloc.vec.Vec.deref out) records contexts choices
    authenticated now generation
  refine ⟨res, hres, ?_⟩
  rw [hdr, vec_deref_val, Document.Doc.lowerScoped_checkAuth hv hd.symm]

/-- The model's scoped lowering of what the translated `lower_scoped`
accepted. -/
theorem lower_scoped_model {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    {ex : Slice (alloc.vec.Vec Std.U8)} {gen : Std.U64} (hroom : ∀ r ∈ doc.rules.val, ArgsRoom r)
    {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.scoped.lower_scoped doc account ex gen = ok (.Ok out)) :
    (denoteDoc doc).lowerScoped (bytesOf account.val) (ex.val.map denoteBytes) (denoteU64 gen) =
      .ok (denoteRules out.val) := by
  obtain ⟨res, h', hd⟩ := lower_scoped_eq doc account ex gen hroom
  obtain rfl := Result.ok_injective (h.symm.trans h')
  exact hd.symm

/-- Exclusion on the translation: no rule set the translated `lower_scoped`
returns allows a call to the account or to a contract of the excluded set. -/
theorem lower_scoped_allows_excluded {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    {ex : Slice (alloc.vec.Vec Std.U8)} {gen : Std.U64} (hroom : ∀ r ∈ doc.rules.val, ArgsRoom r)
    {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.scoped.lower_scoped doc account ex gen = ok (.Ok out))
    {contract function : alloc.vec.Vec Std.U8} {args : alloc.vec.Vec rule_eval.val.Val}
    {authenticated : Slice rule_eval.signer.Signer}
    (ha : rule_eval.rule_set.allows (alloc.vec.Vec.deref out) (.Call contract function args)
      authenticated = ok true) :
    contract.val ≠ account.val ∧ ∀ e ∈ ex.val, contract.val ≠ e.val := by
  rw [allows_eq, vec_deref_val] at ha
  have := Document.Doc.lowerScoped_allows_excluded (lower_scoped_model hroom h)
    (Result.ok_injective ha)
  refine ⟨fun he => this.1 (by simp [denoteBytes, he]), fun e he hce => this.2 ?_⟩
  exact List.mem_map.mpr ⟨e, he, by simp [denoteBytes, hce]⟩

/-- Exclusion survives the translated attenuation steps. -/
theorem derives_allows_excluded {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    {ex : Slice (alloc.vec.Vec Std.U8)} {gen : Std.U64} (hroom : ∀ r ∈ doc.rules.val, ArgsRoom r)
    {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.scoped.lower_scoped doc account ex gen = ok (.Ok out))
    {grant : Slice rule_eval.rule.Rule} (hd : Derives (alloc.vec.Vec.deref out) grant)
    {contract function : alloc.vec.Vec Std.U8} {args : alloc.vec.Vec rule_eval.val.Val}
    {authenticated : Slice rule_eval.signer.Signer}
    (ha : rule_eval.rule_set.allows grant (.Call contract function args) authenticated = ok true) :
    contract.val ≠ account.val ∧ ∀ e ∈ ex.val, contract.val ≠ e.val :=
  lower_scoped_allows_excluded hroom h (hd.narrower _ _ ha)

/-- Every rule the translated `lower_scoped` returns carries the generation it
was issued under. -/
theorem lower_scoped_generation {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    {ex : Slice (alloc.vec.Vec Std.U8)} {gen : Std.U64} (hroom : ∀ r ∈ doc.rules.val, ArgsRoom r)
    {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.scoped.lower_scoped doc account ex gen = ok (.Ok out)) :
    ∀ r ∈ out.val, r.generation = some gen := by
  intro r hr
  have := Document.Doc.lowerScoped_generation (lower_scoped_model hroom h) (denoteRule r)
    (List.mem_map_of_mem hr)
  simp only [denoteRule] at this
  cases hg : r.generation with
  | none => rw [hg] at this; cases this
  | some g =>
    rw [hg] at this
    simp only [Option.map_some, Option.some.injEq] at this
    rw [denoteU64_injective this]

/-- No rule the translated `lower` returns carries a generation. -/
theorem lower_generation {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    (hroom : LowerRoom doc) {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.lowering.lower doc account = ok out) : ∀ r ∈ out.val, r.generation = none := by
  obtain ⟨out', h', hd⟩ := lower_eq doc account hroom
  obtain rfl := Result.ok_injective (h.symm.trans h')
  intro r hr
  have := Document.Doc.lower_generation (denoteDoc doc) (bytesOf account.val) (denoteRule r)
    (by rw [← hd]; exact List.mem_map_of_mem hr)
  simp only [denoteRule, Option.map_eq_none_iff] at this
  exact this

/-- The containment chain on the translation: anything the translated
`check_auth` accepts under a grant derived by translated steps from the rules
the translated `lower_scoped` returns for a valid scoped document, under the
excluded set the translated `excluded` takes from the admin document, is
allowed by the scoped document, touches neither the account nor a contract of
the excluded set, and is made in the generation the document was issued
under. -/
theorem chain {admin doc : rule_eval.document.Doc} {account : Slice Std.U8} {gen : Std.U64}
    (hv : (denoteDoc doc).Valid) (hroom : ∀ r ∈ doc.rules.val, ArgsRoom r)
    {ex : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hex : rule_eval.scoped.excluded admin account = ok ex)
    {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.scoped.lower_scoped doc account (alloc.vec.Vec.deref ex) gen = ok (.Ok out))
    {grant : Slice rule_eval.rule.Rule} {f : Nat → Nat}
    (hd : DerivesAlong (alloc.vec.Vec.deref out) grant f)
    {records : Slice rule_eval.cap.SpendRecord} {contexts : Slice rule_eval.context.Context}
    {choices : Slice Std.U32} {authenticated : Slice rule_eval.signer.Signer} {now : Std.U32}
    {generation : Std.U64} {recs : alloc.vec.Vec rule_eval.cap.SpendRecord}
    (ha : rule_eval.authorize.check_auth grant records contexts choices authenticated now
      generation = ok (.Ok recs)) :
    (∀ c ∈ contexts.val, (denoteDoc doc).allows (bytesOf account.val) (denoteContext c)
        (denoteSigners authenticated.val) = true) ∧
      (∀ c ∈ contexts.val, ∀ contract function args, c = .Call contract function args →
        denoteBytes contract ∉ (denoteDoc admin).excluded (bytesOf account.val)) ∧
      (contexts.val ≠ [] → generation = gen) := by
  obtain ⟨exv, hexv, hexd⟩ := excluded_eq admin account
  obtain rfl := Result.ok_injective (hex.symm.trans hexv)
  have hmodel := lower_scoped_model hroom h
  simp only [vec_deref_val] at hmodel
  rw [hexd] at hmodel
  have hall := allows_all_of_narrower hd.derives.narrower contexts authenticated
    (check_auth_allows_all ha)
  rw [allows_all_eq, vec_deref_val] at hall
  have hall := (Chain.RuleSet.allowsAll_iff _ _ _).mp (Result.ok_injective hall)
  refine ⟨fun c hc => ?_, fun c hc contract function args he => ?_, fun hne => ?_⟩
  · rw [← Document.Doc.lowerScoped_allows hv hmodel]
    exact hall _ (List.mem_map_of_mem hc)
  · have := hall _ (List.mem_map_of_mem hc)
    rw [he] at this
    exact (Document.Doc.lowerScoped_allows_excluded hmodel this).2
  · by_cases hg : generation = gen
    · exact hg
    · exact absurd (check_auth_contexts_nil_of_stale ha
        (hd.generation_eq fun r hr => lower_scoped_generation hroom h r (by simpa using hr))
        (Ne.symm hg)) hne

/-- The chain through caps on the translation: every run of authorizations the
grant accepts from empty records, the rules the translated `lower_scoped`
returns accept from theirs, with each choice renumbered by `f`; and the
translated `check_auth` on those rules accepts exactly what the scoped document,
issued under the generation, accepts, with the same records. -/
theorem chain_trace {doc : rule_eval.document.Doc} {account : Slice Std.U8}
    {ex : Slice (alloc.vec.Vec Std.U8)} {gen : Std.U64} (hv : (denoteDoc doc).Valid)
    (hroom : ∀ r ∈ doc.rules.val, ArgsRoom r) {out : alloc.vec.Vec rule_eval.rule.Rule}
    (h : rule_eval.scoped.lower_scoped doc account ex gen = ok (.Ok out))
    {grant : Slice rule_eval.rule.Rule} {f : Nat → Nat}
    (hd : DerivesAlong (alloc.vec.Vec.deref out) grant f) :
    TraceNarrower grant (alloc.vec.Vec.deref out) f ∧
      ∀ (records : Slice rule_eval.cap.SpendRecord) (contexts : Slice rule_eval.context.Context)
        (choices : Slice Std.U32) (authenticated : Slice rule_eval.signer.Signer) (now : Std.U32)
        (generation : Std.U64) (ctl : Chain.Context → List Chain.Signer → Bool),
        ∃ res, rule_eval.authorize.check_auth (alloc.vec.Vec.deref out) records contexts choices
            authenticated now generation = ok res ∧
          (denoteAuthorized res).toOption =
            (denoteDoc doc).checkAuth (bytesOf account.val) ctl (some (denoteU64 gen))
              (records.val.map denoteRecord)
              (denoteAuthorization contexts choices authenticated now generation) :=
  ⟨hd.traceNarrower, fun records contexts choices authenticated now generation ctl =>
    lower_scoped_check_auth hv hroom h records contexts choices authenticated now generation ctl⟩

/-! ## Former names

The names these theorems had before the evaluator's entry point was renamed
`check_auth`, kept so that citations of them still resolve. -/

@[deprecated lower_check_auth (since := "2026-11-08")]
theorem lower_authorize : type_of% @lower_check_auth := @lower_check_auth

@[deprecated lower_scoped_check_auth (since := "2026-11-08")]
theorem lower_scoped_authorize : type_of% @lower_scoped_check_auth := @lower_scoped_check_auth

end RuleCore.Extracted
