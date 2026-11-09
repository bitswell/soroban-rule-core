import RuleCore.Vocab.Lowering
import RuleCore.Theorems.Chain

/-!
# Compile soundness

The rules a document lowers to allow exactly what the document says
(`RuleCore.Vocab.Document`), apart from the recovery rule, which allows more.

Without time, generation or caps:

* `Doc.lowerRule_allows`: each lowered rule allows exactly what its document
  rule allows, for a valid rule;
* `Doc.lowerRules_allows`: the rules a document's rules lower to allow exactly
  what the document allows;
* `Doc.lower_allows`, `Doc.lower_allows_of_recovery_none`: the admin
  document's lowering allows what the document allows or what the recovery
  rule allows, which is every call to the account's `apply_doc`
  (`recoveryRule_allows`); with no recovery configured, exactly what the
  document allows.

Through `checkAuth`, which adds the ledger, the generation and the caps:

* `Doc.lower_checkAuth`: on every authorization, the admin document's lowering
  accepts exactly when the document does (`Doc.checkAuth`) with the recovery
  controller's check taken as `applyDocCheck`, every call to `apply_doc`, and
  it returns the same records; `Doc.lower_checkAuth_of_recovery_none` drops the
  controller check when no recovery is configured;
* `Doc.checkAuth_mono`, `Doc.lower_checkAuth_of_check`: the recovery rule is an
  over-approximation. Whatever the document accepts under a controller check
  that accepts only `apply_doc` calls, the lowering accepts too, with the same
  records.
-/

namespace RuleCore.Document

open RuleCore RuleCore.Chain

/-! ## Lists -/

theorem eraseDups_of_nodup {α : Type} [DecidableEq α] : ∀ {l : List α}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: as, h => by
    have ha : a ∉ as := (List.nodup_cons.mp h).1
    rw [List.eraseDups_cons, List.filter_eq_self.mpr (fun b hb => by
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
      intro e
      subst e
      exact ha hb), eraseDups_of_nodup (List.nodup_cons.mp h).2]

/-! ## One rule -/

theorem Rule.mem_lowerFunctions (r : Rule) (f : Bytes) :
    f ∈ r.lowerFunctions ↔
      (∀ fs, r.functions = some fs → f ∈ fs) ∧ (r.cap.isSome → f = transfer) := by
  rcases r with ⟨scope, principals, functions, args, notAfter, cap⟩
  cases cap with
  | none =>
    cases functions <;> simp [Rule.lowerFunctions]
  | some k =>
    cases functions with
    | none => simp [Rule.lowerFunctions, coversTransfer]
    | some fs =>
      simp only [Rule.lowerFunctions, coversTransfer]
      by_cases ht : transfer ∈ fs
      · simp only [ht, decide_true, ↓reduceIte, Functions.mem_only, List.mem_singleton]
        constructor
        · rintro rfl; simp [ht]
        · intro h; exact h.2 rfl
      · simp only [ht, decide_false, Bool.false_eq_true, ↓reduceIte, Functions.mem_only,
          List.not_mem_nil, false_iff]
        rintro ⟨hf, he⟩
        exact ht (he rfl ▸ hf fs rfl)

theorem Rule.covers_iff (r : Rule) (acct contract function : Bytes) :
    r.covers acct contract function = true ↔
      contract = r.scope.contractOn acct ∧ (∀ fs, r.functions = some fs → function ∈ fs) ∧
        (r.cap.isSome → function = transfer) := by
  rcases r with ⟨scope, principals, functions, args, notAfter, cap⟩
  cases cap <;> cases functions <;> simp [Rule.covers, and_assoc]

theorem i128Max_toInt : i128Max.toInt = 2 ^ 127 - 1 := by
  simp only [i128Max, BitVec.toInt_ofInt]
  decide

/-- `amountCond` holds exactly of an argument list with an `i128` at index 2. -/
theorem amountCond_holds (args : List Val) :
    amountCond.holds args =
      (match (args[2]? : Option Val) with
        | some (.i128 _) => true
        | _ => false) := by
  simp only [amountCond, amountArg, Cond.holds]
  have h2 : (2 : UInt32).toNat = 2 := rfl
  rw [h2]
  cases args[2]? with
  | none => rfl
  | some v =>
    cases v with
    | i128 v =>
      have hv := BitVec.toInt_lt (x := v)
      simp only [decide_eq_true_eq, i128Max_toInt]
      simp at hv
      omega
    | _ => rfl

theorem Pred.lower_holds (acct : Bytes) (i : UInt32) (p : Pred) (args : List Val) :
    (p.lower acct i).holds args = p.holds acct args[i.toNat]? := by
  cases p with
  | isSelf => rfl
  | addressEq a => rfl
  | stringIn values =>
    simp only [Pred.lower, Cond.holds, Pred.holds]
    cases args[i.toNat]? with
    | none => rfl
    | some v =>
      cases v <;> simp [List.mem_map, List.mem_filter, and_comm]
  | stringPrefix pre =>
    simp only [Pred.lower, Cond.holds, Pred.holds]
    rfl
  | u32Eq v => rfl

theorem Rule.lowerConds_all (r : Rule) (acct : Bytes) (args : List Val) :
    ((r.lowerConds acct).all fun c => c.holds args) = r.argsHold acct args := by
  rcases r with ⟨scope, principals, functions, cs, notAfter, cap⟩
  have hp : ((fun c => c.holds args) ∘ ArgConstraint.lower acct) =
      fun c : ArgConstraint => c.pred.holds acct args[c.index.toNat]? :=
    funext fun c => Pred.lower_holds acct c.index c.pred args
  simp only [Rule.lowerConds, Rule.argsHold, List.all_append, List.all_map, hp]
  cases cap with
  | none => rfl
  | some k =>
    simp only [List.all_cons, List.all_nil, Bool.and_true, amountCond_holds]
    rfl

theorem Rule.signed_lowerRule {d : Doc} {r : Rule} (hv : Rule.Valid d r) (acct : Bytes)
    (gen : Option UInt64) (auth : List Signer) :
    (d.lowerRule acct gen r).signed auth = d.signed r.principals auth := by
  rw [Bool.eq_iff_iff, Chain.Rule.signed_iff]
  rcases r with ⟨scope, principals, functions, args, notAfter, cap⟩
  cases principals with
  | all ids =>
    have hnd := hv.allDistinct ids rfl
    have hfit := hv.allFits ids rfl
    simp only at hnd hfit
    have hn : (UInt32.ofNat (min (d.named (.all ids)).length 4294967295)).toNat =
        (d.named (.all ids)).length := by
      rw [UInt32.toNat_ofNat']
      omega
    have hle := List.length_filter_le (fun s => decide (s ∈ auth)) (d.named (.all ids))
    simp only [Doc.lowerRule, Doc.threshold, Doc.signed, List.all_eq_true, decide_eq_true_eq]
    rw [eraseDups_of_nodup hnd, hn]
    constructor
    · intro h s hs
      have := (List.length_filter_eq_length_iff (l := d.named (.all ids))
        (p := fun s => decide (s ∈ auth))).mp (by omega) s hs
      simpa using this
    · intro h
      rw [List.length_filter_eq_length_iff.mpr (fun s hs => by simpa using h s hs)]
      exact Nat.le_refl _
  | threshold ids m => simp [Doc.lowerRule, Doc.threshold, Doc.signed]

/-- Each lowered rule allows exactly what its document rule allows, under
every authenticated signer list, for a valid rule. -/
theorem Doc.lowerRule_allows {d : Doc} {r : Rule} (hv : Rule.Valid d r) (acct : Bytes)
    (gen : Option UInt64) (c : Context) (auth : List Signer) :
    (d.lowerRule acct gen r).allows c auth = d.ruleAllows acct r c auth := by
  cases c with
  | create w => rfl
  | call contract function args =>
    have hs := Rule.signed_lowerRule hv acct gen auth
    have hc := Rule.lowerConds_all r acct args
    simp only [Chain.Rule.signed] at hs
    simp only [Chain.Rule.allows, RuleCore.Rule.allows, Doc.ruleAllows]
    rw [hs]
    simp only [Chain.Rule.denote, Chain.Rule.scope, List.all_map, Function.comp_def, Cond.denote,
      Doc.lowerRule]
    rw [hc, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Rule.covers_iff, Rule.mem_lowerFunctions,
      and_assoc]

/-! ## Rule sets -/

theorem RuleSet.allows_eq_any (rs : Chain.RuleSet) (c : Context) (auth : List Signer) :
    rs.allows c auth = rs.any fun r => r.allows c auth := by
  simp only [Chain.RuleSet.allows, Chain.RuleSet.denote, RuleCore.RuleSet.allows,
    RuleCore.RuleSet.ofRules, List.any_map, Function.comp_def, Chain.Rule.allows]

/-- The rules a valid document's rules lower to allow exactly what the
document allows, whatever generation they carry. -/
theorem Doc.lowerRules_allows {d : Doc} (hv : d.Valid) (acct : Bytes) (gen : Option UInt64)
    (c : Context) (auth : List Signer) :
    (d.lowerRules acct gen).allows c auth = d.allows acct c auth := by
  rw [RuleSet.allows_eq_any, Doc.lowerRules, List.any_map, Doc.allows]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  simp only [Function.comp_apply]
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, Doc.lowerRule_allows (hv r hr) acct gen c auth ▸ h⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, (Doc.lowerRule_allows (hv r hr) acct gen c auth).symm ▸ h⟩

/-- The recovery rule allows every call to the account's `apply_doc`, with any
arguments and under any signers, and nothing else. -/
theorem recoveryRule_allows (acct : Bytes) (c : Context) (auth : List Signer) :
    (recoveryRule acct).allows c auth =
      match c with
      | .call contract function _ => decide (contract = acct) && decide (function = applyDoc)
      | .create _ => false := by
  cases c with
  | create w => rfl
  | call contract function args =>
    simp [Chain.Rule.allows, RuleCore.Rule.allows, recoveryRule, Chain.Rule.denote,
      Chain.Rule.scope, RuleCore.Rule.signed, RuleCore.Rule.present]

/-- The admin document's lowering allows what the document allows, or what
the recovery rule allows when the document configures recovery. -/
theorem Doc.lower_allows {d : Doc} (hv : d.Valid) (acct : Bytes) (c : Context)
    (auth : List Signer) :
    (d.lower acct).allows c auth =
      (d.allows acct c auth ||
        match d.recovery with
        | some _ => (recoveryRule acct).allows c auth
        | none => false) := by
  have h1 := Doc.lowerRules_allows hv acct none c auth
  rw [RuleSet.allows_eq_any] at h1
  rw [RuleSet.allows_eq_any, Doc.lower, List.any_append, h1]
  cases hr : d.recovery <;> simp [Doc.recoveryRules, hr]

/-- With no recovery configured, the admin document's lowering allows exactly
what the document allows. -/
theorem Doc.lower_allows_of_recovery_none {d : Doc} (hv : d.Valid) (hr : d.recovery = none)
    (acct : Bytes) (c : Context) (auth : List Signer) :
    (d.lower acct).allows c auth = d.allows acct c auth := by
  rw [Doc.lower_allows hv, hr, Bool.or_false]


/-! ## Authorization -/

/-- The rules a document lowers to are its installed rules, each lowered. -/
theorem Doc.lowerAll_eq_map (d : Doc) (acct : Bytes) (gen : Option UInt64) :
    d.lowerRules acct gen ++ d.recoveryRules acct = d.installed.map (Installed.lower d acct gen) := by
  simp only [Doc.lowerRules, Doc.recoveryRules, Doc.installed, List.map_append, List.map_map]
  congr 1
  cases d.recovery <;> rfl

theorem Doc.mem_rules_of_installed {d : Doc} {j : Nat} {r : Rule}
    (h : d.installed[j]? = some (.rule r)) : r ∈ d.rules := by
  have hm := List.mem_of_getElem? h
  simp only [Doc.installed, List.mem_append, List.mem_map] at hm
  rcases hm with ⟨r', hr', he⟩ | hm
  · cases he
    exact hr'
  · cases d.recovery <;> simp at hm

theorem Doc.lastLedger_toNat {x : UInt32} (hx : 0 < x.toNat) : (lastLedger x).toNat = x.toNat - 1 := by
  simp only [lastLedger, UInt32.toNat_ofNat']
  have := x.toNat_lt
  omega

/-- The first pass: the lowered rule chosen for a context passes `checkAuth`'s
checks exactly when the document's installed rule validates it. -/
theorem Doc.checkChoice_lower {d : Doc} (hv : d.Valid) (acct : Bytes) (gen : Option UInt64)
    (a : Chain.Authorization) (x : Context × UInt32) :
    (d.lowerRules acct gen ++ d.recoveryRules acct).denote.checkChoice a.auth a.now.toNat
        a.generation.toNat a.contexts.head? (x.1, x.2.toNat) = .ok () ↔
      d.validates acct applyDocCheck gen a x = true := by
  rw [RuleCore.RuleSet.checkChoice_ok_iff, Chain.RuleSet.denote_get, Doc.lowerAll_eq_map,
    List.getElem?_map]
  simp only [Doc.validates]
  cases hj : d.installed[x.2.toNat]? with
  | none => simp
  | some i =>
    cases i with
    | rule r =>
      have hrv := hv r (Doc.mem_rules_of_installed hj)
      simp only [Option.map_some, Option.some.injEq, exists_eq_left', Installed.lower,
        Bool.and_eq_true]
      have ha := Doc.lowerRule_allows hrv acct gen x.1 a.auth
      simp only [Chain.Rule.allows] at ha
      simp only [RuleCore.Rule.allowsIn, Bool.and_eq_true]
      rw [ha]
      have hroot : (d.lowerRule acct gen r).denote.rootMatches a.contexts.head? =
          r.rootMatches a.contexts.head? := by
        simp only [RuleCore.Rule.rootMatches, Chain.Rule.denote, Doc.lowerRule, Rule.rootMatches]
        cases r.effectiveRoot <;> cases a.contexts.head? <;> rfl
      rw [hroot]
      have he : (d.lowerRule acct gen r).denote.expired a.now.toNat = false ↔
          r.live a.now.toNat = true := by
        simp only [Chain.Rule.denote, Doc.lowerRule, RuleCore.Rule.expired, Rule.live]
        cases hx : r.notAfterLedger with
        | none => simp
        | some x =>
          have hpos := hrv.notAfterPos x hx
          simp only [Option.map_some, decide_eq_false_iff_not, decide_eq_true_eq,
            Doc.lastLedger_toNat hpos]
          omega
      have hs : (d.lowerRule acct gen r).denote.stale a.generation.toNat = false ↔
          (gen.all fun g => decide (g = a.generation)) = true := by
        simp only [Chain.Rule.denote, Doc.lowerRule, RuleCore.Rule.stale]
        cases gen with
        | none => simp
        | some g =>
          simp only [Option.map_some, decide_eq_false_iff_not, Option.all_some,
            decide_eq_true_eq, ne_eq, Decidable.not_not]
          exact ⟨fun h => UInt64.toNat_inj.mp h, fun h => h ▸ rfl⟩
      rw [he, hs]
      simp only [and_assoc]
    | recovery =>
      simp only [Option.map_some, Option.some.injEq, exists_eq_left', Installed.lower]
      have ha := recoveryRule_allows acct x.1 a.auth
      simp only [Chain.Rule.allows] at ha
      simp only [RuleCore.Rule.allowsIn, Bool.and_eq_true]
      rw [ha]
      simp only [RuleCore.Rule.rootMatches, recoveryRule, Chain.Rule.denote, RuleCore.Rule.expired, RuleCore.Rule.stale,
        Option.map_none, true_and]
      cases x.1 with
      | create w => simp [onAccount]
      | call contract function args => simp [onAccount, applyDocCheck]

/-- The second pass: an authenticated signer is a signer of a chosen lowered
rule exactly when a chosen document rule names it. -/
theorem Doc.signerChosen_lower (d : Doc) (acct : Bytes) (gen : Option UInt64)
    (choices : List UInt32) (s : Signer) :
    (d.lowerRules acct gen ++ d.recoveryRules acct).denote.signerChosen (choices.map (·.toNat)) s =
      d.signerChosen choices s := by
  simp only [RuleCore.RuleSet.signerChosen, Doc.signerChosen, List.any_map, Function.comp_def,
    Chain.RuleSet.denote_get, Doc.lowerAll_eq_map, List.getElem?_map]
  apply List.any_congr rfl
  intro j
  cases d.installed[j.toNat]? with
  | none => rfl
  | some i =>
    cases i with
    | rule r => simp [Installed.lower, Chain.Rule.denote, Doc.lowerRule]
    | recovery => simp [Installed.lower, Chain.Rule.denote, recoveryRule]

/-- The third pass, one context: charging the lowered rule chosen for it gives
the records charging the document's installed rule gives, or neither gives
any. -/
theorem Doc.charge_lower (d : Doc) (acct : Bytes) (gen : Option UInt64) (now : Nat)
    (records : List RuleCore.Cap.Record) (x : Context × UInt32) :
    ((d.lowerRules acct gen ++ d.recoveryRules acct).denote.charge now records
        (x.1, x.2.toNat)).toOption = d.charge now records x := by
  simp only [RuleCore.RuleSet.charge, Doc.charge, Chain.RuleSet.denote_get, Doc.lowerAll_eq_map,
    List.getElem?_map]
  cases d.installed[x.2.toNat]? with
  | none => rfl
  | some i =>
    cases i with
    | recovery => simp [Installed.lower, Chain.Rule.denote, recoveryRule, Except.toOption]
    | rule r =>
      simp only [Option.map_some, Installed.lower, Chain.Rule.denote, Doc.lowerRule]
      cases r.cap with
      | none => rfl
      | some k =>
        simp only [Option.map_some, Chain.Cap.denote, Cap.lower, Chain.Cap.amount, amountArg,
          Chain.Cap.params]
        have h2 : (2 : UInt32).toNat = 2 := rfl
        rw [h2]
        cases x.1 with
        | create w => rfl
        | call contract function args =>
          simp only [spendAmount]
          cases (args[2]? : Option Val) with
          | none => rfl
          | some v =>
            cases v with
            | i128 v =>
              simp only
              cases records[x.2.toNat]? with
              | none => rfl
              | some rec =>
                simp only
                cases RuleCore.Cap.Params.check _ rec now v.toInt <;> rfl
            | _ => rfl

theorem Doc.foldlM_charge_lower (d : Doc) (acct : Bytes) (gen : Option UInt64) (now : Nat) :
    ∀ (l : List (Context × UInt32)) (records : List RuleCore.Cap.Record),
      ((l.map fun x => (x.1, x.2.toNat)).foldlM
          ((d.lowerRules acct gen ++ d.recoveryRules acct).denote.charge now) records).toOption =
        l.foldlM (d.charge now) records
  | [], records => rfl
  | x :: l, records => by
    rw [List.map_cons, RuleCore.foldlM_except_cons, List.foldlM_cons]
    have hc := Doc.charge_lower d acct gen now records x
    cases h : (d.lowerRules acct gen ++ d.recoveryRules acct).denote.charge now records
        (x.1, x.2.toNat) with
    | error e =>
      rw [h] at hc
      simp only [Except.toOption] at hc
      rw [← hc]
      rfl
    | ok records' =>
      rw [h] at hc
      simp only [Except.toOption] at hc
      rw [← hc]
      exact Doc.foldlM_charge_lower d acct gen now l records'

theorem toOption_eq_some {ε α : Type} {e : Except ε α} {x : α} : e.toOption = some x ↔ e = .ok x := by
  cases e <;> simp [Except.toOption]

theorem toOption_eq_of_iff {ε α : Type} {e : Except ε α} {o : Option α}
    (h : ∀ x, e = .ok x ↔ o = some x) : e.toOption = o := by
  cases e with
  | ok x => exact ((h x).mp rfl).symm
  | error err =>
    cases o with
    | none => rfl
    | some x => exact absurd ((h x).mpr rfl) (by simp)

theorem Doc.checkAuth_eq_some_iff (d : Doc) (acct : Bytes) (ctl : Context → List Signer → Bool)
    (issued : Option UInt64) (records records' : List RuleCore.Cap.Record) (a : Chain.Authorization) :
    d.checkAuth acct ctl issued records a = some records' ↔
      a.choices.length = a.contexts.length ∧ records.length = d.installed.length ∧
        (∀ x ∈ a.contexts.zip a.choices, d.validates acct ctl issued a x = true) ∧
        (∀ s ∈ a.auth, d.signerChosen a.choices s = true) ∧
        (a.contexts.zip a.choices).foldlM (d.charge a.now.toNat) records = some records' := by
  unfold Doc.checkAuth
  split <;> rename_i h
  · simp only [List.all_eq_true] at h
    constructor
    · intro hf
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hf⟩
    · rintro ⟨-, -, -, -, hf⟩
      exact hf
  · simp only [List.all_eq_true] at h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h1, h2, h3, h4, -⟩
    exact h ⟨h1, h2, h3, h4⟩

/-- On every authorization, the rules a valid document lowers to (carrying
`gen`) accept exactly when the document accepts with `issued := gen` and the
recovery controller's check read as `applyDocCheck`, and they return the same
records. -/
theorem Doc.checkAuth_lowerAll {d : Doc} (hv : d.Valid) (acct : Bytes) (gen : Option UInt64)
    (records : List RuleCore.Cap.Record) (a : Chain.Authorization) :
    ((d.lowerRules acct gen ++ d.recoveryRules acct).checkAuth records a).toOption =
      d.checkAuth acct applyDocCheck gen records a := by
  apply toOption_eq_of_iff
  intro records'
  rw [Chain.RuleSet.checkAuth, RuleCore.RuleSet.checkAuth_eq_ok_iff, Doc.checkAuth_eq_some_iff,
    RuleCore.RuleSet.checkSigners_ok_iff]
  have hchosen : a.denote.chosen = (a.contexts.zip a.choices).map fun x => (x.1, x.2.toNat) := by
    simp [RuleCore.Authorization.chosen, Chain.Authorization.denote, List.zip_map_right]
  have hlen : (d.lowerRules acct gen ++ d.recoveryRules acct).denote.rules.length =
      d.installed.length := by
    rw [Chain.RuleSet.rules_denote, List.length_map, Doc.lowerAll_eq_map, List.length_map]
  rw [hchosen, hlen, ← Doc.foldlM_charge_lower d acct gen a.now.toNat]
  simp only [Chain.Authorization.denote, List.length_map, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Doc.checkChoice_lower hv, Doc.signerChosen_lower]
  simp only [toOption_eq_some]

/-- Compile soundness through `checkAuth`: on every authorization, the admin
document's lowering accepts exactly when the document accepts with the
recovery controller's check read as `applyDocCheck`, with the same records. -/
theorem Doc.lower_checkAuth {d : Doc} (hv : d.Valid) (acct : Bytes)
    (records : List RuleCore.Cap.Record) (a : Chain.Authorization) :
    ((d.lower acct).checkAuth records a).toOption =
      d.checkAuth acct applyDocCheck none records a :=
  Doc.checkAuth_lowerAll hv acct none records a

/-- A document that configures no recovery never reads the controller's
check. -/
theorem Doc.checkAuth_of_recovery_none {d : Doc} (hr : d.recovery = none) (acct : Bytes)
    (ctl ctl' : Context → List Signer → Bool) (issued : Option UInt64)
    (records : List RuleCore.Cap.Record) (a : Chain.Authorization) :
    d.checkAuth acct ctl issued records a = d.checkAuth acct ctl' issued records a := by
  have hv : ∀ x, d.validates acct ctl issued a x = d.validates acct ctl' issued a x := by
    intro x
    simp only [Doc.validates]
    cases hj : d.installed[x.2.toNat]? with
    | none => rfl
    | some i =>
      cases i with
      | rule r => rfl
      | recovery =>
        have hm := List.mem_of_getElem? hj
        simp [Doc.installed, hr] at hm
  have hv' : d.validates acct ctl issued a = d.validates acct ctl' issued a := funext hv
  simp only [Doc.checkAuth, hv']

/-- With no recovery configured, the admin document's lowering accepts exactly
what the document accepts, whatever the controller's check, with the same
records. -/
theorem Doc.lower_checkAuth_of_recovery_none {d : Doc} (hv : d.Valid) (hr : d.recovery = none)
    (acct : Bytes) (ctl : Context → List Signer → Bool) (records : List RuleCore.Cap.Record)
    (a : Chain.Authorization) :
    ((d.lower acct).checkAuth records a).toOption = d.checkAuth acct ctl none records a := by
  rw [Doc.lower_checkAuth hv, Doc.checkAuth_of_recovery_none hr]

/-- The document's acceptance only grows with the controller's check. -/
theorem Doc.checkAuth_mono {d : Doc} {acct : Bytes} {ctl ctl' : Context → List Signer → Bool}
    (hctl : ∀ c auth, ctl c auth = true → ctl' c auth = true) {issued : Option UInt64}
    {records records' : List RuleCore.Cap.Record} {a : Chain.Authorization}
    (h : d.checkAuth acct ctl issued records a = some records') :
    d.checkAuth acct ctl' issued records a = some records' := by
  rw [Doc.checkAuth_eq_some_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, fun x hx => ?_, h4, h5⟩
  have := h3 x hx
  simp only [Doc.validates] at this ⊢
  cases hj : d.installed[x.2.toNat]? with
  | none => rw [hj] at this; exact this
  | some i =>
    rw [hj] at this
    cases i with
    | rule r => exact this
    | recovery =>
      simp only [Bool.and_eq_true] at this ⊢
      exact ⟨this.1, hctl _ _ this.2⟩

/-- The recovery rule over-approximates: every authorization the document
accepts under a recovery controller whose check accepts only calls to
`apply_doc`, the admin document's lowering accepts, with the same records. -/
theorem Doc.lower_checkAuth_of_check {d : Doc} (hv : d.Valid) {acct : Bytes}
    {ctl : Context → List Signer → Bool}
    (hctl : ∀ c auth, ctl c auth = true → applyDocCheck c auth = true)
    {records records' : List RuleCore.Cap.Record} {a : Chain.Authorization}
    (h : d.checkAuth acct ctl none records a = some records') :
    (d.lower acct).checkAuth records a = .ok records' := by
  have := Doc.lower_checkAuth hv acct records a
  rw [Doc.checkAuth_mono hctl h] at this
  cases e : (d.lower acct).checkAuth records a with
  | ok r => rw [e] at this; cases this; rfl
  | error err => rw [e] at this; cases this

/-! ## Former names

The names these theorems had before the evaluator's entry point was renamed
`check_auth`, kept so that citations of them still resolve. -/

@[deprecated Doc.checkAuth_eq_some_iff (since := "2026-11-08")]
theorem Doc.authorize_eq_some_iff : type_of% @Doc.checkAuth_eq_some_iff := @Doc.checkAuth_eq_some_iff

@[deprecated Doc.checkAuth_lowerAll (since := "2026-11-08")]
theorem Doc.authorize_lowerAll : type_of% @Doc.checkAuth_lowerAll := @Doc.checkAuth_lowerAll

@[deprecated Doc.lower_checkAuth (since := "2026-11-08")]
theorem Doc.lower_authorize : type_of% @Doc.lower_checkAuth := @Doc.lower_checkAuth

@[deprecated Doc.checkAuth_of_recovery_none (since := "2026-11-08")]
theorem Doc.authorize_of_recovery_none : type_of% @Doc.checkAuth_of_recovery_none := @Doc.checkAuth_of_recovery_none

@[deprecated Doc.lower_checkAuth_of_recovery_none (since := "2026-11-08")]
theorem Doc.lower_authorize_of_recovery_none : type_of% @Doc.lower_checkAuth_of_recovery_none := @Doc.lower_checkAuth_of_recovery_none

@[deprecated Doc.checkAuth_mono (since := "2026-11-08")]
theorem Doc.authorize_mono : type_of% @Doc.checkAuth_mono := @Doc.checkAuth_mono

@[deprecated Doc.lower_checkAuth_of_check (since := "2026-11-08")]
theorem Doc.lower_authorize_of_check : type_of% @Doc.lower_checkAuth_of_check := @Doc.lower_checkAuth_of_check

end RuleCore.Document
