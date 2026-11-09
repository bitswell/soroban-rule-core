import RuleCore.Vocab.Chain
import RuleCore.Theorems.Authorize
import RuleCore.Theorems.Bytes

/-!
# Chain vocabulary: theorems

Evaluation:

* `Rule.allows_call_iff`, `Rule.allows_iff`, `RuleSet.allows_iff`,
  `RuleSet.allowsAll_iff`: what each verdict means in the vocabulary's terms.

Signers:

* `Rule.signed_iff`, `Rule.mem_present`: the signer requirement holds exactly
  when at least `threshold` distinct rule signers are authenticated, a signer
  counting only when exactly that signer is.
* `Signer.delegated_ne_external`, `Signer.delegated_eq_iff`,
  `Signer.external_eq_iff`, `Signer.delegated_append_ne`: signers compare
  exactly, constructor first, with no prefix or extension match.
* `Rule.signed_of_threshold_zero`, `Rule.allows_of_threshold_zero`: threshold
  0 is no signer requirement.
* `Rule.signed_iff_of_threshold_eq`: a threshold equal to the number of
  distinct signers requires all of them.
* `Rule.allows_false_of_lt`: a threshold above the number of distinct signers
  allows nothing.
* `Rule.allows_of_subset`, `RuleSet.allows_of_subset`,
  `RuleSet.allowsAll_of_subset`: authenticating more signers never turns an
  allow into a refusal.
* `RuleSet.allows_congr`, `RuleSet.allowsAll_congr`, `RuleSet.allows_eraseDups`,
  `Rule.allows_congr_signers`, `Rule.allows_eraseDups_signers`: repeats and
  order in either signer list do not change the verdict.

Contract creation:

* `Rule.allows_create`, `RuleSet.allows_create`: no rule and no rule set
  allows a contract creation.
* `RuleSet.allowsAll_false_of_create_mem`: a batch containing a creation is
  denied.

Arguments:

* `Cond.argEq_holds_iff`, `Cond.argI128AtMost_holds_iff`,
  `Cond.argIn_holds_iff`, `Cond.argStrPrefix_holds_iff`: what each condition
  means; `Cond.argIn_holds_iff_argEq`: `argIn` compares as `argEq` does.
* `Cond.holds_false_of_length_le`: a condition on a missing argument is false.
* `Val.ne_of_kind_ne`, `Val.string_ne_symbol`: values of different
  constructors are never equal; a string is never a symbol.
* `Cond.argEq_kind`, `Cond.argStrPrefix_kind`: `argEq` holds only for an
  argument of the same constructor, and `argStrPrefix` only for a string.
* `Cond.argEq_false_of_kind_ne`, `Cond.argEq_bytes_false_of_other`,
  `Cond.argEq_string_false_of_symbol`, `Cond.argStrPrefix_false_of_kind_ne`,
  `Cond.argStrPrefix_false_of_symbol`: an argument of another constructor fails
  `argEq` and `argStrPrefix`, whatever its payload.

Byte strings (with `RuleCore.Bytes.eq_iff`):

* `Rule.contract_eq_of_allows`: a rule allows only calls to exactly its
  contract and exactly one of its functions.
* `Rule.allows_false_of_functions_nil`: a rule with an empty function list
  allows nothing.
* `Rule.allows_call_any`: the wildcard matches every function of the rule's
  contract.
* `Rule.allows_extension_false`, `Rule.allows_prefix_false`: a call to a
  proper extension or a proper prefix of the rule's contract id is denied.

Attenuation:

* `RuleSet.rules_denote`: a rule set denotes the list of its rules' denotations.
* `Rule.denote_addCond`, `Rule.denote_removeFunctions`,
  `Rule.denote_restrictFunctions`, `Rule.denote_removeSigners`,
  `RuleSet.denote_modifyRule`, `RuleSet.denote_dropRule`,
  `RuleSet.denote_addCond`, `RuleSet.denote_removeFunctions`,
  `RuleSet.denote_restrictFunctions`, `RuleSet.denote_removeSigners`,
  `RuleSet.denote_raiseThreshold`, `RuleSet.denote_addCap`,
  `RuleSet.denote_lowerCapLimit`, `RuleSet.denote_lengthenCapPeriod`,
  `RuleSet.denote_lowerValidUntil`, `RuleSet.denote_attenuate`,
  `RuleSet.denote_attenuateAll`: each chain step, and each list of steps,
  denotes the generic step of the same kind; removing and restricting functions
  both denote restricting the scope.
* `RuleSet.dropRule_narrower`, `RuleSet.addCond_narrower`,
  `RuleSet.removeFunctions_narrower`, `RuleSet.restrictFunctions_narrower`,
  `RuleSet.removeSigners_narrower`, `RuleSet.raiseThreshold_narrower`,
  `RuleSet.addCap_narrower`, `RuleSet.lowerCapLimit_narrower`,
  `RuleSet.lengthenCapPeriod_narrower`, `RuleSet.lowerValidUntil_narrower`,
  `RuleSet.attenuate_narrower`: each step yields a narrower rule set.
* `RuleSet.narrower_refl`, `RuleSet.narrower_trans`: `narrower` is a preorder.
* `RuleSet.Derives.narrower`, `RuleSet.attenuateAll_derives`,
  `RuleSet.attenuateAll_narrower`: any chain of steps stays inside its root.
* `RuleSet.allowsAll_of_narrower`: a narrower rule set allows a batch only if
  its ancestor does.
* `Rule.mem_removeFunctions`, `Rule.mem_removeSigners`: removing `fs` or `ss`
  keeps exactly the functions or signers not in it, on a list or a wildcard
  (`Functions.mem_remove`); `Rule.mem_restrictFunctions`: restricting to `fs`
  keeps exactly the functions also in it (`Functions.mem_restrict`).
* `RuleSet.dropRule_eq_error_iff`, `RuleSet.addCond_eq_error_iff`,
  `RuleSet.removeFunctions_eq_error_iff`,
  `RuleSet.restrictFunctions_eq_error_iff`, `RuleSet.removeSigners_eq_error_iff`,
  `RuleSet.raiseThreshold_eq_noSuchRule_iff`,
  `RuleSet.lowerValidUntil_eq_noSuchRule_iff`, `RuleSet.modifyRule_eq_error_iff`:
  a step is refused with `noSuchRule` exactly when its index is not below the
  number of rules.
* `RuleSet.lowerValidUntil_eq_validUntilRaised_iff`: `lowerValidUntil` is
  refused with `validUntilRaised` exactly when the rule's last ledger is before
  the new one.
* `RuleSet.raiseThreshold_eq_thresholdLowered_iff`: `raiseThreshold` is refused
  with `thresholdLowered` exactly when the rule exists and the new threshold is
  below its current one.

Authorization:

* `RuleSet.checkAuth_allowsAll`: a rule set that accepts an authorization
  allows its batch under its signers.
* `RuleSet.checkAuth_validUntil`: an accepted authorization chooses no rule
  whose last ledger is before its ledger.
* `RuleSet.checkAuth_generation`, `RuleSet.checkAuth_not_chosen_of_stale`,
  `RuleSet.checkAuth_contexts_nil_of_stale`: it chooses no rule issued under a
  generation other than the current one, so once the current generation is not
  `g` a rule issued under `g` authorizes nothing, and a rule set issued under
  `g` accepts only an empty batch.
* `RuleSet.checkAuth_signers`: every authenticated signer is a signer of a
  chosen rule.
* `RuleSet.attenuate_generation`, `RuleSet.attenuateAll_generation`,
  `RuleSet.attenuateAll_generation_eq`: no step changes a rule's generation, so
  every rule set derived from a root issued under `g` is issued under `g`.
* `RuleSet.attenuate_traceNarrower`, `RuleSet.attenuateAll_traceNarrower`: each
  step, and every chain of steps, is narrowing as trace inclusion on the
  denotations, with the choices renumbered by the map `dropRule` induces
  (`Attenuation.source_denote_dropRule`, `Attenuation.source_denote_of_ne`).
* `RuleSet.attenuate_capsValid`, `RuleSet.attenuateAll_capsValid`: the steps
  keep every cap valid.
* `RuleSet.emptyRecords_denote`, `RuleSet.checkAuthAll_denote`: the chain's
  empty records and runs are the generic ones of the denotation.
-/

namespace RuleCore.Chain

/-! ## Evaluation -/

theorem Rule.signed_iff (r : Rule) (auth : List Signer) :
    r.signed auth = true ↔ r.threshold.toNat ≤ (r.signers.eraseDups.filter (· ∈ auth)).length :=
  RuleCore.Rule.signed_iff r.denote auth

theorem Rule.allows_call_iff (r : Rule) (contract function : Bytes) (args : List Val)
    (auth : List Signer) :
    r.allows (.call contract function args) auth = true ↔
      contract = r.contract ∧ function ∈ r.functions ∧
        (∀ cond ∈ r.conds, cond.holds args = true) ∧ r.signed auth = true := by
  simp [Rule.allows, Rule.signed, Rule.denote, RuleCore.Rule.allows, Rule.scope, Cond.denote,
    and_assoc]

theorem Rule.allows_iff (r : Rule) (c : Context) (auth : List Signer) :
    r.allows c auth = true ↔
      ∃ function args, c = .call r.contract function args ∧ function ∈ r.functions ∧
        (∀ cond ∈ r.conds, cond.holds args = true) ∧ r.signed auth = true := by
  cases c with
  | call contract function args =>
    rw [Rule.allows_call_iff]
    constructor
    · rintro ⟨rfl, hf, hc, hs⟩
      exact ⟨function, args, rfl, hf, hc, hs⟩
    · rintro ⟨function', args', h, hf, hc, hs⟩
      cases h
      exact ⟨rfl, hf, hc, hs⟩
  | create wasmHash =>
    simp [Rule.allows, Rule.denote, RuleCore.Rule.allows, Rule.scope]

@[simp] theorem RuleSet.rules_denote (rs : RuleSet) : rs.denote.rules = rs.map Rule.denote := rfl

theorem RuleSet.allows_iff (rs : RuleSet) (c : Context) (auth : List Signer) :
    rs.allows c auth = true ↔ ∃ r ∈ rs, r.allows c auth = true := by
  rw [RuleSet.allows, RuleCore.RuleSet.allows_iff, RuleSet.rules_denote]
  constructor
  · rintro ⟨_, hm, h⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    exact ⟨r, hr, h⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r.denote, List.mem_map_of_mem hr, h⟩

theorem RuleSet.allowsAll_iff (rs : RuleSet) (cs : List Context) (auth : List Signer) :
    rs.allowsAll cs auth = true ↔ ∀ c ∈ cs, rs.allows c auth = true :=
  RuleCore.RuleSet.allowsAll_iff _ _ _

/-! ## Signers -/

/-- A rule signer counts towards the threshold only when exactly that signer
is authenticated. -/
theorem Rule.mem_present (r : Rule) (auth : List Signer) (s : Signer) :
    s ∈ r.denote.present auth ↔ s ∈ r.signers ∧ s ∈ auth :=
  RuleCore.Rule.mem_present r.denote auth s

/-- A delegated signer is never an external one, even with the same bytes. -/
theorem Signer.delegated_ne_external (a verifier key : Bytes) :
    Signer.delegated a ≠ .external verifier key :=
  fun h => by cases h

theorem Signer.delegated_eq_iff (a b : Bytes) : Signer.delegated a = .delegated b ↔ a = b :=
  Signer.delegated.injEq a b ▸ Iff.rfl

theorem Signer.external_eq_iff (v k w l : Bytes) :
    Signer.external v k = .external w l ↔ v = w ∧ k = l :=
  Signer.external.injEq v k w l ▸ Iff.rfl

/-- No prefix match: a delegated signer is not one whose address extends its
own. -/
theorem Signer.delegated_append_ne (a : Bytes) {ext : Bytes} (h : ext ≠ []) :
    Signer.delegated (a ++ ext) ≠ .delegated a :=
  fun e => Bytes.append_ne_self h ((Signer.delegated_eq_iff _ _).mp e)

theorem Rule.signed_of_threshold_zero {r : Rule} (h : r.threshold = 0) (auth : List Signer) :
    r.signed auth = true :=
  RuleCore.Rule.signed_of_threshold_zero (r := r.denote) (by simp [Rule.denote, h]) auth

/-- With threshold 0 the verdict does not depend on the authenticated
signers. -/
theorem Rule.allows_of_threshold_zero {r : Rule} (h : r.threshold = 0) (c : Context)
    (auth auth' : List Signer) : r.allows c auth = r.allows c auth' := by
  have h0 : r.denote.threshold = 0 := by simp [Rule.denote, h]
  simp only [Rule.allows, RuleCore.Rule.allows_of_threshold_zero h0]

/-- A threshold equal to the number of distinct signers is met exactly when
every signer of the rule is authenticated. -/
theorem Rule.signed_iff_of_threshold_eq {r : Rule}
    (h : r.threshold.toNat = r.signers.eraseDups.length) (auth : List Signer) :
    r.signed auth = true ↔ ∀ s ∈ r.signers, s ∈ auth :=
  RuleCore.Rule.signed_iff_of_threshold_eq (r := r.denote) h auth

/-- A rule whose threshold is above its number of distinct signers allows
nothing. -/
theorem Rule.allows_false_of_lt {r : Rule} (h : r.signers.eraseDups.length < r.threshold.toNat)
    (c : Context) (auth : List Signer) : r.allows c auth = false :=
  RuleCore.Rule.allows_false_of_lt (r := r.denote) h c auth

theorem Rule.allows_of_subset (r : Rule) (c : Context) {auth auth' : List Signer}
    (h : auth ⊆ auth') : r.allows c auth = true → r.allows c auth' = true :=
  RuleCore.Rule.allows_of_subset r.denote c h

/-- Authenticating more signers never turns an allow into a refusal. -/
theorem RuleSet.allows_of_subset (rs : RuleSet) (c : Context) {auth auth' : List Signer}
    (h : auth ⊆ auth') : rs.allows c auth = true → rs.allows c auth' = true :=
  RuleCore.RuleSet.allows_of_subset rs.denote c h

theorem RuleSet.allowsAll_of_subset (rs : RuleSet) (cs : List Context)
    {auth auth' : List Signer} (h : auth ⊆ auth') :
    rs.allowsAll cs auth = true → rs.allowsAll cs auth' = true :=
  RuleCore.RuleSet.allowsAll_of_subset rs.denote cs h

/-- The verdict depends only on which signers are authenticated, not on their
order or repeats. -/
theorem RuleSet.allows_congr (rs : RuleSet) (c : Context) {auth auth' : List Signer}
    (h : ∀ s, s ∈ auth ↔ s ∈ auth') : rs.allows c auth = rs.allows c auth' :=
  RuleCore.RuleSet.allows_congr rs.denote c h

theorem RuleSet.allowsAll_congr (rs : RuleSet) (cs : List Context) {auth auth' : List Signer}
    (h : ∀ s, s ∈ auth ↔ s ∈ auth') : rs.allowsAll cs auth = rs.allowsAll cs auth' :=
  RuleCore.RuleSet.allowsAll_congr rs.denote cs h

theorem RuleSet.allows_eraseDups (rs : RuleSet) (c : Context) (auth : List Signer) :
    rs.allows c auth.eraseDups = rs.allows c auth :=
  RuleCore.RuleSet.allows_eraseDups rs.denote c auth

/-- The verdict depends only on which signers a rule lists, not on their order
or repeats. -/
theorem Rule.allows_congr_signers (r : Rule) {ss : List Signer}
    (h : ∀ s, s ∈ ss ↔ s ∈ r.signers) (c : Context) (auth : List Signer) :
    { r with signers := ss }.allows c auth = r.allows c auth := by
  show RuleCore.Rule.allows (Rule.denote { r with signers := ss }) c auth = r.denote.allows c auth
  exact RuleCore.Rule.allows_congr_signers (r := Rule.denote ({ r with signers := ss } : Rule))
    (r' := r.denote) rfl rfl h rfl c auth

theorem Rule.allows_eraseDups_signers (r : Rule) (c : Context) (auth : List Signer) :
    { r with signers := r.signers.eraseDups }.allows c auth = r.allows c auth :=
  r.allows_congr_signers (fun _ => List.mem_eraseDups) c auth

/-! ## Contract creation -/

@[simp] theorem Rule.allows_create (r : Rule) (wasmHash : Bytes) (auth : List Signer) :
    r.allows (.create wasmHash) auth = false := rfl

/-- No rule set allows a contract creation, whatever signers are
authenticated. -/
@[simp] theorem RuleSet.allows_create (rs : RuleSet) (wasmHash : Bytes) (auth : List Signer) :
    rs.allows (.create wasmHash) auth = false := by
  cases h : rs.allows (.create wasmHash) auth
  · rfl
  · obtain ⟨r, _, hr⟩ := (RuleSet.allows_iff _ _ _).mp h
    simp at hr

/-- A batch containing a contract creation is denied. -/
theorem RuleSet.allowsAll_false_of_create_mem (rs : RuleSet) {cs : List Context}
    {wasmHash : Bytes} (h : .create wasmHash ∈ cs) (auth : List Signer) :
    rs.allowsAll cs auth = false := by
  cases hall : rs.allowsAll cs auth
  · rfl
  · have := (RuleSet.allowsAll_iff _ _ _).mp hall _ h
    simp at this

/-! ## Arguments -/

/-- The index of the argument a condition reads. -/
def Cond.index : Cond → UInt32
  | .argEq i _ => i
  | .argI128AtMost i _ => i
  | .argIn i _ => i
  | .argStrPrefix i _ => i

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
  | argIn i vals =>
    simp only [Cond.index] at h
    simp [Cond.holds, List.getElem?_eq_none h]
  | argStrPrefix i pre =>
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

theorem Cond.argIn_holds_iff (i : UInt32) (vals args : List Val) :
    (Cond.argIn i vals).holds args = true ↔ ∃ v ∈ vals, args[i.toNat]? = some v := by
  simp only [Cond.holds]
  split <;> simp_all

/-- `argIn` compares as `argEq` does: it holds exactly when `argEq` holds for
one of its values. -/
theorem Cond.argIn_holds_iff_argEq (i : UInt32) (vals args : List Val) :
    (Cond.argIn i vals).holds args = true ↔ ∃ v ∈ vals, (Cond.argEq i v).holds args = true := by
  simp only [Cond.argIn_holds_iff, Cond.argEq_holds_iff]

theorem Cond.argStrPrefix_holds_iff (i : UInt32) (pre : Bytes) (args : List Val) :
    (Cond.argStrPrefix i pre).holds args = true ↔
      ∃ v, args[i.toNat]? = some (.string v) ∧ pre <+: v := by
  simp only [Cond.holds]
  split <;> simp_all

/-- `argStrPrefix` holds only for an argument that is a string. -/
theorem Cond.argStrPrefix_kind {i : UInt32} {pre : Bytes} {args : List Val}
    (h : (Cond.argStrPrefix i pre).holds args = true) :
    ∃ w, args[i.toNat]? = some w ∧ w.kind = .string := by
  obtain ⟨v, hv, -⟩ := (Cond.argStrPrefix_holds_iff i pre args).mp h
  exact ⟨.string v, hv, rfl⟩

/-- An argument of another constructor fails `argStrPrefix`, whatever its
payload: a symbol is not a string, even with the same bytes. -/
theorem Cond.argStrPrefix_false_of_kind_ne {i : UInt32} {pre : Bytes} {w : Val} {args : List Val}
    (hw : args[i.toNat]? = some w) (hk : w.kind ≠ .string) :
    (Cond.argStrPrefix i pre).holds args = false := by
  cases h : (Cond.argStrPrefix i pre).holds args
  · rfl
  · obtain ⟨w', hw', hk'⟩ := Cond.argStrPrefix_kind h
    rw [hw] at hw'
    cases hw'
    exact absurd hk' hk

/-- A symbol argument never satisfies `argStrPrefix`, even when its bytes start
with the prefix. -/
theorem Cond.argStrPrefix_false_of_symbol {i : UInt32} {pre v : Bytes} {args : List Val}
    (hw : args[i.toNat]? = some (.symbol v)) : (Cond.argStrPrefix i pre).holds args = false :=
  Cond.argStrPrefix_false_of_kind_ne hw (by simp [Val.kind])

/-- A string is never a symbol, even with the same bytes. -/
theorem Val.string_ne_symbol (a b : Bytes) : Val.string a ≠ .symbol b :=
  Val.ne_of_kind_ne (by simp [Val.kind])

/-- An `argEq` on a string fails on a symbol argument with the same bytes. -/
theorem Cond.argEq_string_false_of_symbol {i : UInt32} {b : Bytes} {args : List Val}
    (hw : args[i.toNat]? = some (.symbol b)) : (Cond.argEq i (.string b)).holds args = false :=
  Cond.argEq_false_of_kind_ne hw (by simp [Val.kind])

/-! ## Byte strings -/

/-- A rule allows only calls to exactly its contract and exactly one of its
functions. -/
theorem Rule.contract_eq_of_allows {r : Rule} {contract function : Bytes} {args : List Val}
    {auth : List Signer} (h : r.allows (.call contract function args) auth = true) :
    contract = r.contract ∧ function ∈ r.functions :=
  let ⟨hc, hf, _⟩ := (Rule.allows_call_iff r contract function args auth).mp h
  ⟨hc, hf⟩

/-- A rule with an empty function list allows nothing. -/
theorem Rule.allows_false_of_functions_nil {r : Rule} (h : r.functions = .only []) (c : Context)
    (auth : List Signer) : r.allows c auth = false := by
  cases ha : r.allows c auth
  · rfl
  · obtain ⟨_, _, _, hf, _⟩ := (Rule.allows_iff r c auth).mp ha
    simp [h] at hf

/-- The wildcard matches every function: a rule whose functions are
`Functions.any` allows a call to its contract exactly when its conditions and
signer requirement hold, whatever the function. -/
theorem Rule.allows_call_any {r : Rule} (h : r.functions = Functions.any)
    (function : Bytes) (args : List Val) (auth : List Signer) :
    r.allows (.call r.contract function args) auth = true ↔
      (∀ cond ∈ r.conds, cond.holds args = true) ∧ r.signed auth = true := by
  rw [Rule.allows_call_iff]
  simp [h, Functions.any]

/-- No prefix match: a call to a proper extension of the rule's contract id is
denied. -/
theorem Rule.allows_extension_false (r : Rule) {ext : Bytes} (h : ext ≠ [])
    (function : Bytes) (args : List Val) (auth : List Signer) :
    r.allows (.call (r.contract ++ ext) function args) auth = false := by
  cases ha : r.allows (.call (r.contract ++ ext) function args) auth
  · rfl
  · exact absurd (Rule.contract_eq_of_allows ha).1 (Bytes.append_ne_self h)

/-- A call to a proper prefix of the rule's contract id is denied. -/
theorem Rule.allows_prefix_false (r : Rule) {contract ext : Bytes}
    (hp : contract ++ ext = r.contract) (h : ext ≠ []) (function : Bytes) (args : List Val)
    (auth : List Signer) : r.allows (.call contract function args) auth = false := by
  cases ha : r.allows (.call contract function args) auth
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

theorem Functions.mem_remove (fs : Functions) (gs : List Bytes) (f : Bytes) :
    f ∈ fs.remove gs ↔ f ∈ fs ∧ f ∉ gs := by
  cases fs <;> simp [Functions.remove, not_or]

theorem Functions.mem_restrict (fs : Functions) (gs : List Bytes) (f : Bytes) :
    f ∈ fs.restrict gs ↔ f ∈ fs ∧ f ∈ gs := by
  cases fs <;> simp [Functions.restrict, and_comm]

@[simp] theorem Functions.mem_any (f : Bytes) : f ∈ Functions.any := by
  simp [Functions.any]

theorem Rule.mem_removeFunctions (r : Rule) (fs : List Bytes) (f : Bytes) :
    f ∈ (r.removeFunctions fs).functions ↔ f ∈ r.functions ∧ f ∉ fs :=
  Functions.mem_remove r.functions fs f

theorem Rule.mem_restrictFunctions (r : Rule) (fs : List Bytes) (f : Bytes) :
    f ∈ (r.restrictFunctions fs).functions ↔ f ∈ r.functions ∧ f ∈ fs :=
  Functions.mem_restrict r.functions fs f

theorem Rule.denote_removeFunctions (r : Rule) (fs : List Bytes) :
    (r.removeFunctions fs).denote = r.denote.restrictScope (notCalling fs) := by
  simp only [Rule.denote, RuleCore.Rule.restrictScope, RuleCore.Rule.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext c
  cases c with
  | call contract function args =>
    have := Rule.mem_removeFunctions r fs function
    by_cases hm : function ∈ (r.removeFunctions fs).functions <;>
      simp_all [Rule.scope, notCalling, Bool.and_assoc] <;> rfl
  | create wasmHash => rfl

theorem Rule.denote_restrictFunctions (r : Rule) (fs : List Bytes) :
    (r.restrictFunctions fs).denote = r.denote.restrictScope (calling fs) := by
  simp only [Rule.denote, RuleCore.Rule.restrictScope, RuleCore.Rule.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext c
  cases c with
  | call contract function args =>
    have := Rule.mem_restrictFunctions r fs function
    by_cases hm : function ∈ (r.restrictFunctions fs).functions <;>
      simp_all [Rule.scope, calling, Bool.and_assoc] <;> rfl
  | create wasmHash => simp [Rule.scope, calling]

theorem Rule.mem_removeSigners (r : Rule) (ss : List Signer) (s : Signer) :
    s ∈ (r.removeSigners ss).signers ↔ s ∈ r.signers ∧ s ∉ ss := by
  simp [Rule.removeSigners]

theorem Rule.denote_removeSigners (r : Rule) (ss : List Signer) :
    (r.removeSigners ss).denote = r.denote.removeSigners ss := rfl

theorem RuleSet.denote_modifyRule (rs : RuleSet) (i : Nat) (f : Rule → Rule)
    (g : RuleCore.Rule Context Signer → RuleCore.Rule Context Signer)
    (hfg : ∀ r, (f r).denote = g r.denote) :
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

theorem RuleSet.denote_restrictFunctions (rs : RuleSet) (i : UInt32) (fs : List Bytes) :
    (rs.restrictFunctions i fs).map RuleSet.denote =
      rs.denote.restrictScope i.toNat (calling fs) :=
  RuleSet.denote_modifyRule rs i.toNat _ _ (fun r => Rule.denote_restrictFunctions r fs)

theorem RuleSet.denote_removeSigners (rs : RuleSet) (i : UInt32) (ss : List Signer) :
    (rs.removeSigners i ss).map RuleSet.denote = rs.denote.removeSigners i.toNat ss :=
  RuleSet.denote_modifyRule rs i.toNat _ _ (fun r => Rule.denote_removeSigners r ss)

theorem RuleSet.denote_raiseThreshold (rs : RuleSet) (i k : UInt32) :
    (rs.raiseThreshold i k).map RuleSet.denote = rs.denote.raiseThreshold i.toNat k.toNat := by
  unfold RuleSet.raiseThreshold RuleCore.RuleSet.raiseThreshold
  simp only [RuleSet.rules_denote, List.getElem?_map]
  cases h : rs[i.toNat]? with
  | none => rfl
  | some r =>
    have hlt : (k < r.threshold) = (k.toNat < r.denote.threshold) := by
      simp [Rule.denote, UInt32.lt_iff_toNat_lt]
    simp only [Option.map_some, hlt]
    split
    · rfl
    · simp only [Except.map, RuleSet.denote, List.map_set, Rule.denote]
      rfl

theorem Cap.valid_denote (k : Cap) : k.denote.params.valid = k.valid := rfl

theorem RuleSet.denote_addCap (rs : RuleSet) (i : UInt32) (k : Cap) :
    (rs.addCap i k).map RuleSet.denote = rs.denote.addCap i.toNat k.denote := by
  unfold RuleSet.addCap RuleCore.RuleSet.addCap
  simp only [RuleSet.rules_denote, List.getElem?_map]
  cases h : rs[i.toNat]? with
  | none => rfl
  | some r =>
    simp only [Option.map_some]
    cases hc : r.cap with
    | some k' => simp [Rule.denote, hc, Except.map]
    | none =>
      have hd : r.denote.cap = none := by simp [Rule.denote, hc]
      simp only [hd, Cap.valid_denote]
      by_cases hv : k.valid = true
      · simp only [hv, ↓reduceIte, Except.map, RuleSet.denote, List.map_set, Rule.denote]
        rfl
      · simp [hv, Except.map]

theorem RuleSet.denote_lowerCapLimit (rs : RuleSet) (i : UInt32) (limit : I128) :
    (rs.lowerCapLimit i limit).map RuleSet.denote = rs.denote.lowerCapLimit i.toNat limit.toInt := by
  unfold RuleSet.lowerCapLimit RuleCore.RuleSet.lowerCapLimit
  simp only [RuleSet.rules_denote, List.getElem?_map]
  cases h : rs[i.toNat]? with
  | none => rfl
  | some r =>
    simp only [Option.map_some]
    cases hc : r.cap with
    | none => simp [Rule.denote, hc, Except.map]
    | some k =>
      have hd : r.denote.cap = some k.denote := by simp [Rule.denote, hc]
      simp only [hd]
      have hl : k.denote.params.limit = k.limit.toInt := rfl
      simp only [hl]
      by_cases h₁ : k.limit.toInt < limit.toInt
      · simp [h₁, Except.map]
      · by_cases h₂ : limit.toInt ≤ 0
        · simp [h₁, h₂, Except.map]
        · simp only [h₁, h₂, ↓reduceIte, Except.map, RuleSet.denote, List.map_set, Rule.denote]
          rfl

theorem RuleSet.denote_lengthenCapPeriod (rs : RuleSet) (i period : UInt32) :
    (rs.lengthenCapPeriod i period).map RuleSet.denote =
      rs.denote.lengthenCapPeriod i.toNat period.toNat := by
  unfold RuleSet.lengthenCapPeriod RuleCore.RuleSet.lengthenCapPeriod
  simp only [RuleSet.rules_denote, List.getElem?_map]
  cases h : rs[i.toNat]? with
  | none => rfl
  | some r =>
    simp only [Option.map_some]
    cases hc : r.cap with
    | none => simp [Rule.denote, hc, Except.map]
    | some k =>
      have hd : r.denote.cap = some k.denote := by simp [Rule.denote, hc]
      simp only [hd]
      have hlt : (period < k.period) = (period.toNat < k.denote.params.period) := by
        simp [Cap.denote, Cap.params, UInt32.lt_iff_toNat_lt]
      simp only [hlt]
      by_cases h₁ : period.toNat < k.denote.params.period
      · simp [h₁, Except.map]
      · simp only [h₁, ↓reduceIte, Except.map, RuleSet.denote, List.map_set, Rule.denote]
        rfl

theorem RuleSet.denote_lowerValidUntil (rs : RuleSet) (i v : UInt32) :
    (rs.lowerValidUntil i v).map RuleSet.denote = rs.denote.lowerValidUntil i.toNat v.toNat := by
  unfold RuleSet.lowerValidUntil RuleCore.RuleSet.lowerValidUntil
  simp only [RuleSet.rules_denote, List.getElem?_map]
  cases h : rs[i.toNat]? with
  | none => rfl
  | some r =>
    simp only [Option.map_some]
    cases hv : r.validUntil with
    | none =>
      have hd : r.denote.validUntil = none := by simp [Rule.denote, hv]
      simp only [hd]
      simp only [Except.map, RuleSet.denote, List.map_set, Rule.denote]
      rfl
    | some last =>
      have hd : r.denote.validUntil = some last.toNat := by simp [Rule.denote, hv]
      simp only [hd]
      have hlt : (last < v) = (last.toNat < v.toNat) := by simp [UInt32.lt_iff_toNat_lt]
      simp only [hlt]
      by_cases h₁ : last.toNat < v.toNat
      · simp [h₁, Except.map]
      · simp only [h₁, ↓reduceIte, Except.map, RuleSet.denote, List.map_set, Rule.denote]
        rfl

theorem RuleSet.denote_attenuate (rs : RuleSet) (a : Attenuation) :
    (rs.attenuate a).map RuleSet.denote = rs.denote.attenuate a.denote := by
  cases a with
  | dropRule i => exact RuleSet.denote_dropRule rs i
  | addCond i cond => exact RuleSet.denote_addCond rs i cond
  | removeFunctions i fs => exact RuleSet.denote_removeFunctions rs i fs
  | restrictFunctions i fs => exact RuleSet.denote_restrictFunctions rs i fs
  | removeSigners i ss => exact RuleSet.denote_removeSigners rs i ss
  | raiseThreshold i k => exact RuleSet.denote_raiseThreshold rs i k
  | addCap i k => exact RuleSet.denote_addCap rs i k
  | lowerCapLimit i limit => exact RuleSet.denote_lowerCapLimit rs i limit
  | lengthenCapPeriod i period => exact RuleSet.denote_lengthenCapPeriod rs i period
  | lowerValidUntil i v => exact RuleSet.denote_lowerValidUntil rs i v

theorem RuleSet.denote_attenuateAll :
    ∀ (rs : RuleSet) (steps : List Attenuation),
      (rs.attenuateAll steps).map RuleSet.denote =
        rs.denote.attenuateAll (steps.map Attenuation.denote)
  | rs, [] => rfl
  | rs, a :: steps => by
    simp only [RuleSet.attenuateAll, RuleCore.RuleSet.attenuateAll, List.map_cons,
      List.foldlM_cons] at *
    have hd := RuleSet.denote_attenuate rs a
    cases ha : rs.attenuate a with
    | error e =>
      rw [ha] at hd
      rw [← hd]
      rfl
    | ok rs₁ =>
      rw [ha] at hd
      rw [← hd]
      exact RuleSet.denote_attenuateAll rs₁ steps

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

theorem RuleSet.restrictFunctions_narrower {rs rs' : RuleSet} {i : UInt32} {fs : List Bytes}
    (h : rs.restrictFunctions i fs = .ok rs') : rs'.narrower rs :=
  RuleSet.attenuate_narrower (a := .restrictFunctions i fs) h

theorem RuleSet.lowerValidUntil_narrower {rs rs' : RuleSet} {i v : UInt32}
    (h : rs.lowerValidUntil i v = .ok rs') : rs'.narrower rs :=
  RuleSet.attenuate_narrower (a := .lowerValidUntil i v) h

theorem RuleSet.removeSigners_narrower {rs rs' : RuleSet} {i : UInt32} {ss : List Signer}
    (h : rs.removeSigners i ss = .ok rs') : rs'.narrower rs :=
  RuleSet.attenuate_narrower (a := .removeSigners i ss) h

theorem RuleSet.raiseThreshold_narrower {rs rs' : RuleSet} {i k : UInt32}
    (h : rs.raiseThreshold i k = .ok rs') : rs'.narrower rs :=
  RuleSet.attenuate_narrower (a := .raiseThreshold i k) h

theorem RuleSet.addCap_narrower {rs rs' : RuleSet} {i : UInt32} {k : Cap}
    (h : rs.addCap i k = .ok rs') : rs'.narrower rs :=
  RuleSet.attenuate_narrower (a := .addCap i k) h

theorem RuleSet.lowerCapLimit_narrower {rs rs' : RuleSet} {i : UInt32} {limit : I128}
    (h : rs.lowerCapLimit i limit = .ok rs') : rs'.narrower rs :=
  RuleSet.attenuate_narrower (a := .lowerCapLimit i limit) h

theorem RuleSet.lengthenCapPeriod_narrower {rs rs' : RuleSet} {i period : UInt32}
    (h : rs.lengthenCapPeriod i period = .ok rs') : rs'.narrower rs :=
  RuleSet.attenuate_narrower (a := .lengthenCapPeriod i period) h

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
    (cs : List Context) (auth : List Signer) :
    rs'.allowsAll cs auth = true → rs.allowsAll cs auth = true :=
  RuleCore.RuleSet.allowsAll_of_narrower h cs auth

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

theorem RuleSet.restrictFunctions_eq_error_iff (rs : RuleSet) (i : UInt32) (fs : List Bytes) :
    rs.restrictFunctions i fs = .error .noSuchRule ↔ rs.length ≤ i.toNat :=
  RuleSet.modifyRule_eq_error_iff rs i.toNat _

theorem RuleSet.lowerValidUntil_eq_noSuchRule_iff (rs : RuleSet) (i v : UInt32) :
    rs.lowerValidUntil i v = .error .noSuchRule ↔ rs.length ≤ i.toNat := by
  unfold RuleSet.lowerValidUntil
  split <;> rename_i h
  · have hi := (List.getElem?_eq_some_iff.mp h).1
    constructor
    · intro he
      split at he
      · split at he <;> cases he
      · cases he
    · intro hle
      exact absurd hi (Nat.not_lt.mpr hle)
  · simp only [true_iff]
    exact List.getElem?_eq_none_iff.mp h

/-- `lowerValidUntil` refuses to move a last ledger later, and refuses nothing
else with `validUntilRaised`. -/
theorem RuleSet.lowerValidUntil_eq_validUntilRaised_iff (rs : RuleSet) (i v : UInt32) :
    rs.lowerValidUntil i v = .error .validUntilRaised ↔
      ∃ r last, rs[i.toNat]? = some r ∧ r.validUntil = some last ∧ last < v := by
  unfold RuleSet.lowerValidUntil
  split <;> rename_i h
  · split <;> rename_i hc
    · split <;> rename_i hp <;> simp [h, hc, hp]
    · simp [h, hc]
  · simp [h]

theorem RuleSet.removeSigners_eq_error_iff (rs : RuleSet) (i : UInt32) (ss : List Signer) :
    rs.removeSigners i ss = .error .noSuchRule ↔ rs.length ≤ i.toNat :=
  RuleSet.modifyRule_eq_error_iff rs i.toNat _

theorem RuleSet.raiseThreshold_eq_noSuchRule_iff (rs : RuleSet) (i k : UInt32) :
    rs.raiseThreshold i k = .error .noSuchRule ↔ rs.length ≤ i.toNat := by
  unfold RuleSet.raiseThreshold
  split <;> rename_i h
  · have hi := (List.getElem?_eq_some_iff.mp h).1
    constructor
    · intro he
      split at he <;> cases he
    · intro hle
      exact absurd hi (Nat.not_lt.mpr hle)
  · simp only [true_iff]
    exact List.getElem?_eq_none_iff.mp h

/-- `raiseThreshold` refuses to lower a threshold, and refuses nothing else
with `thresholdLowered`. -/
theorem RuleSet.raiseThreshold_eq_thresholdLowered_iff (rs : RuleSet) (i k : UInt32) :
    rs.raiseThreshold i k = .error .thresholdLowered ↔
      ∃ r, rs[i.toNat]? = some r ∧ k < r.threshold := by
  unfold RuleSet.raiseThreshold
  split <;> rename_i h
  · split <;> rename_i hk
    · simp [h, hk]
    · simp [h, hk]
  · simp [h]

/-! ## Authorization -/

theorem RuleSet.emptyRecords_denote (rs : RuleSet) : rs.denote.emptyRecords = rs.emptyRecords := by
  simp [RuleCore.RuleSet.emptyRecords, RuleSet.emptyRecords, RuleSet.rules_denote]

theorem RuleSet.checkAuthAll_denote (rs : RuleSet) (records : List RuleCore.Cap.Record)
    (as : List Authorization) :
    rs.checkAuthAll records as = rs.denote.checkAuthAll records (as.map Authorization.denote) := by
  simp only [RuleSet.checkAuthAll, RuleCore.RuleSet.checkAuthAll]
  induction as generalizing records with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldlM_cons, List.map_cons]
    have hd : rs.denote.checkAuth records a.denote = rs.checkAuth records a := rfl
    rw [hd]
    cases rs.checkAuth records a with
    | error e => rfl
    | ok r => exact ih r

/-- Soundness of the stateful check: a rule set that accepts an authorization
allows its whole batch under its signers. -/
theorem RuleSet.checkAuth_allowsAll {rs : RuleSet} {records records' : List RuleCore.Cap.Record}
    {a : Authorization} (h : rs.checkAuth records a = .ok records') :
    rs.allowsAll a.contexts a.auth = true :=
  RuleCore.RuleSet.checkAuth_allowsAll h

theorem RuleSet.denote_get (rs : RuleSet) (j : Nat) :
    rs.denote.rules[j]? = rs[j]?.map Rule.denote := by
  simp [RuleSet.rules_denote, List.getElem?_map]

/-- Expiry: an accepted authorization chooses no rule whose last ledger is
before the authorization's ledger. -/
theorem RuleSet.checkAuth_validUntil {rs : RuleSet} {records records' : List RuleCore.Cap.Record}
    {a : Authorization} (h : rs.checkAuth records a = .ok records') {j : UInt32}
    (hj : j ∈ a.choices) {r : Rule} (hr : rs[j.toNat]? = some r) {last : UInt32}
    (hl : r.validUntil = some last) : a.now ≤ last := by
  have := RuleCore.RuleSet.checkAuth_validUntil (a := a.denote) h (j := j.toNat)
    (by simpa [Authorization.denote] using List.mem_map_of_mem (f := (·.toNat)) hj)
    (r := r.denote) (by simp [hr]) (last := last.toNat)
    (by simp [Rule.denote, hl])
  simpa [Authorization.denote, UInt32.le_iff_toNat_le] using this

/-- Generation: an accepted authorization chooses no rule issued under a
generation other than the current one. -/
theorem RuleSet.checkAuth_generation {rs : RuleSet} {records records' : List RuleCore.Cap.Record}
    {a : Authorization} (h : rs.checkAuth records a = .ok records') {j : UInt32}
    (hj : j ∈ a.choices) {r : Rule} (hr : rs[j.toNat]? = some r) {g : UInt64}
    (hg : r.generation = some g) : g = a.generation := by
  have := RuleCore.RuleSet.checkAuth_generation (a := a.denote) h (j := j.toNat)
    (by simpa [Authorization.denote] using List.mem_map_of_mem (f := (·.toNat)) hj)
    (r := r.denote) (by simp [hr]) (g := g.toNat)
    (by simp [Rule.denote, hg])
  exact UInt64.toNat_inj.mp (by simpa [Authorization.denote] using this)

/-- Once the current generation is not `g`, a rule issued under `g` authorizes
nothing: no accepted authorization chooses it. -/
theorem RuleSet.checkAuth_not_chosen_of_stale {rs : RuleSet}
    {records records' : List RuleCore.Cap.Record} {a : Authorization}
    (h : rs.checkAuth records a = .ok records') {j : UInt32} {r : Rule}
    (hr : rs[j.toNat]? = some r) {g : UInt64} (hg : r.generation = some g)
    (hne : g ≠ a.generation) : j ∉ a.choices :=
  fun hj => hne (RuleSet.checkAuth_generation h hj hr hg)

/-- A rule set every rule of which was issued under `g` accepts, once the
current generation is not `g`, only an authorization with no contexts. -/
theorem RuleSet.checkAuth_contexts_nil_of_stale {rs : RuleSet}
    {records records' : List RuleCore.Cap.Record} {a : Authorization}
    (h : rs.checkAuth records a = .ok records') {g : UInt64}
    (hall : ∀ r ∈ rs, r.generation = some g) (hne : g ≠ a.generation) : a.contexts = [] := by
  have := RuleCore.RuleSet.checkAuth_contexts_nil_of_stale (a := a.denote) h (g := g.toNat)
    (by
      intro r hr
      rw [RuleSet.rules_denote, List.mem_map] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := hr
      simp [Rule.denote, hall r₀ hr₀])
    (by
      intro he
      exact hne (UInt64.toNat_inj.mp (by simpa [Authorization.denote] using he)))
  simpa [Authorization.denote] using this

/-- Signers: every signer an accepted authorization authenticated is a signer
of some rule it chose. -/
theorem RuleSet.checkAuth_signers {rs : RuleSet} {records records' : List RuleCore.Cap.Record}
    {a : Authorization} (h : rs.checkAuth records a = .ok records') :
    ∀ s ∈ a.auth, ∃ j ∈ a.choices, ∃ r, rs[j.toNat]? = some r ∧ s ∈ r.signers := by
  intro s hs
  obtain ⟨j, hj, r, hr, hsr⟩ := RuleCore.RuleSet.checkAuth_signers (a := a.denote) h s hs
  simp only [Authorization.denote, List.mem_map] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  rw [RuleSet.denote_get] at hr
  cases hk' : rs[k.toNat]? with
  | none => rw [hk'] at hr; cases hr
  | some r₀ =>
    rw [hk'] at hr
    cases hr
    exact ⟨k, hk, r₀, hk', hsr⟩

/-- No chain step changes a rule's generation: each rule after a step carries
the generation of the rule it comes from. -/
theorem RuleSet.attenuate_generation {rs rs' : RuleSet} {a : Attenuation}
    (h : rs.attenuate a = .ok rs') {j : Nat} {r' : Rule} (hj : rs'[j]? = some r') :
    ∃ r, rs[a.denote.source j]? = some r ∧ r'.generation = r.generation := by
  have hd := RuleSet.denote_attenuate rs a
  rw [h] at hd
  obtain ⟨r, hr, hg⟩ := RuleCore.RuleSet.attenuate_generation hd.symm
    (j := j) (r' := r'.denote) (by simp [hj])
  rw [RuleSet.denote_get] at hr
  cases hr₀ : rs[a.denote.source j]? with
  | none => rw [hr₀] at hr; cases hr
  | some r₀ =>
    rw [hr₀] at hr
    cases hr
    refine ⟨r₀, rfl, ?_⟩
    simp only [Rule.denote] at hg
    exact Option.map_injective (fun _ _ e => UInt64.toNat_inj.mp e) hg

/-- Each rule at the end of a chain of steps carries the generation of the
root rule it comes from. -/
theorem RuleSet.attenuateAll_generation {root rs : RuleSet} {steps : List Attenuation}
    (h : root.attenuateAll steps = .ok rs) {j : Nat} {r' : Rule} (hj : rs[j]? = some r') :
    ∃ r, root[Attenuation.chainSource steps j]? = some r ∧ r'.generation = r.generation := by
  have hd := RuleSet.denote_attenuateAll root steps
  rw [h] at hd
  obtain ⟨r, hr, hg⟩ := RuleCore.RuleSet.attenuateAll_generation hd.symm
    (j := j) (r' := r'.denote) (by simp [hj])
  have hcs : RuleCore.Attenuation.chainSource (steps.map Attenuation.denote) j =
      Attenuation.chainSource steps j := rfl
  rw [RuleSet.denote_get, hcs] at hr
  cases hr₀ : root[Attenuation.chainSource steps j]? with
  | none =>
    rw [hr₀] at hr
    cases hr
  | some r₀ =>
    rw [hr₀] at hr
    cases hr
    refine ⟨r₀, rfl, ?_⟩
    simp only [Rule.denote] at hg
    exact Option.map_injective (fun _ _ e => UInt64.toNat_inj.mp e) hg

/-- A rule set derived by a chain of steps from a root every rule of which was
issued under `g` has every rule issued under `g`: once the current generation
is not `g`, it too accepts only an empty batch. -/
theorem RuleSet.attenuateAll_generation_eq {root rs : RuleSet} {steps : List Attenuation}
    (h : root.attenuateAll steps = .ok rs) {g : UInt64}
    (hall : ∀ r ∈ root, r.generation = some g) : ∀ r ∈ rs, r.generation = some g := by
  intro r' hr'
  obtain ⟨j, hj, hjr⟩ := List.getElem_of_mem hr'
  obtain ⟨r, hr, hg⟩ := RuleSet.attenuateAll_generation h
    (List.getElem?_eq_some_iff.mpr ⟨hj, hjr⟩)
  rw [hg]
  exact hall r (List.mem_of_getElem? hr)

theorem Attenuation.source_denote_dropRule (i : UInt32) (j : Nat) :
    (Attenuation.dropRule i).denote.source j = if j < i.toNat then j else j + 1 := rfl

theorem Attenuation.source_denote_of_ne {a : Attenuation} (h : ∀ i, a ≠ .dropRule i) (j : Nat) :
    a.denote.source j = j := by
  cases a with
  | dropRule i => exact absurd rfl (h i)
  | _ => rfl

/-- Each step is narrowing as trace inclusion, with the choices renumbered by
the map the step induces. -/
theorem RuleSet.attenuate_traceNarrower {rs rs' : RuleSet} {a : Attenuation}
    (h : rs.attenuate a = .ok rs') : rs'.TraceNarrower rs a.denote.source := by
  have hd := RuleSet.denote_attenuate rs a
  rw [h] at hd
  exact RuleCore.RuleSet.attenuate_traceNarrower hd.symm

/-- Every chain of steps is narrowing as trace inclusion, with the choices
renumbered by the map the chain induces. -/
theorem RuleSet.attenuateAll_traceNarrower {root rs : RuleSet} {steps : List Attenuation}
    (h : root.attenuateAll steps = .ok rs) :
    rs.TraceNarrower root (Attenuation.chainSource steps) := by
  have hd := RuleSet.denote_attenuateAll root steps
  rw [h] at hd
  exact RuleCore.RuleSet.attenuateAll_traceNarrower hd.symm

theorem RuleSet.attenuate_capsValid {rs rs' : RuleSet} {a : Attenuation}
    (hv : rs.denote.capsValid) (h : rs.attenuate a = .ok rs') : rs'.denote.capsValid := by
  have hd := RuleSet.denote_attenuate rs a
  rw [h] at hd
  exact RuleCore.RuleSet.attenuate_capsValid hv hd.symm

theorem RuleSet.attenuateAll_capsValid {root rs : RuleSet} {steps : List Attenuation}
    (hv : root.denote.capsValid) (h : root.attenuateAll steps = .ok rs) : rs.denote.capsValid := by
  have hd := RuleSet.denote_attenuateAll root steps
  rw [h] at hd
  exact RuleCore.RuleSet.attenuateAll_capsValid hv hd.symm

/-! ## Former names

The names these theorems had before the evaluator's entry point was renamed
`check_auth`, kept so that citations of them still resolve. -/

@[deprecated RuleSet.checkAuthAll_denote (since := "2026-11-08")]
theorem RuleSet.authorizeAll_denote : type_of% @RuleSet.checkAuthAll_denote := @RuleSet.checkAuthAll_denote

@[deprecated RuleSet.checkAuth_allowsAll (since := "2026-11-08")]
theorem RuleSet.authorize_allowsAll : type_of% @RuleSet.checkAuth_allowsAll := @RuleSet.checkAuth_allowsAll

@[deprecated RuleSet.checkAuth_validUntil (since := "2026-11-08")]
theorem RuleSet.authorize_validUntil : type_of% @RuleSet.checkAuth_validUntil := @RuleSet.checkAuth_validUntil

@[deprecated RuleSet.checkAuth_generation (since := "2026-11-08")]
theorem RuleSet.authorize_generation : type_of% @RuleSet.checkAuth_generation := @RuleSet.checkAuth_generation

@[deprecated RuleSet.checkAuth_not_chosen_of_stale (since := "2026-11-08")]
theorem RuleSet.authorize_not_chosen_of_stale : type_of% @RuleSet.checkAuth_not_chosen_of_stale := @RuleSet.checkAuth_not_chosen_of_stale

@[deprecated RuleSet.checkAuth_contexts_nil_of_stale (since := "2026-11-08")]
theorem RuleSet.authorize_contexts_nil_of_stale : type_of% @RuleSet.checkAuth_contexts_nil_of_stale := @RuleSet.checkAuth_contexts_nil_of_stale

@[deprecated RuleSet.checkAuth_signers (since := "2026-11-08")]
theorem RuleSet.authorize_signers : type_of% @RuleSet.checkAuth_signers := @RuleSet.checkAuth_signers

end RuleCore.Chain
