import RuleCore.Vocab.Lowering
import RuleCore.Equiv.Denote

/-!
# Denotation of the translated document types

The functions below map the types Aeneas generates for the `document` and
`scoped` modules of `crates/rule-eval` to the document vocabulary
(`RuleCore/Vocab/Document.lean`). They are part of the specification, as
`RuleCore.Equiv.Denote`'s are, and they are structural:

* byte strings, `i128` and `u32` values, signers and rules as in
  `RuleCore.Equiv.Denote`;
* `Scope`, `Principals`, `Pred` and `ScopeError` map each constructor to the
  constructor of the same name (`SelfAdmin` to `selfAdmin`, `U32Eq` to `u32Eq`,
  `ExcludedScope` to `excludedScope`);
* `ArgConstraint`, `DocCap`, `DocRule`, `SignerDecl`, `ZkFactor`, `Recovery` and
  `Doc` map each field to the field of the same name (`period_ledgers` to
  `periodLedgers`, `not_after_ledger` to `notAfterLedger`), an optional field
  to the optional denoted value, and a vector to the list of its elements'
  denotations;
* a result of `lower_scoped` is the `Except` of the denoted rules or error.

Every denotation is injective (`denoteScope_injective`, `denotePrincipals_injective`,
`denotePred_injective`, `denoteArg_injective`, `denoteDocCap_injective`,
`denoteDocRule_injective`, `denoteDecl_injective`, `denoteZk_injective`,
`denoteRecovery_injective`, `denoteDoc_injective`, `denoteScopeError_injective`,
`denoteScoped_injective`).
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std

def denoteScope : rule_eval.document.Scope → Document.Scope
  | .Contract a => .contract (denoteBytes a)
  | .SelfAdmin => .selfAdmin

def denotePrincipals : rule_eval.document.Principals → Document.Principals
  | .All ids => .all (ids.val.map denoteBytes)
  | .Threshold ids m => .threshold (ids.val.map denoteBytes) (denoteU32 m)

def denotePred : rule_eval.document.Pred → Document.Pred
  | .IsSelf => .isSelf
  | .AddressEq a => .addressEq (denoteBytes a)
  | .StringIn values => .stringIn (values.val.map denoteBytes)
  | .StringPrefix pre => .stringPrefix (denoteBytes pre)
  | .U32Eq v => .u32Eq (denoteU32 v)

def denoteArg (c : rule_eval.document.ArgConstraint) : Document.ArgConstraint :=
  ⟨denoteU32 c.index, denotePred c.pred⟩

def denoteDocCap (k : rule_eval.document.DocCap) : Document.Cap :=
  ⟨k.limit.bv, denoteU32 k.period_ledgers⟩

def denoteDocRule (r : rule_eval.document.DocRule) : Document.Rule where
  scope := denoteScope r.scope
  principals := denotePrincipals r.principals
  functions := r.functions.map fun fs => fs.val.map denoteBytes
  args := r.args.map fun cs => cs.val.map denoteArg
  notAfterLedger := r.not_after_ledger.map denoteU32
  cap := r.cap.map denoteDocCap

def denoteDecl (s : rule_eval.document.SignerDecl) : Document.SignerDecl :=
  ⟨denoteBytes s.id, denoteSigner s.signer⟩

def denoteZk (z : rule_eval.document.ZkFactor) : Document.ZkFactor :=
  ⟨denoteBytes z.adapter, denoteBytes z.pool⟩

def denoteRecovery (rc : rule_eval.document.Recovery) : Document.Recovery :=
  ⟨denoteBytes rc.controller, rc.zk.map denoteZk⟩

def denoteDoc (d : rule_eval.document.Doc) : Document.Doc where
  signers := d.signers.val.map denoteDecl
  rules := d.rules.val.map denoteDocRule
  recovery := d.recovery.map denoteRecovery

def denoteScopeError : rule_eval.scoped.ScopeError → Document.ScopeError
  | .RecoveryConfigured => .recoveryConfigured
  | .ExcludedScope => .excludedScope

/-- What `lower_scoped` returned, as the model's outcome. -/
def denoteScoped :
    core.result.Result (alloc.vec.Vec rule_eval.rule.Rule) rule_eval.scoped.ScopeError →
      Except Document.ScopeError Chain.RuleSet
  | .Ok out => .ok (denoteRules out.val)
  | .Err e => .error (denoteScopeError e)

/-! ## Injectivity -/

theorem vec_map_inj {α β : Type} {f : α → β} (hf : Function.Injective f)
    {v w : alloc.vec.Vec α} (h : v.val.map f = w.val.map f) : v = w :=
  alloc.vec.Vec.ext _ _ ((List.map_injective_iff.mpr hf).eq_iff.mp h)

theorem denoteScope_injective : Function.Injective denoteScope := by
  intro a b h
  cases a <;> cases b <;> simp only [denoteScope, reduceCtorEq,
    Document.Scope.contract.injEq] at h <;> first
    | rfl
    | rw [denoteBytes_injective h]

theorem denotePrincipals_injective : Function.Injective denotePrincipals := by
  intro a b h
  cases a <;> cases b <;> simp only [denotePrincipals, reduceCtorEq,
    Document.Principals.all.injEq, Document.Principals.threshold.injEq] at h
  · rw [vec_map_inj denoteBytes_injective h]
  · rw [vec_map_inj denoteBytes_injective h.1, denoteU32_injective h.2]

theorem denotePred_injective : Function.Injective denotePred := by
  intro a b h
  cases a <;> cases b <;> simp only [denotePred, reduceCtorEq, Document.Pred.addressEq.injEq,
    Document.Pred.stringIn.injEq, Document.Pred.stringPrefix.injEq,
    Document.Pred.u32Eq.injEq] at h <;> first
    | rfl
    | rw [denoteBytes_injective h]
    | rw [vec_map_inj denoteBytes_injective h]
    | rw [denoteU32_injective h]

theorem denoteArg_injective : Function.Injective denoteArg := by
  intro a b h
  simp only [denoteArg, Document.ArgConstraint.mk.injEq] at h
  cases a
  cases b
  simp only [rule_eval.document.ArgConstraint.mk.injEq]
  exact ⟨denoteU32_injective h.1, denotePred_injective h.2⟩

theorem denoteDocCap_injective : Function.Injective denoteDocCap := by
  intro a b h
  simp only [denoteDocCap, Document.Cap.mk.injEq] at h
  cases a
  cases b
  simp only [rule_eval.document.DocCap.mk.injEq]
  exact ⟨i128_bv_injective h.1, denoteU32_injective h.2⟩

theorem denoteDocRule_injective : Function.Injective denoteDocRule := by
  intro a b h
  simp only [denoteDocRule, Document.Rule.mk.injEq] at h
  obtain ⟨hs, hp, hf, ha, hn, hc⟩ := h
  cases a
  cases b
  simp only [rule_eval.document.DocRule.mk.injEq]
  exact ⟨denoteScope_injective hs, denotePrincipals_injective hp,
    Option.map_injective (fun _ _ e => vec_map_inj denoteBytes_injective e) hf,
    Option.map_injective (fun _ _ e => vec_map_inj denoteArg_injective e) ha,
    Option.map_injective denoteU32_injective hn, Option.map_injective denoteDocCap_injective hc⟩

theorem denoteDecl_injective : Function.Injective denoteDecl := by
  intro a b h
  simp only [denoteDecl, Document.SignerDecl.mk.injEq] at h
  cases a
  cases b
  simp only [rule_eval.document.SignerDecl.mk.injEq]
  exact ⟨denoteBytes_injective h.1, denoteSigner_injective h.2⟩

theorem denoteZk_injective : Function.Injective denoteZk := by
  intro a b h
  simp only [denoteZk, Document.ZkFactor.mk.injEq] at h
  cases a
  cases b
  simp only [rule_eval.document.ZkFactor.mk.injEq]
  exact ⟨denoteBytes_injective h.1, denoteBytes_injective h.2⟩

theorem denoteRecovery_injective : Function.Injective denoteRecovery := by
  intro a b h
  simp only [denoteRecovery, Document.Recovery.mk.injEq] at h
  cases a
  cases b
  simp only [rule_eval.document.Recovery.mk.injEq]
  exact ⟨denoteBytes_injective h.1, Option.map_injective denoteZk_injective h.2⟩

theorem denoteDoc_injective : Function.Injective denoteDoc := by
  intro a b h
  simp only [denoteDoc, Document.Doc.mk.injEq] at h
  cases a
  cases b
  simp only [rule_eval.document.Doc.mk.injEq]
  exact ⟨vec_map_inj denoteDecl_injective h.1, vec_map_inj denoteDocRule_injective h.2.1,
    Option.map_injective denoteRecovery_injective h.2.2⟩

theorem denoteScopeError_injective : Function.Injective denoteScopeError := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

theorem denoteScoped_injective : Function.Injective denoteScoped := by
  intro a b h
  cases a with
  | Ok out =>
    cases b with
    | Ok out' =>
      simp only [denoteScoped, Except.ok.injEq] at h
      rw [alloc.vec.Vec.ext _ _ (denoteRules_injective h)]
    | Err e => simp [denoteScoped] at h
  | Err e =>
    cases b with
    | Ok out => simp [denoteScoped] at h
    | Err e' =>
      simp only [denoteScoped, Except.error.injEq] at h
      rw [denoteScopeError_injective h]

end RuleCore.Equiv
