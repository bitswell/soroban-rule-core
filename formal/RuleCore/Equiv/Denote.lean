import RuleCore.Vocab.Chain
import RuleCore.Extracted.RuleEval

/-!
# Denotation of the extracted types

The functions below map the types Aeneas generates for `crates/rule-eval`
(`RuleCore/Extracted/RuleEval.lean`) to the chain vocabulary
(`RuleCore/Vocab/Chain.lean`). They are part of the specification: the
equivalence theorems in `RuleCore.Equiv` say that the extracted functions
compute the model's functions on the denotations of their inputs.

Each is structural, constructor for constructor and field for field:

* a byte string (`Vec<u8>` or `&[u8]`, a structure over `List Std.U8`) is the
  `Bytes` of the same bytes, each `Std.U8` the `UInt8` with the same bit vector;
* an `i128` is its bit vector, a `u64` and a `u32` the `UInt64` and `UInt32`
  with the same bit vector;
* `Val`, `Context`, `Cond` and `Signer` map each constructor to the
  constructor of the same name, and `Rule` maps each field to the field of the
  same name;
* a slice or vector of rules or signers is the list of its elements'
  denotations;
* `AttenuationError::NoSuchRule` is `AttenuationError.noSuchRule` and
  `AttenuationError::ThresholdLowered` is `AttenuationError.thresholdLowered`,
  and a Rust `Result` of the attenuation steps is the `Except` with the denoted
  payload.

Every denotation is injective (`denoteVal_injective`, `denoteContext_injective`,
`denoteCond_injective`, `denoteSigner_injective`, `denoteSigners_injective`,
`denoteRule_injective`, `denoteRules_injective`, `denoteOutcome_injective`), so
two extracted values with the same meaning are the same value.
-/

namespace RuleCore.Equiv

open Aeneas Aeneas.Std

/-- A Rust `u8` as a byte of the model. -/
def byte (x : Std.U8) : UInt8 := UInt8.ofBitVec x.bv

/-- A Rust byte string as the model's `Bytes`. -/
def bytesOf (l : List Std.U8) : Bytes := l.map byte

/-- A Rust `Vec<u8>` as the model's `Bytes`. -/
def denoteBytes (v : alloc.vec.Vec Std.U8) : Bytes := bytesOf v.val

def denoteU32 (x : Std.U32) : UInt32 := UInt32.ofBitVec x.bv

def denoteU64 (x : Std.U64) : UInt64 := UInt64.ofBitVec x.bv

def denoteVal : rule_eval.val.Val → Chain.Val
  | .I128 x => .i128 x.bv
  | .U64 x => .u64 (denoteU64 x)
  | .Bool b => .bool b
  | .Bytes v => .bytes (denoteBytes v)
  | .Address v => .address (denoteBytes v)
  | .Symbol v => .symbol (denoteBytes v)
  | .Other v => .other (denoteBytes v)

def denoteContext : rule_eval.context.Context → Chain.Context
  | .Call contract function args =>
    .call (denoteBytes contract) (denoteBytes function) (args.val.map denoteVal)
  | .Create wasmHash => .create (denoteBytes wasmHash)

def denoteCond : rule_eval.rule.Cond → Chain.Cond
  | .ArgEq index val => .argEq (denoteU32 index) (denoteVal val)
  | .ArgI128AtMost index bound => .argI128AtMost (denoteU32 index) bound.bv

def denoteSigner : rule_eval.signer.Signer → Chain.Signer
  | .Delegated address => .delegated (denoteBytes address)
  | .External verifier key => .external (denoteBytes verifier) (denoteBytes key)

/-- The signers of a Rust slice or vector of signers. -/
def denoteSigners (signers : List rule_eval.signer.Signer) : List Chain.Signer :=
  signers.map denoteSigner

def denoteRule (r : rule_eval.rule.Rule) : Chain.Rule where
  contract := denoteBytes r.contract
  functions := r.functions.val.map denoteBytes
  conds := r.conds.val.map denoteCond
  signers := denoteSigners r.signers.val
  threshold := denoteU32 r.threshold

/-- The rules of a Rust slice or vector of rules, as a chain rule set. -/
def denoteRules (rules : List rule_eval.rule.Rule) : Chain.RuleSet := rules.map denoteRule

def denoteError : rule_eval.attenuate.AttenuationError → AttenuationError
  | .NoSuchRule => .noSuchRule
  | .ThresholdLowered => .thresholdLowered

/-- What an attenuation step returned, as the model's outcome. -/
def denoteOutcome :
    core.result.Result (alloc.vec.Vec rule_eval.rule.Rule) rule_eval.attenuate.AttenuationError →
      Except AttenuationError Chain.RuleSet
  | .Ok out => .ok (denoteRules out.val)
  | .Err e => .error (denoteError e)

/-! ## Indices -/

@[simp] theorem denoteU32_toNat (x : Std.U32) : (denoteU32 x).toNat = x.val := rfl

/-- Widening a `u32` index to `usize` keeps its value. -/
@[simp] theorem cast_usize_val (x : Std.U32) : (UScalar.cast .Usize x).val = x.val :=
  U32.cast_Usize_val_eq x

/-! ## Injectivity -/

theorem byte_injective : Function.Injective byte := by
  intro x y h
  have hbv : x.bv = y.bv := congrArg UInt8.toBitVec h
  cases x
  cases y
  simp_all

theorem bytesOf_inj {l₁ l₂ : List Std.U8} : bytesOf l₁ = bytesOf l₂ ↔ l₁ = l₂ :=
  (List.map_injective_iff.mpr byte_injective).eq_iff

theorem denoteBytes_inj {v w : alloc.vec.Vec Std.U8} :
    denoteBytes v = denoteBytes w ↔ v.val = w.val :=
  bytesOf_inj

theorem denoteBytes_injective : Function.Injective denoteBytes :=
  fun _ _ h => alloc.vec.Vec.ext _ _ (denoteBytes_inj.mp h)

theorem denoteU32_injective : Function.Injective denoteU32 := by
  intro x y h
  have hbv : x.bv = y.bv := congrArg UInt32.toBitVec h
  cases x
  cases y
  simp_all

theorem denoteU64_injective : Function.Injective denoteU64 := by
  intro x y h
  have hbv : x.bv = y.bv := congrArg UInt64.toBitVec h
  cases x
  cases y
  simp_all

theorem i128_bv_injective : Function.Injective (fun x : Std.I128 => x.bv) := by
  intro x y h
  cases x
  cases y
  simp_all

theorem i128_bv_inj {x y : Std.I128} : x.bv = y.bv ↔ x = y :=
  ⟨fun h => i128_bv_injective h, fun h => h ▸ rfl⟩

theorem denoteU64_inj {x y : Std.U64} : denoteU64 x = denoteU64 y ↔ x = y :=
  ⟨fun h => denoteU64_injective h, fun h => h ▸ rfl⟩

theorem denoteVal_injective : Function.Injective denoteVal := by
  intro a b h
  cases a <;> cases b <;> simp only [denoteVal, reduceCtorEq, Chain.Val.i128.injEq, Chain.Val.u64.injEq,
    Chain.Val.bool.injEq, Chain.Val.bytes.injEq, Chain.Val.address.injEq, Chain.Val.symbol.injEq,
    Chain.Val.other.injEq] at h <;> first
    | rw [i128_bv_injective h]
    | rw [denoteU64_injective h]
    | rw [h]
    | rw [denoteBytes_injective h]

theorem denoteContext_injective : Function.Injective denoteContext := by
  intro a b h
  cases a <;> cases b <;> simp only [denoteContext, reduceCtorEq, Chain.Context.call.injEq,
    Chain.Context.create.injEq] at h
  · obtain ⟨hc, hf, ha⟩ := h
    rw [denoteBytes_injective hc, denoteBytes_injective hf,
      alloc.vec.Vec.ext _ _ ((List.map_injective_iff.mpr denoteVal_injective).eq_iff.mp ha)]
  · rw [denoteBytes_injective h]

theorem denoteCond_injective : Function.Injective denoteCond := by
  intro a b h
  cases a <;> cases b <;> simp only [denoteCond, reduceCtorEq, Chain.Cond.argEq.injEq,
    Chain.Cond.argI128AtMost.injEq] at h
  · rw [denoteU32_injective h.1, denoteVal_injective h.2]
  · rw [denoteU32_injective h.1, i128_bv_injective h.2]

theorem denoteSigner_injective : Function.Injective denoteSigner := by
  intro a b h
  cases a <;> cases b <;> simp only [denoteSigner, reduceCtorEq, Chain.Signer.delegated.injEq,
    Chain.Signer.external.injEq] at h
  · rw [denoteBytes_injective h]
  · rw [denoteBytes_injective h.1, denoteBytes_injective h.2]

theorem denoteSigners_injective : Function.Injective denoteSigners :=
  List.map_injective_iff.mpr denoteSigner_injective

theorem denoteRule_injective : Function.Injective denoteRule := by
  intro a b h
  simp only [denoteRule, Chain.Rule.mk.injEq] at h
  obtain ⟨hc, hf, hk, hs, ht⟩ := h
  cases a
  cases b
  simp only [rule_eval.rule.Rule.mk.injEq]
  exact ⟨denoteBytes_injective hc,
    alloc.vec.Vec.ext _ _ ((List.map_injective_iff.mpr denoteBytes_injective).eq_iff.mp hf),
    alloc.vec.Vec.ext _ _ ((List.map_injective_iff.mpr denoteCond_injective).eq_iff.mp hk),
    alloc.vec.Vec.ext _ _ (denoteSigners_injective hs), denoteU32_injective ht⟩

theorem denoteRules_injective : Function.Injective denoteRules :=
  List.map_injective_iff.mpr denoteRule_injective

theorem denoteError_injective : Function.Injective denoteError := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

theorem denoteOutcome_injective : Function.Injective denoteOutcome := by
  intro a b h
  cases a with
  | Ok out =>
    cases b with
    | Ok out' =>
      simp only [denoteOutcome, Except.ok.injEq] at h
      rw [alloc.vec.Vec.ext _ _ (denoteRules_injective h)]
    | Err e => simp [denoteOutcome] at h
  | Err e =>
    cases b with
    | Ok out => simp [denoteOutcome] at h
    | Err e' =>
      simp only [denoteOutcome, Except.error.injEq] at h
      rw [denoteError_injective h]

end RuleCore.Equiv
