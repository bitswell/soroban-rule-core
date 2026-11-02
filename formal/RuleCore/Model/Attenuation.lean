import RuleCore.Model.RuleSet

/-!
# Attenuation

A holder of a rule set derives a narrower one by attenuation steps. There are
exactly eight, each naming a rule by its index:

* `dropRule i`: remove rule `i`.
* `addCond i p`: append condition `p` to rule `i`.
* `restrictScope i s`: restrict rule `i`'s scope to the contexts that also
  satisfy `s`. In the chain vocabulary this is removing functions from the
  rule's function list.
* `removeSigners i ss`: remove every signer in `ss` from rule `i`'s signers,
  keeping its threshold.
* `raiseThreshold i k`: set rule `i`'s threshold to `k`, refused with
  `AttenuationError.thresholdLowered` when `k` is below the current threshold.
* `addCap i k`: give rule `i` the cap `k`, refused with `capPresent` when the
  rule has a cap and with `invalidCap` when `k`'s parameters are not valid
  (`Cap.Params.valid`).
* `lowerCapLimit i limit`: set the limit of rule `i`'s cap to `limit`, refused
  with `noCap` when the rule has no cap, with `limitRaised` when `limit` is
  above the current limit, and with `invalidCap` when `limit` is not
  positive.
* `lengthenCapPeriod i period`: set the period of rule `i`'s cap to `period`,
  refused with `noCap` when the rule has no cap and with `periodShortened`
  when `period` is below the current period.

Each step returns the new rule set, or `AttenuationError.noSuchRule` when its
index is not below the number of rules, before any other refusal. Nothing else
is an attenuation step.
-/

namespace RuleCore

variable {Ctx Sig : Type}

/-- Why an attenuation step was refused. -/
inductive AttenuationError where
  /-- The rule index is not below the number of rules. -/
  | noSuchRule
  /-- The new threshold is below the rule's current threshold. -/
  | thresholdLowered
  /-- The rule already has a cap. -/
  | capPresent
  /-- The rule has no cap. -/
  | noCap
  /-- The cap would not be valid: its limit is not positive or its period is
  0. -/
  | invalidCap
  /-- The new limit is above the rule's current limit. -/
  | limitRaised
  /-- The new period is below the rule's current period. -/
  | periodShortened
  deriving DecidableEq, Repr

/-- Rule `r` with condition `p` appended to its conditions. -/
def Rule.addCond (r : Rule Ctx Sig) (p : Ctx → Bool) : Rule Ctx Sig :=
  { r with conds := r.conds ++ [p] }

/-- Rule `r` matching only the contexts its scope matches and `s` accepts. -/
def Rule.restrictScope (r : Rule Ctx Sig) (s : Ctx → Bool) : Rule Ctx Sig :=
  { r with scope := fun c => r.scope c && s c }

/-- Rule `r` without the signers in `ss`, its threshold unchanged. -/
def Rule.removeSigners [DecidableEq Sig] (r : Rule Ctx Sig) (ss : List Sig) : Rule Ctx Sig :=
  { r with signers := r.signers.filter (· ∉ ss) }

/-- Replace rule `i` by `f` of it. -/
def RuleSet.modifyRule (rs : RuleSet Ctx Sig) (i : Nat) (f : Rule Ctx Sig → Rule Ctx Sig) :
    Except AttenuationError (RuleSet Ctx Sig) :=
  match rs.rules[i]? with
  | some r => .ok (.ofRules (rs.rules.set i (f r)))
  | none => .error .noSuchRule

def RuleSet.dropRule (rs : RuleSet Ctx Sig) (i : Nat) : Except AttenuationError (RuleSet Ctx Sig) :=
  if i < rs.rules.length then .ok (.ofRules (rs.rules.eraseIdx i)) else .error .noSuchRule

def RuleSet.addCond (rs : RuleSet Ctx Sig) (i : Nat) (p : Ctx → Bool) :
    Except AttenuationError (RuleSet Ctx Sig) :=
  rs.modifyRule i (·.addCond p)

def RuleSet.restrictScope (rs : RuleSet Ctx Sig) (i : Nat) (s : Ctx → Bool) :
    Except AttenuationError (RuleSet Ctx Sig) :=
  rs.modifyRule i (·.restrictScope s)

def RuleSet.removeSigners [DecidableEq Sig] (rs : RuleSet Ctx Sig) (i : Nat) (ss : List Sig) :
    Except AttenuationError (RuleSet Ctx Sig) :=
  rs.modifyRule i (·.removeSigners ss)

def RuleSet.raiseThreshold (rs : RuleSet Ctx Sig) (i k : Nat) :
    Except AttenuationError (RuleSet Ctx Sig) :=
  match rs.rules[i]? with
  | some r =>
    if k < r.threshold then .error .thresholdLowered
    else .ok (.ofRules (rs.rules.set i { r with threshold := k }))
  | none => .error .noSuchRule

/-- Cap `k` with its limit set to `limit`. -/
def RuleCap.withLimit (k : RuleCap Ctx) (limit : Int) : RuleCap Ctx :=
  { k with params := { k.params with limit } }

/-- Cap `k` with its period set to `period`. -/
def RuleCap.withPeriod (k : RuleCap Ctx) (period : Nat) : RuleCap Ctx :=
  { k with params := { k.params with period } }

def RuleSet.addCap (rs : RuleSet Ctx Sig) (i : Nat) (k : RuleCap Ctx) :
    Except AttenuationError (RuleSet Ctx Sig) :=
  match rs.rules[i]? with
  | some r =>
    match r.cap with
    | some _ => .error .capPresent
    | none =>
      if k.params.valid then .ok (.ofRules (rs.rules.set i { r with cap := some k }))
      else .error .invalidCap
  | none => .error .noSuchRule

def RuleSet.lowerCapLimit (rs : RuleSet Ctx Sig) (i : Nat) (limit : Int) :
    Except AttenuationError (RuleSet Ctx Sig) :=
  match rs.rules[i]? with
  | some r =>
    match r.cap with
    | some k =>
      if k.params.limit < limit then .error .limitRaised
      else if limit ≤ 0 then .error .invalidCap
      else .ok (.ofRules (rs.rules.set i { r with cap := some (k.withLimit limit) }))
    | none => .error .noCap
  | none => .error .noSuchRule

def RuleSet.lengthenCapPeriod (rs : RuleSet Ctx Sig) (i period : Nat) :
    Except AttenuationError (RuleSet Ctx Sig) :=
  match rs.rules[i]? with
  | some r =>
    match r.cap with
    | some k =>
      if period < k.params.period then .error .periodShortened
      else .ok (.ofRules (rs.rules.set i { r with cap := some (k.withPeriod period) }))
    | none => .error .noCap
  | none => .error .noSuchRule

/-- One attenuation step. -/
inductive Attenuation (Ctx Sig : Type) where
  | dropRule (i : Nat)
  | addCond (i : Nat) (p : Ctx → Bool)
  | restrictScope (i : Nat) (s : Ctx → Bool)
  | removeSigners (i : Nat) (ss : List Sig)
  | raiseThreshold (i k : Nat)
  | addCap (i : Nat) (k : RuleCap Ctx)
  | lowerCapLimit (i : Nat) (limit : Int)
  | lengthenCapPeriod (i period : Nat)

def RuleSet.attenuate [DecidableEq Sig] (rs : RuleSet Ctx Sig) :
    Attenuation Ctx Sig → Except AttenuationError (RuleSet Ctx Sig)
  | .dropRule i => rs.dropRule i
  | .addCond i p => rs.addCond i p
  | .restrictScope i s => rs.restrictScope i s
  | .removeSigners i ss => rs.removeSigners i ss
  | .raiseThreshold i k => rs.raiseThreshold i k
  | .addCap i k => rs.addCap i k
  | .lowerCapLimit i limit => rs.lowerCapLimit i limit
  | .lengthenCapPeriod i period => rs.lengthenCapPeriod i period

/-- Apply `steps` in order, failing with the first step that fails. -/
def RuleSet.attenuateAll [DecidableEq Sig] (rs : RuleSet Ctx Sig)
    (steps : List (Attenuation Ctx Sig)) : Except AttenuationError (RuleSet Ctx Sig) :=
  steps.foldlM RuleSet.attenuate rs

/-- `Derives root rs`: `rs` is reachable from `root` by zero or more
attenuation steps. -/
inductive RuleSet.Derives [DecidableEq Sig] (root : RuleSet Ctx Sig) : RuleSet Ctx Sig → Prop where
  | refl : Derives root root
  | step {rs rs' : RuleSet Ctx Sig} (a : Attenuation Ctx Sig) :
      Derives root rs → rs.attenuate a = .ok rs' → Derives root rs'

end RuleCore
