import RuleCore.Model.RuleSet

/-!
# Attenuation

A holder of a rule set derives a narrower one by attenuation steps. There are
exactly three, each naming a rule by its index:

* `dropRule i`: remove rule `i`.
* `addCond i p`: append condition `p` to rule `i`.
* `restrictScope i s`: restrict rule `i`'s scope to the contexts that also
  satisfy `s`. In the chain vocabulary this is removing functions from the
  rule's function list.

Each step returns the new rule set, or `AttenuationError.noSuchRule` when its
index is not below the number of rules. Nothing else is an attenuation step.
-/

namespace RuleCore

variable {Ctx : Type}

/-- Why an attenuation step was refused. -/
inductive AttenuationError where
  /-- The rule index is not below the number of rules. -/
  | noSuchRule
  deriving DecidableEq, Repr

/-- Rule `r` with condition `p` appended to its conditions. -/
def Rule.addCond (r : Rule Ctx) (p : Ctx → Bool) : Rule Ctx :=
  { r with conds := r.conds ++ [p] }

/-- Rule `r` matching only the contexts its scope matches and `s` accepts. -/
def Rule.restrictScope (r : Rule Ctx) (s : Ctx → Bool) : Rule Ctx :=
  { r with scope := fun c => r.scope c && s c }

/-- Replace rule `i` by `f` of it. -/
def RuleSet.modifyRule (rs : RuleSet Ctx) (i : Nat) (f : Rule Ctx → Rule Ctx) :
    Except AttenuationError (RuleSet Ctx) :=
  match rs.rules[i]? with
  | some r => .ok (.ofRules (rs.rules.set i (f r)))
  | none => .error .noSuchRule

def RuleSet.dropRule (rs : RuleSet Ctx) (i : Nat) : Except AttenuationError (RuleSet Ctx) :=
  if i < rs.rules.length then .ok (.ofRules (rs.rules.eraseIdx i)) else .error .noSuchRule

def RuleSet.addCond (rs : RuleSet Ctx) (i : Nat) (p : Ctx → Bool) :
    Except AttenuationError (RuleSet Ctx) :=
  rs.modifyRule i (·.addCond p)

def RuleSet.restrictScope (rs : RuleSet Ctx) (i : Nat) (s : Ctx → Bool) :
    Except AttenuationError (RuleSet Ctx) :=
  rs.modifyRule i (·.restrictScope s)

/-- One attenuation step. -/
inductive Attenuation (Ctx : Type) where
  | dropRule (i : Nat)
  | addCond (i : Nat) (p : Ctx → Bool)
  | restrictScope (i : Nat) (s : Ctx → Bool)

def RuleSet.attenuate (rs : RuleSet Ctx) :
    Attenuation Ctx → Except AttenuationError (RuleSet Ctx)
  | .dropRule i => rs.dropRule i
  | .addCond i p => rs.addCond i p
  | .restrictScope i s => rs.restrictScope i s

/-- Apply `steps` in order, failing with the first step that fails. -/
def RuleSet.attenuateAll (rs : RuleSet Ctx) (steps : List (Attenuation Ctx)) :
    Except AttenuationError (RuleSet Ctx) :=
  steps.foldlM RuleSet.attenuate rs

/-- `Derives root rs`: `rs` is reachable from `root` by zero or more
attenuation steps. -/
inductive RuleSet.Derives (root : RuleSet Ctx) : RuleSet Ctx → Prop where
  | refl : Derives root root
  | step {rs rs' : RuleSet Ctx} (a : Attenuation Ctx) :
      Derives root rs → rs.attenuate a = .ok rs' → Derives root rs'

end RuleCore
