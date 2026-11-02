/-!
# Rule sets

The readable model of rule evaluation, generic in the context type `Ctx`.

A context is one thing an authorization covers; in the chain vocabulary
(`RuleCore.Vocab.Chain`) it is a contract call or a contract creation. A rule
has a scope (in the chain vocabulary: one contract and a list of its functions)
and a list of conditions. Each condition is a predicate on the context it is
evaluated against, so a condition belongs to its rule and only ever reads the
arguments of a call that rule's scope matched.

A rule allows a context when its scope matches and every condition holds. A
rule set allows a context when some rule allows it, and allows a batch (every
context of a Soroban authorization tree) when it allows every context in it.
`rs'` is narrower than `rs` when every context `rs'` allows, `rs` allows too.
-/

namespace RuleCore

variable {Ctx : Type}

structure Rule (Ctx : Type) where
  scope : Ctx → Bool          -- contract and function match
  conds : List (Ctx → Bool)   -- conditions on this call's arguments

def Rule.allows (r : Rule Ctx) (c : Ctx) : Bool :=
  r.scope c && r.conds.all (· c)

def RuleSet (Ctx : Type) := List (Rule Ctx)

def RuleSet.allows (rs : RuleSet Ctx) (c : Ctx) : Bool :=
  rs.any (·.allows c)

def RuleSet.allowsAll (rs : RuleSet Ctx) (cs : List Ctx) : Bool :=
  cs.all rs.allows

def RuleSet.narrower (rs' rs : RuleSet Ctx) : Prop :=
  ∀ c, rs'.allows c = true → rs.allows c = true

/-- The rules of a rule set, as a list. `RuleSet` is a plain definition, so
list notation such as `r ∈ rs.rules` and `rs.rules[i]?` goes through this. -/
def RuleSet.rules (rs : RuleSet Ctx) : List (Rule Ctx) := rs

/-- The rule set whose rules are `l`. -/
def RuleSet.ofRules (l : List (Rule Ctx)) : RuleSet Ctx := l

@[simp] theorem RuleSet.rules_ofRules (l : List (Rule Ctx)) : (RuleSet.ofRules l).rules = l := rfl

end RuleCore
