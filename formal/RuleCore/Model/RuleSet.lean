import RuleCore.Model.Cap

/-!
# Rule sets

The readable model of rule evaluation, generic in the context type `Ctx` and
the signer type `Sig`.

A context is one thing an authorization covers; in the chain vocabulary
(`RuleCore.Vocab.Chain`) it is a contract call or a contract creation. A rule
has a scope (in the chain vocabulary: one contract and a list of its functions)
and a list of conditions. Each condition is a predicate on the context it is
evaluated against, so a condition belongs to its rule and only ever reads the
arguments of a call that rule's scope matched.

A rule also names its signers and a threshold. An authorization carries the
signers it authenticated, one list for every context it covers, and a rule's
signer requirement holds when at least `threshold` distinct signers of the
rule are among them. The count takes the rule's signers without repeats
(`eraseDups`, which keeps each signer at its first position), so a signer
listed twice in the rule, or authenticated twice, counts once. A threshold of
0 is no requirement.

A rule may carry a spending cap (`RuleCap`): the cap's parameters and the
amount a context spends, read from the context. `Rule.allows` does not read
the cap; `RuleSet.authorize` (`RuleCore.Model.Authorize`) charges it.

A rule may carry a last ledger (`validUntil`) and the generation it was issued
under (`generation`). `Rule.allows` reads neither: it is the view without time
or generation. `RuleSet.authorize` refuses a rule after its last ledger
(`Rule.expired`) and outside its generation (`Rule.stale`).

A rule allows a context when its scope matches, every condition holds and its
signer requirement holds. A rule set allows a context when some rule allows
it, and allows a batch (every context of a Soroban authorization tree) when it
allows every context in it. `rs'` is narrower than `rs` when every context
`rs'` allows under some authenticated signers, `rs` allows under the same
signers.
-/

namespace RuleCore

variable {Ctx Sig : Type}

/-- A rule's spending cap: at most `params.limit` spent within `params.period`
consecutive ledgers, each context spending `amount` of it, or naming no amount
when `amount` is `none`. -/
structure RuleCap (Ctx : Type) where
  params : Cap.Params
  amount : Ctx → Option Int

structure Rule (Ctx Sig : Type) where
  scope : Ctx → Bool          -- contract and function match
  conds : List (Ctx → Bool)   -- conditions on this call's arguments
  signers : List Sig          -- the signers that count towards the threshold
  threshold : Nat             -- how many distinct signers must be authenticated
  cap : Option (RuleCap Ctx) := none  -- the rule's spending cap, if it has one
  validUntil : Option Nat := none     -- the last ledger it authorizes in, if any
  generation : Option Nat := none     -- the generation it was issued under, if any

/-- Rule `r` has expired at ledger `now`: it has a last ledger before `now`. -/
def Rule.expired (r : Rule Ctx Sig) (now : Nat) : Bool :=
  match r.validUntil with
  | some last => decide (last < now)
  | none => false

/-- Rule `r` was issued under a generation other than `gen`. -/
def Rule.stale (r : Rule Ctx Sig) (gen : Nat) : Bool :=
  match r.generation with
  | some issued => decide (issued ≠ gen)
  | none => false

def RuleSet (Ctx Sig : Type) := List (Rule Ctx Sig)

section

variable [DecidableEq Sig]

/-- The rule's distinct signers that are among the authenticated `auth`. -/
def Rule.present (r : Rule Ctx Sig) (auth : List Sig) : List Sig :=
  r.signers.eraseDups.filter (· ∈ auth)

/-- The rule's signer requirement: at least `threshold` of its distinct
signers are authenticated. -/
def Rule.signed (r : Rule Ctx Sig) (auth : List Sig) : Bool :=
  decide (r.threshold ≤ (r.present auth).length)

def Rule.allows (r : Rule Ctx Sig) (c : Ctx) (auth : List Sig) : Bool :=
  r.scope c && r.conds.all (· c) && r.signed auth

def RuleSet.allows (rs : RuleSet Ctx Sig) (c : Ctx) (auth : List Sig) : Bool :=
  rs.any (·.allows c auth)

def RuleSet.allowsAll (rs : RuleSet Ctx Sig) (cs : List Ctx) (auth : List Sig) : Bool :=
  cs.all (rs.allows · auth)

def RuleSet.narrower (rs' rs : RuleSet Ctx Sig) : Prop :=
  ∀ c auth, rs'.allows c auth = true → rs.allows c auth = true

end

/-- The rules of a rule set, as a list. `RuleSet` is a plain definition, so
list notation such as `r ∈ rs.rules` and `rs.rules[i]?` goes through this. -/
def RuleSet.rules (rs : RuleSet Ctx Sig) : List (Rule Ctx Sig) := rs

/-- The rule set whose rules are `l`. -/
def RuleSet.ofRules (l : List (Rule Ctx Sig)) : RuleSet Ctx Sig := l

@[simp] theorem RuleSet.rules_ofRules (l : List (Rule Ctx Sig)) :
    (RuleSet.ofRules l).rules = l := rfl

end RuleCore
