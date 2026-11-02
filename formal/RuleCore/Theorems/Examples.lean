import RuleCore.Vocab.Chain

/-!
# Examples

Concrete verdicts of the chain vocabulary, each checked by the kernel with
`decide` or `rfl`. A rule allows `transfer` on one token contract with argument 2 (the
amount) capped at 100.
-/

namespace RuleCore.Chain.Examples

def token : Bytes := [0xAA, 0xBB]
def transfer : Bytes := [0x74, 0x72]
def from' : Val := .address [1]
def to : Val := .address [2]

def capped : Rule :=
  { contract := token, functions := [transfer], conds := [.argI128AtMost 2 100] }

/-- At the cap. -/
example : RuleSet.allows [capped] (.call token transfer [from', to, .i128 100]) = true := by
  decide

/-- Over the cap. -/
example : RuleSet.allows [capped] (.call token transfer [from', to, .i128 101]) = false := by
  decide

/-- The comparison is signed. -/
example : RuleSet.allows [capped] (.call token transfer [from', to, .i128 (-5)]) = true := by
  decide

/-- An amount of another constructor fails the cap. -/
example : RuleSet.allows [capped] (.call token transfer [from', to, .u64 1]) = false := by
  decide

/-- A missing amount fails the cap. -/
example : RuleSet.allows [capped] (.call token transfer [from', to]) = false := by
  decide

/-- A prefix of the contract id does not match. -/
example : RuleSet.allows [capped] (.call [0xAA] transfer [from', to, .i128 1]) = false := by
  decide

/-- No rule allows a creation, so a batch containing one is denied. -/
example : RuleSet.allowsAll [capped]
    [.call token transfer [from', to, .i128 1], .create token] = false := by
  decide

/-- An argument index past the end of the arguments reads a missing argument. -/
example : RuleSet.allows [{ capped with conds := [.argEq 4294967295 (.bool true)] }]
    (.call token transfer [from', to, .i128 1]) = false := by
  decide

/-- Removing the rule's only function leaves a rule that matches nothing. -/
example :
    RuleSet.removeFunctions [capped] 0 [transfer] = .ok [{ capped with functions := [] }] :=
  rfl

/-- An out-of-range rule index is refused. -/
example : RuleSet.dropRule [capped] 1 = .error .noSuchRule :=
  rfl

end RuleCore.Chain.Examples
