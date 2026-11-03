import RuleCore.Vocab.Chain

/-!
# Examples

Concrete verdicts of the chain vocabulary, each checked by the kernel with
`decide` or `rfl`. A rule allows `transfer` on one token contract with argument 2 (the
amount) capped at 100, with no signer requirement. A second rule allows the same
call when two of three signers are authenticated. A wildcard rule allows every
function of the token, a rule with `argIn` and `argStrPrefix` conditions reads
string arguments, and authorizations show the expiry, generation and
unauthorized-signer refusals.
-/

namespace RuleCore.Chain.Examples

def token : Bytes := [0xAA, 0xBB]
def transfer : Bytes := [0x74, 0x72]
def from' : Val := .address [1]
def to : Val := .address [2]

def capped : Rule :=
  { contract := token, functions := .only [transfer], conds := [.argI128AtMost 2 100], signers := [],
    threshold := 0 }

/-- At the cap. -/
example : RuleSet.allows [capped] (.call token transfer [from', to, .i128 100]) [] = true := by
  decide

/-- Over the cap. -/
example : RuleSet.allows [capped] (.call token transfer [from', to, .i128 101]) [] = false := by
  decide

/-- The comparison is signed. -/
example : RuleSet.allows [capped] (.call token transfer [from', to, .i128 (-5)]) [] = true := by
  decide

/-- An amount of another constructor fails the cap. -/
example : RuleSet.allows [capped] (.call token transfer [from', to, .u64 1]) [] = false := by
  decide

/-- A missing amount fails the cap. -/
example : RuleSet.allows [capped] (.call token transfer [from', to]) [] = false := by
  decide

/-- A prefix of the contract id does not match. -/
example : RuleSet.allows [capped] (.call [0xAA] transfer [from', to, .i128 1]) [] = false := by
  decide

/-- No rule allows a creation, so a batch containing one is denied. -/
example : RuleSet.allowsAll [capped]
    [.call token transfer [from', to, .i128 1], .create token] [] = false := by
  decide

/-- An argument index past the end of the arguments reads a missing argument. -/
example : RuleSet.allows [{ capped with conds := [.argEq 4294967295 (.bool true)] }]
    (.call token transfer [from', to, .i128 1]) [] = false := by
  decide

def alice : Signer := .delegated [1]
def bob : Signer := .delegated [2]
def key : Signer := .external [9] [1]

/-- Two of alice, bob and an external key. -/
def twoOfThree : Rule :=
  { capped with signers := [alice, bob, key], threshold := 2 }

def send : Context := .call token transfer [from', to, .i128 1]

/-- Two distinct signers meet the threshold. -/
example : RuleSet.allows [twoOfThree] send [alice, key] = true := by
  decide

/-- One signer authenticated twice counts once. -/
example : RuleSet.allows [twoOfThree] send [alice, alice] = false := by
  decide

/-- A signer listed twice in the rule counts once. -/
example : RuleSet.allows [{ twoOfThree with signers := [alice, alice, bob] }] send [alice] =
    false := by
  decide

/-- An external signer whose verifier holds alice's bytes is not alice. -/
example : RuleSet.allows [twoOfThree] send [bob, .external [1] []] = false := by
  decide

/-- A threshold above the number of distinct signers is never met. -/
example : RuleSet.allows [{ twoOfThree with threshold := 4 }] send [alice, bob, key] = false := by
  decide

/-- Lowering a threshold is refused. -/
example : RuleSet.raiseThreshold [twoOfThree] 0 1 = .error .thresholdLowered :=
  rfl

/-- Removing a signer keeps the threshold, so the rule then needs both others. -/
example : RuleSet.removeSigners [twoOfThree] 0 [alice] =
    .ok [{ twoOfThree with signers := [bob, key] }] :=
  rfl

/-- Removing the rule's only function leaves a rule that matches nothing. -/
example :
    RuleSet.removeFunctions [capped] 0 [transfer] = .ok [{ capped with functions := .only [] }] :=
  rfl

def approve : Bytes := [0x61, 0x70]

/-- Every function of the token, with no other requirement. -/
def anyCall : Rule :=
  { contract := token, functions := .any, conds := [], signers := [], threshold := 0 }

/-- The wildcard matches a function it was never told about. -/
example : RuleSet.allows [anyCall] (.call token [0x00] []) [] = true := by
  decide

/-- Removing a function from the wildcard excludes exactly that function. -/
example : RuleSet.removeFunctions [anyCall] 0 [approve] =
    .ok [{ anyCall with functions := .anyExcept [approve] }] :=
  rfl

example : RuleSet.allows [{ anyCall with functions := .anyExcept [approve] }]
    (.call token approve []) [] = false := by
  decide

/-- Restricting the wildcard to a list leaves that list. -/
example : RuleSet.restrictFunctions [anyCall] 0 [transfer] =
    .ok [{ anyCall with functions := .only [transfer] }] :=
  rfl

def pkg : Bytes := [0x70, 0x6B, 0x67]

/-- Argument 0 is one of two values, and argument 1 is a string starting with
`pkg`. -/
def named : Rule :=
  { anyCall with conds := [.argIn 0 [.u64 1, .u64 2], .argStrPrefix 1 pkg] }

example : RuleSet.allows [named] (.call token transfer [.u64 2, .string (pkg ++ [0x5F])]) [] =
    true := by
  decide

/-- A value outside the list fails `argIn`. -/
example : RuleSet.allows [named] (.call token transfer [.u64 3, .string pkg]) [] = false := by
  decide

/-- A symbol with the same bytes is not a string. -/
example : RuleSet.allows [named] (.call token transfer [.u64 1, .symbol pkg]) [] = false := by
  decide

/-- A string shorter than the prefix does not start with it. -/
example : RuleSet.allows [named] (.call token transfer [.u64 1, .string [0x70]]) [] = false := by
  decide

/-- The wildcard rule for alice, valid until ledger 10, issued under
generation 3. -/
def grant : Rule :=
  { anyCall with signers := [alice], threshold := 1, validUntil := some 10, generation := some 3 }

def call0 : Context := .call token transfer []

/-- At its last ledger, in its generation, signed by alice: authorized. -/
example : RuleSet.authorize [grant] [.empty] ⟨[call0], [0], [alice], 10, 3⟩ = .ok [.empty] :=
  rfl

/-- One ledger later: expired. -/
example : RuleSet.authorize [grant] [.empty] ⟨[call0], [0], [alice], 11, 3⟩ =
    .error .expired :=
  rfl

/-- After the generation moves on: stale. -/
example : RuleSet.authorize [grant] [.empty] ⟨[call0], [0], [alice], 10, 4⟩ =
    .error .staleGeneration :=
  rfl

/-- A further authenticated signer that belongs to no chosen rule is refused,
though alice alone meets the threshold. -/
example : RuleSet.authorize [grant] [.empty] ⟨[call0], [0], [alice, bob], 10, 3⟩ =
    .error .unauthorizedSigner :=
  rfl

/-- `allows` reads neither time nor generation. -/
example : RuleSet.allows [grant] call0 [alice, bob] = true := by
  decide

/-- Moving a last ledger later is refused; moving it earlier is a step. -/
example : RuleSet.lowerValidUntil [grant] 0 11 = .error .validUntilRaised :=
  rfl

example : RuleSet.lowerValidUntil [grant] 0 9 = .ok [{ grant with validUntil := some 9 }] :=
  rfl

/-- An out-of-range rule index is refused. -/
example : RuleSet.dropRule [capped] 1 = .error .noSuchRule :=
  rfl

end RuleCore.Chain.Examples
