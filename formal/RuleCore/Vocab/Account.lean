import RuleCore.Vocab.Lowering

/-!
# The account's generation

The account keeps its admin document and a generation counter. Scoped
documents are issued under the account's current generation and lowered
against the excluded set of its current admin document (`Account.issue`). The
admin document's own rules carry no generation (`Account.adminRules`).

Two events change the account:

* `applyDoc d`: the owner applies a new admin document. The generation stays.
* `completeRecovery target`: a recovery completes and its target becomes the
  admin document. The generation advances by one. This is the one event that
  advances it. At `UInt64` maximum the completion is refused
  (`generationExhausted`) instead of wrapping the counter to a value an earlier
  scoped document may carry.

`Account.run` applies events in order, a refused one leaving the account as it
was, and `Account.completions` counts the recoveries a run completes.
-/

namespace RuleCore.Document

open RuleCore RuleCore.Chain

structure Account where
  /-- The account's address, as its `ScAddress` XDR. -/
  address : Bytes
  admin : Doc
  generation : UInt64
  deriving DecidableEq, Repr

inductive Event where
  /-- The owner applies a new admin document. -/
  | applyDoc (d : Doc)
  /-- A recovery completes; its target becomes the admin document. -/
  | completeRecovery (target : Doc)
  deriving DecidableEq, Repr

inductive AccountError where
  /-- The generation is at its maximum and cannot advance. -/
  | generationExhausted
  deriving DecidableEq, Repr

/-- The largest generation. -/
def maxGeneration : UInt64 := 18446744073709551615

def Account.step (s : Account) : Event → Except AccountError Account
  | .applyDoc d => .ok { s with admin := d }
  | .completeRecovery target =>
    if s.generation = maxGeneration then .error .generationExhausted
    else .ok { s with admin := target, generation := s.generation + 1 }

/-- The account after every event of `es`, each refused one leaving it as it
was. -/
def Account.run (s : Account) : List Event → Account
  | [] => s
  | e :: es =>
    match s.step e with
    | .ok s' => s'.run es
    | .error _ => s.run es

/-- The number of recoveries a run completes. -/
def Account.completions (s : Account) : List Event → Nat
  | [] => 0
  | e :: es =>
    match e, s.step e with
    | .completeRecovery _, .ok s' => 1 + s'.completions es
    | _, .ok s' => s'.completions es
    | _, .error _ => s.completions es

/-- The rules the scoped document `sd` lowers to, issued now: under the
excluded set of the current admin document and the current generation. -/
def Account.issue (s : Account) (sd : Doc) : Except ScopeError Chain.RuleSet :=
  sd.lowerScoped s.address (s.admin.excluded s.address) s.generation

/-- The rules the current admin document lowers to. -/
def Account.adminRules (s : Account) : Chain.RuleSet :=
  s.admin.lower s.address

end RuleCore.Document
