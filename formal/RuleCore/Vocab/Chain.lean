import RuleCore.Model.Attenuation
import RuleCore.Vocab.Bytes

/-!
# Chain vocabulary

The concrete rules installed on chain, and their meaning as generic rules.

A context is a contract call (contract, function, arguments) or a contract
creation. A rule names one contract, a list of its functions, and conditions on
the call's arguments. `Rule.denote` gives each rule's meaning as a generic
`RuleCore.Rule Context`: its scope matches a call to the rule's contract and one
of its functions, and each condition reads the arguments of the call it is
evaluated against. A creation has no arguments, every scope is false on it, and
so no rule allows a creation.

Argument values follow Soroban's: `i128` is `BitVec 128` compared as a signed
two's-complement integer and `u64` is `UInt64`, matching the bit-vector
representation Aeneas gives Rust's `i128` and `u64`. Argument and rule indices
are `UInt32`, as in the Rust evaluator, and are read as list positions through
`toNat`: an index past the end of the arguments is a missing argument, and one
past the end of the rule set is `AttenuationError.noSuchRule`. An argument of a type the
other constructors do not model is `other` of its full XDR. Values of different
constructors are never equal, so an `argEq` written for one type never holds
on an argument of another.

`allows`, `allowsAll` and `narrower` on chain rule sets are the generic ones on
the denotation, and each chain attenuation operation denotes the generic step of
the same kind (`Attenuation.denote`). The theorems in `RuleCore.Theorems.Chain`
carry the generic results over and state the vocabulary's own properties.
-/

namespace RuleCore.Chain

/-- A Soroban `i128`, as a two's-complement bit vector. -/
abbrev I128 := BitVec 128

inductive Val where
  | i128 (v : I128)
  | u64 (v : UInt64)
  | bool (v : Bool)
  | bytes (v : Bytes)
  | address (v : Bytes)
  | symbol (v : Bytes)
  /-- An argument of a type the other constructors do not model, as its full
  XDR. -/
  | other (xdr : Bytes)
  deriving DecidableEq, Repr

/-- A value's constructor, without its payload. -/
inductive Kind where
  | i128 | u64 | bool | bytes | address | symbol | other
  deriving DecidableEq, Repr

def Val.kind : Val → Kind
  | .i128 _ => .i128
  | .u64 _ => .u64
  | .bool _ => .bool
  | .bytes _ => .bytes
  | .address _ => .address
  | .symbol _ => .symbol
  | .other _ => .other

/-- One context of a Soroban authorization tree. -/
inductive Context where
  | call (contract : Bytes) (function : Bytes) (args : List Val)
  | create (wasmHash : Bytes)
  deriving DecidableEq, Repr

/-- A condition on the arguments of the call its rule matches. -/
inductive Cond where
  /-- Argument `index` exists and equals `val`. -/
  | argEq (index : UInt32) (val : Val)
  /-- Argument `index` exists, is an `i128`, and is at most `n` (signed). -/
  | argI128AtMost (index : UInt32) (n : I128)
  deriving DecidableEq, Repr

def Cond.holds : Cond → List Val → Bool
  | .argEq i val, args => decide (args[i.toNat]? = some val)
  | .argI128AtMost i n, args =>
    match args[i.toNat]? with
    | some (.i128 v) => decide (v.toInt ≤ n.toInt)
    | _ => false

structure Rule where
  contract : Bytes
  functions : List Bytes
  conds : List Cond
  deriving DecidableEq, Repr

abbrev RuleSet := List Rule

/-! ## Denotation -/

/-- The contexts a rule's contract and function list match: calls to that
contract and one of those functions. -/
def Rule.scope (r : Rule) : Context → Bool
  | .call contract function _ => decide (contract = r.contract) && decide (function ∈ r.functions)
  | .create _ => false

/-- A condition, read on the arguments of the context it is evaluated against.
A creation has no arguments, so every condition is false on it. -/
def Cond.denote (cond : Cond) : Context → Bool
  | .call _ _ args => cond.holds args
  | .create _ => false

def Rule.denote (r : Rule) : RuleCore.Rule Context :=
  { scope := r.scope, conds := r.conds.map Cond.denote }

def RuleSet.denote (rs : RuleSet) : RuleCore.RuleSet Context :=
  .ofRules (rs.map Rule.denote)

def Rule.allows (r : Rule) (c : Context) : Bool :=
  r.denote.allows c

def RuleSet.allows (rs : RuleSet) (c : Context) : Bool :=
  rs.denote.allows c

def RuleSet.allowsAll (rs : RuleSet) (cs : List Context) : Bool :=
  rs.denote.allowsAll cs

def RuleSet.narrower (rs' rs : RuleSet) : Prop :=
  rs'.denote.narrower rs.denote

/-! ## Attenuation -/

/-- Rule `r` with `cond` appended to its conditions. -/
def Rule.addCond (r : Rule) (cond : Cond) : Rule :=
  { r with conds := r.conds ++ [cond] }

/-- Rule `r` with every function in `fs` removed from its function list. -/
def Rule.removeFunctions (r : Rule) (fs : List Bytes) : Rule :=
  { r with functions := r.functions.filter (fun f => decide (f ∉ fs)) }

/-- Replace the rule at position `i` by `f` of it. -/
def RuleSet.modifyRule (rs : RuleSet) (i : Nat) (f : Rule → Rule) :
    Except AttenuationError RuleSet :=
  match rs[i]? with
  | some r => .ok (rs.set i (f r))
  | none => .error .noSuchRule

def RuleSet.dropRule (rs : RuleSet) (i : UInt32) : Except AttenuationError RuleSet :=
  if i.toNat < rs.length then .ok (rs.eraseIdx i.toNat) else .error .noSuchRule

def RuleSet.addCond (rs : RuleSet) (i : UInt32) (cond : Cond) : Except AttenuationError RuleSet :=
  rs.modifyRule i.toNat (·.addCond cond)

def RuleSet.removeFunctions (rs : RuleSet) (i : UInt32) (fs : List Bytes) :
    Except AttenuationError RuleSet :=
  rs.modifyRule i.toNat (·.removeFunctions fs)

/-- One attenuation step. -/
inductive Attenuation where
  | dropRule (i : UInt32)
  | addCond (i : UInt32) (cond : Cond)
  | removeFunctions (i : UInt32) (fs : List Bytes)
  deriving DecidableEq, Repr

def RuleSet.attenuate (rs : RuleSet) : Attenuation → Except AttenuationError RuleSet
  | .dropRule i => rs.dropRule i
  | .addCond i cond => rs.addCond i cond
  | .removeFunctions i fs => rs.removeFunctions i fs

/-- Apply `steps` in order, failing with the first step that fails. -/
def RuleSet.attenuateAll (rs : RuleSet) (steps : List Attenuation) :
    Except AttenuationError RuleSet :=
  steps.foldlM RuleSet.attenuate rs

/-- `Derives root rs`: `rs` is reachable from `root` by zero or more
attenuation steps. -/
inductive RuleSet.Derives (root : RuleSet) : RuleSet → Prop where
  | refl : Derives root root
  | step {rs rs' : RuleSet} (a : Attenuation) :
      Derives root rs → rs.attenuate a = .ok rs' → Derives root rs'

/-- The contexts that are not a call to a function in `fs`. Removing `fs` from
a rule restricts its scope to these. -/
def notCalling (fs : List Bytes) : Context → Bool
  | .call _ function _ => decide (function ∉ fs)
  | .create _ => true

/-- The generic attenuation step a chain step denotes. -/
def Attenuation.denote : Attenuation → RuleCore.Attenuation Context
  | .dropRule i => .dropRule i.toNat
  | .addCond i cond => .addCond i.toNat cond.denote
  | .removeFunctions i fs => .restrictScope i.toNat (notCalling fs)

end RuleCore.Chain
