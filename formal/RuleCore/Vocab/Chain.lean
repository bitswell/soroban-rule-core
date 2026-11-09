import RuleCore.Model.Authorize
import RuleCore.Vocab.Bytes

/-!
# Chain vocabulary

The concrete rules installed on chain, and their meaning as generic rules.

A context is a contract call (contract, function, arguments) or a contract
creation. A rule names one contract, the functions it matches there
(`Functions`), conditions on the call's arguments, a list of signers, a
threshold and, optionally, a spending cap, a last ledger and the generation it
was issued under. `Rule.denote` gives each rule's meaning as a generic
`RuleCore.Rule Context Signer`: its scope matches a call to the rule's contract
and one of its functions, each condition reads the arguments of the call it is
evaluated against, and its signers, threshold, cap, last ledger (a `u32`) and
generation (a `u64`) are the rule's own, the last two read as natural numbers.
A creation has no arguments, every scope is false on it, and so no rule allows
a creation.

An optional `authRoot` carries an exact contract/function pair at this entry's
root. `Rule.denote` maps it to the generic root predicate. Local `allows` and
`allowsAll` ignore it; `allowsIn`, `allowsBatch` and `checkAuth` enforce it.
The full authorization derives that root from its own contexts' head.

A rule's functions are a list (`only`), or every function except a list
(`anyExcept`). The wildcard, every function on the contract, is `anyExcept []`
(`Functions.any`). Removing functions from a list drops them; removing them
from `anyExcept removed` adds them to `removed`, so removal never refuses and
the result matches exactly the functions it matched before but the removed
ones. Restricting functions to a list `fs` keeps the functions also in `fs`;
on `anyExcept removed` it gives the list of `fs` not in `removed`.

A cap (`Cap`) is a limit, an `i128`, a period in ledgers and the index of the
argument that holds the amount, both `u32`. Its meaning (`Cap.denote`) is the
cap parameters `⟨limit, period⟩` of `RuleCore.Cap`, read as an integer and a
natural number, and the amount a call spends: its argument at `amountArg`
when that argument exists and is an `i128`, and no amount otherwise. A cap may
be added to a rule only when it is valid (`Cap.valid`).

A signer follows OpenZeppelin's smart-account signer kinds: `delegated` is an
address that authorizes for itself, as its `ScAddress` XDR; `external` is a
key checked by a verifier contract, as the verifier's address and the key's
bytes. Signers compare exactly, constructor first: a delegated signer never
equals an external one, whatever their bytes. An authorization carries the
signers it authenticated, one list for every context of its batch.

Argument values follow Soroban's: `i128` is `BitVec 128` compared as a signed
two's-complement integer and `u64` is `UInt64`, matching the bit-vector
representation Aeneas gives Rust's `i128` and `u64`. A `string` is its bytes,
and a `symbol` with the same bytes is a different value. Argument and rule indices
and thresholds are `UInt32`, as in the Rust evaluator; indices are read as list
positions and thresholds as counts through `toNat`: an index past the end of
the arguments is a missing argument, and one past the end of the rule set is
`AttenuationError.noSuchRule`. An argument of a type the other constructors do
not model is `other` of its full XDR. Values of different constructors are
never equal, so an `argEq` written for one type never holds on an argument of
another.

`allows`, `allowsAll` and `narrower` on chain rule sets are the generic ones on
the denotation, and each chain attenuation operation denotes the generic step of
the same kind (`Attenuation.denote`): removing or restricting functions denotes
restricting the scope. `RuleSet.checkAuth` is the generic authorization of
`RuleCore.Model.Authorize` on the denotation, with an authorization's choices
and ledger, `u32` here, and its generation, a `u64`, read as natural numbers;
the records are the cap model's own. The theorems in `RuleCore.Theorems.Chain`
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
  /-- A string, as its bytes. -/
  | string (v : Bytes)
  /-- An argument of a type the other constructors do not model, as its full
  XDR. -/
  | other (xdr : Bytes)
  deriving DecidableEq, Repr

/-- A value's constructor, without its payload. -/
inductive Kind where
  | i128 | u64 | bool | bytes | address | symbol | string | other
  deriving DecidableEq, Repr

def Val.kind : Val → Kind
  | .i128 _ => .i128
  | .u64 _ => .u64
  | .bool _ => .bool
  | .bytes _ => .bytes
  | .address _ => .address
  | .symbol _ => .symbol
  | .string _ => .string
  | .other _ => .other

/-- A signer: an address that authorizes for itself, or a key checked by a
verifier contract. -/
inductive Signer where
  /-- An address, as its `ScAddress` XDR. -/
  | delegated (address : Bytes)
  /-- A verifier contract's address, as its `ScAddress` XDR, and a key. -/
  | external (verifier : Bytes) (key : Bytes)
  deriving DecidableEq, Repr

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
  /-- Argument `index` exists and equals one of `vals`. -/
  | argIn (index : UInt32) (vals : List Val)
  /-- Argument `index` exists, is a `string`, and starts with the bytes
  `pre`. -/
  | argStrPrefix (index : UInt32) (pre : Bytes)
  deriving DecidableEq, Repr

def Cond.holds : Cond → List Val → Bool
  | .argEq i val, args => decide (args[i.toNat]? = some val)
  | .argI128AtMost i n, args =>
    match args[i.toNat]? with
    | some (.i128 v) => decide (v.toInt ≤ n.toInt)
    | _ => false
  | .argIn i vals, args =>
    match args[i.toNat]? with
    | some v => decide (v ∈ vals)
    | none => false
  | .argStrPrefix i pre, args =>
    match args[i.toNat]? with
    | some (.string v) => decide (pre <+: v)
    | _ => false

/-- The functions a rule matches on its contract: every function except the
listed ones, or only the listed ones. -/
inductive Functions where
  | anyExcept (removed : List Bytes)
  | only (listed : List Bytes)
  deriving DecidableEq, Repr

/-- The wildcard: every function. -/
def Functions.any : Functions := .anyExcept []

/-- Function `f` is one of `fs`. -/
def Functions.Mem (fs : Functions) (f : Bytes) : Prop :=
  match fs with
  | .anyExcept removed => f ∉ removed
  | .only listed => f ∈ listed

instance : Membership Bytes Functions := ⟨Functions.Mem⟩

@[simp] theorem Functions.mem_anyExcept {f : Bytes} {removed : List Bytes} :
    f ∈ Functions.anyExcept removed ↔ f ∉ removed := Iff.rfl

@[simp] theorem Functions.mem_only {f : Bytes} {listed : List Bytes} :
    f ∈ Functions.only listed ↔ f ∈ listed := Iff.rfl

instance (f : Bytes) : (fs : Functions) → Decidable (f ∈ fs)
  | .anyExcept removed => inferInstanceAs (Decidable (f ∉ removed))
  | .only listed => inferInstanceAs (Decidable (f ∈ listed))

/-- `fs` without the functions in `gs`. -/
def Functions.remove (fs : Functions) (gs : List Bytes) : Functions :=
  match fs with
  | .anyExcept removed => .anyExcept (removed ++ gs)
  | .only listed => .only (listed.filter fun f => decide (f ∉ gs))

/-- `fs` restricted to the functions in `gs`. -/
def Functions.restrict (fs : Functions) (gs : List Bytes) : Functions :=
  match fs with
  | .anyExcept removed => .only (gs.filter fun f => decide (f ∉ removed))
  | .only listed => .only (listed.filter fun f => decide (f ∈ gs))

/-- A spending cap: at most `limit` spent within `period` consecutive ledgers,
each call spending its argument at index `amountArg`. -/
structure Cap where
  limit : I128
  period : UInt32
  amountArg : UInt32
  deriving DecidableEq, Repr

/-- An exact contract/function pair at this account's authorization root. -/
structure AuthRoot where
  contract : Bytes
  function : Bytes
  deriving DecidableEq, Repr

def AuthRoot.matches (r : AuthRoot) : Context → Bool
  | .call contract function _ => decide (contract = r.contract) && decide (function = r.function)
  | .create _ => false

/-- Optional exact requirement evaluated on an optional entry root. -/
def AuthRoot.matchesOpt (requirement : Option AuthRoot) (root : Option Context) : Bool :=
  match requirement with
  | none => true
  | some expected => match root with
    | some c => expected.matches c
    | none => false

/-- Narrowing of the root component alone; an exact parent requires the
same exact child. Other rule constraints must be checked independently. -/
def AuthRoot.narrows (child parent : Option AuthRoot) : Bool :=
  match parent with
  | none => true
  | some expected => match child with
    | some actual => decide (actual.contract = expected.contract) &&
        decide (actual.function = expected.function)
    | none => false

structure Rule where
  contract : Bytes
  functions : Functions
  conds : List Cond
  signers : List Signer
  threshold : UInt32
  cap : Option Cap := none
  validUntil : Option UInt32 := none
  generation : Option UInt64 := none
  authRoot : Option AuthRoot := none
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

/-- A cap's parameters: its limit as a signed integer and its period as a
natural number. -/
def Cap.params (k : Cap) : RuleCore.Cap.Params :=
  ⟨k.limit.toInt, k.period.toNat⟩

/-- The amount a context spends under cap `k`: the call's argument at
`amountArg`, when it exists and is an `i128`. A creation spends no amount. -/
def Cap.amount (k : Cap) : Context → Option Int
  | .call _ _ args =>
    match args[k.amountArg.toNat]? with
    | some (.i128 v) => some v.toInt
    | _ => none
  | .create _ => none

/-- Whether cap `k` may be added to a rule: a positive limit and a nonzero
period. -/
def Cap.valid (k : Cap) : Bool :=
  k.params.valid

def Cap.denote (k : Cap) : RuleCap Context :=
  ⟨k.params, k.amount⟩

def Rule.denote (r : Rule) : RuleCore.Rule Context Signer :=
  { scope := r.scope, conds := r.conds.map Cond.denote, signers := r.signers,
    threshold := r.threshold.toNat, cap := r.cap.map Cap.denote,
    validUntil := r.validUntil.map (·.toNat), generation := r.generation.map (·.toNat),
    authRoot := r.authRoot.map AuthRoot.matches }

def RuleSet.denote (rs : RuleSet) : RuleCore.RuleSet Context Signer :=
  .ofRules (rs.map Rule.denote)

/-- The rule's signer requirement: at least `threshold` of its distinct
signers are among the authenticated `auth`. -/
def Rule.signed (r : Rule) (auth : List Signer) : Bool :=
  r.denote.signed auth

def Rule.allows (r : Rule) (c : Context) (auth : List Signer) : Bool :=
  r.denote.allows c auth

def RuleSet.allows (rs : RuleSet) (c : Context) (auth : List Signer) : Bool :=
  rs.denote.allows c auth

def RuleSet.allowsAll (rs : RuleSet) (cs : List Context) (auth : List Signer) : Bool :=
  rs.denote.allowsAll cs auth

def Rule.allowsIn (r : Rule) (root : Option Context) (c : Context) (auth : List Signer) : Bool :=
  r.denote.allowsIn root c auth

def RuleSet.allowsIn (rs : RuleSet) (root : Option Context) (c : Context)
    (auth : List Signer) : Bool :=
  rs.denote.allowsIn root c auth

def RuleSet.allowsBatch (rs : RuleSet) (cs : List Context) (auth : List Signer) : Bool :=
  rs.denote.allowsBatch cs auth

def RuleSet.narrower (rs' rs : RuleSet) : Prop :=
  rs'.denote.narrower rs.denote

/-! ## Attenuation -/

/-- Rule `r` with `cond` appended to its conditions. -/
def Rule.addCond (r : Rule) (cond : Cond) : Rule :=
  { r with conds := r.conds ++ [cond] }

/-- Rule `r` with every function in `fs` removed from its functions. -/
def Rule.removeFunctions (r : Rule) (fs : List Bytes) : Rule :=
  { r with functions := r.functions.remove fs }

/-- Rule `r` with its functions restricted to those in `fs`. -/
def Rule.restrictFunctions (r : Rule) (fs : List Bytes) : Rule :=
  { r with functions := r.functions.restrict fs }

/-- Rule `r` with every signer in `ss` removed from its signer list, its
threshold unchanged. -/
def Rule.removeSigners (r : Rule) (ss : List Signer) : Rule :=
  { r with signers := r.signers.filter (fun s => decide (s ∉ ss)) }

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

def RuleSet.restrictFunctions (rs : RuleSet) (i : UInt32) (fs : List Bytes) :
    Except AttenuationError RuleSet :=
  rs.modifyRule i.toNat (·.restrictFunctions fs)

def RuleSet.removeSigners (rs : RuleSet) (i : UInt32) (ss : List Signer) :
    Except AttenuationError RuleSet :=
  rs.modifyRule i.toNat (·.removeSigners ss)

/-- Set rule `i`'s threshold to `k`, refusing to lower it. -/
def RuleSet.raiseThreshold (rs : RuleSet) (i k : UInt32) : Except AttenuationError RuleSet :=
  match rs[i.toNat]? with
  | some r =>
    if k < r.threshold then .error .thresholdLowered
    else .ok (rs.set i.toNat { r with threshold := k })
  | none => .error .noSuchRule

/-- Give rule `i` the cap `k`, refusing a rule that has a cap and a cap that is
not valid. -/
def RuleSet.addCap (rs : RuleSet) (i : UInt32) (k : Cap) : Except AttenuationError RuleSet :=
  match rs[i.toNat]? with
  | some r =>
    match r.cap with
    | some _ => .error .capPresent
    | none => if k.valid then .ok (rs.set i.toNat { r with cap := some k }) else .error .invalidCap
  | none => .error .noSuchRule

/-- Set the limit of rule `i`'s cap to `limit`, refusing a rule without a cap,
a higher limit and a limit that is not positive. -/
def RuleSet.lowerCapLimit (rs : RuleSet) (i : UInt32) (limit : I128) :
    Except AttenuationError RuleSet :=
  match rs[i.toNat]? with
  | some r =>
    match r.cap with
    | some k =>
      if k.limit.toInt < limit.toInt then .error .limitRaised
      else if limit.toInt ≤ 0 then .error .invalidCap
      else .ok (rs.set i.toNat { r with cap := some { k with limit } })
    | none => .error .noCap
  | none => .error .noSuchRule

/-- Set the period of rule `i`'s cap to `period`, refusing a rule without a cap
and a shorter period. -/
def RuleSet.lengthenCapPeriod (rs : RuleSet) (i period : UInt32) :
    Except AttenuationError RuleSet :=
  match rs[i.toNat]? with
  | some r =>
    match r.cap with
    | some k =>
      if period < k.period then .error .periodShortened
      else .ok (rs.set i.toNat { r with cap := some { k with period } })
    | none => .error .noCap
  | none => .error .noSuchRule

/-- Set rule `i`'s last ledger to `v`, refusing to move it later. -/
def RuleSet.lowerValidUntil (rs : RuleSet) (i v : UInt32) : Except AttenuationError RuleSet :=
  match rs[i.toNat]? with
  | some r =>
    match r.validUntil with
    | some last =>
      if last < v then .error .validUntilRaised
      else .ok (rs.set i.toNat { r with validUntil := some v })
    | none => .ok (rs.set i.toNat { r with validUntil := some v })
  | none => .error .noSuchRule

/-- One attenuation step. -/
inductive Attenuation where
  | dropRule (i : UInt32)
  | addCond (i : UInt32) (cond : Cond)
  | removeFunctions (i : UInt32) (fs : List Bytes)
  | restrictFunctions (i : UInt32) (fs : List Bytes)
  | removeSigners (i : UInt32) (ss : List Signer)
  | raiseThreshold (i k : UInt32)
  | addCap (i : UInt32) (k : Cap)
  | lowerCapLimit (i : UInt32) (limit : I128)
  | lengthenCapPeriod (i period : UInt32)
  | lowerValidUntil (i v : UInt32)
  deriving DecidableEq, Repr

def RuleSet.attenuate (rs : RuleSet) : Attenuation → Except AttenuationError RuleSet
  | .dropRule i => rs.dropRule i
  | .addCond i cond => rs.addCond i cond
  | .removeFunctions i fs => rs.removeFunctions i fs
  | .restrictFunctions i fs => rs.restrictFunctions i fs
  | .removeSigners i ss => rs.removeSigners i ss
  | .raiseThreshold i k => rs.raiseThreshold i k
  | .addCap i k => rs.addCap i k
  | .lowerCapLimit i limit => rs.lowerCapLimit i limit
  | .lengthenCapPeriod i period => rs.lengthenCapPeriod i period
  | .lowerValidUntil i v => rs.lowerValidUntil i v

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

/-- The contexts that are a call to a function in `fs`. Restricting a rule's
functions to `fs` restricts its scope to these. -/
def calling (fs : List Bytes) : Context → Bool
  | .call _ function _ => decide (function ∈ fs)
  | .create _ => false

/-- The generic attenuation step a chain step denotes. -/
def Attenuation.denote : Attenuation → RuleCore.Attenuation Context Signer
  | .dropRule i => .dropRule i.toNat
  | .addCond i cond => .addCond i.toNat cond.denote
  | .removeFunctions i fs => .restrictScope i.toNat (notCalling fs)
  | .restrictFunctions i fs => .restrictScope i.toNat (calling fs)
  | .removeSigners i ss => .removeSigners i.toNat ss
  | .raiseThreshold i k => .raiseThreshold i.toNat k.toNat
  | .addCap i k => .addCap i.toNat k.denote
  | .lowerCapLimit i limit => .lowerCapLimit i.toNat limit.toInt
  | .lengthenCapPeriod i period => .lengthenCapPeriod i.toNat period.toNat
  | .lowerValidUntil i v => .lowerValidUntil i.toNat v.toNat

/-! ## Authorization -/

/-- One authorization: a batch of contexts, the index of the rule chosen for
each, the signers it authenticated, the ledger it is made in and the current
generation. -/
structure Authorization where
  contexts : List Context
  choices : List UInt32
  auth : List Signer
  now : UInt32
  generation : UInt64
  deriving DecidableEq, Repr

def Authorization.denote (a : Authorization) : RuleCore.Authorization Context Signer :=
  ⟨a.contexts, a.choices.map (·.toNat), a.auth, a.now.toNat, a.generation.toNat⟩

/-- The records after authorization `a`, or why it is refused. -/
def RuleSet.checkAuth (rs : RuleSet) (records : List RuleCore.Cap.Record) (a : Authorization) :
    Except Refusal (List RuleCore.Cap.Record) :=
  rs.denote.checkAuth records a.denote

/-- The records of a rule set that has spent nothing: one empty record per
rule. -/
def RuleSet.emptyRecords (rs : RuleSet) : List RuleCore.Cap.Record :=
  rs.map fun _ => .empty

/-- Apply every authorization in order, failing with the first refusal. -/
def RuleSet.checkAuthAll (rs : RuleSet) (records : List RuleCore.Cap.Record)
    (as : List Authorization) : Except Refusal (List RuleCore.Cap.Record) :=
  as.foldlM rs.checkAuth records

/-- `rs'` is narrower than `rs` as trace inclusion along `f`, on the
denotations. -/
def RuleSet.TraceNarrower (rs' rs : RuleSet) (f : Nat → Nat) : Prop :=
  rs'.denote.TraceNarrower rs.denote f

/-- The renumbering a list of chain steps induces, on the denoted steps. -/
def Attenuation.chainSource (steps : List Attenuation) : Nat → Nat :=
  RuleCore.Attenuation.chainSource (steps.map Attenuation.denote)

end RuleCore.Chain
