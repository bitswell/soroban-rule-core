import RuleCore.Model.Attenuation

/-!
# Authorization

A rule set authorizes a batch with state. An authorization names, for each
context of its batch, the index of the rule that authorizes it: `choices[i]` is
the rule for `contexts[i]`, as OpenZeppelin's `AuthPayload::context_rule_ids`
selects one context rule per authorization context. Every rule keeps a
spending record (`Cap.Record`), `records[j]` for rule `j`; a rule without a
cap never changes its record.

An authorization is made at a ledger (`now`) and in a generation (the
account's current one). `RuleSet.authorize` first refuses a choice list whose
length is not the batch's (`choicesMismatch`) and a record list whose length is
not the rule set's (`recordsMismatch`), then works in three passes, as
OpenZeppelin's `do_check_auth` validates every context, then checks the
authenticated signers, before it enforces any policy:

1. in context order, every chosen rule exists (`noSuchRule`), has not expired
   at `now` (`expired`), was issued under the current generation when it
   carries one (`staleGeneration`), and allows its context under the
   authenticated signers and its root predicate at this batch's head (`notAllowed`);
2. every authenticated signer is a signer of some chosen rule
   (`unauthorizedSigner`);
3. in context order, every context whose chosen rule has a cap names an
   amount under that cap (`noAmount`) and is charged to the rule's record with
   `Cap.Params.check` (`cap e` when the check refuses), each charge against the
   record the charges before it left, so two contexts charging one rule
   accumulate.

It returns the records after every charge, or the first refusal, which leaves
the records as they were.

A run is a list of authorizations applied in order. `RuleSet.run` keeps the
records on a refused authorization; `RuleSet.authorizeAll` fails with the first
refusal, so `RuleSet.Accepts` says a run is accepted authorization by
authorization. `RuleSet.charged` lists the calls a run charges to one rule, and
`RuleSet.spent` the spends it records there: every charged call with a
positive amount.

`RuleSet.TraceNarrower rs' rs f` is narrowing as trace inclusion: every run
`rs'` accepts from its empty records, `rs` accepts from its own empty records,
with each choice `j` renumbered to `f j`. `Attenuation.source` is the
renumbering an attenuation step induces: `dropRule i` moves every rule after
`i` down by one, and every other step keeps each rule at its index.
`Attenuation.chainSource` composes it along a list of steps.
-/

namespace RuleCore

variable {Ctx Sig : Type}

/-- Why an authorization was refused. -/
inductive Refusal where
  /-- The choices do not hold exactly one rule index per context. -/
  | choicesMismatch
  /-- The records do not hold exactly one record per rule. -/
  | recordsMismatch
  /-- A chosen index is not below the number of rules. -/
  | noSuchRule
  /-- A chosen rule's last ledger is before the authorization's. -/
  | expired
  /-- A chosen rule was issued under a generation other than the current one. -/
  | staleGeneration
  /-- A chosen rule does not allow its context under the authenticated
  signers. -/
  | notAllowed
  /-- An authenticated signer is a signer of no chosen rule. -/
  | unauthorizedSigner
  /-- A chosen rule has a cap and its context names no amount under it. -/
  | noAmount
  /-- A chosen rule's cap refused the spend. -/
  | cap (e : Cap.CapError)
  deriving DecidableEq, Repr

/-- One authorization: a batch of contexts, the rule chosen for each, the
signers it authenticated, the ledger it is made in and the current
generation. -/
structure Authorization (Ctx Sig : Type) where
  contexts : List Ctx
  choices : List Nat
  auth : List Sig
  now : Nat
  generation : Nat

/-- The contexts of `a`, each with the index of the rule chosen for it. -/
def Authorization.chosen (a : Authorization Ctx Sig) : List (Ctx × Nat) :=
  a.contexts.zip a.choices

/-- The records of a rule set that has spent nothing: one empty record per
rule. -/
def RuleSet.emptyRecords (rs : RuleSet Ctx Sig) : List Cap.Record :=
  rs.rules.map fun _ => .empty

/-- The third pass for one context `x.1` and its chosen rule `x.2`: the
records after charging the context to that rule's record when the rule has a
cap, unchanged when it has none. -/
def RuleSet.charge (rs : RuleSet Ctx Sig) (now : Nat) (records : List Cap.Record)
    (x : Ctx × Nat) : Except Refusal (List Cap.Record) :=
  match rs.rules[x.2]? with
  | some r =>
    match r.cap with
    | some k =>
      match k.amount x.1 with
      | some amount =>
        match records[x.2]? with
        | some rec =>
          match k.params.check rec now amount with
          | .ok rec' => .ok (records.set x.2 rec')
          | .error e => .error (.cap e)
        | none => .error .recordsMismatch
      | none => .error .noAmount
    | none => .ok records
  | none => .error .noSuchRule

section

variable [DecidableEq Sig]

/-- The first pass for one context `x.1` and its chosen rule `x.2`, at ledger
`now` in generation `gen`: the rule exists, has not expired, is not stale, and
allows the context under `auth`. -/
def RuleSet.checkChoice (rs : RuleSet Ctx Sig) (auth : List Sig) (now gen : Nat)
    (root : Option Ctx) (x : Ctx × Nat) : Except Refusal Unit :=
  match rs.rules[x.2]? with
  | some r =>
    if r.expired now then .error .expired
    else if r.stale gen then .error .staleGeneration
    else if r.allowsIn root x.1 auth then .ok () else .error .notAllowed
  | none => .error .noSuchRule

/-- Signer `s` is a signer of some rule that `choices` names. -/
def RuleSet.signerChosen (rs : RuleSet Ctx Sig) (choices : List Nat) (s : Sig) : Bool :=
  choices.any fun j =>
    match rs.rules[j]? with
    | some r => decide (s ∈ r.signers)
    | none => false

/-- The second pass: every authenticated signer is a signer of some chosen
rule. -/
def RuleSet.checkSigners (rs : RuleSet Ctx Sig) (auth : List Sig) (choices : List Nat) :
    Except Refusal Unit :=
  if auth.all (rs.signerChosen choices) then .ok () else .error .unauthorizedSigner

/-- The records after authorization `a`, or why it is refused. -/
def RuleSet.authorize (rs : RuleSet Ctx Sig) (records : List Cap.Record)
    (a : Authorization Ctx Sig) : Except Refusal (List Cap.Record) :=
  if a.choices.length ≠ a.contexts.length then .error .choicesMismatch
  else if records.length ≠ rs.rules.length then .error .recordsMismatch
  else do
    a.chosen.forM (rs.checkChoice a.auth a.now a.generation a.contexts.head?)
    rs.checkSigners a.auth a.choices
    a.chosen.foldlM (rs.charge a.now) records

/-! ## Runs -/

/-- The records after one authorization: the authorized records, or the same
records when it is refused. -/
def RuleSet.step (rs : RuleSet Ctx Sig) (records : List Cap.Record)
    (a : Authorization Ctx Sig) : List Cap.Record :=
  match rs.authorize records a with
  | .ok records' => records'
  | .error _ => records

/-- The records after every authorization of `as`, each refused one leaving
them as they were. -/
def RuleSet.run (rs : RuleSet Ctx Sig) (records : List Cap.Record)
    (as : List (Authorization Ctx Sig)) : List Cap.Record :=
  as.foldl rs.step records

/-- Apply every authorization in order, failing with the first refusal. -/
def RuleSet.authorizeAll (rs : RuleSet Ctx Sig) (records : List Cap.Record)
    (as : List (Authorization Ctx Sig)) : Except Refusal (List Cap.Record) :=
  as.foldlM rs.authorize records

/-- `rs` accepts every authorization of `as`, starting from `records`. -/
def RuleSet.Accepts (rs : RuleSet Ctx Sig) (records : List Cap.Record)
    (as : List (Authorization Ctx Sig)) : Prop :=
  ∃ records', rs.authorizeAll records as = .ok records'

/-- The calls `a` charges to rule `j` under its cap `k`: one call at `a.now` for
each context that chose `j`, spending the amount `k` reads from it. -/
def Authorization.charges (a : Authorization Ctx Sig) (k : RuleCap Ctx) (j : Nat) :
    List Cap.Call :=
  a.chosen.filterMap fun x => if x.2 = j then (k.amount x.1).map (⟨a.now, ·⟩) else none

/-- The calls a run charges to rule `j` under its cap `k`: the charges of each
authorization the run accepts, in order. -/
def RuleSet.charged (rs : RuleSet Ctx Sig) (k : RuleCap Ctx) (j : Nat) :
    List Cap.Record → List (Authorization Ctx Sig) → List Cap.Call
  | _, [] => []
  | records, a :: as =>
    match rs.authorize records a with
    | .ok records' => a.charges k j ++ rs.charged k j records' as
    | .error _ => rs.charged k j records as

/-- The spends a run records for rule `j` under its cap `k`: each call it
charges there with a positive amount, as an entry. -/
def RuleSet.spent (rs : RuleSet Ctx Sig) (k : RuleCap Ctx) (j : Nat)
    (records : List Cap.Record) (as : List (Authorization Ctx Sig)) : List Cap.Entry :=
  ((rs.charged k j records as).filter (fun x => decide (0 < x.amount))).map
    fun x => ⟨x.now, x.amount⟩

end

/-! ## Narrowing as trace inclusion -/

/-- Authorization `a` with each choice `j` renumbered to `f j`. -/
def Authorization.renumber (a : Authorization Ctx Sig) (f : Nat → Nat) :
    Authorization Ctx Sig :=
  { a with choices := a.choices.map f }

/-- `rs'` is narrower than `rs` as trace inclusion along `f`: every run of
authorizations `rs'` accepts from its empty records, `rs` accepts from its own
empty records, with each choice `j` renumbered to `f j`. -/
def RuleSet.TraceNarrower [DecidableEq Sig] (rs' rs : RuleSet Ctx Sig) (f : Nat → Nat) :
    Prop :=
  ∀ as, rs'.Accepts rs'.emptyRecords as →
    rs.Accepts rs.emptyRecords (as.map (·.renumber f))

/-- The renumbering step `a` induces: the rule at index `j` after the step is
the rule at index `a.source j` before it. -/
def Attenuation.source : Attenuation Ctx Sig → Nat → Nat
  | .dropRule i, j => if j < i then j else j + 1
  | _, j => j

/-- The renumbering a list of steps induces: the rule at index `j` after every
step is the rule at index `chainSource steps j` of the root. -/
def Attenuation.chainSource : List (Attenuation Ctx Sig) → Nat → Nat
  | [], j => j
  | a :: steps, j => a.source (chainSource steps j)

/-- Every cap of `rs` may be installed: its parameters are valid. -/
def RuleSet.capsValid (rs : RuleSet Ctx Sig) : Prop :=
  ∀ r ∈ rs.rules, ∀ k, r.cap = some k → k.params.valid = true

end RuleCore
