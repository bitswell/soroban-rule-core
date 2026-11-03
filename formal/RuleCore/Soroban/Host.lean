import RuleCore.Soroban.Storage
import RuleCore.Soroban.Auth

/-!
# Calls, rollback and authorization

A model of how `soroban-env-host` 27.0.1 runs a transaction of contract calls
with enforcing authorization, as soroban-sdk 27.0.6's testutils drive it with
`set_auths`.

A contract call (`Call`) is a contract, a function, arguments and a body of
steps: storage operations on the contract's own storage, `require_auth` of an
address, a call of another contract, caught or not, and failure (a contract
error or a trap, which the host treats alike). A contract account's
`__check_auth` is a program of `AccountStep`s: storage operations, a check of
the received contexts against a rule set (`checkRules`, the evaluator a shell
calls), delegation to a delegated signer (CAP-71) and failure.

## Rollback

Every call is a frame. When a call fails, the store, the used nonces and every
tracker are put back as they were when its frame was pushed, and the call's
caller fails too unless it caught the failure (`try_call`); a failed
transaction leaves storage as it was. Events (`Event`) are not rolled back:
they record what ran. A contract may not call a contract already on the call
stack; that call fails before a frame is pushed.

Instance storage is part of the store, so the call's own instance writes are
visible to a re-entrant `__check_auth` of the same contract, as on host 25 and
later (host #1617).

## `require_auth`

`require_auth` of address `a` in a frame with context `f`, in order:

1. it holds when the frame's direct caller is the contract `a` (`via` invoker);
2. otherwise the first tracker of `a` that `Tracker.extend` matches decides
   it, matching the root only when no tracker of `a` is active and not yet
   matched in this frame;
3. the first time a tracker matches, its entry is authenticated: `a`'s
   `__check_auth` runs with the payload, the signature and the tree's contexts
   in preorder (`Event.checkAuth`), then the signature must not have expired
   (the ledger is at most its last valid ledger), then its nonce is consumed,
   refused when already used.

No match, or any failure in step 3, fails `require_auth` and so the call.

`__check_auth` of `a` is refused when `a` is on the call stack below the
current frame (re-entry). A delegate's `__check_auth` is called with the
top-level payload and contexts and the delegate's own signature, may delegate
to its own delegates, is refused when the delegate is anywhere on the call
stack, and each delegate may be used once per authentication.

Only contract accounts authenticate: an entry or a delegate whose address is
a Stellar account (ed25519 signatures) is outside the model, and so are
`require_auth` inside `__check_auth`, `require_auth_for_args`,
`authorize_as_current_contract`, contract creation and source-account
credentials.
-/

namespace RuleCore.Soroban

open RuleCore

inductive FailKind where
  /-- The call returns a contract error. -/
  | error
  /-- The call traps. -/
  | trap
  deriving DecidableEq, Repr

mutual

/-- A step of a contract call. -/
inductive Step where
  | get (d : Durability) (key : Val)
  | has (d : Durability) (key : Val)
  | put (d : Durability) (key val : Val)
  | remove (d : Durability) (key : Val)
  | requireAuth (address : Address)
  /-- A call of another contract; with `catches`, a failure of it is caught. -/
  | call (callee : Call) (catches : Bool)
  | fail (kind : FailKind)

/-- A call of `fn` on `contract` with `args`, which runs `body`. -/
inductive Call where
  | mk (contract : Address) (fn : Bytes) (args : List Val) (body : List Step)

end

def Call.contract : Call → Address
  | .mk c _ _ _ => c

def Call.context : Call → AuthFn
  | .mk c f args _ => .contract c f args

def Call.body : Call → List Step
  | .mk _ _ _ body => body

/-- A step of an account's `__check_auth`. -/
inductive AccountStep where
  | get (d : Durability) (key : Val)
  | put (d : Durability) (key val : Val)
  | remove (d : Durability) (key : Val)
  /-- Fail unless `rules` allow every received context under `authenticated`. -/
  | checkRules (rules : Chain.RuleSet) (authenticated : List Chain.Signer)
  /-- Delegate to a delegated signer of the entry being authenticated. -/
  | delegate (address : Address)
  | fail (kind : FailKind)
  deriving Repr

/-- How a `require_auth` was satisfied. -/
inductive Via where
  /-- The frame's direct caller is the address. -/
  | invoker
  /-- An authorization entry of the address matched. -/
  | entry
  deriving DecidableEq, Repr

inductive Event where
  /-- `__check_auth` of `account` ran with the payload of `preimage`,
  `signature` and `contexts`. -/
  | checkAuth (account : Address) (preimage : Preimage) (signature : Val) (contexts : List AuthFn)
  /-- A `get` by `contract` read `value`. -/
  | read (contract : Address) (d : Durability) (key : Val) (value : Option Val)
  /-- A `has` by `contract` found `present`. -/
  | found (contract : Address) (d : Durability) (key : Val) (present : Bool)
  /-- `require_auth` of `address` held in a frame with context `fn`. -/
  | authorized (address : Address) (fn : AuthFn) (via : Via)
  deriving Repr

/-- What a transaction sees and changes. -/
structure World where
  store : Store := []
  /-- The used nonces, kept in storage by the host and rolled back with it. -/
  nonces : List (Address × Int) := []
  trackers : List Tracker := []
  /-- What ran, in order; never rolled back. -/
  log : List Event := []
  deriving Repr

/-- What is fixed during a transaction. -/
structure Config where
  /-- Each account's `__check_auth`; an address without one accepts. -/
  accounts : List (Address × List AccountStep)
  /-- The ledger's sequence number. -/
  ledger : Nat

def Config.program (cfg : Config) (a : Address) : List AccountStep :=
  ((cfg.accounts.find? fun e => decide (e.1 = a)).map (·.2)).getD []

def World.logged (w : World) (e : Event) : World :=
  { w with log := w.log ++ [e] }

/-- A storage operation by `contract`, recording what `get` and `has` read:
whether it succeeded, and the world after it. -/
def World.op (w : World) (contract : Address) (op : Op) : Bool × World :=
  match op.apply contract w.store with
  | none => (false, w)
  | some (obs, s) =>
    let w := { w with store := s }
    match op, obs with
    | .get d k, .value v => (true, w.logged (.read contract d k v))
    | .has d k, .present b => (true, w.logged (.found contract d k b))
    | _, _ => (true, w)

/-! ## `__check_auth` -/

/-- The first delegate in `ds` with address `a`, with its index. -/
def findDelegate (a : Address) : List Delegate → Nat → Option (Nat × Delegate)
  | [], _ => none
  | d :: ds, i => if d.address = a then some (i, d) else findDelegate a ds (i + 1)

theorem findDelegate_mem {a : Address} :
    ∀ {ds : List Delegate} {i j : Nat} {d : Delegate},
      findDelegate a ds i = some (j, d) → d ∈ ds
  | [], _, _, _, h => by simp [findDelegate] at h
  | x :: xs, i, j, d, h => by
    unfold findDelegate at h
    split at h
    · simp at h; simp [h.2]
    · exact List.mem_cons_of_mem _ (findDelegate_mem h)

theorem sizeOf_nested_lt {a : Address} {s : Val} {nested ds : List Delegate}
    (h : Delegate.mk a s nested ∈ ds) : sizeOf nested < sizeOf ds := by
  have := List.sizeOf_lt_of_mem h
  simp only [Delegate.mk.sizeOf_spec] at this
  omega

/-- Runs `steps` of `acct`'s `__check_auth` for an entry with payload `pre` and
contexts `ctxs`. `node` holds the delegates `acct` may delegate to, the
children of the delegate at `path`, and `used` the delegates already used in
this authentication. Returns whether it accepted, the world and the delegates
used. -/
def runAccount (cfg : Config) (stack : List Address) (pre : Preimage) (ctxs : List AuthFn)
    (node : List Delegate) (path : List Nat) (acct : Address) :
    List AccountStep → List (List Nat) → World → Bool × World × List (List Nat)
  | [], used, w => (true, w, used)
  | .get d k :: rest, used, w =>
    match w.op acct (.get d k) with
    | (true, w) => runAccount cfg stack pre ctxs node path acct rest used w
    | (false, w) => (false, w, used)
  | .put d k v :: rest, used, w =>
    match w.op acct (.set d k v) with
    | (true, w) => runAccount cfg stack pre ctxs node path acct rest used w
    | (false, w) => (false, w, used)
  | .remove d k :: rest, used, w =>
    match w.op acct (.remove d k) with
    | (true, w) => runAccount cfg stack pre ctxs node path acct rest used w
    | (false, w) => (false, w, used)
  | .checkRules rs auth :: rest, used, w =>
    if Chain.RuleSet.allowsAll rs (ctxs.map AuthFn.toChain) auth then
      runAccount cfg stack pre ctxs node path acct rest used w
    else (false, w, used)
  | .fail _ :: _, used, w => (false, w, used)
  | .delegate a :: rest, used, w =>
    match _h : findDelegate a node 0 with
    | none => (false, w, used)
    | some (i, .mk _ sig nested) =>
      if path ++ [i] ∈ used then (false, w, used)
      else if a ∈ stack then (false, w, used)
      else
        match a with
        | .contract _ =>
          match runAccount cfg (stack ++ [a]) pre ctxs nested (path ++ [i]) a (cfg.program a)
              (used ++ [path ++ [i]]) (w.logged (.checkAuth a pre sig ctxs)) with
          | (true, w, used) => runAccount cfg stack pre ctxs node path acct rest used w
          | (false, w, used) => (false, w, used)
        | _ => (false, w, used)
termination_by steps => (sizeOf node, sizeOf steps)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp; omega)
    | (apply Prod.Lex.left; exact sizeOf_nested_lt (findDelegate_mem _h))

/-- Authenticates entry `e` in a frame on top of `stack`: runs its address's
`__check_auth`. Refused when the address is on the stack below the top frame,
or is not a contract. -/
def authenticate (cfg : Config) (stack : List Address) (e : Entry) (w : World) : Bool × World :=
  if e.address ∈ stack ∧ stack.getLast? ≠ some e.address then (false, w)
  else
    match e.address with
    | .contract _ =>
      let ctxs := e.root.preorder
      let r := runAccount cfg (stack ++ [e.address]) e.preimage ctxs e.delegates [] e.address
        (cfg.program e.address) [] (w.logged (.checkAuth e.address e.preimage e.signature ctxs))
      (r.1, r.2.1)
    | _ => (false, w)

/-! ## `require_auth` -/

/-- Whether the frame on top of `stack` was called directly by contract `a`. -/
def invokedBy (stack : List Address) (a : Address) : Bool :=
  decide (stack.length ≥ 2) && decide (stack[stack.length - 2]? = some a)

/-- The first tracker of `a`, from position `i` on, that matches `f`: its
position and the tracker after the match. -/
def findTracker (f : AuthFn) (a : Address) (allowRoot : Bool) :
    List Tracker → Nat → Option (Nat × Tracker)
  | [], _ => none
  | t :: ts, i =>
    if t.entry.address = a then
      match t.extend f allowRoot with
      | some t' => some (i, t')
      | none => findTracker f a allowRoot ts (i + 1)
    else findTracker f a allowRoot ts (i + 1)

/-- `require_auth` of `a` in the frame on top of `stack`, whose context is
`f`. -/
def requireAuth (cfg : Config) (stack : List Address) (f : AuthFn) (a : Address) (w : World) :
    Bool × World :=
  if invokedBy stack a then (true, w.logged (.authorized a f .invoker))
  else
    let allowRoot := !(w.trackers.any fun t =>
      decide (t.entry.address = a) && t.active && !t.currentMatched)
    match findTracker f a allowRoot w.trackers 0 with
    | none => (false, w)
    | some (i, t) =>
      let w := { w with trackers := w.trackers.set i t }
      if t.verified then (true, w.logged (.authorized a f .entry))
      else
        match authenticate cfg stack t.entry w with
        | (false, w) => (false, w)
        | (true, w) =>
          if t.entry.expiration < cfg.ledger then (false, w)
          else if (a, t.entry.nonce) ∈ w.nonces then (false, w)
          else
            (true, { w with
              nonces := (a, t.entry.nonce) :: w.nonces,
              trackers := w.trackers.set i { t with verified := true } }.logged
              (.authorized a f .entry))

/-! ## Calls -/

mutual

/-- Runs a call from a frame stack `stack`: whether it succeeded, and the
world after it, rolled back to the world before it when it failed. -/
def execCall (cfg : Config) (stack : List Address) : Call → World → Bool × World
  | .mk c fn args body, w =>
    if c ∈ stack then (false, w)
    else
      let w1 := { w with trackers := w.trackers.map Tracker.push }
      let r := execSteps cfg (stack ++ [c]) (.contract c fn args) c body w1
      let w2 := if r.1 then r.2 else { w1 with log := r.2.log }
      (r.1, { w2 with trackers := w2.trackers.map Tracker.pop })

/-- Runs the steps of a call by `self` with context `f`, stopping at the
first failure. -/
def execSteps (cfg : Config) (stack : List Address) (f : AuthFn) (self : Address) :
    List Step → World → Bool × World
  | [], w => (true, w)
  | s :: rest, w =>
    let r := execStep cfg stack f self s w
    if r.1 then execSteps cfg stack f self rest r.2 else r

def execStep (cfg : Config) (stack : List Address) (f : AuthFn) (self : Address) :
    Step → World → Bool × World
  | .get d k, w => w.op self (.get d k)
  | .has d k, w => w.op self (.has d k)
  | .put d k v, w => w.op self (.set d k v)
  | .remove d k, w => w.op self (.remove d k)
  | .requireAuth a, w => requireAuth cfg stack f a w
  | .call c catches, w =>
    let r := execCall cfg stack c w
    if r.1 then r else (catches, r.2)
  | .fail _, w => (false, w)

end

/-! ## Transactions -/

/-- A transaction: the authorization entries it carries, its call and the
ledger it runs in. -/
structure Tx where
  entries : List Entry
  call : Call
  ledger : Nat

/-- Runs a transaction on a world: whether it succeeded, and the world after
it, with no trackers left. -/
def Tx.run (accounts : List (Address × List AccountStep)) (tx : Tx) (w : World) : Bool × World :=
  let r := execCall ⟨accounts, tx.ledger⟩ [] tx.call
    { w with trackers := tx.entries.map Tracker.ofEntry }
  (r.1, { r.2 with trackers := [] })

end RuleCore.Soroban
