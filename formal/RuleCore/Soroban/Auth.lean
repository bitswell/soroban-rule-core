import RuleCore.Soroban.Context

/-!
# Signed authorization trees

An authorization entry (`Entry`) is what an address signs: an invocation tree
(`Invocation`), a nonce, the last ledger the signature is valid in, the
signature and the kind of credentials. There are three kinds, as in protocol
27 (CAP-46-11, CAP-71):

* `address` (`SOROBAN_CREDENTIALS_ADDRESS`): the signature payload is the hash
  of `HashIdPreimage::SorobanAuthorization`, which does not name the address;
* `addressV2` (`SOROBAN_CREDENTIALS_ADDRESS_V2`): the payload is the hash of
  `HashIdPreimage::SorobanAuthorizationWithAddress`, which binds the address;
* `withDelegates` (`SOROBAN_CREDENTIALS_ADDRESS_WITH_DELEGATES`): the
  address-bound payload, and a tree of delegates, each an address with its own
  signature and delegates of its own.

`Entry.preimage` is what the payload hashes: the network id (the ledger's),
the address when the credentials bind it, the nonce, the last valid ledger and
the whole invocation tree. `Invocation.preorder` is the tree's nodes in
preorder, the contexts `__check_auth` receives.

## Matching

`Tracker` follows `soroban-env-host` 27.0.1's `AccountAuthorizationTracker`.
It holds one entry, the nodes of its tree already matched (`exhausted`, as
paths of child indices, `[]` the root), and a match state for each frame on
the call stack (`stack`, outermost first): unmatched, the root, or the child
of the previous match with that index. `Tracker.extend` matches a
`require_auth` of the frame on top of the stack:

* nothing, if the top frame already matched in this tracker;
* when a frame on the stack matched the root, the first unexhausted child of
  the deepest matched node whose context is the frame's;
* otherwise the root, when it is unexhausted, the frame's context is the
  root's and no other tracker of the address is active (`allowRoot`).

A tracker is active from the frame that matched its root until that frame
returns (`active`), and then done for the rest of the transaction.
-/

namespace RuleCore.Soroban

open RuleCore

/-- A node of a signed tree: the context it authorizes and the calls under it. -/
inductive Invocation where
  | node (fn : AuthFn) (subs : List Invocation)
  deriving Repr

def Invocation.fn : Invocation → AuthFn
  | .node f _ => f

def Invocation.subs : Invocation → List Invocation
  | .node _ subs => subs

mutual

/-- The tree's contexts in preorder: the node, then each child's subtree. -/
def Invocation.preorder : Invocation → List AuthFn
  | .node f subs => f :: Invocation.preorderList subs

def Invocation.preorderList : List Invocation → List AuthFn
  | [] => []
  | i :: is => i.preorder ++ Invocation.preorderList is

end

/-- The node reached by following child indices `p` from the root. -/
def Invocation.at : Invocation → List Nat → Option Invocation
  | i, [] => some i
  | .node _ subs, j :: p =>
    match subs[j]? with
    | some c => c.at p
    | none => none

/-- A delegated signer (CAP-71): its address, its signature and its own
delegates. -/
inductive Delegate where
  | mk (address : Address) (signature : Val) (nested : List Delegate)
  deriving Repr

def Delegate.address : Delegate → Address
  | .mk a _ _ => a

inductive Credentials where
  /-- `SOROBAN_CREDENTIALS_ADDRESS`. -/
  | address
  /-- `SOROBAN_CREDENTIALS_ADDRESS_V2`. -/
  | addressV2
  /-- `SOROBAN_CREDENTIALS_ADDRESS_WITH_DELEGATES`. -/
  | withDelegates (delegates : List Delegate)
  deriving Repr

structure Entry where
  address : Address
  nonce : Int
  /-- The last ledger the signature is valid in. -/
  expiration : Nat
  signature : Val
  credentials : Credentials
  root : Invocation
  deriving Repr

/-- What an entry's signature payload is the SHA-256 hash of, besides the
ledger's network id. -/
structure Preimage where
  /-- The signer's address, when the credentials bind it. -/
  address : Option Address
  nonce : Int
  expiration : Nat
  invocation : Invocation
  deriving Repr

def Entry.preimage (e : Entry) : Preimage :=
  { address := match e.credentials with
      | .address => none
      | _ => some e.address,
    nonce := e.nonce, expiration := e.expiration, invocation := e.root }

/-- The entry's delegates; none unless its credentials carry them. -/
def Entry.delegates (e : Entry) : List Delegate :=
  match e.credentials with
  | .withDelegates ds => ds
  | _ => []

/-! ## The tracker -/

/-- How a frame on the call stack matched a tracker's tree. -/
inductive Match where
  | unmatched
  | root
  /-- The child with this index of the node matched before. -/
  | sub (index : Nat)
  deriving DecidableEq, Repr

structure Tracker where
  entry : Entry
  /-- The matched nodes, as paths from the root. -/
  exhausted : List (List Nat) := []
  /-- One match state per frame on the call stack, outermost first. -/
  stack : List Match := []
  /-- The frame that matched the root, by its position on the stack. -/
  rootFrame : Option Nat := none
  /-- The root's frame has returned. -/
  done : Bool := false
  /-- The entry has been authenticated: its `__check_auth` accepted, its
  signature had not expired and its nonce was unused. -/
  verified : Bool := false
  deriving Repr

def Tracker.ofEntry (e : Entry) : Tracker :=
  { entry := e }

/-- The path of the deepest matched node on the stack: the child indices
recorded after the root's frame, or nothing when no frame on the stack matched
the root. -/
def lastPath : List Match → Option (List Nat)
  | [] => none
  | .root :: rest => some (subPath rest)
  | _ :: rest => lastPath rest
where
  subPath : List Match → List Nat
    | [] => []
    | .sub i :: rest => i :: subPath rest
    | _ :: rest => subPath rest

/-- Whether the frame on top of the stack already matched in this tracker. -/
def Tracker.currentMatched (t : Tracker) : Bool :=
  match t.stack.getLast? with
  | some .unmatched | none => false
  | _ => true

def Tracker.active (t : Tracker) : Bool :=
  decide ([] ∈ t.exhausted) && !t.done

/-- The first child of the node at `p`, from position `i` on, that is
unexhausted and authorizes `f`: its index. -/
def firstFree (exhausted : List (List Nat)) (p : List Nat) (f : AuthFn) :
    List Invocation → Nat → Option Nat
  | [], _ => none
  | c :: cs, i =>
    if decide (p ++ [i] ∉ exhausted) && decide (c.fn = f) then some i
    else firstFree exhausted p f cs (i + 1)

/-- The stack with its last match state replaced. -/
def setTop (s : List Match) (m : Match) : List Match :=
  s.dropLast ++ [m]

/-- Matches a `require_auth` of the top frame, whose context is `f`: the
tracker after the match, or nothing when this tracker does not match it. -/
def Tracker.extend (t : Tracker) (f : AuthFn) (allowRoot : Bool) : Option Tracker :=
  if t.currentMatched then none
  else
    match lastPath t.stack with
    | some p =>
      match t.entry.root.at p with
      | some n =>
        match firstFree t.exhausted p f n.subs 0 with
        | some i => some { t with exhausted := (p ++ [i]) :: t.exhausted, stack := setTop t.stack (.sub i) }
        | none => none
      | none => none
    | none =>
      if decide ([] ∉ t.exhausted) && allowRoot && decide (t.entry.root.fn = f) then
        some { t with
          exhausted := [] :: t.exhausted,
          stack := setTop t.stack .root,
          rootFrame := some (t.stack.length - 1) }
      else none

/-- A frame is pushed on the call stack. -/
def Tracker.push (t : Tracker) : Tracker :=
  { t with stack := t.stack ++ [.unmatched] }

/-- The top frame returns: when it is the root's frame, the tracker is done. -/
def Tracker.pop (t : Tracker) : Tracker :=
  let s := t.stack.dropLast
  { t with
    stack := s,
    done := t.done || match t.rootFrame with
      | some r => decide (s.length ≤ r)
      | none => false }

end RuleCore.Soroban
