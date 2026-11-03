import Conformance.Random
import Conformance.Soroban.Values

/-!
# Host traces

A host trace is the `__check_auth` programs of some contract accounts and a
list of transactions, each a ledger, the authorization entries it carries and
a call tree. `Trace.toJson` runs the transactions through the model's
`Tx.run`, each on the world the transactions before it left, and writes each
with what the model gives for it: whether it succeeded, the events it
recorded, and the value of every slot the trace touches afterwards.

The named traces cover `require_auth` matched against the signed tree (the
exact tree, mismatched arguments, a replayed nonce, an expired signature, a
refusing `__check_auth`, nested and missing nodes, a tree rooted below the top
call, an unused signed node, two `require_auth`s in one frame, disjoint
entries), what `__check_auth` receives for each kind of credentials
(including delegation, nested delegation and its refusals), the invoker rule,
re-entry, rollback of storage and of authorization state on caught and
uncaught failures, instance storage seen by a re-entrant `__check_auth`, and
an account that checks its contexts with `rule-eval`. The randomized traces
draw call trees over a few contracts and two accounts, with entries built
from the tree's `require_auth`s and then often changed.
-/

namespace Conformance.Soroban.Host

open RuleCore RuleCore.Soroban
open Conformance.Soroban.Values
open Conformance.Random (Gen below pick listOf pad)

/-- The version of the host trace format in `conformance/README.md`. -/
def formatVersion : Nat := 1

/-- The number of committed randomized traces, of the vectors' seed. -/
def defaultCount : Nat := 60

structure Trace where
  name : String
  description : String
  accounts : List (Address × List AccountStep) := []
  txs : List Tx

/-! ## What a trace touches -/

mutual

/-- The calls of a tree, the top one first. -/
def callsOf : Call → List Call
  | c@(.mk _ _ _ body) => c :: callsOfSteps body

def callsOfSteps : List Step → List Call
  | [] => []
  | .call c _ :: rest => callsOf c ++ callsOfSteps rest
  | _ :: rest => callsOfSteps rest

end

def stepSlot (c : Address) : Step → Option Slot
  | .get d k | .has d k | .put d k _ | .remove d k => some ⟨c, d, k⟩
  | _ => none

def accountStepSlot (c : Address) : AccountStep → Option Slot
  | .get d k | .put d k _ | .remove d k => some ⟨c, d, k⟩
  | _ => none

mutual

def delegateAddresses : List Delegate → List Address
  | [] => []
  | .mk a _ nested :: ds => a :: delegateAddresses nested ++ delegateAddresses ds

end

def Trace.calls (t : Trace) : List Call :=
  t.txs.flatMap fun tx => callsOf tx.call

/-- Every slot a call or an account program reads or writes. -/
def Trace.slots (t : Trace) : List Slot :=
  (t.calls.flatMap (fun c => c.body.filterMap (stepSlot c.contract)) ++
    t.accounts.flatMap fun (a, prog) => prog.filterMap (accountStepSlot a)).eraseDups

def requireAuthTargets (c : Call) : List Address :=
  c.body.filterMap fun
    | .requireAuth a => some a
    | _ => none

/-- Every contract the harness registers. -/
def Trace.contracts (t : Trace) : List Address :=
  (t.calls.map Call.contract ++ t.accounts.map (·.1) ++
    t.txs.flatMap (fun tx => tx.entries.flatMap fun e => e.address :: delegateAddresses e.delegates) ++
    t.calls.flatMap requireAuthTargets).eraseDups

/-! ## The domain the harness can drive -/

def isContract : Address → Bool
  | .contract i => i.length == 32
  | _ => false

/-- A symbol the host accepts: at most 32 characters from `[a-zA-Z0-9_]`. -/
def symbolOk (s : Bytes) : Bool :=
  s.length ≤ 32 && s.all fun c =>
    (c ≥ 48 && c ≤ 57) || (c ≥ 65 && c ≤ 90) || (c ≥ 97 && c ≤ 122) || c == 95

def u32Ascending : List Val → Bool
  | .u32 x :: .u32 y :: rest => x < y && u32Ascending (.u32 y :: rest)
  | [.u32 _] | [] => true
  | _ => false

mutual

/-- Whether the host accepts the value: valid symbols, 32-byte account and
contract addresses, and map keys that are `u32`s in increasing order. -/
def hostOk : Val → Bool
  | .symbol s => symbolOk s
  | .address (.contract i) | .address (.account i) | .address (.muxedAccount _ i) => i.length == 32
  | .vec items => hostOkList items
  | .map es => u32Ascending (es.map (·.1)) && hostOkEntries es
  | _ => true

def hostOkList : List Val → Bool
  | [] => true
  | v :: vs => hostOk v && hostOkList vs

def hostOkEntries : List (Val × Val) → Bool
  | [] => true
  | (k, v) :: es => hostOk k && hostOk v && hostOkEntries es

end

def authFnOk : AuthFn → Bool
  | .contract c f args => isContract c && symbolOk f && args.all Conformance.Soroban.Host.hostOk
  | .create .. => false

mutual

def invocationOk : Invocation → Bool
  | .node f subs => authFnOk f && invocationsOk subs

def invocationsOk : List Invocation → Bool
  | [] => true
  | i :: is => invocationOk i && invocationsOk is

end

def idOf : Address → Bytes
  | .contract i => i
  | _ => []

def bytesLt : Bytes → Bytes → Bool
  | [], _ :: _ => true
  | x :: xs, y :: ys => x < y || (x == y && bytesLt xs ys)
  | _, _ => false

mutual

/-- Delegates are contracts, in increasing order of address at each level, as
the host requires. -/
def delegatesOk : List Delegate → Bool
  | [] => true
  | .mk a sig nested :: ds =>
    isContract a && hostOk sig && delegatesOk nested && delegatesOk ds &&
      match ds with
      | .mk a' _ _ :: _ => bytesLt (idOf a) (idOf a')
      | [] => true

end

def slotOk (s : Slot) : Bool :=
  hostOk s.key && (s.key.storable || s.durability != .contractInstance)

def stepOk (c : Address) : Step → Bool
  | .requireAuth a => isContract a
  | s => match stepSlot c s with
    | some slot => slotOk slot && match s with
      | .put _ _ v => hostOk v
      | _ => true
    | none => true

def accountStepOk (a : Address) : AccountStep → Bool
  | .delegate d => isContract d
  | s => match accountStepSlot a s with
    | some slot => slotOk slot && match s with
      | .put _ _ v => hostOk v
      | _ => true
    | none => true

/-- Whether the harness can drive the trace on the host: contracts and their
calls are well formed, entries and delegates are for contracts, muxed keys
stay out of instance storage, every transaction runs between ledgers 100 and
115 (so temporary entries and nonces stay live) and every signature is valid
for at most 1000 ledgers past its transaction. -/
def Trace.inDomain (t : Trace) : Bool :=
  t.contracts.all isContract &&
  t.calls.all (fun c => authFnOk c.context && c.body.all (stepOk c.contract)) &&
  t.accounts.all (fun (a, prog) => isContract a && prog.all (accountStepOk a)) &&
  t.txs.all fun tx =>
    100 ≤ tx.ledger && tx.ledger ≤ 115 &&
    tx.entries.all fun e =>
      isContract e.address && invocationOk e.root && hostOk e.signature &&
      delegatesOk e.delegates && e.expiration ≤ tx.ledger + 1000 &&
      -(2 ^ 63) ≤ e.nonce && e.nonce < 2 ^ 63

/-! ## Running and encoding -/

def Trace.outcomes (t : Trace) : List (Bool × List Event × Store) :=
  go t.txs {}
where
  go : List Tx → World → List (Bool × List Event × Store)
    | [], _ => []
    | tx :: txs, w =>
      let r := tx.run t.accounts { w with log := [] }
      (r.1, r.2.log, r.2.store) :: go txs r.2

def encodeStore (slots : List Slot) (s : Store) : Json :=
  .arr (slots.map fun k => .obj [
    ("contract", encodeAddress k.contract),
    ("durability", encodeDurability k.durability),
    ("key", encodeValue k.key),
    ("value", encodeOption encodeValue (s.get k))])

def Trace.toJson (t : Trace) : Json :=
  let slots := t.slots
  .obj [
    ("format", .num formatVersion),
    ("name", .str t.name),
    ("description", .str t.description),
    ("contracts", .arr (t.contracts.map encodeAddress)),
    ("accounts", .arr (t.accounts.map fun (a, prog) =>
      .obj [("address", encodeAddress a), ("check_auth", .arr (prog.map encodeAccountStep))])),
    ("txs", .arr ((t.txs.zip t.outcomes).map fun (tx, ok, events, store) => .obj [
      ("ledger", .num tx.ledger),
      ("entries", .arr (tx.entries.map encodeEntry)),
      ("call", encodeCall tx.call),
      ("expected", .obj [
        ("ok", .bool ok),
        ("events", .arr (events.map encodeEvent)),
        ("store", encodeStore slots store)])]))]

/-! ## Builders -/

def token : Address := contract 0x01
def router : Address := contract 0x02
def vault : Address := contract 0x03
def account1 : Address := contract 0xa1
def account2 : Address := contract 0xa2
def delegate1 : Address := contract 0xd1
def delegate2 : Address := contract 0xd2
/-- A Stellar account, as an argument. -/
def payee : Address := account 0x09

def addr (a : Address) : Val := .address a
def key (s : String) : Val := .symbol (b s)

def mkCall (c : Address) (f : String) (args : List Val) (body : List Step) : Call :=
  .mk c (b f) args body

def node (c : Address) (f : String) (args : List Val) (subs : List Invocation := []) : Invocation :=
  .node (.contract c (b f) args) subs

def nodeOf (c : Call) (subs : List Invocation := []) : Invocation :=
  .node c.context subs

def entry (a : Address) (nonce : Int) (root : Invocation) (expiration : Nat := 150)
    (signature : Val := .void) (credentials : Credentials := .address) : Entry :=
  { address := a, nonce, expiration, signature, credentials, root }

def tx (entries : List Entry) (call : Call) (ledger : Nat := 100) : Tx :=
  { entries, call, ledger }

/-- `token.pay(from, to, amount)`, which requires `from`. -/
def pay (from_ to : Address) (amount : Int) : Call :=
  mkCall token "pay" [addr from_, addr to, i128 amount] [.requireAuth from_]

/-- A rule allowing every function of `c`, with no signer requirement. -/
def anyRule (c : Address) : Chain.Rule :=
  { contract := c.xdr, functions := .any, conds := [], signers := [], threshold := 0 }

def onlyRule (c : Address) (fs : List String) : Chain.Rule :=
  { contract := c.xdr, functions := .only (fs.map b), conds := [], signers := [], threshold := 0 }

/-! ## Named traces -/

def payTx (nonce : Int) (amount : Int := 10) (signed : Int := 10) (expiration : Nat := 150)
    (credentials : Credentials := .address) (ledger : Nat := 100) : Tx :=
  tx [entry account1 nonce (nodeOf (pay account1 payee signed)) expiration (credentials := credentials)]
    (pay account1 payee amount) ledger

/-- `router.pay_nested(from, token, amount)`: requires `from`, then calls
`token.pay(from, router, amount)`. -/
def payNested : Call :=
  mkCall router "pay_nested" [addr account1, addr token, i128 5]
    [.requireAuth account1, .call (pay account1 router 5) false]

/-- `router.relay(from, token, amount)`: calls `token.pay(from, router,
amount)` without requiring `from` itself. -/
def relay : Call :=
  mkCall router "relay" [addr account1, addr token, i128 5] [.call (pay account1 router 5) false]

def payTwice : Call :=
  mkCall token "pay_twice" [addr account1, addr payee, i128 5] [.requireAuth account1, .requireAuth account1]

/-- `account.admin_set(7)`: writes instance key `x`, then requires the
account itself, as OpenZeppelin's smart account does. -/
def adminSet (a : Address) : Call :=
  mkCall a "admin_set" [.u32 7] [.put .contractInstance (key "x") (.u32 7), .requireAuth a]

def putThenFail (c : Address) (kind : FailKind) : Call :=
  mkCall c (match kind with | .error => "put_then_fail" | .trap => "put_then_trap") [.u32 2]
    [.put .persistent (key "k") (.u32 2), .fail kind]

def withDelegate1 : Credentials :=
  .withDelegates [.mk delegate1 (.u32 1) []]

def named : List Trace := [
  { name := "host-exact-tree"
    description := "The signed tree is exactly the call: accepted, with one __check_auth of the whole tree."
    txs := [payTx 1] },
  { name := "host-arguments-mismatch"
    description := "The call pays 11 where the tree signed 10: no node matches, so the call is refused."
    txs := [payTx 2 (amount := 11)] },
  { name := "host-nonce-replay"
    description :=
      "The same entry twice: the second transaction's __check_auth accepts, then its used nonce " ++
      "refuses it."
    txs := [payTx 3, payTx 3 (ledger := 101)] },
  { name := "host-expired-signature"
    description := "The signature's last ledger is before the transaction's: __check_auth runs, then the call is refused."
    txs := [payTx 4 (expiration := 99)] },
  { name := "host-signature-valid-in-its-last-ledger"
    description := "A signature is still valid in its last ledger."
    txs := [payTx 5 (expiration := 100)] },
  { name := "host-check-auth-refuses"
    description := "The account's __check_auth fails, with an error and then with a trap."
    accounts := [(account1, [.fail .error]), (account2, [.fail .trap])]
    txs := [
      payTx 6,
      tx [entry account2 6 (nodeOf (pay account2 payee 10))] (pay account2 payee 10)] },
  { name := "host-nested-tree"
    description := "A call and a call it makes, both requiring the account: one __check_auth of both, in preorder."
    txs := [tx [entry account1 10 (nodeOf payNested [nodeOf (pay account1 router 5)])] payNested] },
  { name := "host-nested-call-missing"
    description := "The tree omits the nested call, so its require_auth is refused."
    txs := [tx [entry account1 11 (nodeOf payNested)] payNested] },
  { name := "host-disjoint-entries"
    description :=
      "Two entries, one for each call: while the first is active the second cannot match a root, " ++
      "so the nested call is refused."
    txs := [tx [entry account1 12 (nodeOf payNested), entry account1 13 (nodeOf (pay account1 router 5))]
      payNested] },
  { name := "host-root-below-top-call"
    description := "The tree is rooted at a call below the transaction's top call: accepted."
    txs := [tx [entry account1 14 (nodeOf (pay account1 router 5))] relay] },
  { name := "host-unused-signed-node"
    description :=
      "The tree signs a call that never happens: accepted, and __check_auth still receives that " ++
      "node's context."
    txs := [tx [entry account1 15 (nodeOf (pay account1 payee 10) [node vault "run" []])]
      (pay account1 payee 10)] },
  { name := "host-require-auth-twice-in-one-frame"
    description := "Two require_auths in one frame need two entries: one is refused, two are accepted."
    txs := [
      tx [entry account1 16 (nodeOf payTwice)] payTwice,
      tx [entry account1 17 (nodeOf payTwice), entry account1 18 (nodeOf payTwice)] payTwice] },
  { name := "host-two-signers"
    description := "One call requiring two accounts, each with its own entry and its own __check_auth."
    txs := [
      let swap := mkCall token "swap" [addr account1, addr account2]
        [.requireAuth account1, .requireAuth account2]
      tx [entry account2 20 (nodeOf swap), entry account1 19 (nodeOf swap)] swap] },
  { name := "host-address-bound-payload"
    description := "ADDRESS_V2 credentials: the payload's preimage binds the account's address."
    txs := [payTx 21 (credentials := .addressV2)] },
  { name := "host-delegation"
    description :=
      "ADDRESS_WITH_DELEGATES credentials: the delegate's __check_auth receives the top-level " ++
      "payload and contexts and its own signature."
    accounts := [(account1, [.delegate delegate1])]
    txs := [payTx 22 (credentials := withDelegate1)] },
  { name := "host-nested-delegation"
    description := "A delegate delegates to a delegate of its own, which receives the same payload and contexts."
    accounts := [(account1, [.delegate delegate1]), (delegate1, [.delegate delegate2])]
    txs := [payTx 23 (credentials := .withDelegates [.mk delegate1 (.u32 1) [.mk delegate2 (.u32 2) []]])] },
  { name := "host-delegate-twice"
    description := "A delegate may be used once per authentication: delegating to it again is refused."
    accounts := [(account1, [.delegate delegate1, .delegate delegate1])]
    txs := [payTx 24 (credentials := withDelegate1)] },
  { name := "host-delegate-not-listed"
    description := "Delegating to an address the credentials do not list is refused."
    accounts := [(account1, [.delegate delegate2])]
    txs := [payTx 25 (credentials := withDelegate1)] },
  { name := "host-delegate-refuses"
    description := "A refusing delegate refuses the account's authentication."
    accounts := [(account1, [.delegate delegate1]), (delegate1, [.fail .trap])]
    txs := [payTx 26 (credentials := withDelegate1)] },
  { name := "host-unused-delegate"
    description := "A listed delegate the account never calls changes nothing."
    txs := [payTx 27 (credentials := .withDelegates [.mk delegate1 (.u32 1) [], .mk delegate2 (.u32 2) []])] },
  { name := "host-invoker"
    description :=
      "A contract's direct calls are authorized for it: no entry, no __check_auth, accepted. A " ++
      "call two levels down is not."
    txs := [
      tx [] (mkCall router "forward" [] [.call (pay router payee 1) false]),
      tx [] (mkCall router "forward_deep" []
        [.call (mkCall vault "relay" [] [.call (pay router payee 1) false]) false])] },
  { name := "host-reentrant-instance"
    description :=
      "The account writes its instance storage, then requires itself: its __check_auth sees the write."
    accounts := [(account1, [.get .contractInstance (key "x")])]
    txs := [tx [entry account1 30 (nodeOf (adminSet account1))] (adminSet account1)] },
  { name := "host-check-auth-writes-instance"
    description := "What the account's __check_auth writes to its instance storage, the call sees afterwards."
    accounts := [(account1, [.put .contractInstance (key "seen") (.u32 1)])]
    txs := [
      let c := mkCall account1 "admin" []
        [.requireAuth account1, .get .contractInstance (key "seen")]
      tx [entry account1 31 (nodeOf c)] c] },
  { name := "host-account-deeper-on-stack"
    description :=
      "The account's __check_auth cannot run while the account is on the call stack below the " ++
      "current call, so the require_auth is refused."
    txs := [
      let inner := pay account1 payee 3
      let c := mkCall account1 "outer" [] [.call (mkCall router "relay_from" [] [.call inner false]) false]
      tx [entry account1 32 (nodeOf inner)] c] },
  { name := "host-rollback-error-and-trap"
    description := "A call that writes and then fails, with an error or a trap, leaves storage as it was."
    txs := [tx [] (putThenFail token .error), tx [] (putThenFail token .trap)] },
  { name := "host-rollback-caught"
    description := "The caller catches the callee's failure: the caller's write stays, the callee's is gone."
    txs := [tx [] (mkCall router "outer_catch" []
      [.put .persistent (key "k") (.u32 1), .call (putThenFail token .error) true])] },
  { name := "host-rollback-uncaught"
    description := "The caller does not catch the callee's failure: both writes are gone."
    txs := [tx [] (mkCall router "outer_nocatch" []
      [.put .persistent (key "k") (.u32 1), .call (putThenFail token .trap) false])] },
  { name := "host-rollback-unconsumes-nonce"
    description :=
      "An authorized call inside a failed, caught call is rolled back with it, nonce and match " ++
      "included: the same entry authorizes the call again, and a later transaction with its " ++
      "nonce is refused."
    txs := [
      let p := pay account1 payee 10
      let c := mkCall router "retry" []
        [.call (mkCall vault "attempt" [] [.call p false, .fail .error]) true, .call p false]
      tx [entry account1 33 (nodeOf p)] c,
      payTx 33 (ledger := 101)] },
  { name := "host-rollback-rematches-node"
    description :=
      "A signed node matched inside a failed, caught call is unmatched again, so the same node " ++
      "authorizes the retry."
    txs := [
      let p := pay account1 payee 10
      let c := mkCall router "retry_signed" [addr account1]
        [.requireAuth account1, .call (mkCall vault "attempt" [] [.call p false, .fail .error]) true,
          .call p false]
      tx [entry account1 34 (nodeOf c [nodeOf p])] c] },
  { name := "host-reentrant-call"
    description := "A call of a contract already on the call stack fails; caught, the transaction goes on."
    txs := [
      tx [] (mkCall router "a" [] [.call (mkCall token "b" [] [.call (mkCall router "c" [] []) false]) false]),
      tx [] (mkCall router "a2" []
        [.call (mkCall token "b2" [] [.call (mkCall router "c" [] []) true, .put .persistent (key "b") (.u32 1)]) false])] },
  { name := "host-muxed-key"
    description := "A call using a key that holds a muxed address fails, and its writes are rolled back."
    txs := [tx [] (mkCall token "f" []
      [.put .persistent (key "before") (.u32 1),
        .put .temporary (.address (.muxedAccount 7 (key32 1))) (.u32 1)])] },
  { name := "host-storage-in-calls"
    description := "Reads, presence checks and writes across three durabilities and two contracts."
    txs := [
      tx [] (mkCall token "w" [] [
        .put .persistent (key "a") (.u32 1), .put .temporary (key "a") (.u32 2),
        .put .contractInstance (key "a") (.u32 3),
        .call (mkCall vault "w" [] [.put .persistent (key "a") (.u32 4), .has .persistent (key "a")]) false,
        .get .persistent (key "a"), .has .temporary (key "a"), .remove .temporary (key "a"),
        .has .temporary (key "a"), .get .contractInstance (key "a")]),
      tx [] (mkCall token "r" [] [.get .persistent (key "a"), .get .temporary (key "a"),
        .get .contractInstance (key "a")]) 101] },
  { name := "host-check-rules-allows"
    description := "The account's __check_auth asks rule-eval about its contexts, and the rules allow them."
    accounts := [(account1, [.checkRules [anyRule router, onlyRule token ["pay"]] []])]
    txs := [tx [entry account1 40 (nodeOf payNested [nodeOf (pay account1 router 5)])] payNested] },
  { name := "host-check-rules-refuses-unused-node"
    description :=
      "rule-eval checks every signed context, a node that never runs included: a rule set without " ++
      "the vault refuses the authorization."
    accounts := [(account1, [.checkRules [onlyRule token ["pay"]] []])]
    txs := [tx [entry account1 41 (nodeOf (pay account1 payee 10) [node vault "run" []])]
      (pay account1 payee 10)] },
  { name := "host-check-rules-arguments"
    description := "A rule with a condition on the amount allows 10 and refuses 11."
    accounts := [(account1, [.checkRules
      [{ onlyRule token ["pay"] with conds := [.argI128AtMost 2 (BitVec.ofInt 128 10)] }] []])]
    txs := [payTx 42, payTx 43 (amount := 11) (signed := 11)] }]

/-! ## Randomized traces -/

instance : Inhabited Address := ⟨token⟩
instance : Inhabited Val := ⟨.void⟩
instance : Inhabited Durability := ⟨.persistent⟩
instance : Inhabited FailKind := ⟨.error⟩
instance : Inhabited AccountStep := ⟨.fail .error⟩
instance : Inhabited Credentials := ⟨.address⟩

def callees : List Address := [token, router, vault, account1, account2]
def fnNames : List String := ["pay", "run", "admin"]
def accounts : List Address := [account1, account2]
def keys : List Val := [key "a", key "b", .u32 1]
def values : List Val := [.u32 0, .u32 1, i128 (-1), .bool true, addr account1]
def durabilities : List Durability := [.persistent, .temporary, .contractInstance]

/-- A random call of depth at most `depth`. Its last argument is `.u32 id`, so
no two calls of a transaction share a context. -/
def randomCall : Nat → Nat → Gen (Call × Nat)
  | depth, id => do
    let c ← pick callees
    let f ← pick fnNames
    let args ← pick [[], [addr account1], [addr account2, i128 5], [addr payee]]
    let n ← below 7
    let mut body : List Step := []
    let mut next := id + 1
    for _ in List.range n do
      match ← below 10 with
      | 0 | 1 | 2 => body := body ++ [.requireAuth (← pick accounts)]
      | 3 | 4 =>
        match depth with
        | 0 => body := body ++ [.get (← pick durabilities) (← pick keys)]
        | d + 1 =>
          let (callee, n') ← randomCall d next
          next := n'
          body := body ++ [.call callee ((← below 3) == 0)]
      | 5 => body := body ++ [.put (← pick durabilities) (← pick keys) (← pick values)]
      | 6 => body := body ++ [.get (← pick durabilities) (← pick keys)]
      | 7 => body := body ++ [.has (← pick durabilities) (← pick keys)]
      | 8 => body := body ++ [.remove (← pick durabilities) (← pick keys)]
      | _ => if (← below 3) == 0 then body := body ++ [.fail (← pick [.error, .trap])]
    return (mkCall c f (args ++ [.u32 (UInt32.ofNat id)]) body, next)

mutual

/-- The tree of `a`'s `require_auth`s in a call tree: a node for each call
requiring `a`, holding the nodes found under it. -/
def project (a : Address) : Call → List Invocation
  | c@(.mk _ _ _ body) =>
    let subs := projectSteps a body
    if body.any (fun s => match s with | .requireAuth x => x == a | _ => false) then
      [.node c.context subs]
    else subs

def projectSteps (a : Address) : List Step → List Invocation
  | [] => []
  | .call c _ :: rest => project a c ++ projectSteps a rest
  | _ :: rest => projectSteps a rest

end

/-- `i` with a change to its arguments, its children or neither. -/
def mutate : Invocation → Gen Invocation
  | i@(.node f subs) => do
    match ← below 8 with
    | 0 => match f with
      | .contract c fn args => return .node (.contract c fn (args ++ [.u32 999])) subs
      | _ => return i
    | 1 => return .node f []
    | 2 => return .node f (subs ++ [node vault "unused" []])
    | _ => return i

def randomProgram (a : Address) : Gen (List AccountStep) := do
  match ← below 10 with
  | 0 => return [.get .contractInstance (key "a")]
  | 1 => return [.put .temporary (key "seen") (.u32 1)]
  | 2 => return [.checkRules [anyRule token, anyRule router, anyRule vault, anyRule account1,
      anyRule account2] []]
  | 3 => return [.checkRules [onlyRule token ["pay"], anyRule router] []]
  | 4 => return [.delegate delegate1]
  | 5 => return if a == account1 then [.fail .error] else []
  | _ => return []

def randomCredentials : Gen Credentials := do
  match ← below 6 with
  | 0 | 1 => return .addressV2
  | 2 => return .withDelegates [.mk delegate1 (.u32 1) []]
  | 3 => return .withDelegates [.mk delegate1 (.u32 1) [.mk delegate2 (.u32 2) []]]
  | _ => return .address

def trace (seed : UInt64) (n : Nat) : Trace :=
  let g : Gen Trace := do
    let mut progs : List (Address × List AccountStep) := []
    for a in accounts do
      progs := progs ++ [(a, ← randomProgram a)]
    progs := progs ++ [(delegate1, ← pick [[], [], [.delegate delegate2], [.fail .trap]])]
    let mut txs : List Tx := []
    let mut nonce : Int := Int.ofNat (n * 100)
    let mut used : List Int := []
    let count := (← below 3) + 1
    for i in List.range count do
      let (c, _) ← randomCall 2 (i * 100)
      let mut entries : List Entry := []
      for a in accounts do
        for root in project a c do
          if (← below 6) != 0 then
            let root ← mutate root
            let reuse ← below 8
            let nc := if reuse == 0 && !used.isEmpty then used.head! else nonce
            nonce := nonce + 1
            used := nc :: used
            let expiration ← pick [150, 150, 150, 99]
            entries := entries ++
              [entry a nc root expiration (← pick [.void, .u32 1]) (← randomCredentials)]
      txs := txs ++ [tx entries c (100 + i)]
    return {
      name := s!"host-random-{pad 3 n}"
      description := s!"Randomized host trace {n} of seed {seed}."
      accounts := progs
      txs }
  (g.run ⟨seed + UInt64.ofNat n⟩).1

def traces (seed : UInt64) (count : Nat) : List Trace :=
  named ++ (List.range count).map (trace seed)

end Conformance.Soroban.Host
