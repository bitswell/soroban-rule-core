import Conformance.Soroban.Host
import Conformance.Soroban.Storage

/-!
# Seed traces

The authorization and storage tests of `soroban-env-host` 29.0.1
(`src/test/auth.rs`, `auth_delegation.rs`, `invoker_auth.rs`, `storage.rs`
and `frame.rs`), transcribed into host and storage traces wherever the models
express them: from `auth.rs`, the cases of `AuthTest::tree_test_enforcing`
and its variants, and `test_out_of_order_auth`; from `auth_delegation.rs`,
the cases whose test account only checks what it receives and delegates;
from `storage.rs`, the storage operations. Each case keeps the host test's
own expectation (`success`, `is_ok`, `is_err`, a value read back, and the
nonces `verify_nonces_consumed` counts). The generator runs each trace on the
model, writes the model's outcome into the trace as every other trace does,
and refuses to write anything when the model's outcome differs from the host
test's. Every test of the five files is listed in `coverage` with the cases
the traces express and, for the rest, the reason they are outside the models.

## How a case is transcribed

* **Signers.** The host tests sign with Stellar accounts (ed25519 keys); the
  models authenticate contract accounts only. Each signer becomes a contract
  account whose `__check_auth` accepts, so a case tests what it is about,
  matching the signed trees, with the account's `__check_auth` taking the
  place of the signature check. The entries keep the host tests' credentials:
  `ADDRESS_V2` for even-numbered signers and `ADDRESS` for odd ones, signature
  expiration ledger 1000, ledger 100. The nonces, random in the host tests,
  are distinct in each trace.
* **`AuthContract::tree_fn`.** A node requires each address its `need_auth`
  marks, in order, with `require_auth_for_args(addr, [])`, then calls its
  children, through `try_invoke_contract` where the child is a `try_call`.
  The traces call `tree_fn` with no arguments, so a plain `require_auth` has
  the context `require_auth_for_args(addr, [])` has in the host test, and the
  signed nodes (`SignNode::tree_fn`, no arguments) are the host test's.
  `stree_fn` reads the addresses from storage and calls its children's
  `tree_fn`; the traces require the same addresses.
* **Delegation** (`builtin_auth_delegation`). Each account's `__check_auth`
  runs its signature's instructions. `BuiltinDelegated(a)` is the model's
  `delegate a`. `Payload` and `Context` assert what `__check_auth` receives;
  the traces check the same through the payload and contexts of every
  `__check_auth` event. The order of the instructions is the order the test
  lists them in (the host test shuffles them, and no case depends on it).
  `update_signers`, which the test account checks before delegating, has no
  counterpart: a model account delegates to any delegate its credentials
  list.
* **Storage** (`contract_data`). Each call of the storage test contract is
  one operation of a storage trace.
-/

namespace Conformance.Soroban.Seed

open RuleCore RuleCore.Soroban
open Conformance.Soroban.Values
open Conformance.Soroban.Host (mkCall entry tx)

/-- The host release the tests are transcribed from. -/
def hostRelease : String := "soroban-env-host 29.0.1"

/-! ## Expectations and coverage -/

/-- A transaction of a seed trace and what the host test expects of it. -/
structure Expect where
  /-- The line of the case in the host test file. -/
  line : Nat
  ok : Bool
  /-- For each address, its entries' nonces and how many of them the
  transaction consumes (`verify_nonces_consumed`). -/
  nonces : List (Address × List Int × Nat) := []

structure SeedTrace where
  file : String
  test : String
  trace : Host.Trace
  /-- One per transaction. -/
  expects : List Expect

/-- A storage operation and what the host test expects of it: the model's
`Obs`, or `none` for a refusal. -/
structure SeedStorage where
  file : String
  test : String
  trace : Storage.Trace
  /-- One per operation: its line in the host test file and what it gives. -/
  expects : List (Nat × Option Obs)

/-- A test of the host and how much of it the seed traces express. -/
structure Coverage where
  file : String
  test : String
  /-- The test's cases: each call with an expected outcome. -/
  cases : Nat
  /-- The cases the traces do not express, by reason. -/
  left : List (Nat × String) := []

/-! ## Reasons a case is outside the models -/

def recording : String :=
  "recording authorization (simulation) is not modelled"
def resources : String :=
  "resource metering is not modelled"
def accountMissing : String :=
  "a Stellar account signer whose account entry is missing: the models authenticate contract " ++
    "accounts only"
def invokerAuth : String :=
  "authorize_as_current_contract is not modelled"
def requireAuthInCheckAuth : String :=
  "require_auth inside __check_auth is not modelled"
def requireAuthForArgs : String :=
  "require_auth_for_args with arguments other than the call's, and account programs that " ++
    "compute stored values, are not modelled"
def storageBranch : String :=
  "the account's __check_auth branches on its storage; the model's account programs do not branch"
def signatureCheck : String :=
  "the test account refuses because it compares its payload or contexts with values the test " ++
    "computed; the model's account programs make no such comparison (the payload and contexts " ++
    "themselves are checked on every __check_auth event)"
def entryValidation : String :=
  "the host refuses the entries when they are installed (duplicate, unsorted or too deeply " ++
    "nested delegates); the model takes the delegate list as given, and the traces keep delegates " ++
    "sorted, unique and shallow"
def delegatedSignersGetter : String :=
  "get_delegated_signers_for_current_auth_check is not modelled"
def callsFromCheckAuth : String :=
  "__check_auth calling other contracts is not modelled"
def perEntryProgram : String :=
  "the account's __check_auth acts on each entry's own signature; the model gives an account one " ++
    "program for every entry"
def classicDelegates : String :=
  "Stellar account (classic) delegates: the models authenticate contract accounts only"
def delegateOutsideCheckAuth : String :=
  "delegate_account_auth and get_delegated_signers outside __check_auth: the model's delegation " ++
    "is an account step"
def ttl : String :=
  "time to live and its extension are not modelled"
def footprint : String :=
  "footprints are not modelled"
def sizeLimits : String :=
  "the budget's limits on value and key size are not modelled"
def hostInternal : String :=
  "a test of a host-internal or test-only function, not of a contract's behaviour"
def instanceMuxedKey : String :=
  "a muxed address as an instance storage key: the host refuses it when it writes the instance " ++
    "back, which the model leaves out"

/-! ## `AuthContract::tree_fn` -/

/-- A node of a `tree_fn` call tree (`SetupNode`): a contract, by its index in
the test, whether it requires each address, and its children. `t` is a node
whose caller catches its failure (`SetupNode::new_try_call`). -/
inductive Setup where
  | n (contract : Nat) (needAuth : List Bool) (children : List Setup)
  | t (contract : Nat) (needAuth : List Bool) (children : List Setup)

/-- A signed node (`SignNode::tree_fn`, or `SignNode::tree_fn_stored` for
`ss`): a contract and the signed calls under it. -/
inductive Sign where
  | s (contract : Nat) (children : List Sign)
  | ss (contract : Nat) (children : List Sign)

/-- The test's contract `i`. -/
def ctr (i : Nat) : Address := contract (0x10 + i)

/-- The test's signer `i`, a contract account. -/
def signer (i : Nat) : Address := contract (0xb0 + i)

def Setup.isTry : Setup → Bool
  | .t .. => true
  | .n .. => false

def needs (addresses : List Address) (needAuth : List Bool) : List Step :=
  (addresses.zip needAuth).filterMap fun (a, n) => if n then some (.requireAuth a) else none

mutual

def Setup.call (addresses : List Address) (fn : String) : Setup → Call
  | .n c need children => mkCall (ctr c) fn [] (needs addresses need ++ Setup.calls addresses children)
  | .t c need children => mkCall (ctr c) fn [] (needs addresses need ++ Setup.calls addresses children)

def Setup.calls (addresses : List Address) : List Setup → List Step
  | [] => []
  | x :: xs => .call (x.call addresses "tree_fn") x.isTry :: Setup.calls addresses xs

end

mutual

def Sign.inv : Sign → Invocation
  | .s c children => .node (.contract (ctr c) (b "tree_fn") []) (Sign.invs children)
  | .ss c children => .node (.contract (ctr c) (b "stree_fn") []) (Sign.invs children)

def Sign.invs : List Sign → List Invocation
  | [] => []
  | x :: xs => x.inv :: Sign.invs xs

end

/-- A call of `AuthTest::tree_test_enforcing`, `…_with_addresses` or
`…_with_stored_addresses`, and the `verify_nonces_consumed` after it. -/
structure TreeCase where
  line : Nat
  success : Bool
  stored : Bool := false
  /-- The addresses `tree_fn` receives, as signer indices; by default each
  signer once, in order. -/
  addresses : Option (List Nat) := none
  /-- For each signer, the roots it signs. -/
  signs : List (List Sign)
  nonces : Option (List Nat) := none

structure TreeTest where
  test : String
  name : String
  line : Nat
  signers : Nat
  setup : Setup
  cases : List TreeCase
  left : List (Nat × String) := []

def credentialsOf (i : Nat) : Credentials :=
  if i % 2 == 0 then .addressV2 else .address

/-- A case's transaction, its entries' nonces from `base` on, and what the
host test expects of it. -/
def TreeCase.toTx (t : TreeTest) (c : TreeCase) (base : Nat) : Tx × Expect :=
  let addresses := (c.addresses.getD (List.range t.signers)).map signer
  let fn := if c.stored then "stree_fn" else "tree_fn"
  let roots := c.signs.zipIdx.flatMap fun (rs, i) => rs.map fun r => (i, r)
  let entries := roots.zipIdx.map fun ((i, r), k) =>
    entry (signer i) (Int.ofNat (base + k)) r.inv 1000 .void (credentialsOf i)
  let nonces := match c.nonces with
    | none => []
    | some counts => counts.zipIdx.map fun (n, i) =>
      (signer i, (entries.filter (·.address == signer i)).map (·.nonce), n)
  (tx entries (t.setup.call addresses fn) 100, { line := c.line, ok := c.success, nonces })

def TreeTest.seed (t : TreeTest) : SeedTrace :=
  let txs := t.cases.zipIdx.map fun (c, i) => c.toTx t (1000 * (i + 1))
  { file := "auth.rs", test := t.test
    trace := {
      name := t.name
      description :=
        s!"{t.test} of {hostRelease} src/test/auth.rs (line {t.line}): one transaction for " ++
          s!"each case, at lines {t.cases.map (·.line)} in order."
      txs := txs.map (·.1) }
    expects := txs.map (·.2) }

/-- The tests of `auth.rs` built on `AuthTest::tree_test_enforcing`. -/
def treeTests : List TreeTest := [
  { test := "test_single_authorized_call", name := "seed-auth-single-authorized-call", line := 515, signers := 1
    setup := (.n 0 [true] [])
    cases := [
      { line := 530, success := true, nonces := some [1]
        signs := [[(.s 0 [])]] },
      { line := 543, success := true, nonces := some [1]
        signs := [[(.s 1 []), (.s 0 [])]] },
      { line := 554, success := true, nonces := some [1]
        signs := [[(.s 0 [(.s 1 [])])]] },
      { line := 566, success := false
        signs := [[]] },
      { line := 568, success := false, nonces := some [0]
        signs := [[(.s 1 [])]] },
      { line := 577, success := false
        signs := [[(.s 1 [(.s 0 [])])]] }]
    left := [(2, recording), (1, accountMissing)]
  },
  { test := "test_single_authorized_call_for_multiple_addresses", name := "seed-auth-single-authorized-call-for-multiple-addresses", line := 604, signers := 2
    setup := (.n 0 [true, true] [])
    cases := [
      { line := 629, success := true, nonces := some [1, 1]
        signs := [[(.s 0 [])], [(.s 0 [])]] },
      { line := 634, success := false
        signs := [[], [(.s 0 [])]] },
      { line := 640, success := false
        signs := [[(.s 1 [])], [(.s 0 [])]] },
      { line := 649, success := false
        signs := [[(.s 1 [(.s 0 [])])], [(.s 0 [])]] }]
    left := [(1, recording)]
  },
  { test := "test_single_authorization_for_one_address_among_multiple", name := "seed-auth-single-authorization-for-one-address-among-multiple", line := 662, signers := 2
    setup := (.n 0 [false, true] [])
    cases := [
      { line := 677, success := true, nonces := some [0, 1]
        signs := [[], [(.s 0 [])]] },
      { line := 680, success := true, nonces := some [0, 1]
        signs := [[(.s 0 [])], [(.s 0 [])]] },
      { line := 690, success := true, nonces := some [0, 1]
        signs := [[(.s 1 [])], [(.s 0 [])]] },
      { line := 702, success := false
        signs := [[(.s 0 [])], []] }]
    left := [(1, recording)]
  },
  { test := "test_single_authorized_call_tree", name := "seed-auth-single-authorized-call-tree", line := 709, signers := 1
    setup := (.n 0 [true] [(.n 1 [true] [(.n 3 [true] []), (.n 2 [true] [])]), (.n 2 [true] [(.n 4 [true] []), (.n 3 [true] [])])])
    cases := [
      { line := 763, success := true, nonces := some [1]
        signs := [[(.s 0 [(.s 2 [(.s 3 []), (.s 4 [])]), (.s 1 [(.s 2 []), (.s 3 [])])])]] },
      { line := 789, success := true, nonces := some [1]
        signs := [[(.s 0 [(.s 1 [(.s 2 []), (.s 3 []), (.s 4 [])]), (.s 2 [(.s 3 []), (.s 4 [])]), (.s 3 [])]), (.s 0 [])]] },
      { line := 821, success := false
        signs := [[(.s 0 [(.s 1 [(.s 2 [])]), (.s 2 [(.s 3 []), (.s 2 [])])])]] },
      { line := 843, success := false
        signs := [[(.s 0 [(.s 4 [(.s 2 []), (.s 3 [])]), (.s 2 [(.s 3 []), (.s 4 [])])])]] },
      { line := 869, success := false
        signs := [[(.s 0 []), (.s 0 [(.s 1 [(.s 2 []), (.s 3 [])]), (.s 2 [(.s 3 []), (.s 4 [])])])]] }]
    left := [(1, recording)]
  },
  { test := "test_disjoint_tree_not_allowed", name := "seed-auth-disjoint-tree-not-allowed", line := 897, signers := 1
    setup := (.n 0 [true] [(.n 1 [true] [])])
    cases := [
      { line := 906, success := true, nonces := some [1]
        signs := [[(.s 0 [(.s 1 [])])]] },
      { line := 917, success := false
        signs := [[(.s 0 []), (.s 1 [])]] }]
  },
  { test := "test_two_authorized_trees", name := "seed-auth-two-authorized-trees", line := 927, signers := 1
    setup := (.n 0 [false] [(.n 1 [true] [(.n 3 [true] []), (.n 2 [true] [])]), (.n 2 [true] [(.n 4 [true] []), (.n 3 [true] [])])])
    cases := [
      { line := 983, success := true, nonces := some [2]
        signs := [[(.s 1 [(.s 2 []), (.s 3 [])]), (.s 2 [(.s 3 []), (.s 4 [])])]] },
      { line := 1207, success := false
        signs := [[(.s 0 [(.s 1 [(.s 2 []), (.s 3 [])]), (.s 2 [(.s 3 []), (.s 4 [])])])]] }]
    left := [(1, recording), (1, resources)]
  },
  { test := "test_two_authorized_trees_with_rollback", name := "seed-auth-two-authorized-trees-with-rollback", line := 1232, signers := 1
    setup := (.n 0 [false] [(.t 1 [true] [(.n 3 [true] []), (.n 2 [true] [])]), (.t 2 [true] [(.n 4 [true] []), (.n 3 [true] [])])])
    cases := [
      { line := 1259, success := true, nonces := some [0]
        signs := [[(.s 1 [(.s 2 [])]), (.s 2 [(.s 3 [])])]] },
      { line := 1282, success := true, nonces := some [1]
        signs := [[(.s 1 [(.s 2 [])]), (.s 2 [(.s 3 []), (.s 4 [])])]] },
      { line := 1305, success := true, nonces := some [1]
        signs := [[(.s 1 [(.s 2 []), (.s 3 [])]), (.s 2 [(.s 3 [])])]] },
      { line := 1328, success := true, nonces := some [1]
        signs := [[(.s 2 [(.s 3 []), (.s 4 [])])]] },
      { line := 1342, success := true, nonces := some [0]
        signs := [[]] }]
  },
  { test := "test_rolled_back_auth_entry_can_be_reused", name := "seed-auth-rolled-back-auth-entry-can-be-reused", line := 1346, signers := 1
    setup := (.n 0 [false] [(.t 1 [true] [(.n 3 [true] []), (.n 2 [true] [])]), (.n 1 [true] [(.n 3 [true] []), (.n 4 [true] [])])])
    cases := [
      { line := 1373, success := true, nonces := some [1]
        signs := [[(.s 1 [(.s 3 []), (.s 4 [])])]] },
      { line := 1388, success := false
        signs := [[(.s 1 [(.s 3 []), (.s 2 [])])]] }]
  },
  { test := "test_three_authorized_trees", name := "seed-auth-three-authorized-trees", line := 1439, signers := 1
    setup := (.n 0 [false] [(.n 1 [false] [(.n 3 [true] []), (.n 2 [true] [])]), (.n 2 [true] [(.n 4 [true] []), (.n 3 [true] [])])])
    cases := [
      { line := 1495, success := true, nonces := some [3]
        signs := [[(.s 2 []), (.s 2 [(.s 3 []), (.s 4 [])]), (.s 3 [])]] },
      { line := 1514, success := false
        signs := [[(.s 0 [(.s 1 [(.s 2 []), (.s 3 [])]), (.s 2 [(.s 3 []), (.s 4 [])])])]] },
      { line := 1539, success := false
        signs := [[(.s 1 [(.s 2 []), (.s 3 [])]), (.s 2 [(.s 3 []), (.s 4 [])])]] },
      { line := 1566, success := false
        signs := [[(.s 2 [(.s 3 []), (.s 4 [])]), (.s 2 []), (.s 3 [])]] }]
    left := [(1, recording)]
  },
  { test := "test_multi_address_trees", name := "seed-auth-multi-address-trees", line := 1583, signers := 3
    setup := (.n 0 [true, false, true] [(.n 1 [true, true, false] [(.n 3 [false, true, true] []), (.n 2 [true, false, false] [])]), (.n 2 [true, true, false] [(.n 4 [true, false, true] []), (.n 3 [true, true, true] [])])])
    cases := [
      { line := 1665, success := true, nonces := some [1, 2, 1]
        signs := [[(.s 0 [(.s 1 [(.s 2 [])]), (.s 2 [(.s 3 []), (.s 4 [])])])], [(.s 2 [(.s 3 [])]), (.s 1 [(.s 3 [])])], [(.s 0 [(.s 3 []), (.s 3 []), (.s 4 [])])]] },
      { line := 1709, success := false
        signs := [[(.s 0 [(.s 1 [(.s 2 [])]), (.s 2 [(.s 3 []), (.s 4 [])])])], [(.s 1 [(.s 3 [])]), (.s 2 [(.s 3 [])])], [(.s 0 [(.s 3 []), (.s 4 [])])]] }]
    left := [(1, recording)]
  },
  { test := "test_multi_address_auth_with_stored_addresses", name := "seed-auth-multi-address-auth-with-stored-addresses", line := 2635, signers := 3
    setup := (.n 0 [true, true, true] [(.n 1 [true, false, false] [(.n 3 [true, true, false] []), (.n 2 [true, true, false] [])]), (.n 2 [true, true, false] [(.n 4 [false, false, false] []), (.n 3 [true, true, false] [])]), (.n 1 [true, false, false] [(.n 3 [true, true, false] []), (.n 2 [true, true, false] [])])])
    cases := [
      { line := 2725, success := true, stored := true, nonces := some [1, 1, 1]
        signs := [[(.ss 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 3 [])]), (.s 1 [(.s 3 []), (.s 2 [])])])], [(.ss 0 [(.s 3 []), (.s 2 []), (.s 2 [(.s 3 [])]), (.s 3 []), (.s 2 [])])], [(.ss 0 [])]] },
      { line := 2772, success := false, stored := true
        signs := [[(.ss 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 3 [])]), (.s 1 [(.s 3 []), (.s 2 [])])])], [(.ss 0 [(.s 3 []), (.s 2 []), (.s 2 []), (.s 3 []), (.s 3 []), (.s 2 [])])], [(.ss 0 [])]] },
      { line := 2815, success := false, stored := true
        signs := [[(.ss 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 3 [])])]), (.s 1 [(.s 3 []), (.s 2 [])])], [(.ss 0 [(.s 3 []), (.s 2 []), (.s 2 [(.s 3 [])]), (.s 3 []), (.s 2 [])])], [(.ss 0 [])]] }]
    left := [(1, recording)]
  },
  { test := "test_same_auth_tree_with_duplicate_addresses", name := "seed-auth-same-auth-tree-with-duplicate-addresses", line := 2862, signers := 2
    setup := (.n 0 [true, true, true, true] [(.n 1 [true, true, true, true] [(.n 3 [true, true, true, true] []), (.n 2 [true, true, true, true] [])]), (.n 2 [true, true, true, true] [(.n 4 [true, true, true, true] []), (.n 3 [true, true, true, true] [])])])
    cases := [
      { line := 2994, success := true, addresses := some [0, 1, 1, 0], nonces := some [2, 2]
        signs := [[(.s 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 4 []), (.s 3 [])])]), (.s 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 4 []), (.s 3 [])])])], [(.s 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 4 []), (.s 3 [])])]), (.s 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 4 []), (.s 3 [])])])]] },
      { line := 3085, success := false, addresses := some [0, 1, 1, 0]
        signs := [[(.s 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 4 []), (.s 3 [])])])], [(.s 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 4 []), (.s 3 [])])])]] },
      { line := 3133, success := false, addresses := some [0, 1, 1, 0]
        signs := [[(.s 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 4 []), (.s 3 [])]), (.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 4 []), (.s 3 [])])]), (.s 0 [])], [(.s 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 4 []), (.s 3 [])])]), (.s 0 [(.s 1 [(.s 3 []), (.s 2 [])]), (.s 2 [(.s 4 []), (.s 3 [])])])]] }]
    left := [(1, recording)]
  },
  { test := "test_different_auth_trees_with_duplicate_addresses", name := "seed-auth-different-auth-trees-with-duplicate-addresses", line := 3222, signers := 2
    setup := (.n 0 [true, true, true, true] [(.n 1 [true, false, true, false] [(.n 3 [false, true, true, true] []), (.n 2 [true, true, true, false] [])]), (.n 2 [false, true, true, false] [(.n 4 [true, false, true, false] []), (.n 3 [false, false, true, true] [])])])
    cases := [
      { line := 3322, success := true, addresses := some [0, 1, 1, 0], nonces := some [2, 2]
        signs := [[(.s 0 [(.s 3 []), (.s 3 [])]), (.s 0 [(.s 1 [(.s 2 [])]), (.s 4 [])])], [(.s 0 [(.s 1 [(.s 2 []), (.s 3 [])]), (.s 2 [(.s 3 []), (.s 4 [])])]), (.s 0 [(.s 2 []), (.s 3 []), (.s 2 [])])]] },
      { line := 3381, success := false, addresses := some [0, 1, 1, 0]
        signs := [[(.s 0 [(.s 3 []), (.s 3 []), (.s 1 [(.s 2 [])])]), (.s 0 [(.s 4 [])])], [(.s 0 [(.s 1 [(.s 2 []), (.s 3 [])]), (.s 2 [(.s 3 []), (.s 4 [])])]), (.s 0 [(.s 2 []), (.s 3 []), (.s 2 [])])]] },
      { line := 3440, success := false, addresses := some [0, 1, 1, 0]
        signs := [[(.s 0 [(.s 3 []), (.s 3 [])]), (.s 0 [(.s 1 [(.s 2 [])]), (.s 4 [])])], [(.s 0 [(.s 1 [(.s 2 []), (.s 3 [])])]), (.s 0 [(.s 2 []), (.s 3 []), (.s 2 []), (.s 2 [(.s 3 []), (.s 4 [])])])]] }]
    left := [(1, recording)]
  }]

/-- `test_out_of_order_auth`: `order_fn(addr, child)` calls
`child.do_auth(addr, 10)`, which requires `addr`, and then requires `addr`
itself. -/
def outOfOrder : SeedTrace :=
  let k := signer 0
  let doAuth := mkCall (ctr 1) "do_auth" [.address k, .u32 10] [.requireAuth k]
  let orderFn := mkCall (ctr 0) "order_fn" [.address k, .address (ctr 1)]
    [.call doAuth false, .requireAuth k]
  let e (nonce : Int) (root : Invocation) := entry k nonce root 1000 .void .addressV2
  { file := "auth.rs", test := "test_out_of_order_auth"
    trace := {
      name := "seed-auth-out-of-order-auth"
      description :=
        s!"test_out_of_order_auth of {hostRelease} src/test/auth.rs (line 1750): two separate " ++
          "trees for order_fn and the do_auth it calls first are accepted (line 1811); one tree " ++
          "with do_auth under order_fn is refused (line 1846)."
      txs := [
        tx [e 1000 (Host.nodeOf orderFn), e 1001 (Host.nodeOf doAuth)] orderFn,
        tx [e 2000 (Host.nodeOf orderFn [Host.nodeOf doAuth])] orderFn] }
    expects := [
      { line := 1811, ok := true, nonces := [(k, [1000, 1001], 2)] },
      { line := 1846, ok := false }] }

/-! ## Delegation (`auth_delegation.rs`) -/

mutual

/-- An `AuthBuilder`: the test contract `account` and the instructions of its
signature. -/
inductive Builder where
  | b (account : Nat) (instrs : List Instr)

inductive Instr where
  /-- `expect_valid_payload`. -/
  | pay
  /-- `expect_context` with the call's own context. -/
  | ctx
  /-- `sign_builtin_delegated`: a delegate in the credentials, and a
  `BuiltinDelegated` instruction for it. -/
  | del (builder : Builder)
  /-- `add_builtin_delegated_sig`: a `BuiltinDelegated` instruction for an
  account the credentials do not list. -/
  | add (account : Nat)

end

/-- The delegation test's contract `i`. -/
def dctr (i : Nat) : Address := contract (0x30 + i)

/-- The delegates the instructions put in the credentials, in their order. -/
def delegatesOf : List Instr → List Delegate
  | [] => []
  | .del (.b a is) :: rest => .mk (dctr a) .void (delegatesOf is) :: delegatesOf rest
  | _ :: rest => delegatesOf rest

/-- The `__check_auth` program the instructions make. -/
def programOf (is : List Instr) : List AccountStep :=
  is.filterMap fun
    | .del (.b a _) => some (.delegate (dctr a))
    | .add a => some (.delegate (dctr a))
    | _ => none

/-- Every builder under the instructions, outermost first. -/
def buildersOf : List Instr → List (Nat × List Instr)
  | [] => []
  | .del (.b a is) :: rest => (a, is) :: buildersOf is ++ buildersOf rest
  | _ :: rest => buildersOf rest

/-- Each account's program, from the outermost builder of it: a builder
nested under the same account is refused before its program runs. -/
def programsOf (a : Nat) (is : List Instr) : List (Address × List AccountStep) :=
  ((a, is) :: buildersOf is).foldl (init := []) fun acc (x, xs) =>
    if acc.any (·.1 == dctr x) then acc else acc ++ [(dctr x, programOf xs)]

/-- A `call_auth_fn` of `auth_fn(address, 123)` on contract 0, which requires
`address`, signed by `builder`. -/
structure DCase where
  line : Nat
  ok : Bool
  builder : Builder
  /-- `force_credential_with_delegates`. -/
  withDelegates : Bool := false

def DCase.seed (test : String) (name : String) (c : DCase) : SeedTrace :=
  match c.builder with
  | .b a is =>
    let call := mkCall (dctr 0) "auth_fn" [.address (dctr a), .u32 123] [.requireAuth (dctr a)]
    let ds := delegatesOf is
    let credentials : Credentials :=
      if ds.isEmpty && !c.withDelegates then .address else .withDelegates ds
    { file := "auth_delegation.rs", test
      trace := {
        name
        description :=
          s!"{test} of {hostRelease} src/test/auth_delegation.rs: the case at line {c.line}."
        accounts := programsOf a is
        txs := [tx [entry (dctr a) 1 (Host.nodeOf call) 1000 .void credentials] call] }
      expects := [{ line := c.line, ok := c.ok }] }

/-- The cases of one delegation test, one trace each, since each case gives
its accounts their own programs. -/
def delegationSeeds (test : String) (stem : String) (cs : List DCase) : List SeedTrace :=
  cs.zipIdx.map fun (c, i) => c.seed test s!"seed-delegation-{stem}-{i + 1}"

open Builder Instr in
def delegation : List SeedTrace :=
  delegationSeeds "test_credential_with_delegates_uses_preimage_with_address"
    "credential-with-delegates-uses-preimage-with-address" [
      { line := 537, ok := true, builder := b 1 [pay] },
      { line := 542, ok := true, builder := b 1 [pay], withDelegates := true },
      { line := 552, ok := true, builder := b 1 [pay, del (b 2 [])] }] ++
  delegationSeeds "test_duplicate_and_unsorted_delegated_signers_are_not_allowed"
    "duplicate-and-unsorted-delegated-signers-are-not-allowed" [
      { line := 612, ok := true
        builder := b 1 [del (b 2 [del (b 4 [del (b 5 []), del (b 6 [])])]), del (b 3 [])] }] ++
  delegationSeeds "test_signature_payload_forwarded_to_delegated_signers"
    "signature-payload-forwarded-to-delegated-signers" [
      { line := 728, ok := true, builder := b 1 [pay, del (b 2 [pay])] },
      { line := 746, ok := true
        builder := b 1 [pay, del (b 2 [pay, del (b 3 [pay, del (b 5 [pay])]), del (b 4 [pay])])] }] ++
  delegationSeeds "test_context_forwarded_to_delegated_signers"
    "context-forwarded-to-delegated-signers" [
      { line := 797, ok := true, builder := b 1 [ctx, del (b 2 [ctx])] },
      { line := 808, ok := true
        builder := b 1 [ctx, del (b 2 [ctx, del (b 4 [ctx, del (b 5 [ctx]), del (b 6 [ctx])])]),
          del (b 3 [ctx])] }] ++
  delegationSeeds "test_builtin_delegated_signer_reentrance_not_allowed"
    "builtin-delegated-signer-reentrance-not-allowed" [
      { line := 885, ok := true, builder := b 1 [del (b 2 [del (b 3 []), del (b 4 [])])] },
      { line := 896, ok := false, builder := b 1 [del (b 1 []), del (b 2 [])] },
      { line := 908, ok := false, builder := b 1 [del (b 2 [del (b 2 []), del (b 3 [])])] },
      { line := 920, ok := false
        builder := b 1 [del (b 2 [del (b 1 []), del (b 3 []), del (b 4 [])])] }] ++
  delegationSeeds "test_builtin_delegated_signers_must_be_present_in_payload"
    "builtin-delegated-signers-must-be-present-in-payload" [
      { line := 976, ok := true
        builder := b 1 [del (b 2 [del (b 4 []), del (b 5 [])]), del (b 3 [])] },
      { line := 990, ok := false, builder := b 1 [add 2] },
      { line := 1000, ok := false
        builder := b 1 [del (b 2 [del (b 4 []), del (b 5 [])]), add 3] },
      { line := 1015, ok := false, builder := b 1 [del (b 2 [add 4, del (b 5 [])])] },
      { line := 1028, ok := false, builder := b 1 [add 2], withDelegates := true }] ++
  delegationSeeds "test_delegate_account_auth_is_not_reused" "delegate-account-auth-is-not-reused" [
      { line := 1045, ok := false
        builder := b 1 [del (b 2 [del (b 4 []), del (b 5 [])]), del (b 3 []), add 3] },
      { line := 1060, ok := false
        builder := b 1 [del (b 2 [del (b 4 []), del (b 5 []), add 4]), del (b 3 [])] }] ++
  delegationSeeds "test_builtin_delegate_can_be_repeated_at_different_levels"
    "builtin-delegate-can-be-repeated-at-different-levels" [
      { line := 1133, ok := true
        builder := b 1 [del (b 2 [del (b 3 [del (b 4 [pay])]), del (b 4 [pay])]),
          del (b 3 [del (b 4 [pay])]), del (b 4 [pay])] }]

/-! ## Storage (`storage.rs`) -/

/-- The operations of `test_storage` on one durability, with the line of each
in `storage.rs` and what the test expects. The three `extend` calls and the
check of the entry's time to live between them are left out. -/
def storageOps (d : Durability) : List (Op × Nat × Option Obs) :=
  let k1 := Val.symbol (b "key_1")
  let k2 := Val.symbol (b "this_is_key_2")
  [(.has d k1, 159, some (.present false)),
    (.set d k1 (.u64 1234), 170, some .done),
    (.has d k1, 181, some (.present true)),
    (.set d k2 (.u64 0xFFFFFFFFFFFFFFFF), 263, some .done),
    (.has d k2, 273, some (.present true)),
    (.get d k1, 296, some (.value (some (.u64 1234)))),
    (.get d k2, 310, some (.value (some (.u64 0xFFFFFFFFFFFFFFFF)))),
    (.set d k2 (.u64 4321), 322, some .done),
    (.get d k2, 332, some (.value (some (.u64 4321)))),
    (.remove d k1, 344, some .done),
    (.remove d k1, 351, some .done),
    (.has d k1, 362, some (.present false)),
    (.has d k2, 376, some (.present true))]

def storageSeed (test : String) (name : String) (ops : List (Op × Nat × Option Obs)) : SeedStorage :=
  { file := "storage.rs", test
    trace := {
      name
      description := s!"{test} of {hostRelease} src/test/storage.rs: one operation for each " ++
        s!"call, at lines {ops.map (·.2.1)} in order."
      contract := contract 0x40
      ops := ops.map (·.1) }
    expects := ops.map (·.2) }

/-- `test_muxed_account_is_not_allowed_as_storage_key` on one durability: a
muxed address is refused as a key and kept as a value. Instance storage
skips the read of the key, and its write of the key is left out. -/
def muxedOps (d : Durability) : List (Op × Nat × Option Obs) :=
  let m := Val.address (.muxedAccount 123 (key32 10))
  let keyOps := match d with
    | .contractInstance => []
    | _ => [(.get d m, 508, none), (.set d m (.u64 1234), 518, none)]
  keyOps ++ [(.set d (.u64 1234) m, 527, some .done), (.get d (.u64 1234), 534, some (.value (some m)))]

def storageSeeds : List SeedStorage := [
  storageSeed "test_persistent_storage" "seed-storage-persistent-storage" (storageOps .persistent),
  storageSeed "test_temp_storage" "seed-storage-temp-storage" (storageOps .temporary),
  storageSeed "test_instance_storage" "seed-storage-instance-storage" (storageOps .contractInstance),
  storageSeed "test_storage_mix" "seed-storage-storage-mix"
    (storageOps .persistent ++ storageOps .temporary ++ storageOps .contractInstance),
  storageSeed "test_muxed_account_is_not_allowed_as_storage_key"
    "seed-storage-muxed-account-is-not-allowed-as-storage-key"
    (muxedOps .persistent ++ muxedOps .temporary ++ muxedOps .contractInstance)]

/-! ## The seed traces and their coverage -/

def treeSeeds : List SeedTrace := treeTests.map TreeTest.seed ++ [outOfOrder]

def hostSeeds : List SeedTrace := treeSeeds ++ delegation

/-- Every test of the five files: the cases of an expressed test the traces
leave out, by reason, or the reason a whole test is outside the models. -/
structure TestEntry where
  file : String
  test : String
  /-- Cases of an expressed test left out, by reason. -/
  left : List (Nat × String) := []
  /-- Why the whole test is outside the models. -/
  outside : Option String := none

def auth (test : String) (left : List (Nat × String) := []) : TestEntry :=
  { file := "auth.rs", test, left }

def outsideOf (file test reason : String) : TestEntry :=
  { file, test, outside := some reason }

def tests : List TestEntry :=
  treeTests.map (fun t => auth t.test t.left) ++ [
    auth "test_out_of_order_auth" [(1, recording)],
    outsideOf "auth.rs" "test_disable_non_root_recording_auth" recording,
    outsideOf "auth.rs" "test_invoker_subcontract_auth" invokerAuth,
    outsideOf "auth.rs" "test_invoker_subcontract_auth_with_duplicates" invokerAuth,
    outsideOf "auth.rs" "test_invoker_subcontract_with_gaps" invokerAuth,
    outsideOf "auth.rs" "test_invoker_subcontract_auth_with_rollbacks" invokerAuth,
    outsideOf "auth.rs" "test_invoker_subcontract_auth_is_not_reused" invokerAuth,
    outsideOf "auth.rs" "test_invoker_subcontract_auth_without_subcontract_calls" invokerAuth,
    outsideOf "auth.rs" "test_invoker_auth_depth_limit" invokerAuth,
    outsideOf "auth.rs" "test_require_auth_within_check_auth" requireAuthInCheckAuth,
    outsideOf "auth.rs" "test_require_auth_for_self_within_check_auth" requireAuthInCheckAuth,
    outsideOf "auth.rs" "test_rollback_with_conditional_custom_account_auth" storageBranch,
    outsideOf "auth.rs" "test_instance_storage_in_check_auth_with_reentrance" requireAuthForArgs,
    outsideOf "auth_delegation.rs" "test_delegated_auth_functions_not_callable_outside_check_auth"
      delegateOutsideCheckAuth,
    { file := "auth_delegation.rs", test := "test_credential_with_delegates_uses_preimage_with_address"
      left := [(4, signatureCheck)] },
    { file := "auth_delegation.rs", test := "test_duplicate_and_unsorted_delegated_signers_are_not_allowed"
      left := [(6, entryValidation)] },
    { file := "auth_delegation.rs", test := "test_signature_payload_forwarded_to_delegated_signers"
      left := [(2, signatureCheck)] },
    { file := "auth_delegation.rs", test := "test_context_forwarded_to_delegated_signers"
      left := [(6, signatureCheck)] },
    { file := "auth_delegation.rs", test := "test_builtin_delegated_signer_reentrance_not_allowed"
      left := [(2, requireAuthInCheckAuth), (1, callsFromCheckAuth)] },
    { file := "auth_delegation.rs", test := "test_builtin_delegated_signers_must_be_present_in_payload" },
    { file := "auth_delegation.rs", test := "test_delegate_account_auth_is_not_reused" },
    outsideOf "auth_delegation.rs" "test_multiple_auth_entries_with_delegates_for_same_account"
      perEntryProgram,
    { file := "auth_delegation.rs", test := "test_builtin_delegate_can_be_repeated_at_different_levels" },
    outsideOf "auth_delegation.rs" "test_delegated_signers_getter" delegatedSignersGetter,
    outsideOf "auth_delegation.rs" "test_builtin_delegates_within_nested_auth" requireAuthInCheckAuth,
    outsideOf "auth_delegation.rs" "test_builtin_delegates_within_nested_auth_and_rollbacks"
      callsFromCheckAuth,
    outsideOf "auth_delegation.rs" "test_failed_nested_auth_does_not_change_current_auth_frame"
      callsFromCheckAuth,
    outsideOf "auth_delegation.rs" "test_builtin_delegated_signer_with_classic_accounts"
      classicDelegates,
    outsideOf "auth_delegation.rs" "test_deeply_nested_delegate_tree_is_rejected" entryValidation,
    outsideOf "invoker_auth.rs" "test_invalid_invoker_auth_format" invokerAuth,
    outsideOf "invoker_auth.rs" "test_invoker_auth_with_multiple_authorizers" invokerAuth,
    outsideOf "invoker_auth.rs" "test_failure_after_adding_invoker_auth" invokerAuth,
    outsideOf "invoker_auth.rs" "test_invoker_auth_tree_with_rollbacks" invokerAuth,
    outsideOf "invoker_auth.rs" "test_multi_invoker_auth_deep_stack_with_rollbacks" invokerAuth,
    outsideOf "invoker_auth.rs" "test_self_invoker_auth" invokerAuth,
    outsideOf "invoker_auth.rs" "test_randomized_invoker_auth_trees" invokerAuth,
    outsideOf "storage.rs" "footprint_record_access" footprint,
    outsideOf "storage.rs" "footprint_enforce_access" footprint,
    outsideOf "storage.rs" "footprint_enforce_access_not_exist" footprint,
    outsideOf "storage.rs" "footprint_attempt_to_write_readonly_entry" footprint,
    { file := "storage.rs", test := "test_persistent_storage", left := [(4, ttl)] },
    { file := "storage.rs", test := "test_temp_storage", left := [(3, ttl)] },
    { file := "storage.rs", test := "test_instance_storage", left := [(4, ttl)] },
    outsideOf "storage.rs" "test_nested_bump" ttl,
    outsideOf "storage.rs" "muxed_address_storage_key_conversion" hostInternal,
    { file := "storage.rs", test := "test_muxed_account_is_not_allowed_as_storage_key"
      left := [(1, instanceMuxedKey)] },
    { file := "storage.rs", test := "test_storage_mix", left := [(11, ttl)] },
    outsideOf "storage.rs" "test_large_persistent_value" sizeLimits,
    outsideOf "storage.rs" "test_large_instance_value" sizeLimits,
    outsideOf "storage.rs" "test_large_persistent_key" sizeLimits,
    outsideOf "storage.rs" "test_large_instance_key" sizeLimits,
    outsideOf "storage.rs" "test_extend_ttl_v2_persistent" ttl,
    outsideOf "storage.rs" "test_extend_ttl_v2_instance" ttl,
    outsideOf "storage.rs" "test_extend_ttl_v2_temporary" ttl,
    outsideOf "storage.rs" "test_extend_data_ttl_v2_rejects_instance_storage" ttl,
    outsideOf "storage.rs" "test_extend_instance_and_code_ttl_v2_extension_scope" ttl,
    outsideOf "frame.rs" "has_frame" hostInternal,
    outsideOf "frame.rs" "invocation_hook_tracks_top_frame" hostInternal,
    outsideOf "frame.rs" "try_with_test_contract_frame_has_frame" hostInternal,
    outsideOf "frame.rs" "try_with_test_contract_frame_catches_host_error" hostInternal,
    outsideOf "frame.rs" "try_with_test_contract_frame_catches_panic" hostInternal]

/-! ## Checking the model against the host tests -/

/-- The world after each transaction of a trace. -/
def worlds (accounts : List (Address × List AccountStep)) : List Tx → World → List (Bool × World)
  | [], _ => []
  | t :: ts, w =>
    let r := t.run accounts { w with log := [] }
    r :: worlds accounts ts r.2

/-- Whether the model gives a case the host test's outcome. -/
def Expect.agrees (e : Expect) (r : Bool × World) : Bool :=
  r.1 == e.ok && e.nonces.all fun (a, ns, n) => (ns.filter fun x => (a, x) ∈ r.2.nonces).length == n

/-- Each case of a host trace: its line and whether the model agrees. -/
def SeedTrace.verdicts (s : SeedTrace) : List (Nat × Bool) :=
  (s.expects.zip (worlds s.trace.accounts s.trace.txs {})).map fun (e, r) => (e.line, e.agrees r)

/-- What the model's operations give, refusals as `none`. -/
def storageResults (c : Address) : Store → List Op → List (Option Obs)
  | _, [] => []
  | st, op :: ops =>
    match op.apply c st with
    | some (obs, st') => some obs :: storageResults c st' ops
    | none => none :: storageResults c st ops

def SeedStorage.verdicts (s : SeedStorage) : List (Nat × Bool) :=
  (s.expects.zip (storageResults s.trace.contract [] s.trace.ops)).map fun ((line, want), got) =>
    (line, want == got)

/-- Every case the traces express, by test: its line and whether the model
agrees with the host test. -/
def verdicts : List (String × String × List (Nat × Bool)) :=
  hostSeeds.map (fun s => (s.file, s.test, s.verdicts)) ++
    storageSeeds.map (fun s => (s.file, s.test, s.verdicts))

def vectorsOf (file test : String) : List String :=
  (hostSeeds.filter (fun s => s.file == file && s.test == test)).map (·.trace.name) ++
    (storageSeeds.filter (fun s => s.file == file && s.test == test)).map (·.trace.name)

def casesOf (file test : String) : List (Nat × Bool) :=
  (verdicts.filter fun (f, t, _) => f == file && t == test).flatMap (·.2.2)

/-- The cases where the model and the host test differ. -/
def disagreements : List (String × String × Nat) :=
  verdicts.flatMap fun (f, t, vs) => (vs.filter (!·.2)).map fun (line, _) => (f, t, line)

/-- Tests that name no trace, traces that name no test, and expressed tests
with no case: what keeps `tests` and the traces in step. -/
def inconsistencies : List String :=
  (tests.filterMap fun e =>
    match e.outside, casesOf e.file e.test with
    | none, [] => some s!"{e.file} {e.test}: listed as expressed, but no trace draws from it"
    | some _, _ :: _ => some s!"{e.file} {e.test}: listed as outside the models, but a trace draws from it"
    | _, _ => none) ++
  (verdicts.filterMap fun (f, t, _) =>
    if tests.any (fun e => e.file == f && e.test == t) then none
    else some s!"{f} {t}: a trace draws from a test the coverage does not list")

/-! ## The coverage record -/

def coverageFormat : Nat := 1

def TestEntry.toJson (e : TestEntry) : Json :=
  let cs := casesOf e.file e.test
  let leftCount : Nat := e.left.foldl (· + ·.1) 0
  .obj ([("file", .str e.file), ("test", .str e.test)] ++
    match e.outside with
    | some reason => [("expressed", .bool false), ("reason", .str reason)]
    | none => [
      ("expressed", .bool true),
      ("cases", .num (cs.length + leftCount)),
      ("expressed_cases", .num cs.length),
      ("agree", .num (cs.filter (·.2)).length),
      ("disagree", .num (cs.filter (!·.2)).length),
      ("vectors", .arr ((vectorsOf e.file e.test).map .str)),
      ("left", .arr (e.left.map fun (n, reason) => .obj [("cases", .num n), ("reason", .str reason)]))])

def coverageJson : Json :=
  let expressed := tests.filter (·.outside.isNone)
  let cs := expressed.flatMap fun e => casesOf e.file e.test
  let left : Nat := expressed.foldl (fun acc e => acc + e.left.foldl (· + ·.1) 0) 0
  .obj [
    ("format", .num coverageFormat),
    ("host", .str hostRelease),
    ("files", .arr (["auth.rs", "auth_delegation.rs", "invoker_auth.rs", "storage.rs", "frame.rs"].map
      fun f => .str s!"src/test/{f}")),
    ("totals", .obj [
      ("tests", .num tests.length),
      ("tests_expressed", .num expressed.length),
      ("tests_outside", .num (tests.length - expressed.length)),
      ("cases_in_expressed_tests", .num (cs.length + left)),
      ("cases_expressed", .num cs.length),
      ("cases_agree", .num (cs.filter (·.2)).length),
      ("cases_disagree", .num (cs.filter (!·.2)).length),
      ("cases_left", .num left)]),
    ("tests", .arr (tests.map TestEntry.toJson))]

end Conformance.Soroban.Seed
