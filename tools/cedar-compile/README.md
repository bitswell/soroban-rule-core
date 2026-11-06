# Offline Cedar → rule-core prototype

This native tool compiles a **strict, bounded Cedar fragment** into the existing
`rule_eval::Rule` / `Cond` / `AuthRoot` representation. Perch stays on chain.
It is an executable feasibility prototype, **not a production installer, a
full Cedar compiler or a formally proved translation**.

Cedar 4.14.1's official parser produces the policies; its public EST
(`Policy::to_json`) is inspected structurally, never by textual substitution or
regular expressions. Its official `Authorizer` is the independent eligibility
reference. The dependency, lockfile and tests are in this separate workspace;
Cedar is absent from the default workspace, evaluator, contract and extraction
input. No core semantics are changed.

## Run from a fresh checkout

Install Rust 1.99.0 (or the repository's pinned nightly), then from the repository
root run this one command to compile the fixture, compare decisions and run
state/refusal tests:

```sh
bash tools/cedar-compile/check.sh
```

The script uses locked Cargo commands and a temporary build directory unless
`CARGO_TARGET_DIR` is supplied. Its default compiler is `+1.99.0`; set
`CEDAR_TOOLCHAIN=nightly-2026-09-17` to use the repository pin. It prints the
actual emitted rules and test counts. Dependencies need network access on an
empty cache. Individual commands:

```sh
export CARGO_TARGET_DIR="$(mktemp -d)"
cargo +1.99.0 run --locked --manifest-path tools/cedar-compile/Cargo.toml -- \
  tools/cedar-compile/fixtures/guess-transfer.cedar \
  tools/cedar-compile/fixtures/bindings.json
cargo +1.99.0 test --locked --manifest-path tools/cedar-compile/Cargo.toml -- --nocapture
```

The CLI emits **diagnostic JSON**, not an account installation document or a
canonical commitment format. `compile(source, bindings)?.rules()` returns the
real rule-core structs for a Rust consumer. No account/compiler wire-format
support or deployment is implied. The source and binding files together define
the input; publishing only the source is insufficient to identify the grant.

## Accepted source fragment

Each policy has this shape (parentheses and comments follow ordinary Cedar):

```cedar
permit (
    principal == Signer::"session",
    action == Action::"transfer",
    resource == Contract::"xlm"
) when {
    context.from == Account::"alice" &&
    context.to == Contract::"game" &&
    context.amount >= 0 && context.amount <= 100 &&
    context.authRootContract == Contract::"game" &&
    context.authRootFunction == "guess"
};
```

- Only `permit`, exact entity-literal heads and at most one `when` clause.
  No clause is allowed for a zero-argument call. All policies are compiled;
  their parser-assigned `policy0`, `policy1`, … IDs must exactly match the
  binding manifest. Rule indices follow those IDs in sorted order, independent
  of Cedar's policy iteration order. Reordering source changes that association.
- Conditions are `&&` trees of direct `context.field OP literal` comparisons.
  Integer fields support `==`, `<`, `<=`, `>`, `>=`; operands are not reversed.
  String, bool and address fields support only exact `==`. A syntactic negative
  integer literal is supported; general arithmetic is not.
- **Every declared argument must be constrained.** Each integer's conjunction
  must describe a nonempty closed interval of **at most 256 i64 values**, or an
  equality. Intervals emit exact `ArgIn` sets, equality emits `ArgEq`; no lower
  bound or i64 boundary is dropped. Inconsistent integer bounds reject the set.
  Scalar equalities emit `ArgEq` with the exact Soroban value constructor.
- A root condition requires exactly one equality for **both**
  `authRootContract` and `authRootFunction`. They emit the existing `AuthRoot`.
  Half a pair, duplicate constraints or non-contract roots reject the input.
- All annotations, `forbid`, `unless`, wildcards, templates/slots, hierarchy
  (`in` / `is`), entity attributes, `has`, disjunction, negation, arithmetic,
  extensions, sets, records and other operators reject the **whole input**.
  Nothing is silently ignored, including an unsupported policy that would
  never match the example request.

Bounds: 16 KiB source, 64 KiB binding JSON; 1–8 policies; at most 16 principal,
entity or call bindings (principals/calls nonempty); 8 arguments per call;
condition depth 32 and 127 expression nodes; 128-byte canonical UIDs; 32-byte
function/argument symbols; 256-byte string literals/external signer keys. The
source byte bound precedes the official native parser; this is an offline CLI,
not a hardened multi-tenant parsing service. Integer enumeration can still
produce up to 8 × 8 × 256 stored values; no on-chain encoding/size claim is made.

For example, these exit nonzero with policy-specific diagnostics:

```sh
cargo +1.99.0 run --locked --manifest-path tools/cedar-compile/Cargo.toml -- \
  tools/cedar-compile/fixtures/reject-forbid.cedar tools/cedar-compile/fixtures/bindings.json
# policy0: only permit is supported; forbid cannot be dropped
cargo +1.99.0 run --locked --manifest-path tools/cedar-compile/Cargo.toml -- \
  tools/cedar-compile/fixtures/reject-wide-range.cedar tools/cedar-compile/fixtures/bindings.json
# policy1: context.amount: require ... at most 256 values
```

The research report's `0..10000000` amount guard is deliberately **rejected**.
The fixture uses small integer units to demonstrate a faithful fragment. This
limit makes it unsuitable for ordinary broad token-amount ranges today; expanding
it by deleting the lower bound, narrowing i128 by casting or silently rounding
amounts would be incorrect. Extending core predicates is outside this prototype. A symmetric
`ArgI128AtLeast(index, lower)` would let a future compiler use that predicate
and existing `ArgI128AtMost(index, upper)` for an exact closed range, eliminating
enumeration. It would still need to clamp the represented domain to Cedar i64,
handle strict-bound endpoints without overflow and preserve wrong-constructor
refusal. That proposal needs separate core/API/extraction/proof work; it is not
implemented or assumed here. The two-condition observation is about raw
rule-core: Perch document validation allows an argument index only once. A
single inclusive typed i128 range predicate through both document and evaluator
would better preserve that document convention. The core owner is assessing it;
this prototype assumes neither new API.

## Explicit bindings and trust boundary

[bindings.json](fixtures/bindings.json) is the complete example. Unknown JSON
fields, duplicate struct fields, duplicate/aliased identities, conflicting call
bindings, missing entities and extra/missing policy IDs are errors.

| Manifest field | Meaning |
|---|---|
| `principals` | Canonical `Signer` UID → one delegated address or external verifier/key. Distinct UIDs cannot alias the same signer. Threshold is exactly one. This does not verify signatures. |
| `entities` | `Account` or `Contract` UID → typed 32-byte address ID. Mapping is injective. Account XDR includes account + ed25519 discriminants; contract XDR includes the contract discriminant. Muxed addresses are unsupported. |
| `calls` | `Action` UID + contract `resource` UID → exact function symbol and ordered, named, typed arguments (`integer`, `address`, `string`, `bool`). A target/function cannot have two mappings. The same Action UID cannot denote different functions. |
| `policies` | Exact source policy IDs plus optional **Perch-only** `cap`, `valid_until`, `generation`. These attachments are outside Cedar eligibility semantics. A cap names a bound integer argument, positive i64 limit and positive u32 period. |

Bindings are trusted application configuration, not facts a transaction sender
may invent. A real integration must authenticate the signer first, use the
account's actual host-provided `__check_auth` contexts, validate scoped-grant
exclusions/attenuation and bind source + bindings + output to installation.
The fixture uses illustrative IDs, not live accounts or keys. Delegated and
external signer variants describe existing rule-core identities; passkeys,
cryptographic checks, replay protection and multisignature composition remain
account/verifier responsibilities.

`Compiled::request` / `compare` takes **one current authenticated entry**, a
context index and one already-authenticated signer. It derives root fields from
`entry[0]`; there is no independent root or arbitrary context-JSON parameter.
It checks 1–32 contexts, a non-creation contract root, known current
contract/function, exact argument arity/constructors, bound address identities,
UTF-8 strings and checked `i128 → i64`. Out-of-domain input is `Err`, not a Cedar
verdict. This plain Rust function cannot itself prove that its caller obtained
the entry/signature from the host: that is an explicit integration obligation.

Root matching uses `rule_allows_in` for eligibility and **`authorize` for the
full entry**, which independently derives the root from that same entry. Never
use local-only `allows`, `allows_all` or `rule_allows` to approve these rules.
The root is this account's authorization-entry root, not a transaction root,
arbitrary ancestor, caller, another entry or a Cedar entity hierarchy. A wrapper
that does not request this account's auth is absent from the entry.

The game **must require the guesser's auth on `guess`**. A win's entry contains
`[game.guess]` and selects the game rule. A loss contains
`[game.guess, token.transfer]` and selects both rules. If only the transfer
requires auth, its entry starts at transfer and is refused. An independently
authorized game entry cannot lend its root to a direct transfer. The tests
exercise these supplied-entry decisions; this tool adds no new real-host game
contract or signature verification. It relies on the tested base AuthRoot API.

## What the comparisons establish

The tests compare **Cedar eligibility** with `rule_allows_in` over the generated
rules, using the same explicit typed mapping and a single authenticated signer.
Empty entities suffice because accepted policies only compare entity literals.
For valid mapped requests the tests require both agreement and no Cedar errors.
They do not compare Cedar's OR-of-permits against Perch's entire state machine.

The fixed corpus has **2,357 eligibility comparisons**: 284 deterministic
request/signer/root/recipient boundaries, 2,048 generated requests across 32
varied source intervals/operator forms, and 25 integer-extreme/equality/scalar
cases. It also checks 15 malformed/out-of-domain refusals, 28 unsupported-source
cases, 18 binding rejection cases, the 256-value interval boundary, raw Cedar
missing/wrong-type/overflow context behavior, and the skip-on-error forbid trap.
An erroring forbid next to a successful permit can allow in Cedar; this frontend
rejects forbid entirely rather than changing or silently approximating that rule.
Out-of-domain refusals are **not** counted as reference-evaluator agreement.

Every integer rule uses finite exact i128 values, so even raw rule eligibility
cannot wrap an out-of-i64 amount into an allowed value. The reference mapper
also rejects such input. Extra trailing arguments are rejected by the mapper;
raw rule-core conditions do not check arity, and real account integration must
preserve the documented function ABI/domain. The mapping supports one principal
per comparison; it establishes no equivalence for arbitrary multisigner policies.

Separate state tests use `rule_eval::authorize` with explicit chosen indices:
winning game-only authorization, losing transfer charges, repeated transfers
accumulating on one cap, atomic batch refusal with no returned updates, successful
window expiry, wrong choices, missing auth, expiry and generation revocation.
A small account simulation commits returned records only on success. This tests
the pure evaluator contract, **not new ledger-storage rollback or crypto code**.
The prior core/host tests cover their own stated boundaries.

There is **no compiler correspondence theorem**. Existing Cedar model proofs,
Cedar differential tests and rule-core extraction proofs do not prove this EST
whitelist, binding layer, integer enumeration, output association or installer.
The deterministic generated corpus is bounded evidence, not universal coverage.
Before production: a useful wider fragment with a correspondence argument;
independent parser/lowering fuzzing and review; trusted canonical source/binding
commitments; typed installation/wire support; real account/host entry tests;
scoped exclusion and attenuation preservation; and measured compiled storage and
execution costs. No migration, deployment or general Cedar runtime is included.

## Dependencies and licensing

Cedar 4.14.1 is pinned in `Cargo.lock` with registry checksums, including core and
formatter. Its standard default extensions remain enabled as build dependencies
(the spike found optional-feature build failures); the accepted language forbids
all extension calls. Cedar's Apache-2.0 license/notices remain in the dependency
packages. This repository's MIT OR Apache-2.0 license covers the new glue; no
upstream implementation source is copied into it. Preserve dependency notices
when distributing a binary. Upstream references:
[release](https://github.com/cedar-policy/cedar/releases/tag/cedar-policy-cli-v4.14.1),
[API and EST conversion](https://github.com/cedar-policy/cedar/blob/47d82a8293354f235d3f8d092c71071706401741/cedar-policy/src/api.rs),
[license](https://github.com/cedar-policy/cedar/blob/47d82a8293354f235d3f8d092c71071706401741/LICENSE).
