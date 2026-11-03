# conformance

Test vectors for rule-set evaluation and attenuation, traces of the
spending-cap check, traces of `authorize`, traces of the budget tree and
traces of documents, computed by the Lean model in `formal/`, and a runner that checks `rule-eval` against them. Any other implementation of the same rules
(Perch's smart account, the grant signer) can run the same vectors as a
differential test.

| Path | Contents |
| --- | --- |
| `vectors/*.json` | One vector per file: a rule set, a batch of contexts, the authenticated signers, attenuation step lists, and the results the Lean model computes for them. |
| `vectors/caps/*.json` | One cap trace per file: a cap, a starting record, and calls, each with the outcome the Lean model computes for it. |
| `vectors/authorize/*.json` | One authorization trace per file: a rule set, its starting records, and authorizations, each with the outcome the Lean model computes for it. |
| `vectors/budget/*.json` | One budget trace per file: a starting tree, and spends, delegations and refills, each with the outcome the Lean model computes for it. |
| `vectors/documents/*.json` | One document trace per file: a document, its account, the rules the Lean model lowers it to, and authorizations, each with the document's own verdict. |
| `vectors/soroban/values/*.json` | Soroban values, each with its XDR, its reading by `rule-eval` and whether it may be a storage key. |
| `vectors/soroban/contexts/*.json` | One value per file as `__check_auth` would receive it, with the contexts the model reads from it, or none. |
| `vectors/soroban/storage/*.json` | One storage trace per file: a contract's operations on its storage, each with what the model returns. |
| `vectors/soroban/host/*.json` | One host trace per file: contract accounts' `__check_auth` programs and transactions of calls and signed entries, each with the model's outcome, events and storage. |
| `generator/` | The Lake package that writes the vectors and traces: the case specifications and the JSON encoding. |
| `runner/` | The Rust crate `rule-eval-conformance`, which loads every vector and trace and checks `rule-eval` and `soroban-facade` against it. |
| `vectors/soroban/seed/` | soroban-env-host 29.0.1's own authorization and storage tests, transcribed: host traces in `host/`, storage traces in `storage/`, and `coverage.json`, which lists every test of the five test files, what the traces express of it and why the rest is outside the models. |
| `host/` | The host harness: `src/` and `tests/` replay the Soroban vectors on `soroban-env-host`, and each crate beside them (`p29/`, `p30/`) pins one host version. |

## How the vectors are made

`generator/` is a Lake package that requires the `rule-core` package in
`../../formal`. Its cases (`Conformance/Cases.lean` and
`Conformance/Random.lean`) specify inputs only. `lake exe gen-vectors` computes
every expected result with the chain vocabulary's own functions,
`RuleCore.Chain.RuleSet.allows`, `RuleSet.allowsAll` and
`RuleSet.attenuateAll`, the functions the theorems in `formal/` are about, and
writes each case to `<name>.json`. The cap traces (`Conformance/Caps.lean`) are
computed with `RuleCore.Cap.Params.check` and written to `caps/<name>.json`, and
the authorization traces (`Conformance/Authorize.lean`) with
`RuleCore.Chain.RuleSet.authorize` and written to `authorize/<name>.json`, and
the budget traces (`Conformance/Budget.lean`) with `RuleCore.Budget.Op.apply`
and written to `budget/<name>.json`, and the document traces
(`Conformance/Documents.lean`) with `RuleCore.Document.Doc.lower`,
`Doc.lowerScoped`, `Doc.excluded` and `Doc.authorize` and written to
`documents/<name>.json`. The Soroban vectors (`Conformance/Soroban/`) are
computed with the Soroban models' own functions, `Val.xdr`, `Val.toChain`,
`Val.storable`, `contextsOfVal`, `AuthFn.toChain`, `Op.apply` and `Tx.run`,
and written to `soroban/values`, `soroban/contexts`, `soroban/storage` and
`soroban/host`. The seed traces (`Conformance/Soroban/Seed.lean`) are the
host's own tests transcribed, each case with the host test's expectation; the
generator computes each with the same model functions, writes the model's
outcome, and writes nothing at all when one differs from the host test's
(see [Seed traces](#seed-traces)). No expected result is written by hand.

```sh
cd conformance/generator
lake exe gen-vectors ../vectors
```

`gen-vectors <dir>` removes the `.json` files in `<dir>`, `<dir>/caps`,
`<dir>/authorize`, `<dir>/budget` and `<dir>/documents` and writes every named
case plus 100 randomized cases of seed 20261102, every named cap trace plus 50
randomized traces of the same seed, every named authorization trace plus 50
randomized traces of the same seed, every named budget trace plus 50
randomized traces of the same seed, every named document trace plus 40
randomized traces of the same seed, the Soroban value and context vectors,
every named storage trace plus 30 randomized traces of the same seed, and
every named host trace plus 60 randomized traces of the same seed, and the
seed traces with their coverage. It refuses
to write a document trace whose document is not valid or that chooses the
recovery rule, and a host trace the harness cannot drive on the host
(`Trace.inDomain`). `--seed <n>`, `--count <n>`, `--cap-count <n>`,
`--auth-count <n>`, `--budget-count <n>`, `--doc-count <n>`,
`--storage-count <n>` and `--host-count <n>` choose another randomized set,
for a larger run outside the committed vectors:

```sh
lake exe gen-vectors /tmp/vectors --seed 7 --count 5000 --cap-count 5000 --auth-count 5000 --budget-count 5000 --doc-count 5000 --storage-count 1000 --host-count 2000
CONFORMANCE_VECTORS=/tmp/vectors cargo test -p rule-eval-conformance
CONFORMANCE_VECTORS=/tmp/vectors cargo test -p soroban-host-p29
CONFORMANCE_VECTORS=/tmp/vectors cargo test --manifest-path host/p30/Cargo.toml
```

The randomized cases use SplitMix64, written out in `Conformance/Random.lean`,
so a seed produces the same vectors on every Lean release. Case `k` of a seed
is drawn from its own stream. Rule sets, contexts, signers and steps come from
small universes of contract ids, function names, payloads, integers and
signers that include each other's prefixes and extensions, the `i128`, `u64`
and `u32` extremes, and delegated and external signers with equal bytes; calls
are mostly built from a rule of the set with arguments that usually satisfy its
conditions, and the authenticated signers usually include some of the rules'
signers, so allowed and refused contexts both occur. Rules are wildcards a fifth of the
time, and a quarter of the time carry a last ledger or a generation; conditions
include `arg_in` and `arg_str_prefix`, and steps `restrict_functions` and
`lower_valid_until`. The randomized cap traces
draw caps, starting ledgers, amounts and ledger steps from small universes that
include the `u32` and `i128` extremes; ledgers mostly advance by less than a
period and sometimes repeat or go back, so every refusal occurs. Random rules
carry a cap a third of the time, and random steps include the three cap steps.
The randomized authorization traces draw rule sets with caps, batches built
from their rules with amounts near the caps' limits at the caps' argument
indices, choices that usually name the rule a call was built from, signers that
usually belong to the chosen rules, ledgers that mostly advance, and a current
generation that sometimes moves on by one. The randomized budget traces draw trees of up to six
nodes with parents below their own index, allowances from a small universe
that includes the `i128` extremes, an occasional node with a spent amount and
one tree in eight made malformed, and operations whose indices are mostly in
range. The randomized document traces draw documents of up to three rules over
a small universe of contracts, functions, signers and string values, with
`all` and `threshold` principals of distinct declared signers, predicates,
not-after ledgers and caps; an admin document starts with a constraint-free
self-admin rule, and a third of the traces are scoped documents under an admin
document configuring recovery with a zero-knowledge factor; each authorization
is a call built from a rule of the document, usually choosing that rule and
signed by some of its signers, with a further signer now and then.

## Running them against rule-eval

```sh
cargo test -p rule-eval-conformance
```

The runner is a workspace member, so `cargo test --workspace` in
`.github/workflows/rust.yml` runs it on the pinned nightly and on stable. Its
tests check that `rule-eval` reproduces every result of every vector, that the
vectors still cover every value constructor, condition, signer kind, threshold
case, function-set kind, step kind and outcome, and that a vector with a changed expectation is
reported. Its cap tests (`tests/caps.rs`) check that `check_spend` reproduces
every outcome and record of every trace, that the traces still cover every
refusal, ledger 0, `u32::MAX` and invalid caps, and that a changed expectation
is reported. Its authorization tests (`tests/authorize.rs`) check that
`authorize` reproduces every outcome and record of every trace, that the traces
still cover every refusal, two contexts charging one rule, eviction, mismatched
records and the empty batch, and that a changed expectation is reported. Its
budget tests (`tests/budget.rs`) check that `spend`, `delegate` and `refill`
reproduce every outcome and tree of every trace, that the traces still cover
every refusal but `tree_full`, overdrawn refusals at the spender and at an
ancestor, malformed and empty trees and several roots, and that a changed
expectation is reported. Its document tests (`tests/documents.rs`) check that
`lower`, or `lower_scoped` under `excluded` of the admin document, builds every
trace's rules or refuses as it does, that `authorize` reaches every verdict and
record, that the traces still cover admin and scoped documents, recovery,
both scopes, both kinds of principals, rules without functions, caps,
not-after ledgers, every predicate and both scoped refusals, and that a changed
expectation is reported.
Its Soroban tests (`tests/soroban.rs`) check that `soroban-facade` writes and
reads back every value as the model's XDR, converts it for `rule-eval` as the
model does and agrees on which values may be keys; reads every context vector
as the model, refusing the same values; and that its plain storage gives
every storage trace's results.
`rule-eval` itself keeps no dependencies; the runner depends on it,
`soroban-facade`, `serde` and `serde_json`.

## Running them against the host

```sh
cargo test --locked --manifest-path host/p29/Cargo.toml
cargo test --locked --manifest-path host/p29/Cargo.toml --no-default-features
cargo test --locked --manifest-path host/p30/Cargo.toml
```

`host/p29` is the harness at the pin, soroban-sdk 29.0.1 with
soroban-env-host 29.0.1 and stellar-xdr 28.0.0 (protocol 29), and a
workspace member. `host/p30` is the harness at the next release,
soroban-sdk 30.0.0-rc.1 with soroban-env-host 30.0.0 and stellar-xdr 30.0.0
(protocol 30), a workspace of its own with its own lock. Their tests
(`host/tests/host.rs`) replay the value vectors, the storage traces, the host
traces and the seed traces on the host, through soroban-sdk's testutils with enforcing
authorization (`set_auths`, not `mock_all_auths`), and compare outcomes,
events and storage, not error codes: every refusal reaches the caller as the
same host error whatever its cause. Every contract a trace names is a native
contract that runs what the trace says: before each call the harness hands the
callee the body the trace gives it. With the `facade` feature, on by default
in `p29`, its storage, `require_auth` and reading of `__check_auth`'s contexts
go through `soroban-facade`'s real implementation; without it, through the SDK
directly, as in `p30`, whose SDK is not the facade's. They also read every context vector
with the SDK's `auth::Context`, which must read exactly the vectors the model
reads and write them back as the same XDR. `.github/workflows/host.yml` runs
three entries: `p29` with the facade, `p29` without it and `p30`. A crate for
another host version is a directory beside these, named
`soroban-host-p<protocol>` with its library named `harness`, with its own
`Cargo.toml` (holding an empty `[workspace]`) and `Cargo.lock` naming
`../src/lib.rs` and `../tests/host.rs`; a version whose SDK is not the
facade's leaves the `facade` feature off and drives the SDK directly.

`.github/workflows/conformance.yml` rebuilds the generator, regenerates the
vectors and traces into an empty directory and fails if they differ from
`conformance/vectors`, including a committed file the generator no longer
writes. It also checks that `generator/lean-toolchain` matches
`formal/lean-toolchain` and rejects the same unchecked Lean declarations as
`lean.yml`.

## Vector format

Every file is one JSON object. Object fields appear in the order below;
readers should not depend on it.

```json
{
  "format": 4,
  "name": "batch-mixed",
  "description": "A batch of allowed and refused calls is refused as a whole.",
  "rules": [Rule, ...],
  "batch": [Context, ...],
  "authenticated": [Signer, ...],
  "expected": {"allows": [true, false, ...], "allows_all": false},
  "attenuations": [
    {"steps": [Step, ...], "expected": Outcome},
    ...
  ]
}
```

| Field | Meaning |
| --- | --- |
| `format` | The version of this format, `4`. A change a reader of the current version cannot read raises it. |
| `name` | The file name without `.json`. |
| `description` | What the vector exercises, for a reader; carries no data. |
| `rules` | The rule set, in order. |
| `batch` | The contexts of one authorization tree, in order. |
| `authenticated` | The signers the authorization covering `batch` authenticated, one list for every context. |
| `expected.allows` | The rule set's verdict on each context of `batch` under `authenticated`, in the same order. |
| `expected.allows_all` | The rule set's verdict on the whole batch under `authenticated`. |
| `attenuations` | Step lists applied to `rules`; each is independent of the others and starts from `rules`. |

### Encodings

* A **byte string** (contract id, function name, wasm hash, value payload) is a
  JSON string of lowercase hexadecimal, two digits per byte. `""` is the empty
  byte string. Byte strings compare exactly: same length, same bytes.
* An **`i128`** or **`u64`** is a JSON string holding the decimal integer, with
  a leading `-` for a negative `i128`, so that readers holding JSON numbers as
  doubles lose nothing. Bounds run from `-170141183460469231731687303715884105728`
  to `170141183460469231731687303715884105727` and from `0` to
  `18446744073709551615`.
* An **index** (argument index or rule index), a **threshold** or a **period**
  is a JSON number from `0` to `4294967295`, a `u32`.

### Values

A value is an object with exactly one field, naming its constructor:

| JSON | Value |
| --- | --- |
| `{"i128": "-5"}` | A Soroban `i128`. |
| `{"u64": "7"}` | A Soroban `u64`. |
| `{"bool": true}` | A Soroban `bool`. |
| `{"bytes": "6162"}` | A Soroban `Bytes`. |
| `{"address": "..."}` | An address, as its `ScAddress` XDR. |
| `{"symbol": "..."}` | A symbol, as its bytes. |
| `{"string": "..."}` | A string, as its bytes. |
| `{"other": "..."}` | An argument of any other type, as its full `ScVal` XDR. |

Values of different constructors are never equal, even when their payloads
are: `{"bytes": "6162"}` is not `{"other": "6162"}`, and `{"string": "6162"}`
is not `{"symbol": "6162"}`.

### Contexts

```json
{"call": {"contract": "746f6b656e", "function": "7472616e73666572", "args": [Value, ...]}}
{"create": {"wasm_hash": "..."}}
```

A call names a contract, a function and its arguments, indexed from `0`. A
creation is refused by every rule set.

### Signers

```json
{"delegated": {"address": "..."}}
{"external": {"verifier": "...", "key": "..."}}
```

A `delegated` signer is an address that authorizes for itself, as its
`ScAddress` XDR. An `external` signer is a key checked by a verifier contract:
the verifier's address, as its `ScAddress` XDR, and the key's bytes. Signers
compare exactly, constructor first: `{"delegated": {"address": "6162"}}` is not
`{"external": {"verifier": "6162", "key": ""}}`.

### Conditions

```json
{"arg_eq": {"index": 2, "value": Value}}
{"arg_i128_at_most": {"index": 2, "bound": "100"}}
{"arg_in": {"index": 0, "values": [Value, ...]}}
{"arg_str_prefix": {"index": 1, "prefix": "706b675f"}}
```

* `arg_eq` holds when argument `index` exists and equals `value`: the same
  constructor and the same payload.
* `arg_i128_at_most` holds when argument `index` exists, is an `i128`, and is at
  most `bound`, compared as signed integers.
* `arg_in` holds when argument `index` exists and equals one of `values`, each
  compared as `arg_eq` compares. With no values it never holds.
* `arg_str_prefix` holds when argument `index` exists, is a `string`, and its
  bytes start with exactly the bytes of `prefix`. The empty prefix holds on
  every string.

A missing argument, including any index at or past the number of arguments,
makes every condition false. An argument of another constructor makes
`arg_eq`, `arg_i128_at_most` and `arg_str_prefix` false, and `arg_in` false
unless one of its values has that constructor.

### Rules

```json
{"contract": "746f6b656e", "functions": {"only": ["7472616e73666572", ...]},
 "conds": [Condition, ...], "signers": [Signer, ...], "threshold": 2, "cap": Cap,
 "valid_until": 599, "generation": "3"}
```

`functions` is `{"only": [name, ...]}`, the functions listed, or
`{"any_except": [name, ...]}`, every function except those listed; the
wildcard, every function of the contract, is `{"any_except": []}`.
`valid_until` is the rule's last ledger, a `u32`, and `generation` the
generation it was issued under, a decimal `u64` string; either is `null` when
the rule has none. Neither affects the verdicts below: only the authorization
traces read them.

A rule allows a call when the call's contract equals `contract`, its function
is one of the rule's `functions`, every condition in `conds` holds on its arguments,
and at least `threshold` distinct signers of `signers` are in the vector's
`authenticated` list. Each signer counts once: a signer listed twice in
`signers`, or authenticated twice, counts as one. A rule whose `functions` is
`{"only": []}` allows nothing; one with an empty `conds` list puts no
constraint on arguments; one with threshold `0` puts none on signers; one whose
threshold is above its number of distinct signers allows nothing. A rule set allows a context
when some rule allows it, and allows a batch when it allows every context in
it, so every rule set allows the empty batch. A batch collected from a Soroban
authorization tree always holds the root context; a caller that builds batches
another way must refuse an empty one itself.

### Caps

```json
{"limit": "100", "period": 10, "amount_arg": 2}
```

A rule's `cap` is `null` when it has none. A cap allows at most `limit` (an
`i128`) to be spent within `period` consecutive ledgers, each call spending its
argument at index `amount_arg` when that argument is an `i128`. `allows` and
`allows_all` do not read the cap; the authorization traces charge it. A cap
may be added to a rule only when `limit > 0` and `period > 0`.

### Attenuation steps

```json
{"drop_rule": {"index": 1}}
{"add_cond": {"index": 0, "cond": Condition}}
{"remove_functions": {"index": 0, "functions": ["617070726f7665", ...]}}
{"restrict_functions": {"index": 0, "functions": ["7472616e73666572", ...]}}
{"remove_signers": {"index": 0, "signers": [Signer, ...]}}
{"raise_threshold": {"index": 0, "threshold": 3}}
{"add_cap": {"index": 0, "cap": Cap}}
{"lower_cap_limit": {"index": 1, "limit": "50"}}
{"lengthen_cap_period": {"index": 1, "period": 20}}
{"lower_valid_until": {"index": 0, "valid_until": 599}}
```

* `drop_rule` removes rule `index`, keeping the others in order.
* `add_cond` appends `cond` to the conditions of rule `index`.
* `remove_functions` removes every occurrence of every listed name from the
  function list of rule `index`, keeping the remaining names in order, and
  ignores names not in the list. On a wildcard it appends the listed names, in
  order and repeats included, to the names it excludes.
* `restrict_functions` keeps, in order, the functions of rule `index`'s list
  that are also listed; on a wildcard it gives the list of the listed names,
  in their order, that the wildcard does not exclude.
* `remove_signers` removes every occurrence of every listed signer from the
  signers of rule `index`, keeping the remaining signers in order and the
  threshold as it was. Signers not in the list are ignored.
* `raise_threshold` sets the threshold of rule `index` to `threshold`. It is
  refused with `threshold_lowered` when `threshold` is below the rule's
  current threshold.
* `add_cap` gives rule `index` the cap `cap`. It is refused with `cap_present`
  when the rule has a cap, and then with `invalid_cap` when `cap`'s limit is
  not positive or its period is `0`.
* `lower_cap_limit` sets the limit of rule `index`'s cap to `limit`. It is
  refused with `no_cap` when the rule has no cap, then with `limit_raised`
  when `limit` is above the current limit, and then with `invalid_cap` when
  `limit` is not positive.
* `lengthen_cap_period` sets the period of rule `index`'s cap to `period`. It
  is refused with `no_cap` when the rule has no cap, and then with
  `period_shortened` when `period` is below the current period.
* `lower_valid_until` sets the last ledger of rule `index` to `valid_until`. It
  is refused with `valid_until_raised` when the rule has a last ledger before
  `valid_until`.

A step whose `index` is not below the number of rules is refused with
`no_such_rule`, before any other check. A step list is applied in order, each
step to the previous step's result, and stops at the first refused step.

### Outcomes

```json
{"ok": {"rules": [Rule, ...], "allows": [true, ...], "allows_all": false}}
{"error": "no_such_rule"}
{"error": "threshold_lowered"}
```

The errors are `no_such_rule`, `threshold_lowered`, `cap_present`, `no_cap`,
`invalid_cap`, `limit_raised`, `period_shortened` and `valid_until_raised`.
`ok` holds the rule set after every step, compared rule by rule, field by field
(the functions' kind, the cap, the last ledger and the generation included) and
in order, and its verdicts on the vector's `batch` under its
`authenticated` signers, as in `expected`. `error` says a step was refused, and
why.

## The named cases

| Vector | What it exercises |
| --- | --- |
| `arg-eq-i128`, `arg-eq-u64`, `arg-eq-bool` | `arg_eq` on each integer and boolean constructor: equal and unequal values, the same number under another constructor, the extremes. |
| `arg-eq-bytes`, `arg-eq-address`, `arg-eq-symbol`, `arg-eq-other` | `arg_eq` on each byte-string constructor: the same bytes, a prefix, an extension, another case, and the same bytes under every other byte-string constructor. |
| `arg-eq-empty-payload`, `arg-eq-raw-bytes` | Empty payloads, and payloads that are not text. |
| `arg-i128-at-most`, `arg-i128-at-most-extremes` | The signed bound: below, at and above it, at the `i128` extremes, against a `u64` and a missing argument. |
| `missing-arguments`, `index-edges` | Argument indices past the end, and at `0`, `2^31` and `2^32 - 1`. |
| `rule-without-conditions`, `empty-function-list`, `duplicate-functions` | Rules with no conditions, no functions, and a repeated function. |
| `contract-exact-bytes`, `function-exact-bytes` | Exact comparison of contract ids and function names: prefixes, extensions, case, the empty string. |
| `creations`, `creation-empty-rule-set`, `batch-with-creation` | Creations are refused, alone and in a batch. |
| `multi-rule-one-matches`, `overlapping-rules`, `conditions-belong-to-their-rule` | Rule sets of several rules: one rule matching, two rules for the same call, and conditions read only for their own rule. |
| `batch-mixed`, `batch-all-allowed`, `empty-batch`, `empty-batch-empty-rule-set`, `empty-rule-set` | Batch verdicts, the empty batch, and the empty rule set. |
| `attenuate-drop-rule`, `attenuate-add-cond`, `attenuate-remove-functions` | Each step at every index of a three-rule set, and refused at the length, at `2^31` and at `2^32 - 1`. |
| `attenuate-empty-rule-set` | Every step on the empty rule set is refused. |
| `attenuate-chains` | Step lists: the empty list, indices that shift after a drop, and a list refused part-way through. |
| `signers-threshold-none`, `signers-threshold-one`, `signers-threshold-two`, `signers-threshold-all` | Thresholds 0, 1, 2, all three signers and above, with none, one, two and all of the signers authenticated. |
| `signers-repeated-in-rule`, `signers-repeated-in-authenticated` | A signer listed twice in a rule, or authenticated twice, counts once. |
| `signers-delegated-versus-external`, `signers-external-versus-delegated` | Delegated and external signers whose bytes are equal, split between verifier and key in every way, are different signers. |
| `signers-missing` | Signers outside the rule, prefixes and extensions of a rule signer's bytes, and a rule with no signers and threshold 1. |
| `signers-batch-one-missing`, `signers-batch-all-present` | One authenticated list covers a whole batch whose calls need different signers. |
| `attenuate-remove-signers`, `attenuate-raise-threshold` | Each signer step at each index, with exact matching, an emptied list, thresholds at, above and below the current one, and refusals at the length, `2^31` and `2^32 - 1`. |
| `attenuate-signer-chains` | Step lists of all five kinds, including one refused with `threshold_lowered` part-way through. |
| `caps-leave-verdicts`, `attenuate-add-cap`, `attenuate-lower-cap-limit`, `attenuate-lengthen-cap-period`, `attenuate-cap-chains` | Verdicts that ignore caps, each cap step and each of its refusals, and chains mixing them with the other steps. |
| `wildcard-functions` | Wildcards with and without exclusions: unnamed and empty function names, exact comparison of excluded names, other contracts and creations. |
| `allows-reads-no-time-or-generation` | Rules with a last ledger and a generation allow as they would without them. |
| `arg-in`, `arg-str-prefix`, `arg-eq-string` | `arg_in` over values of several constructors and with no values; `arg_str_prefix` on strings, prefixes, extensions and symbols, bytes and other values with the same bytes, and the empty prefix; `arg_eq` on a string. |
| `attenuate-remove-functions-wildcard`, `attenuate-restrict-functions`, `attenuate-lower-valid-until` | `remove_functions` on a wildcard, `restrict_functions` on a wildcard and a list, and `lower_valid_until` adding, lowering, keeping and refusing to raise a last ledger. |

`random-000.json` to `random-099.json` are the randomized cases.

## Cap trace format

A cap trace runs calls through the spending-cap check, `check_spend` in
`rule-eval` and `Params.check` in the model. Every file is one JSON object.
Object fields appear in the order below; readers should not depend on it.

```json
{
  "format": 1,
  "name": "cap-window-slides",
  "description": "...",
  "limit": "100",
  "period": 10,
  "params_valid": true,
  "start": {"history": [{"ledger": 5, "amount": "30"}], "total": "30"},
  "calls": [
    {"now": 12, "amount": "40", "expected": Outcome},
    ...
  ]
}
```

| Field | Meaning |
| --- | --- |
| `format` | The version of this format, `1`. It is versioned apart from the rule vectors. A change a reader of version 1 cannot read raises it. |
| `name` | The file name without `.json`. |
| `description` | What the trace exercises, for a reader; carries no data. |
| `limit` | The cap's limit, an `i128`. |
| `period` | The cap's period in ledgers, a `u32`. |
| `params_valid` | Whether the cap may be installed: `limit > 0` and `period > 0`. The calls run under the cap either way. |
| `start` | The record the first call starts from. |
| `calls` | The calls, in order. Each starts from the record the calls before it left: the record after an accepted call, the same record after a refused one. |
| `calls[i].now` | The current ledger, a `u32`. |
| `calls[i].amount` | The amount spent, an `i128`. |
| `calls[i].expected` | The outcome of the call. |

Ledgers and periods are JSON numbers from `0` to `4294967295`. Amounts, totals
and limits are JSON strings holding the decimal integer, as `i128` values are
in the rule vectors.

A record is `{"history": [Entry, ...], "total": "..."}`, and an entry is
`{"ledger": n, "amount": "..."}`. The history lists entries in the order they
were recorded. Most starting records are what the check could have built: in
ledger order, with positive amounts summing to the total. A few are not, to
exercise the checked sums and eviction's stopping rule, and their descriptions
say so.

### Outcomes

```json
{"ok": Record}
{"error": "limit_exceeded"}
```

`ok` holds the record after the call, compared entry by entry and in order,
and total for total. `error` names the refusal:

| Error | When |
| --- | --- |
| `negative_amount` | `amount < 0`. |
| `ledger_before_newest` | `amount > 0` and `now` is less than the ledger of the history's last entry. |
| `overflow` | The evicted amounts, the total less them, or that plus `amount` does not fit in an `i128`. |
| `limit_exceeded` | The total left after eviction plus `amount` exceeds `limit`. |
| `history_full` | The history left after eviction holds 1000 entries. |

The check, in order: a negative amount is refused; a zero amount is accepted
and leaves the record as it was; a positive amount at a ledger before the
newest entry is refused; the entries at the front of the history whose ledger
is at most `now - period` (0 when `now < period`) are evicted, stopping at the
first later entry, and their amounts summed; then the overflow, limit and
history checks above, in that order; and otherwise `(now, amount)` is appended
and the total increased by `amount`.

### The named traces

| Trace | What it exercises |
| --- | --- |
| `cap-within-limit`, `cap-limit-inclusive` | Spends up to the limit, the limit itself, and one over. |
| `cap-window-slides`, `cap-period-one` | Eviction at the cutoff `now - period` and beside it, and a period of one ledger. |
| `cap-refusal-keeps-record` | A refused spend leaves the record, its eviction included, as it was. |
| `cap-negative-amount`, `cap-zero-amount` | Negative amounts, and zero amounts at any ledger and over a total above the limit. |
| `cap-lowered-limit` | A limit below the starting record's total: spends wait for eviction. |
| `cap-ledger-before-newest`, `cap-same-ledger` | The clock check, and several spends in one ledger. |
| `cap-ledger-zero`, `cap-saturating-cutoff`, `cap-u32-extremes` | The cutoff saturating at ledger 0, and the largest ledger and period. |
| `cap-history-fills`, `cap-history-full-after-limit` | The 1000-entry history bound, and the limit checked before it. |
| `cap-overflow-total`, `cap-overflow-evicted`, `cap-overflow-remaining` | Each checked sum. |
| `cap-eviction-stops-at-first-kept` | Eviction stopping at the first entry after the cutoff, on a history out of ledger order. |
| `cap-invalid-limit`, `cap-invalid-period`, `cap-empty-run` | Caps that are not valid to install, and a trace with no calls. |

`cap-random-00.json` to `cap-random-49.json` are the randomized traces.

## Authorization trace format

An authorization trace runs authorizations through the stateful check,
`authorize` in `rule-eval` and `RuleSet.authorize` in the model. Every file is
one JSON object. Object fields appear in the order below; readers should not
depend on it.

```json
{
  "format": 2,
  "name": "authorize-batch-same-rule",
  "description": "...",
  "rules": [Rule, ...],
  "start": [Record, ...],
  "authorizations": [
    {"batch": [Context, ...], "choices": [0, 0], "authenticated": [Signer, ...], "now": 1,
     "generation": "0", "expected": Outcome},
    ...
  ]
}
```

| Field | Meaning |
| --- | --- |
| `format` | The version of this format, `2`. It is versioned apart from the rule vectors and the cap traces. |
| `name` | The file name without `.json`. |
| `description` | What the trace exercises, for a reader; carries no data. |
| `rules` | The rule set, in the rule vector format, caps included. |
| `start` | The records the first authorization starts from, one per rule: `start[j]` is rule `j`'s. A few traces start from a list of another length, to exercise `records_mismatch`. |
| `authorizations` | The authorizations, in order. Each starts from the records the authorizations before it left: the records after an accepted one, the same records after a refused one. |
| `authorizations[i].batch` | The contexts of one authorization tree, in order. |
| `authorizations[i].choices` | The rule chosen for each context: `choices[k]` is the index of the rule for `batch[k]`, a `u32`. |
| `authorizations[i].authenticated` | The signers the authorization authenticated, one list for every context. |
| `authorizations[i].now` | The current ledger, a `u32`. |
| `authorizations[i].generation` | The account's current generation, a decimal `u64` string. |
| `authorizations[i].expected` | The outcome of the authorization. |

Records are in the cap trace format.

### The check

In order:

1. `choices` must hold exactly one index per context (`choices_mismatch`), and
   the records exactly one record per rule (`records_mismatch`).
2. In context order, the rule `choices[k]` must exist (`no_such_rule`), its
   `valid_until`, when it has one, must not be below `now` (`expired`), its
   `generation`, when it has one, must equal the authorization's
   (`stale_generation`), and it must allow `batch[k]` under `authenticated`
   (`not_allowed`), as in the rule vectors.
3. Every signer in `authenticated` must equal a signer of some rule that
   `choices` names (`unauthorized_signer`).
4. In context order, for each context whose chosen rule has a cap, the
   context's argument at the cap's `amount_arg` must be an `i128` (`no_amount`)
   and is charged to that rule's record with the cap check at ledger `now`,
   from the record the charges before it left. A refusal of the cap check is
   `cap_` followed by its cap trace name.

A rule without a cap reads no amount and keeps its record. A refused
authorization leaves every record as it was, the charges of its earlier
contexts included.

### Outcomes

```json
{"ok": [Record, ...]}
{"error": "cap_limit_exceeded"}
```

`ok` holds the records after the authorization, one per rule, each compared
entry by entry and total for total. `error` names the refusal:
`choices_mismatch`, `records_mismatch`, `no_such_rule`, `expired`,
`stale_generation`, `not_allowed`, `unauthorized_signer`, `no_amount`, `cap_negative_amount`, `cap_ledger_before_newest`, `cap_overflow`,
`cap_limit_exceeded` or `cap_history_full`.

### The named traces

| Trace | What it exercises |
| --- | --- |
| `authorize-batch-same-rule` | Two contexts choosing one capped rule accumulate; the window then evicts both. |
| `authorize-choices-mismatch`, `authorize-records-mismatch` | Choice and record lists of the wrong length, and which is checked first. |
| `authorize-no-such-rule`, `authorize-not-allowed` | Chosen indices out of range; chosen rules that do not allow their context though another rule would. |
| `authorize-missing-amount` | A missing or wrong-typed amount, an uncapped rule reading none, and a cap on another argument. |
| `authorize-window-rolls`, `authorize-ledger-zero` | Charges across ledgers and eviction, and the cutoff saturating at ledger 0. |
| `authorize-refusal-discards-batch`, `authorize-choices-before-charges` | A refusal discarding its batch's earlier charges, and choices checked before any charge. |
| `authorize-cap-refusals`, `authorize-cap-overflow`, `authorize-history-full` | Each refusal of the cap check, passed on. |
| `authorize-own-records`, `authorize-empty-batch` | Rules keeping their own records, uncapped rules keeping theirs, and the empty batch. |
| `authorize-expired`, `authorize-stale-generation` | A rule at and after its last ledger, `u32::MAX` included; a rule in its generation and in others, `u64::MAX` included; rules without either. |
| `authorize-unauthorized-signer` | A further signer refused though the threshold is met, a signer of another chosen rule accepted, an external signer holding a delegated signer's bytes, and the empty batch with and without a signer. |
| `authorize-refusal-order` | The order of `no_such_rule`, `expired`, `stale_generation`, `not_allowed`, `unauthorized_signer` and a cap refusal. |
| `authorize-step-base`, `authorize-step-add-cap`, `authorize-step-lower-cap-limit`, `authorize-step-lengthen-cap-period`, `authorize-step-lower-valid-until`, `authorize-step-restrict-functions`, `authorize-step-drop-rule` | One run on a rule set and on the rule sets each cap step, `lower_valid_until`, `restrict_functions` and `drop_rule` derive from it, the drop with its choices renumbered. |

`authorize-random-00.json` to `authorize-random-49.json` are the randomized
traces.

## Budget trace format

A budget trace runs spends, delegations and refills through the budget
operations, `spend`, `delegate` and `refill` in `rule-eval` and `Op.apply` in
the model. Every file is one JSON object. Object fields appear in the order
below; readers should not depend on it.

```json
{
  "format": 1,
  "name": "budget-oversubscribed-siblings",
  "description": "...",
  "start": [Node, ...],
  "valid": true,
  "ops": [
    {"op": "spend", "node": 1, "amount": "8", "expected": Outcome},
    {"op": "delegate", "parent": 1, "allowance": "20", "expected": Outcome},
    {"op": "refill", "node": 0, "amount": "5", "expected": Outcome},
    ...
  ]
}
```

| Field | Meaning |
| --- | --- |
| `format` | The version of this format, `1`. It is versioned apart from the rule vectors and the other traces. |
| `name` | The file name without `.json`. |
| `description` | What the trace exercises, for a reader; carries no data. |
| `start` | The tree the first operation starts from, its nodes in index order. |
| `valid` | Whether `start` is well formed: every parent index below its node's index, and no allowance or spent amount negative. The operations run on it either way. |
| `ops` | The operations, in order. Each starts from the tree the operations before it left: the tree after an accepted one, the same tree after a refused one. |
| `ops[i].op` | `spend`, `delegate` or `refill`. |
| `ops[i].node` | For a spend or a refill, the node's index, a `u32`. |
| `ops[i].parent` | For a delegation, the parent's index, a `u32`. |
| `ops[i].amount` | For a spend, the amount spent; for a refill, the amount the allowance is raised by. An `i128`. |
| `ops[i].allowance` | For a delegation, the new child's allowance, an `i128`. |
| `ops[i].expected` | The outcome of the operation. |

A node is `{"parent": p, "allowance": "...", "spent": "..."}`, with `parent` a
`u32` index or `null` for a root, and allowances and spent amounts as decimal
`i128` strings.

### The operations

Each refuses a tree that is not well formed (`malformed`) first. Then:

- **spend** refuses a node out of range (`no_such_node`) and a negative amount (`negative_amount`), then walks from the node to its root. A node can take the amount when its spent amount plus the amount fits in an `i128` and is at most its allowance. The first node on the walk that cannot is named in `overdrawn`; otherwise the amount is added to the spent amount of every node on the walk.
- **delegate** refuses a parent out of range (`no_such_node`), a negative allowance (`negative_amount`) and a tree of `u32::MAX` nodes (`tree_full`), and otherwise appends `{"parent": parent, "allowance": allowance, "spent": "0"}`.
- **refill** refuses a node out of range (`no_such_node`), a negative amount (`negative_amount`) and a raised allowance that does not fit in an `i128` (`overflow`), and otherwise raises the node's allowance by the amount.

### Outcomes

```json
{"ok": [Node, ...]}
{"error": "malformed"}
{"error": {"no_such_node": 3}}
{"error": {"overdrawn": 0}}
```

`ok` holds the tree after the operation, compared node by node. `error` names
the refusal: `malformed`, `negative_amount`, `overflow` and `tree_full` as
strings, and `no_such_node` and `overdrawn` as an object holding the index.

### The named traces

| Trace | What it exercises |
| --- | --- |
| `budget-oversubscribed-siblings` | Children whose allowances sum to more than their parent's, sharing it. |
| `budget-middle-exhausted`, `budget-chain-to-root` | A spend exhausting a middle ancestor, and a deep spend charging the whole chain and nothing else. |
| `budget-nearest-overdrawn` | Several overdrawn nodes on a chain, the one nearest the spender named. |
| `budget-overflow` | Spends and refills whose sums do not fit in an `i128`. |
| `budget-malformed-parent-self`, `budget-malformed-parent-later`, `budget-malformed-negative-allowance`, `budget-malformed-negative-spent` | Malformed trees, on which every operation refuses. |
| `budget-delegate-then-spend`, `budget-delegate-refusals` | Delegation, above the parent's allowance included, then spends at the new nodes; delegation's refusals. |
| `budget-refill`, `budget-start-overspent` | Refills unblocking a spend, their refusals, and a tree starting with a node spent above its allowance. |
| `budget-negative-amount`, `budget-no-such-node`, `budget-empty-tree`, `budget-zero-spend`, `budget-several-roots`, `budget-empty-run` | The other refusals and edges. |

`budget-random-00.json` to `budget-random-49.json` are the randomized traces.

## Document trace format

A document trace lowers one document and runs authorizations through the rules
it lowers to. The verdicts are the document's own (`Doc.authorize`), written
from Perch's specification, not the lowering's: an implementation that lowers
the document and checks the authorizations with its own evaluator, Perch's
`compile_doc`, `apply_doc` and `check_auth` among them, should reach the same
ones. Every file is one JSON object; object fields appear in the order below.

```json
{
  "format": 1,
  "name": "document-capped-approve",
  "description": "...",
  "document": Document,
  "account": "6163636f756e74",
  "scoped": null,
  "lowered": {"ok": [Rule, ...]},
  "authorizations": [
    {"batch": [Context, ...], "choices": [1], "authenticated": [Signer, ...], "now": 500,
     "generation": "0", "expected": Verdict},
    ...
  ]
}
```

| Field | Meaning |
| --- | --- |
| `format` | The version of this format, `1`. |
| `name`, `description` | As in the other traces. |
| `document` | The document. |
| `account` | The account's address, as its `ScAddress` XDR in hex. |
| `scoped` | `null` for an admin document. For a scoped document, `{"admin": Document, "generation": "3"}`: the admin document it is issued under and the generation it is issued in, a decimal `u64`. |
| `lowered` | `{"ok": [Rule, ...]}`, the rules the document lowers to in the rule vector format, or `{"error": "recovery_configured"}` or `{"error": "excluded_scope"}`, the scoped lowering's refusal; a refused document has no authorizations. |
| `authorizations` | As in the authorization traces, each starting from the records the authorizations before it left, the first from one empty record per lowered rule. Choice `j` names lowered rule `j`: the document's rule `j`, or, past them, the recovery rule. No authorization chooses the recovery rule. |

### Documents

```json
{
  "signers": [{"id": "6369", "signer": Signer}, ...],
  "rules": [
    {"scope": {"contract": "746f6b656e"}, "principals": {"all": ["6369"]},
     "functions": ["7472616e73666572"], "args": [{"index": 0, "pred": "is_self"}],
     "not_after_ledger": 600, "cap": {"limit": "10", "period_ledgers": 1000}},
    ...
  ],
  "recovery": {"controller": "...", "zk": {"adapter": "...", "pool": "..."}}
}
```

Ids, function names, string values, prefixes and addresses are hex. A
`scope` is `{"contract": hex}` or `"self_admin"`; `principals` is
`{"all": [id, ...]}` or `{"threshold": {"ids": [id, ...], "m": 1}}`; a `pred` is
`"is_self"`, `{"address_eq": hex}`, `{"string_in": [hex, ...]}`,
`{"string_prefix": hex}` or `{"u32_eq": 7}`. `functions`, `args`,
`not_after_ledger`, `cap`, `recovery` and `zk` are `null` when absent. A
`limit` is a decimal `i128`. A shell decodes a Perch document to this form:
strkeys to `ScAddress` XDR, hex keys to bytes, decimal limits to `i128`.

A `u32` argument a `u32_eq` predicate reads is `{"other": hex}` of its
`ScVal` XDR: the discriminant `00000003` and the value, four big-endian bytes.

### Verdicts

```json
{"ok": [Record, ...]}
"refused"
```

`ok` holds the records after the authorization, one per lowered rule. A
refusal names no reason: the document's meaning, like Perch's account, only
accepts or refuses, and the records stay as they were.

### The named traces

| Trace | What it exercises |
| --- | --- |
| `document-capped-approve`, `document-capped-no-functions` | A capped rule listing `approve`, and one listing no functions, authorize only `transfer` with an `i128` at argument 2; the cap reaches its limit. |
| `document-extra-signer` | A signer of no chosen rule refused; a missing signer refused. |
| `document-not-after-ledger` | `not-after-ledger 600` authorizes at 599 and not at 600 or 601. |
| `document-string-in-long`, `document-string-prefix` | A `string-in` value over 256 bytes never matches; `string-prefix` reads strings and not symbols. |
| `document-constraint-free` | A rule with no function list authorizes every function of its contract; the admin rule authorizes any call to the account. |
| `document-predicates`, `document-thresholds` | `is-self`, `address-eq` and `u32-eq`; `all` and `threshold` principals. |
| `document-with-recovery` | A document configuring recovery: the recovery rule lowered last, one record per installed rule. |
| `document-scoped-issued` | A scoped document in its generation and after it moves on. |
| `document-scoped-self-admin`, `document-scoped-account`, `document-scoped-controller`, `document-scoped-adapter`, `document-scoped-pool`, `document-scoped-recovery` | Each refusal of the scoped lowering. |

`document-random-00.json` to `document-random-39.json` are the randomized
traces.

## Soroban vector formats

Values, contexts and the rest share one encoding:

- an address is `{"account": key}`, `{"contract": id}` or `{"muxed_account": {"id": "<decimal u64>", "key": key}}`, keys and ids 32 bytes of lowercase hex;
- a value is `{"void": null}`, `{"bool": b}`, `{"u32": n}`, `{"u64": "<decimal>"}`, `{"i128": "<decimal>"}`, `{"bytes": hex}`, `{"string": hex}`, `{"symbol": hex}`, `{"address": address}`, `{"vec": [value, ...]}`, `{"map": [[key, value], ...]}` with keys in the host's order, or `{"other": hex}`, the full `ScVal` XDR of a value of another kind;
- a durability is `"persistent"`, `"temporary"` or `"instance"`;
- a context is `{"contract": {"contract": address, "fn_name": hex, "args": [value, ...]}}` or `{"create_contract": {"executable": Executable, "salt": hex, "constructor_args": [value, ...]}}`, where an executable is `{"wasm": hex}` (the Wasm hash) or `{"external_ref": {"owner": address, "tag": hex}}` (CAP-85; the tag's string as hex). `rule-eval` reads a creation as `{"create": {"wasm_hash": hex}}` of the Wasm hash, or of the external reference's `ScVal` XDR.

### Value and context vectors

```json
{"format": 1, "name": "values-scalars", "description": "...",
 "values": [{"value": Value, "xdr": "<hex>", "rule_eval": Val, "storable": true}, ...]}

{"format": 1, "name": "contexts-one-call", "description": "...",
 "value": Value, "xdr": "<hex>",
 "expected": {"contexts": [Context, ...], "rule_eval": [Context, ...]} | null}
```

`rule_eval` is a value or context in the encoding of `rule-eval`'s types
above. A context vector's `expected` is `null` when one of the value's
contexts cannot be read.

### Storage traces

```json
{"format": 1, "name": "storage-set-get-remove", "description": "...", "contract": Address,
 "ops": [{"op": "set", "durability": "persistent", "key": Value, "val": Value, "expected": "done"},
         {"op": "get", "durability": "persistent", "key": Value, "expected": {"value": Value | null}},
         {"op": "has", "durability": "temporary", "key": Value, "expected": {"present": true}},
         {"op": "remove", "durability": "instance", "key": Value, "expected": "refused"}, ...]}
```

`refused` marks a key holding a muxed address; it changes nothing.

### Host traces

```json
{"format": 1, "name": "host-exact-tree", "description": "...",
 "contracts": [Address, ...],
 "accounts": [{"address": Address, "check_auth": [AccountStep, ...]}, ...],
 "txs": [{"ledger": 100, "entries": [Entry, ...], "call": Call,
          "expected": {"ok": true, "events": [Event, ...],
                       "store": [{"contract": Address, "durability": "persistent", "key": Value,
                                  "value": Value | null}, ...]}}, ...]}
```

- `contracts` lists every contract the trace calls, signs as or delegates to; an account without an entry in `accounts` accepts every `__check_auth`.
- A call is `{"contract": Address, "fn_name": hex, "args": [Value, ...], "body": [Step, ...]}`. A step is `{"get": {"durability", "key"}}`, `{"has": ...}`, `{"put": {"durability", "key", "val"}}`, `{"remove": ...}`, `{"require_auth": Address}`, `{"call": {"callee": Call, "catches": bool}}` or `{"fail": "error" | "trap"}`.
- An account step is `get`, `put` or `remove` as above, `{"check_rules": {"rules": [Rule, ...], "authenticated": [Signer, ...]}}` (fail unless `rule-eval`'s `allows_all` accepts the contexts read with the facade), `{"delegate": Address}` or `{"fail": kind}`.
- An entry is `{"address": Address, "nonce": "<decimal i64>", "expiration": n, "signature": Value, "credentials": "address" | "address_v2" | {"with_delegates": [Delegate, ...]}, "root": Invocation}`, a delegate `{"address": Address, "signature": Value, "nested": [Delegate, ...]}` and an invocation `{"context": Context, "subs": [Invocation, ...]}`.
- An event is `{"check_auth": {"account", "preimage": {"address": Address | null, "nonce", "expiration", "invocation"}, "signature", "contexts": [Context, ...], "contexts_value": Value, "rule_eval_contexts": [Context, ...]}}`, `{"read": {"contract", "durability", "key", "value"}}`, `{"found": {"contract", "durability", "key", "present"}}` or `{"authorized": {"address", "context", "via": "invoker" | "entry"}}`. The harness compares `via` with nothing: the host does not report it.
- `store` lists every slot the trace touches, with its value after the transaction, `null` when absent.

Two calls of one transaction with the same context may have different
bodies: the harness hands each callee its body as it calls it. Every transaction runs
between ledgers 100 and 115 and every signature is valid for at most 1000
ledgers past it, so temporary entries and used nonces stay live.

### The named traces

- Matching: `host-exact-tree`, `host-arguments-mismatch`, `host-nonce-replay`, `host-expired-signature`, `host-signature-valid-in-its-last-ledger`, `host-check-auth-refuses`, `host-nested-tree`, `host-nested-call-missing`, `host-disjoint-entries`, `host-root-below-top-call`, `host-unused-signed-node`, `host-require-auth-twice-in-one-frame`, `host-two-signers`, `host-invoker`, `host-account-deeper-on-stack`.
- `__check_auth`'s input: `host-address-bound-payload`, `host-delegation`, `host-nested-delegation`, `host-delegate-twice`, `host-delegate-not-listed`, `host-delegate-refuses`, `host-unused-delegate`.
- Storage and rollback: `host-reentrant-instance`, `host-check-auth-writes-instance`, `host-rollback-error-and-trap`, `host-rollback-caught`, `host-rollback-uncaught`, `host-rollback-unconsumes-nonce`, `host-rollback-rematches-node`, `host-reentrant-call`, `host-muxed-key`, `host-storage-in-calls`.
- `rule-eval` in `__check_auth`: `host-check-rules-allows`, `host-check-rules-refuses-unused-node`, `host-check-rules-arguments`.

The randomized traces draw call trees of depth up to three over three
contracts and two accounts, with `require_auth`s, storage operations, caught
and uncaught calls and failures; entries are the tree of each account's
`require_auth`s, often changed (an argument, a dropped or an extra node, an
expired signature, a reused nonce), with each kind of credentials; account
programs read and write storage, check rules, delegate or refuse.

### Seed traces

`soroban/seed/host/*.json` and `soroban/seed/storage/*.json` are host traces
and storage traces in the formats above, transcribed from soroban-env-host
29.0.1's `src/test/auth.rs`, `auth_delegation.rs` and `storage.rs`. Each
trace's description names its host test and the line of each case. A trace
from `auth.rs` holds one transaction per case of one test; a trace from
`auth_delegation.rs` holds one case, since each case gives its accounts
their own programs. The host tests' Stellar-account signers are contract
accounts whose `__check_auth` accepts.

`soroban/seed/coverage.json`:

```json
{"format": 1, "host": "soroban-env-host 29.0.1", "files": ["src/test/auth.rs", ...],
 "totals": {"tests": 74, "tests_expressed": 27, "tests_outside": 47,
            "cases_in_expressed_tests": 213, "cases_expressed": 155,
            "cases_agree": 155, "cases_disagree": 0, "cases_left": 58},
 "tests": [{"file": "auth.rs", "test": "test_single_authorized_call", "expressed": true,
            "cases": 9, "expressed_cases": 6, "agree": 6, "disagree": 0,
            "vectors": ["seed-auth-single-authorized-call"],
            "left": [{"cases": 2, "reason": "..."}, ...]},
           {"file": "invoker_auth.rs", "test": "test_self_invoker_auth", "expressed": false,
            "reason": "..."}, ...]}
```

A case is a call whose outcome the host test asserts. `agree` counts the
cases where the model gives the host test's outcome (and, where the test
counts consumed nonces, the same count); the generator refuses to write
anything when `disagree` would not be 0.
