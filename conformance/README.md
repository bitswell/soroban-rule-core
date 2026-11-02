# conformance

Test vectors for rule-set evaluation and attenuation, and traces of the
spending-cap check, computed by the Lean model in `formal/`, and a runner that
checks `rule-eval` against them. Any other implementation of the same rules
(Perch's smart account, the grant signer) can run the same vectors as a
differential test.

| Path | Contents |
| --- | --- |
| `vectors/*.json` | One vector per file: a rule set, a batch of contexts, the authenticated signers, attenuation step lists, and the results the Lean model computes for them. |
| `vectors/caps/*.json` | One cap trace per file: a cap, a starting record, and calls, each with the outcome the Lean model computes for it. |
| `generator/` | The Lake package that writes the vectors and traces: the case specifications and the JSON encoding. |
| `runner/` | The Rust crate `rule-eval-conformance`, which loads every vector and trace and checks `rule-eval` against it. |

## How the vectors are made

`generator/` is a Lake package that requires the `rule-core` package in
`../../formal`. Its cases (`Conformance/Cases.lean` and
`Conformance/Random.lean`) specify inputs only. `lake exe gen-vectors` computes
every expected result with the chain vocabulary's own functions,
`RuleCore.Chain.RuleSet.allows`, `RuleSet.allowsAll` and
`RuleSet.attenuateAll`, the functions the theorems in `formal/` are about, and
writes each case to `<name>.json`. The cap traces (`Conformance/Caps.lean`) are
computed with `RuleCore.Cap.Params.check` and written to `caps/<name>.json`. No
expected result is written by hand.

```sh
cd conformance/generator
lake exe gen-vectors ../vectors
```

`gen-vectors <dir>` removes the `.json` files in `<dir>` and `<dir>/caps` and
writes every named case plus 100 randomized cases of seed 20261102, and every
named cap trace plus 50 randomized traces of the same seed. `--seed <n>`,
`--count <n>` and `--cap-count <n>` choose another randomized set, for a larger
run outside the committed vectors:

```sh
lake exe gen-vectors /tmp/vectors --seed 7 --count 5000 --cap-count 5000
CONFORMANCE_VECTORS=/tmp/vectors cargo test -p rule-eval-conformance
```

The randomized cases use SplitMix64, written out in `Conformance/Random.lean`,
so a seed produces the same vectors on every Lean release. Case `k` of a seed
is drawn from its own stream. Rule sets, contexts, signers and steps come from
small universes of contract ids, function names, payloads, integers and
signers that include each other's prefixes and extensions, the `i128`, `u64`
and `u32` extremes, and delegated and external signers with equal bytes; calls
are mostly built from a rule of the set with arguments that usually satisfy its
conditions, and the authenticated signers usually include some of the rules'
signers, so allowed and refused contexts both occur. The randomized cap traces
draw caps, starting ledgers, amounts and ledger steps from small universes that
include the `u32` and `i128` extremes; ledgers mostly advance by less than a
period and sometimes repeat or go back, so every refusal occurs.

## Running them against rule-eval

```sh
cargo test -p rule-eval-conformance
```

The runner is a workspace member, so `cargo test --workspace` in
`.github/workflows/rust.yml` runs it on the pinned nightly and on stable. Its
tests check that `rule-eval` reproduces every result of every vector, that the
vectors still cover every value constructor, condition, signer kind, threshold
case, step kind and outcome, and that a vector with a changed expectation is
reported. Its cap tests (`tests/caps.rs`) check that `check_spend` reproduces
every outcome and record of every trace, that the traces still cover every
refusal, ledger 0, `u32::MAX` and invalid caps, and that a changed expectation
is reported. `rule-eval` itself
keeps no dependencies; the runner depends on it, `serde` and `serde_json`.

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
  "format": 2,
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
| `format` | The version of this format, `2`. A change a reader of the current version cannot read raises it. |
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
* An **index** (argument index or rule index) or a **threshold** is a JSON
  number from `0` to `4294967295`, a `u32`.

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
| `{"other": "..."}` | An argument of any other type, as its full `ScVal` XDR. |

Values of different constructors are never equal, even when their payloads
are: `{"bytes": "6162"}` is not `{"other": "6162"}`.

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
```

* `arg_eq` holds when argument `index` exists and equals `value`: the same
  constructor and the same payload.
* `arg_i128_at_most` holds when argument `index` exists, is an `i128`, and is at
  most `bound`, compared as signed integers.

A missing argument, including any index at or past the number of arguments,
makes either condition false, as does an argument of another constructor.

### Rules

```json
{"contract": "746f6b656e", "functions": ["7472616e73666572", ...], "conds": [Condition, ...],
 "signers": [Signer, ...], "threshold": 2}
```

A rule allows a call when the call's contract equals `contract`, its function
equals one of `functions`, every condition in `conds` holds on its arguments,
and at least `threshold` distinct signers of `signers` are in the vector's
`authenticated` list. Each signer counts once: a signer listed twice in
`signers`, or authenticated twice, counts as one. A rule with an empty
`functions` list allows nothing; one with an empty `conds` list puts no
constraint on arguments; one with threshold `0` puts none on signers; one whose
threshold is above its number of distinct signers allows nothing. A rule set allows a context
when some rule allows it, and allows a batch when it allows every context in
it, so every rule set allows the empty batch. A batch collected from a Soroban
authorization tree always holds the root context; a caller that builds batches
another way must refuse an empty one itself.

### Attenuation steps

```json
{"drop_rule": {"index": 1}}
{"add_cond": {"index": 0, "cond": Condition}}
{"remove_functions": {"index": 0, "functions": ["617070726f7665", ...]}}
{"remove_signers": {"index": 0, "signers": [Signer, ...]}}
{"raise_threshold": {"index": 0, "threshold": 3}}
```

* `drop_rule` removes rule `index`, keeping the others in order.
* `add_cond` appends `cond` to the conditions of rule `index`.
* `remove_functions` removes every occurrence of every listed name from the
  function list of rule `index`, keeping the remaining names in order. Names
  not in the list are ignored.
* `remove_signers` removes every occurrence of every listed signer from the
  signers of rule `index`, keeping the remaining signers in order and the
  threshold as it was. Signers not in the list are ignored.
* `raise_threshold` sets the threshold of rule `index` to `threshold`. It is
  refused with `threshold_lowered` when `threshold` is below the rule's
  current threshold.

A step whose `index` is not below the number of rules is refused with
`no_such_rule`, before any other check. A step list is applied in order, each
step to the previous step's result, and stops at the first refused step.

### Outcomes

```json
{"ok": {"rules": [Rule, ...], "allows": [true, ...], "allows_all": false}}
{"error": "no_such_rule"}
{"error": "threshold_lowered"}
```

`ok` holds the rule set after every step, compared rule by rule, field by field
and in order, and its verdicts on the vector's `batch` under its
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
