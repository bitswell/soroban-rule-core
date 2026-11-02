# conformance

Test vectors for rule-set evaluation and attenuation, computed by the Lean
model in `formal/`, and a runner that checks `rule-eval` against them. Any
other implementation of the same rules (Perch's smart account, the grant
signer) can run the same vectors as a differential test.

| Path | Contents |
| --- | --- |
| `vectors/*.json` | One vector per file: a rule set, a batch of contexts, attenuation step lists, and the results the Lean model computes for them. |
| `generator/` | The Lake package that writes the vectors: the case specifications and the JSON encoding. |
| `runner/` | The Rust crate `rule-eval-conformance`, which loads every vector and checks `rule-eval` against it. |

## How the vectors are made

`generator/` is a Lake package that requires the `rule-core` package in
`../../formal`. Its cases (`Conformance/Cases.lean` and
`Conformance/Random.lean`) specify inputs only. `lake exe gen-vectors` computes
every expected result with the chain vocabulary's own functions,
`RuleCore.Chain.RuleSet.allows`, `RuleSet.allowsAll` and
`RuleSet.attenuateAll`, the functions the theorems in `formal/` are about, and
writes each case to `<name>.json`. No expected result is written by hand.

```sh
cd conformance/generator
lake exe gen-vectors ../vectors
```

`gen-vectors <dir>` removes the `.json` files in `<dir>` and writes every named
case plus 100 randomized cases of seed 20261102. `--seed <n>` and `--count <n>`
choose another randomized set, for a larger run outside the committed vectors:

```sh
lake exe gen-vectors /tmp/vectors --seed 7 --count 5000
CONFORMANCE_VECTORS=/tmp/vectors cargo test -p rule-eval-conformance
```

The randomized cases use SplitMix64, written out in `Conformance/Random.lean`,
so a seed produces the same vectors on every Lean release. Case `k` of a seed
is drawn from its own stream. Rule sets, contexts and steps come from small
universes of contract ids, function names, payloads and integers that include
each other's prefixes and extensions and the `i128`, `u64` and `u32` extremes;
calls are mostly built from a rule of the set with arguments that usually
satisfy its conditions, so allowed and refused contexts both occur.

## Running them against rule-eval

```sh
cargo test -p rule-eval-conformance
```

The runner is a workspace member, so `cargo test --workspace` in
`.github/workflows/rust.yml` runs it on the pinned nightly and on stable. Its
tests check that `rule-eval` reproduces every result of every vector, that the
vectors still cover every value constructor, condition, step kind and outcome,
and that a vector with a changed expectation is reported. `rule-eval` itself
keeps no dependencies; the runner depends on it, `serde` and `serde_json`.

`.github/workflows/conformance.yml` rebuilds the generator, regenerates the
vectors into an empty directory and fails if they differ from
`conformance/vectors`, including a committed file the generator no longer
writes. It also checks that `generator/lean-toolchain` matches
`formal/lean-toolchain` and rejects the same unchecked Lean declarations as
`lean.yml`.

## Vector format

Every file is one JSON object. Object fields appear in the order below;
readers should not depend on it.

```json
{
  "format": 1,
  "name": "batch-mixed",
  "description": "A batch of allowed and refused calls is refused as a whole.",
  "rules": [Rule, ...],
  "batch": [Context, ...],
  "expected": {"allows": [true, false, ...], "allows_all": false},
  "attenuations": [
    {"steps": [Step, ...], "expected": Outcome},
    ...
  ]
}
```

| Field | Meaning |
| --- | --- |
| `format` | The version of this format, `1`. A change a reader of version 1 cannot read raises it. |
| `name` | The file name without `.json`. |
| `description` | What the vector exercises, for a reader; carries no data. |
| `rules` | The rule set, in order. |
| `batch` | The contexts of one authorization tree, in order. |
| `expected.allows` | The rule set's verdict on each context of `batch`, in the same order. |
| `expected.allows_all` | The rule set's verdict on the whole batch. |
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
* An **index** (argument index or rule index) is a JSON number from `0` to
  `4294967295`, a `u32`.

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
{"contract": "746f6b656e", "functions": ["7472616e73666572", ...], "conds": [Condition, ...]}
```

A rule allows a call when the call's contract equals `contract`, its function
equals one of `functions`, and every condition in `conds` holds on its
arguments. A rule with an empty `functions` list allows nothing; one with an
empty `conds` list puts no constraint on arguments. A rule set allows a context
when some rule allows it, and allows a batch when it allows every context in
it, so every rule set allows the empty batch. A batch collected from a Soroban
authorization tree always holds the root context; a caller that builds batches
another way must refuse an empty one itself.

### Attenuation steps

```json
{"drop_rule": {"index": 1}}
{"add_cond": {"index": 0, "cond": Condition}}
{"remove_functions": {"index": 0, "functions": ["617070726f7665", ...]}}
```

* `drop_rule` removes rule `index`, keeping the others in order.
* `add_cond` appends `cond` to the conditions of rule `index`.
* `remove_functions` removes every occurrence of every listed name from the
  function list of rule `index`, keeping the remaining names in order. Names
  not in the list are ignored.

A step whose `index` is not below the number of rules is refused with
`no_such_rule`. A step list is applied in order, each step to the previous
step's result, and stops at the first refused step.

### Outcomes

```json
{"ok": {"rules": [Rule, ...], "allows": [true, ...], "allows_all": false}}
{"error": "no_such_rule"}
```

`ok` holds the rule set after every step, compared rule by rule, field by field
and in order, and its verdicts on the vector's `batch`, as in `expected`.
`error` says a step was refused; `no_such_rule` is the only error.

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

`random-000.json` to `random-099.json` are the randomized cases.
