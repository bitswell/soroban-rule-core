# Architecture

## What the repository proves

The goal is one containment chain. Anything an agent authorizes sits inside
its grant. The grant sits inside its scope, and the scope inside the owner's
authority. A completed recovery leaves nothing below the admin document able
to authorize anything.

Authority comes in three nested layers, and all three are made of the same
rule sets:

| Layer | What it is | Who holds it |
| --- | --- | --- |
| Admin document | The owner's authority and recovery: Perch's applied document. | The owner. |
| Scoped documents | Grants the owner issues, one per agent or app: Perch's `apply_scope`. | An agent or an app. |
| Delegated grants | What a holder narrows and passes on under a scope, with budgets on the delegation tree: the grant signer. | Whoever the holder delegates to. |

Each link of the chain is a theorem about rule sets, or about the code that
builds, stores and checks them:

- **Grant inside scope.** A delegated grant is reached from its scope by attenuation steps, so it allows only what the scope allows. Milestone 1 proves this for rule matching (`Derives.narrower`, `Derives.allows_all`). Budgets on the delegation tree come in M3.
- **Scope inside the owner's authority.** A scoped document compiles to rules that reach none of the account, its recovery or the ZK adapter. That is M4.
- **Recovery.** A completed recovery bumps a generation, and every scoped rule issued under an older generation then authorizes nothing. That is also M4.
- **The code is the model.** The Rust that Perch's smart account, the grant signer, the agent host and the relay run is proven equal to the Lean model the theorems are about (M1 for rule matching and attenuation). Soroban's own behaviour enters through Lean models that are tested against the host (M5).

## Dependency direction

```
contract shells (Perch's account, the grant signer)
  ├── rule-eval            pure evaluator, no dependencies
  └── soroban-facade (M5)  SDK subset, wraps soroban-sdk
```

- `crates/rule-eval` depends on nothing: no crates, and no `std` (it uses only `core` and `alloc`).
- `soroban-facade` never appears in `rule-eval`, and `rule-eval` never sees a Soroban type. A shell converts the host's values into `rule-eval`'s plain data (`Val`, `Context`) and calls the evaluator.
- Only contract shells use the facade.
- Each crate is a directory with its own `Cargo.toml` that names its dependencies by path or by version and inherits only `[workspace.package]` metadata. Moving a crate to another repository is a directory move. The `release` and `contract` profiles, with `overflow-checks = true`, are set in the workspace root, so a workspace that takes the crate in sets them the same way.

## Milestone 1: rule matching and attenuation

### The model

`formal/RuleCore/Model/RuleSet.lean` is the readable model, generic in the
context type:

- a `Rule` has a `scope : Ctx → Bool` and a list of conditions `Ctx → Bool`;
- `Rule.allows` is the scope and every condition;
- `RuleSet.allows` holds when some rule allows the context;
- `RuleSet.allowsAll` holds when every context is allowed;
- `narrower rs' rs` says every context `rs'` allows, `rs` allows.

`Model/Attenuation.lean` defines the three steps and nothing else: drop a
rule, add a condition to a rule, and restrict a rule's scope. Each names its
rule by position and fails with `noSuchRule` out of range.

`formal/RuleCore/Vocab/Chain.lean` is the concrete vocabulary:

- a context is a call (contract, function, arguments) or a contract creation;
- a rule names one contract, a list of functions and conditions on that call's arguments;
- `argEq index v` holds when argument `index` exists and equals `v`;
- `argI128AtMost index n` holds when argument `index` exists, is an `i128`, and is at most `n`;
- values are `i128`, `u64`, `bool`, `bytes`, `address`, `symbol` and `other`, which carries the full XDR;
- identifiers are byte strings compared exactly, and values of different constructors are never equal.

Each chain rule denotes a generic rule. Removing functions denotes restricting
the scope to calls of the remaining ones. Every chain scope is false on a
creation.

### The evaluator

`crates/rule-eval` implements the chain vocabulary:

- `allows(rules, context)` and `allows_all(rules, contexts)` evaluate a rule set;
- `drop_rule`, `add_cond` and `remove_functions` are the attenuation steps. Each reads a slice of rules and returns a new `Vec<Rule>` or `AttenuationError::NoSuchRule`.

The code is written in a subset of Rust that Charon and Aeneas translate to
total Lean functions:

- plain structs and enums, with no traits, closures, iterator adaptors or derived impls;
- enums compare by explicit `match`, and byte strings through one loop;
- each loop is one `while i < s.len()` over one slice, with an early return;
- slices are indexed only under `i < s.len()`, and indices taken from rules go through `get`;
- arithmetic is checked, and `overflow-checks = true` holds in the `release` and `contract` profiles;
- no binding is named after a module.

### Extraction and equivalence

`tools/extract.sh` runs Charon and Aeneas at the commits `flake.nix` pins and
writes `formal/RuleCore/Extracted/RuleEval.lean`, which is never edited by
hand. `formal/RuleCore/Equiv/` then proves the translation equal to the model:

- `Denote.lean` maps each translated type to the chain vocabulary. The maps are structural and injective, and they are part of the specification.
- `Eval.lean` and `Attenuation.lean` prove that each translated function returns `ok` of the model's result on every input. Termination is part of that statement, because Aeneas's loops are `partial_fixpoint`s.

`formal/RuleCore/Theorems/Extracted.lean` restates the model's theorems on the
translated functions alone, so they can be read without the model.

### Conformance and the claim ledger

`conformance/vectors` holds verdicts the Lean model computed, in a JSON format
documented for other implementations. Perch and the grant signer will run them
as differential tests. `claims.yaml` lists every claim with its status and
evidence, and `tools/check-claims` fails CI when evidence is missing.

### How later milestones extend it

- **New conditions** are new constructors of `Cond`, each matched by `cond_holds`, with its meaning in `Chain.Cond.holds` and its denotation in `Equiv/Denote.lean`. The generic theorems do not change, because a chain condition denotes a generic one.
- **New rule fields** (signers, caps) extend `Rule` and `Chain.Rule`. Keeping `Rule.denote` a generic rule keeps every attenuation theorem.
- **Stateful checks** (spending, budgets) stay pure in `rule-eval`. The function takes the state as data and returns the new state or an error, and the shell does the storage.

## Later milestones

These are design notes for work that is not built. Where the brief leaves a
choice open, it is listed under [Open questions](#open-questions) and not
decided here.

### M2: signers and caps

A rule gains its signers and per-rule spending caps with rolling windows,
matching Perch's `periodLedgers`.

- **Signers.** A rule names the signers that may use it. Evaluation also takes the signers that authorized the call, and the rule's signer requirement on them is one more conjunct in `Rule.allows`. An attenuation step that removes signers, or makes the requirement stricter, narrows by the same argument as removing functions.
- **Caps.** A cap bounds what one rule may spend within a window measured in ledgers. Checking a cap reads the rule's spend record and the current ledger and returns either the new record or a refusal. The function is pure, and the shell loads and stores the record. "Add a cap" or "lower a cap" are attenuation steps, and each must be proven to narrow over every history of spends, not just over one context.
- **Theorems.** The M1 theorems carry over unchanged for rule matching. New theorems state that a capped rule never lets spending within any window exceed its cap, and that each new step narrows. How the window's time enters these proofs is open.

### M3: the budget tree

Allowances sit on the delegation tree.

- **Charging.** A spend charges the spender and every ancestor, or fails and changes nothing. Oversubscription is allowed: the children's allowances may sum to more than the parent's.
- **Theorem.** For every node and every sequence of spends, what is spent under the node stays within its allowance.
- **Shape in the restricted subset.** The tree is a slice of nodes, each holding its parent's index, its allowance and what it has spent. Walking to the root is a loop bounded by the slice length. The charge first checks every ancestor and then builds the new slice, so a failure leaves the input unchanged by construction. The tree lives in `rule-eval`, or in a sibling crate under the same rules, and depends on nothing.

### M4: compile soundness and scopes

Perch lowers an owner's document to installed rules.

- **Soundness.** The installed rules allow exactly what the document says. This includes cross-token caps, which split into paired rules.
- **Scope.** No scoped document reaches the account itself, its recovery or the ZK adapter. Stated as a theorem: no rule a scoped document compiles to allows a call to those contracts or functions.
- **Recovery.** Each scoped rule carries the generation it was issued under. After a recovery bumps the generation, every scoped rule authorizes nothing, so the chain ends at the admin document.

The lowering is a pure function from the document to rule sets. Its proof
relates the document's meaning to `RuleSet.allows` of its output. Whether
Perch's compiled rules (OpenZeppelin context rules plus policies) map onto this
rule model without loss, or need a richer condition set, is open.

### M5: the Soroban facade

`crates/soroban-facade` and `formal/RuleCore/Soroban/` model the part of
Soroban that the contract shells rely on:

- **Plain data and simple interfaces** for a subset of the SDK: `Address`, `Bytes`, `Symbol`, `i128`, `Vec` and `Map` as data; storage get and set; `require_auth`; and authorization contexts. A shell written against the facade can be run in tests against a plain implementation.
- **A real implementation** that wraps `soroban-sdk`. It is the only code that touches the SDK.
- **Lean models**:
  - storage as a finite map;
  - rollback: a failed call leaves storage as it was;
  - `require_auth` matched against the signed authorization tree;
  - what `__check_auth` receives: the signature payload, the signatures and the authorization contexts. These are the contexts `rule-eval` evaluates.
- **Differential tests.** The models are trusted, so each one is tested against `soroban-env-host` at the pinned version: the same operations run through the model and through the host, and their results are compared. The tests would be generated from the models, as the conformance vectors are.

`rule-eval` stays out of this. The facade gives a shell the authorization
contexts, and the shell converts them to `rule-eval`'s `Context`. That
conversion is a denotation of the same kind as `Equiv/Denote.lean`, tested
against the host. How the Lean models keep in step with new `soroban-env-host`
versions is open.

#### Existing Soroban verification tools

Each entry below cites the vendor's own docs or source code, at the commits
linked. None of these tools produces a kernel-checked proof, and each works on
a different object from this repository.

- **Certora Sunbeam** (the Certora Prover for Soroban).
  - *Technique.* It translates a contract's WebAssembly into Certora's intermediate language and discharges verification conditions with SMT solvers. A result is a pass, a counterexample, a timeout or unknown ([Certora: formally verifying WebAssembly](https://www.certora.com/blog/formally-verifying-webassembly)).
  - *Specifications* are Rust functions marked `#[rule]` that use the CVLR macros `cvlr_assert!`, `cvlr_assume!` and `cvlr_satisfy!` ([Sunbeam usage](https://docs.certora.com/en/latest/docs/sunbeam/usage.html)), with Soroban helpers such as `is_auth` ([cvlr-soroban](https://github.com/Certora/cvlr-soroban)).
  - *Host model* ([`wasm/host/soroban`](https://github.com/Certora/CertoraProver/tree/4ef546d00cd67d333914845dead2d72081e1f014/src/main/kotlin/wasm/host/soroban)):
    - contract-data storage is modelled;
    - `require_auth` succeeds only where an uninterpreted per-address authorization predicate holds;
    - `require_auth_for_args` and `authorize_as_curr_contract` are not modelled;
    - cross-contract calls return unconstrained values.
- **Runtime Verification Komet**, a K semantics of Soroban over KWasm.
  - *Technique.* It executes a contract's WebAssembly. `komet test` fuzzes property functions written in Rust, and `komet prove` runs them symbolically over all inputs ([Komet](https://github.com/runtimeverification/komet), [Komet docs](https://docs.runtimeverification.com/komet)).
  - *Host model* ([soroban-semantics](https://github.com/runtimeverification/komet/tree/a078e296621a4f52fd1497fed64435e9948cc830/src/komet/kdist/soroban-semantics)):
    - instance, persistent and temporary storage, with TTLs;
    - cross-contract calls;
    - rollback: the world state is pushed on each call, restored when the call fails, and dropped when it succeeds;
    - `require_auth` is a placeholder that always succeeds (`host/address.md`: "the auth system is out of scope for now").
- **CoinFabrik Scout**, a static analyser of Soroban Rust source built from lint detectors ([scout-audit](https://github.com/CoinFabrik/scout-audit)). It finds known bug patterns and proves nothing.
- **Galois Formal VerSo** proves properties of Soroban contracts at the MIR level with SAW and crux-mir. Its README describes it as early-stage, supporting a small part of the Soroban API at SDK 0.8.4 ([formal-verso](https://github.com/GaloisInc/formal-verso)).
- **soroban-sdk testutils** run contracts against the real `soroban-env-host` in tests. `mock_all_auths` makes every `require_auth` succeed, and `auths()` returns the authorization trees of the last call ([`Env`](https://docs.rs/soroban-sdk/latest/soroban_sdk/struct.Env.html)). Stellar documents fuzzing with cargo-fuzz on top of them ([fuzzing guide](https://developers.stellar.org/docs/build/guides/testing/fuzzing)).

This repository differs from all of these in four ways.

- **The proofs are Lean proofs**, checked by Lean's kernel, about a function's behaviour on every input. The specification is a readable model, not a set of properties.
- **The object is a pure function**, the rule evaluator, translated from its MIR through Charon and Aeneas. Whole contracts and their compiled WebAssembly are not the object, so rustc's back end is trusted ([`TRUSTED.md`](TRUSTED.md#rustc)), where Sunbeam and Komet check the WebAssembly itself.
- **The host enters through small Lean models** of storage, rollback, `require_auth` matching and `__check_auth`'s input. Each model is tested against `soroban-env-host`. None of the tools above models how `require_auth` is matched against a signed authorization tree, or what `__check_auth` receives.
- **The tools can complement each other.** A contract shell that uses `rule-eval` can also be checked with Sunbeam or Komet. Those tools would cover the shell's storage and call handling, and this repository covers the rule check.

### M6: adoption

Perch moves its pure rule check behind `rule-eval` in small pull requests.
Each one is pinned by a differential test against Perch's current behaviour:
the conformance vectors, plus recorded verdicts of the code being replaced.
The grant signer moves last, once budgets (M3) are proven. Each consumer runs
the conformance vectors in its own CI, so a change to the model shows up as a
failing vector in every consumer.

## Open questions

These are not decided. They wait for the owner's decision.

1. **M2: the time model in the budget proofs.** How rolling-window caps enter the budget proofs.
2. **M4: rule mapping.** Whether Perch's compiled rules (OpenZeppelin context rules plus policies) map onto this rule model without loss, or need a richer condition set.
3. **M5: host versions.** How the Lean Soroban models are kept in step with new `soroban-env-host` versions.
