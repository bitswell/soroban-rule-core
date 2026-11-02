# soroban-rule-core

A verified rule evaluator for Soroban authorization. `crates/rule-eval` is a
`no_std` Rust evaluator with no dependencies, written in a restricted subset of
Rust. `formal/` holds a Lean model of rule sets and its theorems. Charon and
Aeneas translate the evaluator to Lean, and theorems prove the translation
equal to the model. Conformance vectors computed by the model let other
implementations test against the same verdicts.

A rule names one contract, a list of its functions, conditions on that call's
arguments, a list of signers and a threshold. An authorization carries the
signers it authenticated, and a rule's signer requirement holds when at least
its threshold of distinct rule signers are among them. A rule set allows a
call when some rule allows it, and allows a batch (every context of a Soroban
authorization tree, under one list of authenticated signers) when it allows
each one. A holder narrows a rule set in five ways: drop a rule, add a
condition to a rule, remove functions from a rule, remove signers from a rule,
or raise a rule's threshold.
[`ARCHITECTURE.md`](ARCHITECTURE.md) covers the design, and how it serves the
three layers of authority in a smart account.

Every claim the repository makes is in [`claims.yaml`](claims.yaml), with its
status (`proven`, `tested`, `measured`, `assumed` or `unproven`) and its
evidence. `tools/check-claims` checks the evidence in CI.

## What is proven

Each statement below is a Lean theorem checked by the kernel. Every one
depends on at most `propext`, `Quot.sound` and `Classical.choice`
(`formal/RuleCore/Axioms.lean`). [`formal/README.md`](formal/README.md) states
each theorem.

**The model.** `RuleCore` is generic in the context and signer types, and
`RuleCore.Chain` is the vocabulary `rule-eval` implements. Narrower quantifies
over authenticated signer lists as well as contexts.

- Each attenuation step yields a narrower rule set:
  - generic: `RuleSet.dropRule_narrower`, `RuleSet.addCond_narrower`, `RuleSet.restrictScope_narrower`, `RuleSet.removeSigners_narrower`, `RuleSet.raiseThreshold_narrower`, `RuleSet.attenuate_narrower`;
  - chain: `Chain.RuleSet.dropRule_narrower`, `Chain.RuleSet.addCond_narrower`, `Chain.RuleSet.removeFunctions_narrower`, `Chain.RuleSet.removeSigners_narrower`, `Chain.RuleSet.raiseThreshold_narrower`, `Chain.RuleSet.attenuate_narrower`.
- Narrower is reflexive and transitive (`RuleSet.narrower_refl`, `RuleSet.narrower_trans`), and any chain of the five steps stays inside its root (`RuleSet.Derives.narrower`, `RuleSet.attenuateAll_narrower`, and the `Chain` versions).
- A narrower rule set accepts a batch only if its ancestor does (`RuleSet.allowsAll_of_narrower`, `Chain.RuleSet.allowsAll_of_narrower`).
- No rule set allows a contract creation, and a batch containing one is denied (`Chain.RuleSet.allows_create`, `Chain.RuleSet.allowsAll_false_of_create_mem`).
- `argEq` holds only for an argument of the same constructor (`Chain.Cond.argEq_kind`, `Chain.Cond.argEq_false_of_kind_ne`, `Chain.Cond.argEq_bytes_false_of_other`).
- Byte strings compare exactly, with no prefix or extension match (`Bytes.eq_iff`, `Chain.Rule.contract_eq_of_allows`, `Chain.Rule.allows_prefix_false`, `Chain.Rule.allows_extension_false`).
- A rule's conditions read only the arguments of the call that rule matches (`Chain.Rule.allows_call_iff`).
- A rule with an empty function list allows nothing (`Chain.Rule.allows_false_of_functions_nil`).
- Signers:
  - the requirement holds exactly when at least `threshold` distinct rule signers are authenticated (`Rule.signed_iff`, `Rule.mem_present`, `Chain.Rule.signed_iff`);
  - threshold 0 is no requirement (`Rule.signed_of_threshold_zero`, `Chain.Rule.allows_of_threshold_zero`); a threshold equal to the number of distinct signers requires all of them (`Rule.signed_iff_of_threshold_eq`); a threshold above it allows nothing (`Rule.allows_false_of_lt`);
  - authenticating more signers never turns an allow into a refusal (`RuleSet.allows_of_subset`, `RuleSet.allowsAll_of_subset`, and the `Chain` versions);
  - repeats and order in either signer list do not change the verdict (`RuleSet.allows_congr`, `RuleSet.allowsAll_congr`, `RuleSet.allows_eraseDups`, `Rule.signed_congr_signers`, `Chain.Rule.allows_congr_signers`);
  - signers compare exactly, constructor first (`Chain.Signer.delegated_ne_external`, `Chain.Signer.delegated_eq_iff`, `Chain.Signer.external_eq_iff`, `Chain.Signer.delegated_append_ne`).
- A step is refused with `noSuchRule` exactly when its index is out of range (`*_eq_error_iff`, `*_eq_noSuchRule_iff`), and `raiseThreshold` with `thresholdLowered` exactly when the new threshold is below the rule's (`RuleSet.raiseThreshold_eq_thresholdLowered_iff`).

**The translation equals the model.** `RuleCore.Equiv` relates
`formal/RuleCore/Extracted/RuleEval.lean`, which Charon and Aeneas generate
from `crates/rule-eval`, to the chain vocabulary through denotation functions.

- `allows_eq` and `allows_all_eq`: on every input, the translated `allows` and `allows_all` return `ok` of the model's verdict on the denotations, authenticated signers included. `ok` rules out both a panic and divergence, so these theorems also prove that the evaluator terminates and never panics. `signers_met_eq` and `signed_count_eq` do the same for the signer requirement.
- `drop_rule_eq`, `remove_functions_eq`, `remove_signers_eq`, `raise_threshold_eq` and `add_cond_eq`: on every input, each attenuation step returns the model's result, `noSuchRule` and `thresholdLowered` included. `add_cond_eq` takes the stated rule `CondRoom`, and `add_cond_full` shows that rule is exact.
- Every denotation is injective (`denoteVal_injective`, `denoteContext_injective`, `denoteSigner_injective`, `denoteRule_injective`, `denoteRules_injective`, `denoteOutcome_injective`, ...).

**The model's theorems hold of the translation.** `RuleCore.Extracted`
states these on the translated functions alone:

- each step that returns `Ok` narrows (`drop_rule_narrower`, `add_cond_narrower`, `remove_functions_narrower`, `remove_signers_narrower`, `raise_threshold_narrower`, `Step.narrower`);
- chains stay inside their root (`Narrower.trans`, `Derives.narrower`);
- a narrower rule set accepts a batch only if its ancestor does (`allows_all_of_narrower`, `Derives.allows_all`);
- no creation is allowed (`allows_create`, `allows_all_create`);
- `argEq` needs the same constructor (`val_eq_iff`, `val_eq_kind`, `val_eq_other_bytes`, `cond_holds_argEq_iff`, `cond_holds_argEq_false_of_kind_ne`);
- byte strings compare exactly (`bytes_eq_iff`, `rule_allows_call`, `rule_allows_prefix_false`, `rule_allows_extension_false`);
- signers compare exactly (`signer_eq_iff`, `signer_eq_delegated_external`); authenticating more signers never refuses (`allows_of_subset`, `allows_all_of_subset`); repeats and order in either list change nothing (`allows_congr`, `allows_all_congr`, `rule_allows_congr_signers`); threshold 0 ignores the signers, a threshold of all distinct signers needs every one, and a threshold above them allows nothing (`rule_allows_threshold_zero`, `signers_met_all_iff`, `rule_allows_false_of_lt`).

**Stated rules.** These are not theorems. [`TRUSTED.md`](TRUSTED.md) states
each one.

- *The empty batch*: every rule set allows the empty batch (`RuleSet.allowsAll_nil`). A batch collected from a Soroban authorization tree is never empty. A caller that builds batches another way must reject the empty batch.
- *No creation* is a property of the chain vocabulary. The generic model makes no such claim.
- *`CondRoom`*: the rule `add_cond` extends has fewer than `Usize.max` conditions.

**Stated, not proven.** `narrower_of_denote` proves that the model's narrower
on the denotations implies narrower on the translation. The converse, that
narrower on the translation implies the model's narrower on the
denotations, is not stated: model byte strings, argument lists and signer
lists longer than `Usize.max` have no Rust counterpart.

The mapping from OpenZeppelin's context rules and threshold policies to signers
and thresholds here ([`ARCHITECTURE.md`](ARCHITECTURE.md#openzeppelins-rules-as-input-for-m4))
is read from OpenZeppelin's source, recorded as input for M4, and neither
proven nor tested.

## What is tested

- **Conformance vectors.** `conformance/vectors/*.json` holds 148 vectors, each a rule set, a batch, the authenticated signers, the per-context and whole-batch verdicts, and attenuation steps with their results. The Lean model computes every expected result. Of these, 48 are named cases and 100 are drawn from a seeded generator. The signer cases cover thresholds 0, 1, k, all signers and above, repeated signers in either list, delegated and external signers with equal bytes, missing signers, batches under one authenticated list, and both signer steps. CI regenerates them from the model and fails on any difference (`conformance.yml`). The runner in `conformance/runner` checks `rule-eval` against every vector: `rule_eval_agrees_with_every_vector`, `vectors_cover_every_kind` and `a_wrong_expectation_is_reported`. [`conformance/README.md`](conformance/README.md) documents the format, so other implementations can run the same vectors.
- **Exhaustive small universes.** `crates/rule-eval/tests` checks `allows` against an ordinary-Rust reading of the semantics over every rule set of up to two rules and 335 contexts (`allows_agrees_with_the_reference_reading`). It also checks:
  - `allows_all` against `allows` (`allows_all_is_the_conjunction_of_allows`);
  - that no rule set allows a creation (`no_rule_allows_a_creation`);
  - that every step builds its result and only narrows (`every_step_builds_its_result_and_only_narrows`);
  - that every two-step chain stays inside its root (`every_two_step_chain_stays_inside_its_root`);
  - `signers_met` against the reference reading over every signer list of up to three signers, thresholds 0 to 4 and 63 authenticated lists (`signers_met_agrees_with_the_reference_reading`), that authenticating more signers never refuses and that order and repeats change nothing (`authenticating_more_signers_never_refuses`, `the_same_authenticated_signers_in_another_order_or_repeated_give_the_same_verdict`);
  - that every step on rules with signers only narrows under every authenticated list, alone and in two-step chains (`signer_steps_only_narrow_under_every_authenticated_list`).
- **Unit tests** cover every value constructor and both conditions, missing, wrong-typed and `u32::MAX` indices, exact byte and signer comparison, each threshold case, repeated signers, and each step at out-of-range indices and, for `raise_threshold`, below the current threshold.
- **CI gates.** Every pull request and every push to `main` runs:
  - `cargo test`, `cargo clippy -D warnings`, and builds for native and `wasm32v1-none` in the release and contract profiles, on the pinned nightly and on stable (`rust.yml`);
  - `lake build` of every module (`lean.yml`), which also rejects `sorry`, `admit`, `partial`, `unsafe`, `native_decide`, `implemented_by`, `extern` and `axiom` in every Lean source, the translation included;
  - the axioms record in `Axioms.lean`, checked under `#guard_msgs` as part of `lake build`;
  - re-extraction with Charon `--error-on-warnings` and Aeneas `-warnings-as-errors`, which fails on any difference from the committed translation (`extraction.yml`);
  - the claim-ledger check (`claims.yml`, plus a step in `lean.yml`).

The vectors' JSON encoding and decoding are not verified (see
[`TRUSTED.md`](TRUSTED.md#the-conformance-encoding)).

## What is trusted

[`TRUSTED.md`](TRUSTED.md) lists what the proofs rest on:

- rustc;
- Charon and Aeneas at the pinned commits;
- Aeneas's Lean library: its `Result`, its `loop`, and its model of each Rust library item the evaluator calls, listed one by one;
- Lean's kernel;
- the denotation functions, which are part of the specification;
- the stated rules above.

## Building and checking

`flake.nix` pins one Aeneas commit (`ab34bd28`), the Charon commit it fixes
(`7b462d9`), the Rust nightly Charon reads (`nightly-2026-09-17`,
`rust-toolchain.toml`) and Lean `v4.35.0` (`formal/lean-toolchain`).
Evaluating the flake fails if these disagree.

```sh
# Rust: tests (including the conformance runner), lint, builds
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo build -p rule-eval --release --target wasm32v1-none --locked
cargo build -p rule-eval --profile contract --target wasm32v1-none --locked

# Lean: the model, the translation, the equivalence and every theorem
cd formal && lake exe cache get && lake build && cd ..

# Extraction: regenerate the translation, or check it is current (needs Nix)
tools/extract.sh
tools/extract.sh --check

# Conformance vectors: regenerate from the Lean model
cd conformance/generator && lake build && lake exe gen-vectors ../vectors && cd ../..

# Claim ledger (needs uv): the checker's self-tests, then the ledger
tools/tests/check_claims_test.py
tools/check-claims
tools/check-claims --theorems lean --skip-tests   # after lake build
```

Without Nix, `tools/extract.sh` runs in the `nixos/nix` image (see the
script's header).

## Layout

| Path | Contents |
| --- | --- |
| `crates/rule-eval/` | The rule-set evaluator and its attenuation steps: `no_std`, no dependencies, `forbid(unsafe_code)`. |
| `conformance/` | The vectors (`vectors/`), the Lean generator that computes them (`generator/`) and the Rust runner (`runner/`). |
| `formal/` | The Lean package: `Model/`, `Vocab/`, `Extracted/` (generated), `Equiv/`, `Theorems/` and `Axioms.lean`. |
| `tools/extract.sh` | Runs Charon and Aeneas on `crates/rule-eval`. |
| `tools/check-claims`, `tools/tests/` | The claim-ledger checker and its self-tests. |
| `claims.yaml` | The claim ledger. |
| `flake.nix`, `flake.lock`, `rust-toolchain.toml` | The pinned toolchain. |
| `.github/workflows/` | `rust.yml`, `lean.yml`, `extraction.yml`, `conformance.yml`, `claims.yml`. |
| `ARCHITECTURE.md`, `TRUSTED.md` | The design and later milestones; what is trusted. |

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT), at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this repository, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
