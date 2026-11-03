# soroban-rule-core

A verified rule evaluator for Soroban authorization. `crates/rule-eval` is a
`no_std` Rust evaluator with no dependencies, written in a restricted subset of
Rust. `formal/` holds a Lean model of rule sets and its theorems. Charon and
Aeneas translate the evaluator to Lean, and theorems prove the translation
equal to the model. Conformance vectors computed by the model let other
implementations test against the same verdicts.

A rule names one contract, a list of its functions, conditions on that call's
arguments, a list of signers, a threshold and, optionally, a spending cap. An
authorization carries the signers it authenticated, and a rule's signer
requirement holds when at least its threshold of distinct rule signers are
among them. A rule set allows a call when some rule allows it, and allows a
batch (every context of a Soroban authorization tree, under one list of
authenticated signers) when it allows each one. A holder narrows a rule set in
eight ways: drop a rule, add a condition to a rule, remove functions from a
rule, remove signers from a rule, raise a rule's threshold, add a cap to a
rule, lower a cap's limit, or lengthen a cap's period.

A spending cap bounds what one rule may spend: at most `limit` within `period`
consecutive ledgers, each call spending the argument the cap names.
`check_spend` takes a rule's spend record, the cap, the current ledger and the
amount, and returns the record after the spend or a refusal. It mirrors the
spending-limit policy Perch uses, adds a refusal for a ledger earlier than the
newest recorded spend, and refuses every sum that overflows. `authorize` checks
an authorization as OpenZeppelin's smart account does: the caller names one
rule per context, every chosen rule must allow its context, and each context
whose rule has a cap is charged to that rule's record, in order, so two
contexts on one rule accumulate. It returns the records after every charge, or
a refusal that changes nothing.

Budgets sit on the delegation tree, a list of nodes, each with its parent's
index, an allowance and what has been spent at or under it. `spend` charges a
node and every ancestor up to its root, or refuses, changing nothing and
naming the first node on the chain that would be overdrawn, where a refill
request goes. `delegate` appends a child with any allowance, so children's
allowances may sum to more than their parent's, and `refill`, the owner's
action, raises one node's allowance. [`ARCHITECTURE.md`](ARCHITECTURE.md)
covers the design, and how it serves the three layers of authority in a smart
account.

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
  - generic: `RuleSet.dropRule_narrower`, `RuleSet.addCond_narrower`, `RuleSet.restrictScope_narrower`, `RuleSet.removeSigners_narrower`, `RuleSet.raiseThreshold_narrower`, `RuleSet.addCap_narrower`, `RuleSet.lowerCapLimit_narrower`, `RuleSet.lengthenCapPeriod_narrower`, `RuleSet.attenuate_narrower`;
  - chain: `Chain.RuleSet.dropRule_narrower`, `Chain.RuleSet.addCond_narrower`, `Chain.RuleSet.removeFunctions_narrower`, `Chain.RuleSet.removeSigners_narrower`, `Chain.RuleSet.raiseThreshold_narrower`, `Chain.RuleSet.addCap_narrower`, `Chain.RuleSet.lowerCapLimit_narrower`, `Chain.RuleSet.lengthenCapPeriod_narrower`, `Chain.RuleSet.attenuate_narrower`.
- Narrower is reflexive and transitive (`RuleSet.narrower_refl`, `RuleSet.narrower_trans`), and any chain of the eight steps stays inside its root (`RuleSet.Derives.narrower`, `RuleSet.attenuateAll_narrower`, and the `Chain` versions).
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
- A step is refused with `noSuchRule` exactly when its index is out of range (`*_eq_error_iff`, `*_eq_noSuchRule_iff`), and `raiseThreshold` with `thresholdLowered` exactly when the new threshold is below the rule's (`RuleSet.raiseThreshold_eq_thresholdLowered_iff`). Each cap step's other refusals happen exactly in the case they name (`RuleSet.addCap_eq_capPresent_iff`, `RuleSet.addCap_eq_invalidCap_iff`, `RuleSet.lowerCapLimit_eq_noCap_iff`, `RuleSet.lowerCapLimit_eq_limitRaised_iff`, `RuleSet.lowerCapLimit_eq_invalidCap_iff`, `RuleSet.lengthenCapPeriod_eq_noCap_iff`, `RuleSet.lengthenCapPeriod_eq_periodShortened_iff`).

**Spending caps.** `RuleCore.Cap` models the record and the check; runs are
lists of calls `(now, amount)`, with no assumption about the order of ledgers.

- Window safety: from the empty record, for every run and every ledger `t`, the recorded spends after `t - period` and at most `t` sum to at most the limit (`Cap.window_le_limit`). Every window of `period` consecutive ledgers starting at ledger 1 or later does too (`Cap.period_le_limit_of_pos`), and every window does when every call is at ledger 1 or later (`Cap.period_le_limit`). Without that rule, two spends of the whole limit at ledger 0 are both accepted (`Cap.period_ledger_zero`).
- Refinement: the stored history is the recorded spends eviction left at the last spend's ledger, followed by that spend, and the stored total is their sum (`Cap.run_history`, `Cap.run_total`); with a nonzero period and that spend at ledger 1 or later, exactly the recorded spends in its window (`Cap.run_eq_window`).
- A refusal changes nothing (`Cap.step_of_error`, `Cap.run_cons_of_error`); a negative amount is refused and a zero amount changes nothing (`Cap.check_negative`, `Cap.check_zero`); a positive spend earlier than the newest recorded ledger is refused (`Cap.check_ledgerBeforeNewest_iff`).
- Narrowing is trace inclusion: every run a lower limit, a longer period, or a cap where there was none accepts from a valid record, the wider cap accepts (`Cap.Params.accepts_of_narrower`, `Cap.accepts_of_limit_le`, `Cap.accepts_of_period_le`, `Cap.capAccepts_of_capNarrower`). A cap installed over an existing record bounds every window holding a spend made under it (`Cap.window_le_limit_of_valid`).
- The check keeps a record valid (`Cap.run_valid`), and a record never holds more than 1000 entries (`Cap.run_history_length_le`).

**Caps on rules.** `RuleCore.Model.Authorize` models `authorize`, with runs of
authorizations from records holding one record per rule.

- Soundness: an accepted authorization's every context is allowed by the rule chosen for it, so the rule set allows the whole batch under its signers (`RuleSet.authorize_chosen`, `RuleSet.authorize_allowsAll`, `Chain.RuleSet.authorize_allowsAll`).
- A refusal changes nothing (`RuleSet.step_of_error`); an accepted authorization keeps one record per rule (`RuleSet.authorize_length`).
- The stored record of a capped rule is the cap check's own run over the calls a run charged to it, and a rule without a cap keeps its record (`RuleSet.run_get`, `RuleSet.run_get_of_cap_none`, `RuleSet.spent_eq_recorded`).
- Window safety for every capped rule and every run from empty records: the spends recorded for the rule in every window of eviction sum to at most its limit (`RuleSet.window_le_limit`), and so do those in every window of `period` consecutive ledgers from ledger 1 on (`RuleSet.period_le_limit_of_pos`), or in every window when every authorization is at ledger 1 or later (`RuleSet.period_le_limit`).
- The stored record is exactly the rule's spends in the window at its last spend, with their sum as total (`RuleSet.run_eq_window`), and never holds more than 1000 entries (`RuleSet.run_history_length_le`).
- Narrowing as trace inclusion: for each of the eight steps and every chain of them, every run of authorizations the derived rule set accepts from its empty records, the root accepts from its own, with each choice renumbered by the map `dropRule` induces (`RuleSet.attenuate_traceNarrower`, `RuleSet.attenuateAll_traceNarrower`, `Attenuation.source_dropRule`, `Attenuation.source_eq_of_ne_dropRule`, and the `Chain` versions). They rest on `RuleSet.Refines.traceNarrower` and `Cap.check_of_narrower_suffix`; trace inclusion composes (`RuleSet.TraceNarrower.trans`).
- The steps keep every cap valid (`RuleSet.attenuate_capsValid`, `RuleSet.attenuateAll_capsValid`).

**Budgets on the delegation tree.** `RuleCore.Budget` models the tree and its
three operations; runs are lists of spends, delegations and refills, from any
tree.

- Budget safety: for every run from a well-formed tree with nothing spent, the total successfully spent at or under any node is that node's spent amount and never exceeds its allowance (`Budget.Tree.spentUnder_le_allowance`, `Budget.Tree.spentUnder_eq_spent`, from `Budget.Tree.spent_run`). Nothing relates allowances to each other, so the bound holds however much children's allowances oversubscribe their parent's.
- A successful spend adds the amount to the spender and every ancestor, and changes nothing else (`Budget.Tree.spend_ok_charges`, `Budget.Tree.spend_ok_unchanged`, `Budget.Tree.spend_ok_length`, `Budget.Tree.spend_ok_parentOf`, `Budget.Tree.spend_ok_allowance`); a refused operation changes nothing (`Budget.Tree.step_of_error`, `Budget.Tree.run_cons_of_error`).
- The node an `overdrawn` refusal names is on the spender's chain and cannot take the amount, and every node before it on the chain can (`Budget.Tree.spend_overdrawn`). On a well-formed tree, a spend of a non-negative amount at an existing node succeeds exactly when every node on its chain can take it (`Budget.Tree.spend_accepts_iff`, `Budget.Tree.spend_error_overdrawn`).
- A delegation appends exactly the new child, with nothing spent, whatever its allowance; a refill raises exactly one allowance (`Budget.Tree.delegate_ok_iff`, `Budget.Tree.refill_ok_iff`).
- Every operation and every run keeps the tree well formed and every spent amount within its allowance (`Budget.Tree.run_valid`, `Budget.Tree.run_withinAllowance`, and the single-operation versions).

**The translation equals the model.** `RuleCore.Equiv` relates
`formal/RuleCore/Extracted/RuleEval.lean`, which Charon and Aeneas generate
from `crates/rule-eval`, to the chain vocabulary through denotation functions.

- `allows_eq` and `allows_all_eq`: on every input, the translated `allows` and `allows_all` return `ok` of the model's verdict on the denotations, authenticated signers included. `ok` rules out both a panic and divergence, so these theorems also prove that the evaluator terminates and never panics. `signers_met_eq` and `signed_count_eq` do the same for the signer requirement.
- `drop_rule_eq`, `remove_functions_eq`, `remove_signers_eq`, `raise_threshold_eq` and `add_cond_eq`: on every input, each attenuation step returns the model's result, `noSuchRule` and `thresholdLowered` included. `add_cond_eq` takes the stated rule `CondRoom`, and `add_cond_full` shows that rule is exact.
- `check_spend_eq`: on every input, the translated `check_spend` returns `ok` of the cap model's check on the denotations, so it terminates and never panics. It needs no stated bound.
- `authorize_eq`: on every input, the translated `authorize` returns `ok` of the model's authorization on the denotations, every refusal included, so it terminates and never panics. `check_choices_loop_eq` and `charge_all_loop_eq` prove its two passes. `add_cap_eq`, `lower_cap_limit_eq` and `lengthen_cap_period_eq` do the same for the cap steps.
- `spend_eq`, `delegate_eq` and `refill_eq`: on every input, the translated budget operations return `ok` of the budget model's operation on the denotations, every refusal included, so they terminate and never panic. None needs a stated bound. `check_chain_loop_eq` and `charged_loop_eq` prove the checking walk and the charging walk.
- Every denotation is injective (`denoteVal_injective`, `denoteContext_injective`, `denoteSigner_injective`, `denoteCap_injective`, `denoteRule_injective`, `denoteRules_injective`, `denoteOutcome_injective`, `denoteRecord_injective`, `denoteSpend_injective`, `denoteRefusal_injective`, `denoteAuthorized_injective`, `denoteTree_injective`, `denoteBudget_injective`, ...).

**The model's theorems hold of the translation.** `RuleCore.Extracted`
states these on the translated functions alone:

- each step that returns `Ok` narrows (`drop_rule_narrower`, `add_cond_narrower`, `remove_functions_narrower`, `remove_signers_narrower`, `raise_threshold_narrower`, `add_cap_narrower`, `lower_cap_limit_narrower`, `lengthen_cap_period_narrower`, `Step.narrower`);
- chains stay inside their root (`Narrower.trans`, `Derives.narrower`);
- a narrower rule set accepts a batch only if its ancestor does (`allows_all_of_narrower`, `Derives.allows_all`);
- no creation is allowed (`allows_create`, `allows_all_create`);
- `argEq` needs the same constructor (`val_eq_iff`, `val_eq_kind`, `val_eq_other_bytes`, `cond_holds_argEq_iff`, `cond_holds_argEq_false_of_kind_ne`);
- byte strings compare exactly (`bytes_eq_iff`, `rule_allows_call`, `rule_allows_prefix_false`, `rule_allows_extension_false`);
- an `authorize` that returns `Ok` means the translated `allows_all` accepts the batch (`authorize_allows_all`); a run of the translated `authorize` returns records denoting the model's run (`runAuthorizations_eq`), keeps them after a refusal (`runAuthorizations_of_err`), and from empty records bounds every window of each capped rule's spends by its limit, stores exactly the in-window spends and holds at most 1000 entries per record (`runAuthorizations_window_le_limit`, `runAuthorizations_window`, `runAuthorizations_length_le`);
- each translated step, and every chain of them, is trace inclusion along its renumbering (`StepAlong.traceNarrower`, `DerivesAlong.traceNarrower`, from `traceNarrower_of_denote`);
- a run of the translated `check_spend` returns a record denoting the model's run (`runSpends_eq`), so from the empty record it holds at most 1000 entries and is the recorded spends in its window (`runSpends_length_le`, `runSpends_window`); the translated check refuses a negative amount, changes nothing on a zero amount and refuses a spend before the newest recorded ledger (`check_spend_negative`, `check_spend_zero`, `check_spend_before_newest`);
- a run of the translated `spend`, `delegate` and `refill` returns a tree and a log of spends denoting the model's run (`runBudget_eq`), so it keeps the tree well formed and every spent amount within its allowance (`runBudget_valid`, `runBudget_withinAllowance`), and from a well-formed tree with nothing spent the total spent at or under each node is its spent amount and within its allowance (`runBudget_spentUnder_eq_spent`, `runBudget_spentUnder_le_allowance`); a translated spend charges exactly the chain, its `Overdrawn` refusal names the first node that cannot take the amount, and on a well-formed tree it succeeds exactly when every node on the chain can (`budget_spend_charges`, `budget_spend_unchanged`, `budget_spend_overdrawn`, `budget_spend_accepts_iff`);
- signers compare exactly (`signer_eq_iff`, `signer_eq_delegated_external`); authenticating more signers never refuses (`allows_of_subset`, `allows_all_of_subset`); repeats and order in either list change nothing (`allows_congr`, `allows_all_congr`, `rule_allows_congr_signers`); threshold 0 ignores the signers, a threshold of all distinct signers needs every one, and a threshold above them allows nothing (`rule_allows_threshold_zero`, `signers_met_all_iff`, `rule_allows_false_of_lt`).

**Stated rules.** These are not theorems. [`TRUSTED.md`](TRUSTED.md) states
each one.

- *The empty batch*: every rule set allows the empty batch (`RuleSet.allowsAll_nil`). A batch collected from a Soroban authorization tree is never empty. A caller that builds batches another way must reject the empty batch.
- *No creation* is a property of the chain vocabulary. The generic model makes no such claim.
- *`CondRoom`*: the rule `add_cond` extends has fewer than `Usize.max` conditions.
- *Ledgers start at 1*: every call of the cap check is made at ledger 1 or later, as on Stellar, whose genesis ledger is ledger 1. Only `Cap.period_le_limit` takes it.

**Stated, not proven.** `narrower_of_denote` proves that the model's narrower
on the denotations implies narrower on the translation. The converse, that
narrower on the translation implies the model's narrower on the
denotations, is not stated: model byte strings, argument lists and signer
lists longer than `Usize.max` have no Rust counterpart.

On the translation, a renumbered run exists only when each renumbered choice
fits a `u32`, so for a rule set of more than `2^32` rules that drops a rule,
`StepAlong.traceNarrower` says nothing about runs choosing rules no `u32` can
name in the root. The model's statement has no such limit.

The mapping from OpenZeppelin's context rules and threshold policies to signers
and thresholds here ([`ARCHITECTURE.md`](ARCHITECTURE.md#openzeppelins-rules-as-input-for-m4))
is read from OpenZeppelin's source, recorded as input for M4, and neither
proven nor tested. So is the correspondence between `check_spend` and the
spending-limit policy at the revision Perch pins
([`ARCHITECTURE.md`](ARCHITECTURE.md#mirroring-perch)), the correspondence
between `authorize` and OpenZeppelin's `do_check_auth` there
([`ARCHITECTURE.md`](ARCHITECTURE.md#mirroring-openzeppelin)), and the reading
that a record of 816 or more entries does not fit in one mainnet ledger entry.

The budget operations take the node, the amount and the tree as given. Which
node an authorization's spend is charged to, storing the tree only on `Ok`, and
accepting a refill only on the owner's authority are the shell's duties
([`ARCHITECTURE.md`](ARCHITECTURE.md#milestone-3-the-budget-tree)), for the
grant signer in M6; nothing here checks them.

## What is tested

- **Conformance vectors.** `conformance/vectors/*.json` holds 153 vectors, each a rule set, a batch, the authenticated signers, the per-context and whole-batch verdicts, and attenuation steps with their results. The Lean model computes every expected result. Of these, 53 are named cases and 100 are drawn from a seeded generator. The signer cases cover thresholds 0, 1, k, all signers and above, repeated signers in either list, delegated and external signers with equal bytes, missing signers, batches under one authenticated list, and both signer steps. The cap cases cover each cap step and each of its refusals, chains mixing them with the other steps, and verdicts that ignore caps. CI regenerates them from the model and fails on any difference (`conformance.yml`). The runner in `conformance/runner` checks `rule-eval` against every vector: `rule_eval_agrees_with_every_vector`, `vectors_cover_every_kind` and `a_wrong_expectation_is_reported`. [`conformance/README.md`](conformance/README.md) documents the format, so other implementations can run the same vectors.
- **Cap traces.** `conformance/vectors/caps/*.json` holds 72 traces, each a cap, a starting record and calls with the outcome and record the Lean model computes for each. Of these, 22 are named and 50 drawn from the same seeded generator; together they cover every refusal, ledger 0, `u32::MAX`, the history bound and caps that are not valid to install. CI regenerates them with the vectors. The runner checks `check_spend` against every trace: `rule_eval_agrees_with_every_cap_trace`, `cap_traces_cover_every_outcome` and `a_wrong_cap_expectation_is_reported`.
- **Authorization traces.** `conformance/vectors/authorize/*.json` holds 70 traces, each a rule set, its starting records and authorizations with the outcome and records the Lean model computes for each. Of these, 20 are named and 50 drawn from the same seeded generator; they cover every refusal, two contexts charging one rule, a refusal discarding a batch's charges, windows rolling, ledger 0, the history bound, rules keeping their own records, and the rule sets each cap step and `drop_rule` derive from one rule set, run on the same authorizations. The runner checks `authorize` against every trace: `rule_eval_agrees_with_every_authorization_trace`, `authorization_traces_cover_every_outcome` and `a_wrong_authorization_expectation_is_reported`.
- **Budget traces.** `conformance/vectors/budget/*.json` holds 69 traces, each a starting tree and spends, delegations and refills with the outcome and tree the Lean model computes for each. Of these, 19 are named and 50 drawn from the same seeded generator; they cover oversubscribed siblings, a spend exhausting a middle ancestor, the refusal naming the nearest overdrawn node, overflowing sums, malformed and empty trees, delegation then spend, refills and several roots, and every refusal but `tree_full`, which needs `u32::MAX` nodes. The runner checks the budget operations against every trace: `rule_eval_agrees_with_every_budget_trace`, `budget_traces_cover_every_outcome` and `a_wrong_budget_expectation_is_reported`.
- **Exhaustive small universes.** `crates/rule-eval/tests` checks `allows` against an ordinary-Rust reading of the semantics over every rule set of up to two rules and 335 contexts (`allows_agrees_with_the_reference_reading`). It also checks:
  - `allows_all` against `allows` (`allows_all_is_the_conjunction_of_allows`);
  - that no rule set allows a creation (`no_rule_allows_a_creation`);
  - that every step builds its result and only narrows (`every_step_builds_its_result_and_only_narrows`);
  - that every two-step chain stays inside its root (`every_two_step_chain_stays_inside_its_root`);
  - `signers_met` against the reference reading over every signer list of up to three signers, thresholds 0 to 4 and 63 authenticated lists (`signers_met_agrees_with_the_reference_reading`), that authenticating more signers never refuses and that order and repeats change nothing (`authenticating_more_signers_never_refuses`, `the_same_authenticated_signers_in_another_order_or_repeated_give_the_same_verdict`);
  - that every step on rules with signers only narrows under every authenticated list, alone and in two-step chains (`signer_steps_only_narrow_under_every_authenticated_list`);
  - `check_spend` against a plain reading of the check on every run of up to three calls from 25 under 16 small caps, and that every such run keeps every window within the limit (`check_spend_agrees_with_the_reference_reading`, `every_short_run_stays_within_every_window`);
  - `authorize` against a plain reading on 28,024 inputs (every rule set of up to two rules from five capped and uncapped rules, 113 batches with their choices, two signer lists, two ledgers, two starting records), with every accepted batch allowed by `allows_all` (`authorize_agrees_with_the_reference_reading`); 8,653 runs of up to three authorizations over two capped rules, each step against the reading, every window within its limit and every stored record the in-window spends (`authorize::every_short_run_stays_within_every_window`); and trace inclusion for each cap step, `drop_rule` with its renumbering and a chain, over the same runs (`every_step_is_trace_inclusion`);
  - `spend`, `delegate` and `refill` against a plain reading on 152,355 inputs (1,451 trees of up to three nodes, well formed or not, five indices and seven amounts), and over 300 random runs of 40 operations, each node's spent amount stays the total spent at or under it and within its allowance (`every_operation_agrees_with_a_plain_reading_on_small_trees`, `spent_under_a_node_stays_within_its_allowance_over_random_runs`).
- **Unit tests** cover every value constructor and both conditions, missing, wrong-typed and `u32::MAX` indices, exact byte and signer comparison, each threshold case, repeated signers, and each step at out-of-range indices and, for `raise_threshold`, below the current threshold. For caps they cover each refusal and its precedence, eviction at and beside the cutoff, the cutoff at ledger 0 and at `u32::MAX`, the history bound and each checked sum. For `authorize` they cover each refusal and its precedence, choices checked before charges, missing and wrong-typed amounts, charges accumulating, refusals discarding a batch, the window rolling and the empty batch; for the cap steps, what each builds and each refusal. For budgets they cover charging the chain, the nearest overdrawn node, oversubscribed siblings, an exhausted middle ancestor, overflowing sums, malformed trees, each refusal and its precedence, zero spends, delegation and refills.
- **CI gates.** Every pull request and every push to `main` runs:
  - `cargo test`, `cargo clippy -D warnings`, and builds for native and `wasm32v1-none` in the release and contract profiles, on the pinned nightly and on stable (`rust.yml`);
  - `lake build` of every module (`lean.yml`), which also rejects `sorry`, `admit`, `partial`, `unsafe`, `native_decide`, `implemented_by`, `extern` and `axiom` in every Lean source, the translation included;
  - the axioms record in `Axioms.lean`, checked under `#guard_msgs` as part of `lake build`;
  - re-extraction with Charon `--error-on-warnings` and Aeneas `-warnings-as-errors`, which fails on any difference from the committed translation (`extraction.yml`);
  - the claim-ledger check (`claims.yml`, plus a step in `lean.yml`).

The vectors' and traces' JSON encoding and decoding are not verified (see
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

# Conformance vectors and cap, authorization and budget traces: regenerate from the Lean model
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
| `crates/rule-eval/` | The rule-set evaluator, its attenuation steps, the spending-cap check, `authorize` and the budget tree: `no_std`, no dependencies, `forbid(unsafe_code)`. |
| `conformance/` | The vectors (`vectors/`), cap traces (`vectors/caps/`), authorization traces (`vectors/authorize/`) and budget traces (`vectors/budget/`), the Lean generator that computes them (`generator/`) and the Rust runner (`runner/`). |
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
