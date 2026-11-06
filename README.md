# soroban-rule-core

A verified rule evaluator for Soroban authorization, the lowering of
Perch's policy documents to its rules, and a small Soroban facade with Lean
models of the host behaviour the contract shells rely on. `crates/rule-eval`
is a `no_std` Rust evaluator with no dependencies, written in a restricted
subset of Rust. `formal/` holds a Lean model of rule sets and its theorems.
Charon and Aeneas translate the evaluator to Lean, and theorems prove the
translation equal to the model. Conformance vectors computed by the model let
other implementations test against the same verdicts.

A rule names one contract, the functions it matches there (a list, or every
function but a list), conditions on that call's arguments, a list of signers, a
threshold and, optionally, a spending cap, a last ledger and the generation it
was issued under. An authorization carries the signers it authenticated, and a
rule's signer requirement holds when at least its threshold of distinct rule
signers are among them. A rule set allows a call when some rule allows it, and
allows a batch (every context of a Soroban authorization tree, under one list
of authenticated signers) when it allows each one. A holder narrows a rule set
in ten ways: drop a rule, add a condition to a rule, remove functions from a
rule, restrict a rule's functions to a list, remove signers from a rule, raise
a rule's threshold, add a cap to a rule, lower a cap's limit, lengthen a cap's
period, or give a rule an earlier last ledger.

A spending cap bounds what one rule may spend: at most `limit` within `period`
consecutive ledgers, each call spending the argument the cap names.
`check_spend` takes a rule's spend record, the cap, the current ledger and the
amount, and returns the record after the spend or a refusal. It mirrors the
spending-limit policy Perch uses, adds a refusal for a ledger earlier than the
newest recorded spend, and refuses every sum that overflows. `authorize` checks
an authorization as OpenZeppelin's smart account does: the caller names one
rule per context; every chosen rule must be unexpired at the current ledger,
belong to the current generation when it carries one, and allow its context;
every authenticated signer must be a signer of some chosen rule; and each
context whose rule has a cap is charged to that rule's record, in order, so two
contexts on one rule accumulate. It returns the records after every charge, or
a refusal that changes nothing. Once the generation moves on, a rule issued
under an earlier one authorizes nothing.

Budgets sit on the delegation tree, a list of nodes, each with its parent's
index, an allowance and what has been spent at or under it. `spend` charges a
node and every ancestor up to its root, or refuses, changing nothing and
naming the first node on the chain that would be overdrawn, where a refill
request goes. `delegate` appends a child with any allowance, so children's
allowances may sum to more than their parent's, and `refill`, the owner's
action, raises one node's allowance.

`lower` turns a Perch policy document (its declared signers, rules and recovery
configuration, as plain data with identifiers as bytes) into the rules Perch
installs for it on OpenZeppelin's smart account, and the rules allow exactly
what the document says, apart from the recovery rule, which allows every
`apply_doc` on the account where the recovery controller allows only a
recovery's completion. `lower_scoped` turns a scoped document, a grant the
owner issues under the admin document, into rules carrying the generation they
were issued under, and refuses one that names the account, its recovery
controller or its ZK adapter or pool. The account's generation advances only
when a recovery completes, so a completed recovery leaves every earlier grant
authorizing nothing.

`crates/soroban-facade` is the part of soroban-sdk the shells use, as plain
data and two small interfaces: values (addresses, bytes, symbols, `i128`,
vectors, maps and a few more) and their XDR, storage get, has, set and remove
by durability, `require_auth`, and the authorization contexts `__check_auth`
receives, with their conversion to `rule-eval`'s contexts. It has a plain
implementation for tests and a real one over soroban-sdk 29.0.1, the only
code that touches the SDK. `formal/RuleCore/Soroban/` models what the shells
rely on from soroban-env-host 29.0.1 (protocol 29, the protocol mainnet runs): storage as a map, rollback of a failed
call, `require_auth` matched against the signed authorization tree, and what
`__check_auth` receives for each kind of credentials, delegation included.
Vectors computed from those models are replayed on the host itself, on
soroban-env-host 29.0.1 and on the next release, 30.0.0, together with the
host's own authorization and storage tests transcribed into the same form.
[`ARCHITECTURE.md`](ARCHITECTURE.md) covers the design, and how it serves the
three layers of authority in a smart account.

Every claim the repository makes is in [`claims.yaml`](claims.yaml), with its
status (`proven`, `tested`, `measured`, `assumed` or `unproven`) and its
evidence. `tools/check-claims` checks the evidence in CI.

## Optional offline Cedar frontend

[`tools/cedar-compile`](tools/cedar-compile/README.md) is a separate native
workspace that compiles a strictly bounded, permit-only Cedar fragment into
existing rules. It uses the official Cedar parser and a bounded differential
corpus; the new compiler is **not formally proven**. Cedar stays outside the
contract and extraction dependency graph. The prototype deliberately rejects
wide integer ranges and unsupported constructs instead of weakening them.

## Exact authorization roots

An ordinary `Rule` or `DocRule` may carry `auth_root: Some(AuthRoot { contract, function })`.
Both fields compare exact bytes. `authorize(rules, records, contexts, choices,
authenticated, now, generation)` derives the root from `contexts.first()` in the
current account's host-authenticated authorization entry. It checks the selected
rule's root requirement together with its existing local conditions before any
cap charge. Missing, creation, wrong-contract and wrong-function roots cannot
satisfy an exact requirement. This is an entry root, not the transaction's outer
call, an arbitrary ancestor, or a root asserted by the client.

A capped XLM-transfer rule restricted to `game.guess` can authorize a loss in
`[game.guess, token.transfer]`, with one valid selected rule per context and the
usual authenticated signers. A game-only win authenticates without charging the
transfer cap. A direct `[token.transfer]` entry is refused even under the cap;
a game call authorized in another entry cannot satisfy its requirement. Repeated
transfer contexts aggregate under the same cap, and a refused batch returns no
updated records.

`allows_batch` performs root-aware screening of one complete entry; it still
omits choices, cap charging, time, generation and extraneous-signer checks.
`rule_allows_in` screens one context against an explicit root. Existing
`rule_allows`, `allows` and `allows_all` remain local screening helpers and ignore
root constraints. They must not be used to approve root-constrained batches.
The full decision is `authorize`. Empty batches keep their existing no-operation
semantics, including shape and extraneous-signer checks.

Every existing attenuation/copy operation preserves surviving root constraints,
including rule dropping and choice reindexing. `auth_root_narrows(child, parent)`
checks only this component: unrestricted to exact narrows, retaining the exact
pair narrows, and erasing or changing an exact pair does not. Other conditions and
spending constraints require their own narrowing checks.

Ordinary document lowering retains the requirement. Self-admin and generated
recovery rules remain unrestricted to preserve eligibility. A document validator
must reject root constraints on self-admin input; this library's total lowering
ignores that field for self-admin even on unvalidated input. Rust struct literals
must explicitly initialize the new optional field. JSON schemas, canonical
commitments, storage compatibility and real-host entry tests belong to the
integrating account/compiler. This crate does not provide those migrations.

The new formal results are in `formal/RuleCore/Theorems/AuthRoot.lean`: exact
matching, root-component implication, accepted-trace screening, root-preserving
trace inclusion and provenance of every charge. They complement the existing
spending correspondence and failed-batch preservation theorems under the updated
root-aware evaluator. The conformance generator includes both authorization and
document root traces; unrestricted legacy vectors keep their original bytes.

## What is proven

Each statement below is a Lean theorem checked by the kernel. Every one
depends on at most `propext`, `Quot.sound` and `Classical.choice`
(`formal/RuleCore/Axioms.lean`). [`formal/README.md`](formal/README.md) states
each theorem.

**The model.** `RuleCore` is generic in the context and signer types, and
`RuleCore.Chain` is the vocabulary `rule-eval` implements. Narrower quantifies
over authenticated signer lists as well as contexts.

- Each attenuation step yields a narrower rule set:
  - generic: `RuleSet.dropRule_narrower`, `RuleSet.addCond_narrower`, `RuleSet.restrictScope_narrower`, `RuleSet.removeSigners_narrower`, `RuleSet.raiseThreshold_narrower`, `RuleSet.addCap_narrower`, `RuleSet.lowerCapLimit_narrower`, `RuleSet.lengthenCapPeriod_narrower`, `RuleSet.lowerValidUntil_narrower`, `RuleSet.attenuate_narrower`;
  - chain: `Chain.RuleSet.dropRule_narrower`, `Chain.RuleSet.addCond_narrower`, `Chain.RuleSet.removeFunctions_narrower`, `Chain.RuleSet.restrictFunctions_narrower`, `Chain.RuleSet.removeSigners_narrower`, `Chain.RuleSet.raiseThreshold_narrower`, `Chain.RuleSet.addCap_narrower`, `Chain.RuleSet.lowerCapLimit_narrower`, `Chain.RuleSet.lengthenCapPeriod_narrower`, `Chain.RuleSet.lowerValidUntil_narrower`, `Chain.RuleSet.attenuate_narrower`.
- Narrower is reflexive and transitive (`RuleSet.narrower_refl`, `RuleSet.narrower_trans`), and any chain of the steps stays inside its root (`RuleSet.Derives.narrower`, `RuleSet.attenuateAll_narrower`, and the `Chain` versions).
- A narrower rule set accepts a batch only if its ancestor does (`RuleSet.allowsAll_of_narrower`, `Chain.RuleSet.allowsAll_of_narrower`).
- No rule set allows a contract creation, and a batch containing one is denied (`Chain.RuleSet.allows_create`, `Chain.RuleSet.allowsAll_false_of_create_mem`).
- `argEq` holds only for an argument of the same constructor (`Chain.Cond.argEq_kind`, `Chain.Cond.argEq_false_of_kind_ne`, `Chain.Cond.argEq_bytes_false_of_other`); a string is never a symbol, even with the same bytes (`Chain.Val.string_ne_symbol`, `Chain.Cond.argEq_string_false_of_symbol`).
- `argIn` holds exactly when `argEq` holds for one of its values (`Chain.Cond.argIn_holds_iff`, `Chain.Cond.argIn_holds_iff_argEq`); `argStrPrefix` holds exactly when the argument is a string starting with the prefix, so never on a symbol (`Chain.Cond.argStrPrefix_holds_iff`, `Chain.Cond.argStrPrefix_kind`, `Chain.Cond.argStrPrefix_false_of_symbol`).
- The wildcard matches every function of its contract (`Chain.Rule.allows_call_any`); removing functions from a wildcard excludes exactly them, and restricting functions keeps exactly those also named (`Chain.Functions.mem_remove`, `Chain.Functions.mem_restrict`).
- Byte strings compare exactly, with no prefix or extension match (`Bytes.eq_iff`, `Chain.Rule.contract_eq_of_allows`, `Chain.Rule.allows_prefix_false`, `Chain.Rule.allows_extension_false`).
- A rule's conditions read only the arguments of the call that rule matches (`Chain.Rule.allows_call_iff`).
- A rule with an empty function list allows nothing (`Chain.Rule.allows_false_of_functions_nil`).
- Signers:
  - the requirement holds exactly when at least `threshold` distinct rule signers are authenticated (`Rule.signed_iff`, `Rule.mem_present`, `Chain.Rule.signed_iff`);
  - threshold 0 is no requirement (`Rule.signed_of_threshold_zero`, `Chain.Rule.allows_of_threshold_zero`); a threshold equal to the number of distinct signers requires all of them (`Rule.signed_iff_of_threshold_eq`); a threshold above it allows nothing (`Rule.allows_false_of_lt`);
  - authenticating more signers never turns an allow into a refusal (`RuleSet.allows_of_subset`, `RuleSet.allowsAll_of_subset`, and the `Chain` versions);
  - repeats and order in either signer list do not change the verdict (`RuleSet.allows_congr`, `RuleSet.allowsAll_congr`, `RuleSet.allows_eraseDups`, `Rule.signed_congr_signers`, `Chain.Rule.allows_congr_signers`);
  - signers compare exactly, constructor first (`Chain.Signer.delegated_ne_external`, `Chain.Signer.delegated_eq_iff`, `Chain.Signer.external_eq_iff`, `Chain.Signer.delegated_append_ne`).
- A step is refused with `noSuchRule` exactly when its index is out of range (`*_eq_error_iff`, `*_eq_noSuchRule_iff`), `raiseThreshold` with `thresholdLowered` exactly when the new threshold is below the rule's (`RuleSet.raiseThreshold_eq_thresholdLowered_iff`), and `lowerValidUntil` with `validUntilRaised` exactly when the new last ledger is after the rule's (`RuleSet.lowerValidUntil_eq_validUntilRaised_iff`). Each cap step's other refusals happen exactly in the case they name (`RuleSet.addCap_eq_capPresent_iff`, `RuleSet.addCap_eq_invalidCap_iff`, `RuleSet.lowerCapLimit_eq_noCap_iff`, `RuleSet.lowerCapLimit_eq_limitRaised_iff`, `RuleSet.lowerCapLimit_eq_invalidCap_iff`, `RuleSet.lengthenCapPeriod_eq_noCap_iff`, `RuleSet.lengthenCapPeriod_eq_periodShortened_iff`).

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
- Expiry: an accepted authorization chooses no rule whose last ledger is before its ledger (`RuleSet.authorize_validUntil`, `Chain.RuleSet.authorize_validUntil`).
- Generations: it chooses no rule issued under another generation, so once the generation is not `g`, a rule issued under `g` authorizes nothing and a rule set issued under `g` accepts only the empty batch (`RuleSet.authorize_generation`, `RuleSet.authorize_not_chosen_of_stale`, `RuleSet.authorize_contexts_nil_of_stale`, and the `Chain` versions); no step changes a rule's generation, so everything derived from a rule set issued under `g` is issued under `g` (`RuleSet.attenuate_generation`, `RuleSet.attenuateAll_generation`, `RuleSet.attenuateAll_generation_eq`, and the `Chain` versions).
- Signers: every signer an accepted authorization authenticated is a signer of a rule it chose (`RuleSet.authorize_signers`, `Chain.RuleSet.authorize_signers`).
- A refusal changes nothing (`RuleSet.step_of_error`); an accepted authorization keeps one record per rule (`RuleSet.authorize_length`).
- The stored record of a capped rule is the cap check's own run over the calls a run charged to it, and a rule without a cap keeps its record (`RuleSet.run_get`, `RuleSet.run_get_of_cap_none`, `RuleSet.spent_eq_recorded`).
- Window safety for every capped rule and every run from empty records: the spends recorded for the rule in every window of eviction sum to at most its limit (`RuleSet.window_le_limit`), and so do those in every window of `period` consecutive ledgers from ledger 1 on (`RuleSet.period_le_limit_of_pos`), or in every window when every authorization is at ledger 1 or later (`RuleSet.period_le_limit`).
- The stored record is exactly the rule's spends in the window at its last spend, with their sum as total (`RuleSet.run_eq_window`), and never holds more than 1000 entries (`RuleSet.run_history_length_le`).
- Narrowing as trace inclusion: for each step and every chain of them, every run of authorizations the derived rule set accepts from its empty records, the root accepts from its own, with each choice renumbered by the map `dropRule` induces (`RuleSet.attenuate_traceNarrower`, `RuleSet.attenuateAll_traceNarrower`, `Attenuation.source_dropRule`, `Attenuation.source_eq_of_ne_dropRule`, and the `Chain` versions). They rest on `RuleSet.Refines.traceNarrower` and `Cap.check_of_narrower_suffix`; trace inclusion composes (`RuleSet.TraceNarrower.trans`).
- The steps keep every cap valid (`RuleSet.attenuate_capsValid`, `RuleSet.attenuateAll_capsValid`).

**Budgets on the delegation tree.** `RuleCore.Budget` models the tree and its
three operations; runs are lists of spends, delegations and refills, from any
tree.

- Budget safety: for every run from a well-formed tree with nothing spent, the total successfully spent at or under any node is that node's spent amount and never exceeds its allowance (`Budget.Tree.spentUnder_le_allowance`, `Budget.Tree.spentUnder_eq_spent`, from `Budget.Tree.spent_run`). Nothing relates allowances to each other, so the bound holds however much children's allowances oversubscribe their parent's.
- A successful spend adds the amount to the spender and every ancestor, and changes nothing else (`Budget.Tree.spend_ok_charges`, `Budget.Tree.spend_ok_unchanged`, `Budget.Tree.spend_ok_length`, `Budget.Tree.spend_ok_parentOf`, `Budget.Tree.spend_ok_allowance`); a refused operation changes nothing (`Budget.Tree.step_of_error`, `Budget.Tree.run_cons_of_error`).
- The node an `overdrawn` refusal names is on the spender's chain and cannot take the amount, and every node before it on the chain can (`Budget.Tree.spend_overdrawn`). On a well-formed tree, a spend of a non-negative amount at an existing node succeeds exactly when every node on its chain can take it (`Budget.Tree.spend_accepts_iff`, `Budget.Tree.spend_error_overdrawn`).
- A delegation appends exactly the new child, with nothing spent, whatever its allowance; a refill raises exactly one allowance (`Budget.Tree.delegate_ok_iff`, `Budget.Tree.refill_ok_iff`).
- Every operation and every run keeps the tree well formed and every spent amount within its allowance (`Budget.Tree.run_valid`, `Budget.Tree.run_withinAllowance`, and the single-operation versions).

**Documents and their lowering.** `RuleCore.Document` models Perch's
documents, what they mean on chain (`Doc.allows`, `Doc.authorize`, written from
Perch's and OpenZeppelin's source without reference to the lowering), the
lowering, scoped documents and the account's generation. The theorems take
the document to be valid (`Doc.Valid`), as every document Perch's validation
accepts is.

- Compile soundness: each lowered rule allows exactly what its document rule allows, under every signer list (`Doc.lowerRule_allows`, `Doc.lowerRules_allows`); the admin document's lowering allows what the document allows or what the recovery rule allows, exactly the document's verdict with no recovery configured (`Doc.lower_allows`, `Doc.lower_allows_of_recovery_none`).
- Through `authorize`: on every authorization the lowering accepts exactly when the document accepts, with the same records, the recovery controller's check read as every `apply_doc` call (`Doc.lower_authorize`, `Doc.lower_authorize_of_recovery_none`). The recovery rule is the one over-approximation: whatever the document accepts under a controller check that allows only `apply_doc`, the lowering accepts (`recoveryRule_allows`, `Doc.lower_authorize_of_check`).
- Scoped documents: the scoped lowering allows and accepts exactly what the scoped document does in the generation it was issued under (`Doc.lowerScoped_allows`, `Doc.lowerScoped_authorize`); no rule it lowers to, and no rule set attenuated from them, allows a call to the account or to its recovery controller, ZK adapter or pool (`Doc.lowerScoped_contract`, `Doc.lowerScoped_allows_excluded`, `Doc.lowerScoped_attenuateAll_excluded`, `Doc.mem_excluded`).
- The generation: every scoped rule carries the generation it was issued under and no admin rule carries one (`Doc.lowerScoped_generation`, `Doc.lower_generation`); a run of the account advances the generation by exactly the recoveries it completes (`Account.run_generation`), so after a completed recovery every grant attenuated from an earlier scoped document accepts only the empty batch, and the admin rules authorize the same in every generation (`Account.issued_stale`, `Account.adminRules_authorize_generation`, `RuleSet.authorize_generation_none`).
- The chain: anything `authorize` accepts under a grant attenuated from a valid scoped document's rules is allowed by that document, touches no excluded contract, and is made in the generation it was issued under; every run the grant accepts from empty records, the scoped rules accept (`Account.chain`, `Account.chain_trace`, `Account.chain_after_recovery`).

**The Soroban models.** `RuleCore.Soroban` models soroban-env-host 29.0.1's
storage, rollback, `require_auth` and `__check_auth`. The theorems are about
the models; that the models describe the host is tested, below.

- Storage is a map: a slot reads what was last written to it, and a write or removal changes no other slot, durability, or contract (`Store.get_set`, `Store.get_set_ne`, `Store.get_remove`, `Store.get_remove_ne`, `Store.has_iff`, `Store.get_set_durability`, `Store.get_set_contract`); an operation is refused exactly when its key holds a muxed address (`Op.apply_eq_none_iff`).
- What `rule-eval` reads of a context (`AuthFn.toChain`): a creation is a creation, which no rule allows, whether its executable is uploaded Wasm or an external reference (CAP-85), read as more than a hash's 32 bytes (`AuthFn.allows_create`, `Executable.id_externalRef_length`); a `u32` is `other` of `u32Xdr`, the reading Perch's lowering compares a `u32` with (`Val.toChain_u32`); a value is read as an `i128`, `u64`, `bool`, bytes, string or symbol only when it is one, and as an address's XDR only when it is that address (`Val.toChain_eq_i128_iff` and the others, `Val.toChain_eq_address_xdr_iff`, `Address.xdr_injective`). The host's encoding of contexts reads back as the same contexts (`Executable.ofVal_toVal`, `AuthFn.ofVal_toVal`, `contextsOfVal_toVal`).
- What `__check_auth` receives: in every transaction, each `__check_auth` call receives its payload's tree in preorder, root first, so never an empty batch (`Tx.run_checkAuth_contexts`); a delegate receives the authenticated entry's payload and contexts (`authenticate_checkAuth`); the payload binds the address exactly for `ADDRESS_V2` and delegated credentials (`Entry.preimage_address`).
- The containment link: in every transaction, each `require_auth` an authorization entry satisfies is for a context of that entry's tree, and every rule set the address's `__check_auth` checks with `rule-eval` allows it (`Tx.run_authorized_allowed`, from `requireAuth_spec`, `authenticate_spec`, `runAccount_spec` and `Tracker.extend_spec`). So a call the host lets through on an account's signature is inside the rules the account evaluates, and with `allows_all_eq` the translated evaluator gives the same verdict.
- What `__check_auth` sees: it runs on the world the requiring call left and reads that store, the call's own instance writes included (`authenticate_store`, `runAccount_get`).
- Rollback: a failed call leaves storage and the used nonces as they were; a caught failure lets the caller go on, an uncaught one fails it; a failed transaction changes neither (`execCall_fail`, `execStep_call_caught`, `execStep_call_uncaught`, `Tx.run_fail`).

**The translation equals the model.** `RuleCore.Equiv` relates
`formal/RuleCore/Extracted/RuleEval.lean`, which Charon and Aeneas generate
from `crates/rule-eval`, to the chain vocabulary through denotation functions.

- `allows_eq` and `allows_all_eq`: on every input, the translated `allows` and `allows_all` return `ok` of the model's verdict on the denotations, authenticated signers included. `ok` rules out both a panic and divergence, so these theorems also prove that the evaluator terminates and never panics. `signers_met_eq` and `signed_count_eq` do the same for the signer requirement, `functions_match_eq` for a rule's functions, and `val_in_eq` and `bytes_starts_with_eq` for `ArgIn` and `ArgStrPrefix`.
- `drop_rule_eq`, `restrict_functions_eq`, `remove_signers_eq`, `raise_threshold_eq`, `remove_functions_eq` and `add_cond_eq`: on every input, each attenuation step returns the model's result, `noSuchRule` and `thresholdLowered` included. `add_cond_eq` takes the stated rule `CondRoom` and `remove_functions_eq` the stated rule `FunctionsRoomAt`, which every rule with a function list meets; `add_cond_full` and `remove_functions_full` show the rules are exact.
- `check_spend_eq`: on every input, the translated `check_spend` returns `ok` of the cap model's check on the denotations, so it terminates and never panics. It needs no stated bound.
- `authorize_eq`: on every input, the translated `authorize` returns `ok` of the model's authorization on the denotations, every refusal included, so it terminates and never panics. `check_choices_loop_eq`, `signers_chosen_eq` and `charge_all_loop_eq` prove its passes. `add_cap_eq`, `lower_cap_limit_eq`, `lengthen_cap_period_eq` and `lower_valid_until_eq` do the same for the cap and expiry steps.
- `spend_eq`, `delegate_eq` and `refill_eq`: on every input, the translated budget operations return `ok` of the budget model's operation on the denotations, every refusal included, so they terminate and never panic. None needs a stated bound. `check_chain_loop_eq` and `charged_loop_eq` prove the checking walk and the charging walk.
- `lower_eq`, `lower_scoped_eq` and `excluded_eq`: on every input, the translated lowering returns `ok` of the model's lowering on the denotations, the scoped lowering's refusals included, so it terminates and never panics. They take the stated rule `LowerRoom`, which `lower_full` shows exact. `u32_xdr_eq`, `named_eq`, `threshold_of_eq`, `lower_functions_eq`, `strings_within_eq`, `lower_pred_eq`, `lower_conds_eq`, `lower_rule_eq` and `lower_rules_eq` prove its steps.
- Every denotation is injective (`denoteVal_injective`, `denoteContext_injective`, `denoteFunctions_injective`, `denoteSigner_injective`, `denoteCap_injective`, `denoteRule_injective`, `denoteRules_injective`, `denoteOutcome_injective`, `denoteRecord_injective`, `denoteSpend_injective`, `denoteRefusal_injective`, `denoteAuthorized_injective`, `denoteTree_injective`, `denoteBudget_injective`, `denoteDoc_injective`, `denoteScoped_injective`, ...).

**The model's theorems hold of the translation.** `RuleCore.Extracted`
states these on the translated functions alone:

- each step that returns `Ok` narrows (`drop_rule_narrower`, `add_cond_narrower`, `remove_functions_narrower`, `restrict_functions_narrower`, `remove_signers_narrower`, `raise_threshold_narrower`, `add_cap_narrower`, `lower_cap_limit_narrower`, `lengthen_cap_period_narrower`, `lower_valid_until_narrower`, `Step.narrower`);
- chains stay inside their root (`Narrower.trans`, `Derives.narrower`);
- a narrower rule set accepts a batch only if its ancestor does (`allows_all_of_narrower`, `Derives.allows_all`);
- no creation is allowed (`allows_create`, `allows_all_create`);
- `argEq` needs the same constructor (`val_eq_iff`, `val_eq_kind`, `val_eq_other_bytes`, `val_eq_string_symbol`, `cond_holds_argEq_iff`, `cond_holds_argEq_false_of_kind_ne`); `ArgIn` is `ArgEq` for one of its values and `ArgStrPrefix` needs a string starting with the prefix (`cond_holds_argIn_iff`, `cond_holds_argStrPrefix_iff`);
- byte strings compare exactly (`bytes_eq_iff`, `rule_allows_call`, `rule_allows_prefix_false`, `rule_allows_extension_false`); a list matches exactly its functions and a wildcard every function it does not exclude (`functions_match_only_iff`, `functions_match_anyExcept_iff`);
- an `authorize` that returns `Ok` means the translated `allows_all` accepts the batch (`authorize_allows_all`); a run of the translated `authorize` returns records denoting the model's run (`runAuthorizations_eq`), keeps them after a refusal (`runAuthorizations_of_err`), and from empty records bounds every window of each capped rule's spends by its limit, stores exactly the in-window spends and holds at most 1000 entries per record (`runAuthorizations_window_le_limit`, `runAuthorizations_window`, `runAuthorizations_length_le`);
- each translated step, and every chain of them, is trace inclusion along its renumbering (`StepAlong.traceNarrower`, `DerivesAlong.traceNarrower`, from `traceNarrower_of_denote`);
- an `authorize` that returns `Ok` chose no expired rule and no rule of another generation, and authenticated no signer outside its chosen rules (`authorize_valid_until`, `authorize_generation`, `authorize_not_chosen_of_stale`, `authorize_contexts_nil_of_stale`, `authorize_signers`); no translated step changes a rule's generation (`StepAlong.generation`, `DerivesAlong.generation`, `DerivesAlong.generation_eq`);
- a run of the translated `check_spend` returns a record denoting the model's run (`runSpends_eq`), so from the empty record it holds at most 1000 entries and is the recorded spends in its window (`runSpends_length_le`, `runSpends_window`); the translated check refuses a negative amount, changes nothing on a zero amount and refuses a spend before the newest recorded ledger (`check_spend_negative`, `check_spend_zero`, `check_spend_before_newest`);
- a run of the translated `spend`, `delegate` and `refill` returns a tree and a log of spends denoting the model's run (`runBudget_eq`), so it keeps the tree well formed and every spent amount within its allowance (`runBudget_valid`, `runBudget_withinAllowance`), and from a well-formed tree with nothing spent the total spent at or under each node is its spent amount and within its allowance (`runBudget_spentUnder_eq_spent`, `runBudget_spentUnder_le_allowance`); a translated spend charges exactly the chain, its `Overdrawn` refusal names the first node that cannot take the amount, and on a well-formed tree it succeeds exactly when every node on the chain can (`budget_spend_charges`, `budget_spend_unchanged`, `budget_spend_overdrawn`, `budget_spend_accepts_iff`);
- the translated `allows` and `authorize` on the rules the translated `lower` returns give the document's verdicts, with the same records (`lower_allows`, `lower_allows_of_recovery_none`, `lower_authorize`), and the same for scoped documents (`lower_scoped_allows`, `lower_scoped_authorize`); no rule set the translated `lower_scoped` returns, or translated steps derive from it, allows a call to the account or an excluded contract (`lower_scoped_allows_excluded`, `derives_allows_excluded`); scoped rules carry their generation and admin rules none (`lower_scoped_generation`, `lower_generation`); and the chain composes on the translated `excluded`, `lower_scoped`, steps and `authorize` (`chain`, `chain_trace`);
- signers compare exactly (`signer_eq_iff`, `signer_eq_delegated_external`); authenticating more signers never refuses (`allows_of_subset`, `allows_all_of_subset`); repeats and order in either list change nothing (`allows_congr`, `allows_all_congr`, `rule_allows_congr_signers`); threshold 0 ignores the signers, a threshold of all distinct signers needs every one, and a threshold above them allows nothing (`rule_allows_threshold_zero`, `signers_met_all_iff`, `rule_allows_false_of_lt`).

**Stated rules.** These are not theorems. [`TRUSTED.md`](TRUSTED.md) states
each one.

- *The empty batch*: every rule set allows the empty batch (`RuleSet.allowsAll_nil`). A batch collected from a Soroban authorization tree is never empty. A caller that builds batches another way must reject the empty batch.
- *No creation* is a property of the chain vocabulary. The generic model makes no such claim.
- *`CondRoom`*: the rule `add_cond` extends has fewer than `Usize.max` conditions.
- *`FunctionsRoom`*: a wildcard `remove_functions` extends excludes at most `Usize.max` functions together with the removed ones. Every rule with a function list meets it.
- *Ledgers start at 1*: every call of the cap check is made at ledger 1 or later, as on Stellar, whose genesis ledger is ledger 1. Only `Cap.period_le_limit` takes it.
- *`LowerRoom`*: a document configuring recovery has fewer than `Usize.max` rules, and a capped rule fewer than `Usize.max` argument predicates.

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
and thresholds here ([`ARCHITECTURE.md`](ARCHITECTURE.md#openzeppelins-rules-and-what-perch-installs))
is read from OpenZeppelin's source, and neither proven nor tested. So is the correspondence between `check_spend` and the
spending-limit policy at the revision Perch pins
([`ARCHITECTURE.md`](ARCHITECTURE.md#mirroring-perch)), the correspondence
between `authorize` and OpenZeppelin's `do_check_auth` there
([`ARCHITECTURE.md`](ARCHITECTURE.md#mirroring-openzeppelin)), the
correspondence between `authorize`'s expiry and signer checks and
OpenZeppelin's `valid_until` and `UnauthorizedSigner` checks there
([`ARCHITECTURE.md`](ARCHITECTURE.md#milestone-4-the-rule-model-perch-lowers-to)),
what Perch installs on OpenZeppelin's account
([`ARCHITECTURE.md`](ARCHITECTURE.md#openzeppelins-rules-and-what-perch-installs)), and
the reading that a record of 816 or more entries does not fit in one mainnet
ledger entry.

That the document's meaning is what Perch's installed rules do on chain, and
that every document Perch's validation accepts is valid, are read from Perch's
and OpenZeppelin's source ([`ARCHITECTURE.md`](ARCHITECTURE.md#what-a-document-means)).
Perch at `dff2a73` has no scoped documents and no generation that advances only
when a recovery completes; building `apply_scope`, that counter, and the
refusal of an admin document naming a contract a live scoped rule reaches is
M6's ([`ARCHITECTURE.md`](ARCHITECTURE.md#what-perch-adds-in-m6)). Decoding a
document's strkeys, installing exactly the lowered rules and mapping
OpenZeppelin's rule ids to their indices are the shell's
([`ARCHITECTURE.md`](ARCHITECTURE.md#the-shells-part-of-the-lowering)).
[`ARCHITECTURE.md`](ARCHITECTURE.md#what-does-not-compose) lists what of the
chain rests on these.

The budget operations take the node, the amount and the tree as given. Which
node an authorization's spend is charged to, storing the tree only on `Ok`, and
accepting a refill only on the owner's authority are the shell's duties
([`ARCHITECTURE.md`](ARCHITECTURE.md#milestone-3-the-budget-tree)), for the
grant signer in M6; nothing here checks them.

## What is tested

- **Conformance vectors.** `conformance/vectors/*.json` holds 161 vectors, each a rule set, a batch, the authenticated signers, the per-context and whole-batch verdicts, and attenuation steps with their results. The Lean model computes every expected result. Of these, 61 are named cases and 100 are drawn from a seeded generator. The signer cases cover thresholds 0, 1, k, all signers and above, repeated signers in either list, delegated and external signers with equal bytes, missing signers, batches under one authenticated list, and both signer steps. The cap cases cover each cap step and each of its refusals, chains mixing them with the other steps, and verdicts that ignore caps. The Milestone 4 cases cover the wildcard and its exclusions, `argIn`, `argStrPrefix` and strings against symbols, `removeFunctions` on a wildcard, `restrictFunctions`, `lowerValidUntil` and its refusal, and verdicts that read no last ledger or generation. CI regenerates them from the model and fails on any difference (`conformance.yml`). The runner in `conformance/runner` checks `rule-eval` against every vector: `rule_eval_agrees_with_every_vector`, `vectors_cover_every_kind` and `a_wrong_expectation_is_reported`. [`conformance/README.md`](conformance/README.md) documents the format, so other implementations can run the same vectors.
- **Cap traces.** `conformance/vectors/caps/*.json` holds 72 traces, each a cap, a starting record and calls with the outcome and record the Lean model computes for each. Of these, 22 are named and 50 drawn from the same seeded generator; together they cover every refusal, ledger 0, `u32::MAX`, the history bound and caps that are not valid to install. CI regenerates them with the vectors. The runner checks `check_spend` against every trace: `rule_eval_agrees_with_every_cap_trace`, `cap_traces_cover_every_outcome` and `a_wrong_cap_expectation_is_reported`.
- **Authorization traces.** `conformance/vectors/authorize/*.json` holds 76 traces, each a rule set, its starting records and authorizations with the outcome and records the Lean model computes for each. Of these, 26 are named and 50 drawn from the same seeded generator; they cover every refusal, expiry at and after the last ledger, generations, signers outside the chosen rules and the order of the refusals, two contexts charging one rule, a refusal discarding a batch's charges, windows rolling, ledger 0, the history bound, rules keeping their own records, and the rule sets each cap step, `lowerValidUntil`, `restrictFunctions` and `drop_rule` derive from one rule set, run on the same authorizations. The runner checks `authorize` against every trace: `rule_eval_agrees_with_every_authorization_trace`, `authorization_traces_cover_every_outcome` and `a_wrong_authorization_expectation_is_reported`.
- **Budget traces.** `conformance/vectors/budget/*.json` holds 69 traces, each a starting tree and spends, delegations and refills with the outcome and tree the Lean model computes for each. Of these, 19 are named and 50 drawn from the same seeded generator; they cover oversubscribed siblings, a spend exhausting a middle ancestor, the refusal naming the nearest overdrawn node, overflowing sums, malformed and empty trees, delegation then spend, refills and several roots, and every refusal but `tree_full`, which needs `u32::MAX` nodes. The runner checks the budget operations against every trace: `rule_eval_agrees_with_every_budget_trace`, `budget_traces_cover_every_outcome` and `a_wrong_budget_expectation_is_reported`.
- **Document traces.** `conformance/vectors/documents/*.json` holds 57 traces, each a document, the account, for a scoped document the admin document and the generation, the rules the Lean model lowers it to, and authorizations with the document's own verdict and records, computed by `Doc.authorize`. Of these, 17 are named, after the probes Perch's harness runs on OpenZeppelin's smart account and the scoped cases, and 40 are drawn from the same seeded generator; every document is one Perch's validation accepts. The runner lowers each document with `lower` or `lower_scoped` and checks the rules and every verdict: `rule_eval_agrees_with_every_document_trace`, `document_traces_cover_every_construct_and_outcome` and `a_wrong_document_expectation_is_reported`.
- **Soroban vectors.** `conformance/vectors/soroban` holds what the Soroban models compute: 5 value vectors (65 values with their XDR, their reading by `rule-eval` and whether they may be keys), 14 context vectors (values as `__check_auth` receives them, with the contexts read from them, or none), 35 storage traces (636 operations; 5 named, 30 drawn from the seeded generator) and 95 host traces (35 named, 60 drawn from the generator; 156 transactions with their outcomes, every event and the storage after each). The named host traces follow the cases of the host's own behaviour listed in [`ARCHITECTURE.md`](ARCHITECTURE.md#the-vectors-and-the-harness). CI regenerates them with the other vectors. The runner checks `soroban-facade`'s plain code against them: its XDR, its reading of contexts and its conversion for `rule-eval`, and its plain storage (`the_facade_writes_and_reads_every_value_as_the_model_does`, `the_facade_reads_every_context_vector_as_the_model_does`, `plain_storage_agrees_with_every_storage_trace`, `the_soroban_vectors_cover_every_kind`, `a_wrong_soroban_expectation_is_reported`).
- **The models against the host.** `conformance/host/p29` replays the Soroban vectors on soroban-env-host 29.0.1 through soroban-sdk 29.0.1's testutils, with enforcing authorization (`set_auths`): every value crosses the host unchanged (`every_value_crosses_the_host_unchanged`); every storage operation returns what the model gives, through the facade's real implementation (`storage_on_the_host_agrees_with_every_storage_trace`); and every transaction of every host trace succeeds or fails as the model says, with the same events (each `__check_auth`'s payload, signature and contexts, as the host's value, as the facade's real implementation reads them and as `rule-eval` reads those; each read; each `require_auth` that held) and the same storage afterwards (`the_host_agrees_with_every_host_trace`). SDK 29's `auth::Context` reads every context vector exactly when the model does, and writes what it read back as the same XDR (`the_sdk_reads_every_context_vector_as_the_model_does`), and the facade's real implementation refuses an executable tag as a key or a value, which the host itself takes (`the_facade_refuses_an_executable_tag`). `a_wrong_host_expectation_is_reported` checks that a changed outcome, event, payload, read or slot fails, and `the_host_runs_the_pinned_protocol` that the ledger is at protocol 29. `conformance/host/p30` replays the same vectors, with the same tests, on soroban-env-host 30.0.0 through soroban-sdk 30.0.0-rc.1's testutils, at protocol 30. The facade's real implementation is built against soroban-sdk 29.0.1, so there storage, `require_auth` and the reading of contexts go through the SDK directly. `p29` also runs that way, which sets the host version apart from the facade. Every vector agrees on both hosts, so no host behaviour the vectors exercise changed from 29.0.1 to 30.0.0. The CI job is `host.yml`, with three entries: 29.0.1 through the facade, 29.0.1 through the SDK and 30.0.0 through the SDK.
- **The host's own tests.** The authorization and storage tests of soroban-env-host 29.0.1 (`src/test/auth.rs`, `auth_delegation.rs`, `invoker_auth.rs`, `storage.rs` and `frame.rs`, 74 tests) are transcribed into 34 host traces and 5 storage traces in `conformance/vectors/soroban/seed`, each case keeping the host test's own expectation. The models express 27 of the tests, 155 of their 213 cases, and give the host test's outcome in all 155; the generator writes no vectors when one differs. The other 58 cases and 47 tests fall outside the models' stated scope: recording authorization, `authorize_as_current_contract`, `require_auth` inside `__check_auth`, time to live, footprints, size limits, Stellar-account signers and delegates, validation of the delegate list, and host-internal functions. `seed/coverage.json` lists each with its reason. The transcribed traces replay on both hosts (`the_host_agrees_with_every_seed_trace`, `storage_on_the_host_agrees_with_every_seed_storage_trace`).
- **The facade's own tests** (`crates/soroban-facade/tests`) cover its XDR refusals (trailing bytes, nonzero padding, an out-of-range bool, absent vectors and maps, kinds no contract holds, nesting past the limit), addresses as `ScAddress` XDR, a `u32` as `rule-eval`'s `u32_xdr`, a whole batch refused for one unknown context, creations from Wasm and from an external reference reaching `rule-eval` as creations, and the plain implementation's storage and `require_auth`.
- **Exhaustive small universes.** `crates/rule-eval/tests` checks `allows` against an ordinary-Rust reading of the semantics over every rule set of up to two rules, wildcards and all four conditions included, and 407 contexts (`allows_agrees_with_the_reference_reading`). It also checks:
  - `allows_all` against `allows` (`allows_all_is_the_conjunction_of_allows`);
  - that no rule set allows a creation (`no_rule_allows_a_creation`);
  - that every step builds its result and only narrows (`every_step_builds_its_result_and_only_narrows`);
  - that every two-step chain stays inside its root (`every_two_step_chain_stays_inside_its_root`);
  - `signers_met` against the reference reading over every signer list of up to three signers, thresholds 0 to 4 and 63 authenticated lists (`signers_met_agrees_with_the_reference_reading`), that authenticating more signers never refuses and that order and repeats change nothing (`authenticating_more_signers_never_refuses`, `the_same_authenticated_signers_in_another_order_or_repeated_give_the_same_verdict`);
  - that every step on rules with signers only narrows under every authenticated list, alone and in two-step chains (`signer_steps_only_narrow_under_every_authenticated_list`);
  - `check_spend` against a plain reading of the check on every run of up to three calls from 25 under 16 small caps, and that every such run keeps every window within the limit (`check_spend_agrees_with_the_reference_reading`, `every_short_run_stays_within_every_window`);
  - `authorize` against a plain reading on 146,544 inputs (every rule set of up to two rules from five capped and uncapped rules and an expiring wildcard issued under a generation, 142 batches with their choices, three signer lists, two ledgers, two generations, two starting records), with every accepted batch allowed by `allows_all` and the expired, stale-generation and unauthorized-signer refusals each occurring (`authorize_agrees_with_the_reference_reading`); 8,653 runs of up to three authorizations over two capped rules, each step against the reading, every window within its limit and every stored record the in-window spends (`authorize::every_short_run_stays_within_every_window`); and trace inclusion for each cap step, `lower_valid_until`, `drop_rule` with its renumbering and chains, over the same runs (`every_step_is_trace_inclusion`);
  - `spend`, `delegate` and `refill` against a plain reading on 152,355 inputs (1,451 trees of up to three nodes, well formed or not, five indices and seven amounts), and over 300 random runs of 40 operations, each node's spent amount stays the total spent at or under it and within its allowance (`every_operation_agrees_with_a_plain_reading_on_small_trees`, `spent_under_a_node_stays_within_its_allowance_over_random_runs`).
- **Lowering tests** (`crates/rule-eval/tests/lowering.rs`) cover what `lower` builds for every construct, and, through `allows` and `authorize`, the verdicts of Perch's probes: a capped rule listing `approve` authorizes only `transfer`, a capped rule without functions only `transfer`, an extra signer is refused, `not-after-ledger 600` authorizes at 599 and not at 600, an over-long `string-in` value never matches, a constraint-free rule allows every function, and `string-prefix` reads strings and not symbols; and for scoped documents the generation stamp, each refusal and the excluded set.
- **Unit tests** cover every value constructor and every condition, the wildcard, `restrict_functions`, `remove_functions` on a wildcard, `lower_valid_until`, that no step changes a generation, expiry at its boundary, stale generations, signers outside the chosen rules and the order of those refusals, missing, wrong-typed and `u32::MAX` indices, exact byte and signer comparison, each threshold case, repeated signers, and each step at out-of-range indices and, for `raise_threshold`, below the current threshold. For caps they cover each refusal and its precedence, eviction at and beside the cutoff, the cutoff at ledger 0 and at `u32::MAX`, the history bound and each checked sum. For `authorize` they cover each refusal and its precedence, choices checked before charges, missing and wrong-typed amounts, charges accumulating, refusals discarding a batch, the window rolling and the empty batch; for the cap steps, what each builds and each refusal. For budgets they cover charging the chain, the nearest overdrawn node, oversubscribed siblings, an exhausted middle ancestor, overflowing sums, malformed trees, each refusal and its precedence, zero spends, delegation and refills.
- **CI gates.** Every pull request and every push to `main` runs:
  - `cargo test`, `cargo clippy -D warnings`, and builds for native and `wasm32v1-none` in the release and contract profiles, on the pinned nightly and on stable, of `rule-eval` and of `soroban-facade` with and without its real implementation (`rust.yml`);
  - the Soroban vectors, the transcribed host tests included, replayed on soroban-env-host 29.0.1 through the facade and through the SDK, and on soroban-env-host 30.0.0 through the SDK, with the harness linted in each (`host.yml`);
  - `lake build` of every module (`lean.yml`), which also rejects `sorry`, `admit`, `partial`, `unsafe`, `native_decide`, `implemented_by`, `extern` and `axiom` in every Lean source, the translation included;
  - the axioms record in `Axioms.lean`, checked under `#guard_msgs` as part of `lake build`;
  - re-extraction with Charon `--error-on-warnings` and Aeneas `-warnings-as-errors`, which fails on any difference from the committed translation (`extraction.yml`);
  - the claim-ledger check (`claims.yml`, plus a step in `lean.yml`).

The vectors' and traces' JSON encoding and decoding are not verified (see
[`TRUSTED.md`](TRUSTED.md#the-conformance-encoding)). The Soroban vectors run
on two host versions: 29.0.1, the host of the protocol the network runs today,
and 30.0.0, the next. The models describe protocol 29; that they also hold on
30.0.0 is tested only as far as the vectors reach.

## What is trusted

[`TRUSTED.md`](TRUSTED.md) lists what the proofs rest on:

- rustc;
- Charon and Aeneas at the pinned commits;
- Aeneas's Lean library: its `Result`, its `loop`, and its model of each Rust library item the evaluator calls, listed one by one;
- Lean's kernel;
- the denotation functions, which are part of the specification;
- the document's meaning, which says what Perch's installed rules do on chain and is part of the specification;
- the Soroban models, which say what soroban-env-host 29.0.1 does and are part of the specification, within the domain [`TRUSTED.md`](TRUSTED.md#the-soroban-models) states;
- soroban-sdk 29.0.1, soroban-env-host 29.0.1 and stellar-xdr 28.0.0, and soroban-sdk 30.0.0-rc.1, soroban-env-host 30.0.0 and stellar-xdr 30.0.0, the testutils path the harness drives each host through, and each SDK item the facade's real implementation calls, listed one by one;
- the facade's XDR, its reading of contexts and its conversion for `rule-eval`, which vectors test and nothing proves equal to the models;
- the host harness's payload hashing and value passing;
- the stated rules above.

## Building and checking

`flake.nix` pins one Aeneas commit (`ab34bd28`), the Charon commit it fixes
(`7b462d9`), the Rust nightly Charon reads (`nightly-2026-09-17`,
`rust-toolchain.toml`) and Lean `v4.35.0` (`formal/lean-toolchain`).
Evaluating the flake fails if these disagree.

```sh
# Rust: tests (including the conformance runner and the host harness), lint, builds
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo build -p rule-eval --release --target wasm32v1-none --locked
cargo build -p rule-eval --profile contract --target wasm32v1-none --locked
SOROBAN_SDK_BUILD_SYSTEM_SUPPORTS_SPEC_SHAKING_V2=1 \
  cargo build -p soroban-facade --features sdk --profile contract --target wasm32v1-none --locked

# The Soroban vectors on soroban-env-host 29.0.1, through the facade and
# through the SDK, and on soroban-env-host 30.0.0
cargo test --locked --manifest-path conformance/host/p29/Cargo.toml
cargo test --locked --manifest-path conformance/host/p29/Cargo.toml --no-default-features
cargo test --locked --manifest-path conformance/host/p30/Cargo.toml

# Lean: the model, the translation, the equivalence and every theorem
cd formal && lake exe cache get && lake build && cd ..

# Extraction: regenerate the translation, or check it is current (needs Nix)
tools/extract.sh
tools/extract.sh --check

# Conformance vectors, the cap, authorization, budget and document traces and the Soroban vectors: regenerate from the Lean model
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
| `crates/rule-eval/` | The rule-set evaluator, its attenuation steps, the spending-cap check, `authorize`, the budget tree and the lowering of documents: `no_std`, no dependencies, `forbid(unsafe_code)`. |
| `crates/soroban-facade/` | The SDK subset as plain data and interfaces, its XDR, the reading of `__check_auth`'s contexts and their conversion for `rule-eval`; a plain implementation and, with the `sdk` feature, the real one over soroban-sdk 29.0.1. `no_std`, `forbid(unsafe_code)`. |
| `conformance/` | The vectors (`vectors/`), cap traces (`vectors/caps/`), authorization traces (`vectors/authorize/`), budget traces (`vectors/budget/`), document traces (`vectors/documents/`) and Soroban vectors (`vectors/soroban/`, with the host's own tests transcribed in `vectors/soroban/seed/`), the Lean generator that computes them (`generator/`), the Rust runner (`runner/`) and the host harness (`host/`, one crate per host version sharing `host/src` and `host/tests`: `p29` in the workspace, `p30` a workspace of its own with its own lock). |
| `formal/` | The Lean package: `Model/`, `Vocab/`, `Soroban/`, `Extracted/` (generated), `Equiv/`, `Theorems/` and `Axioms.lean`. |
| `tools/extract.sh` | Runs Charon and Aeneas on `crates/rule-eval`. |
| `tools/check-claims`, `tools/tests/` | The claim-ledger checker and its self-tests. |
| `claims.yaml` | The claim ledger. |
| `flake.nix`, `flake.lock`, `rust-toolchain.toml` | The pinned toolchain. |
| `.github/workflows/` | `rust.yml`, `lean.yml`, `extraction.yml`, `conformance.yml`, `claims.yml`, `host.yml`. |
| `ARCHITECTURE.md`, `TRUSTED.md` | The design and later milestones; what is trusted. |

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT), at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this repository, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
