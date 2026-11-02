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

- **Grant inside scope.** A delegated grant is reached from its scope by attenuation steps, so it allows only what the scope allows, under any signers. Milestones 1 and 2 prove this for rule matching and signer requirements (`Derives.narrower`, `Derives.allows_all`). The spending-cap check is proven on its own ([Milestone 2: spending caps](#milestone-2-spending-caps)). Caps on rules come next, and budgets on the delegation tree in M3.
- **Scope inside the owner's authority.** A scoped document compiles to rules that reach none of the account, its recovery or the ZK adapter. That is M4.
- **Recovery.** A completed recovery bumps a generation, and every scoped rule issued under an older generation then authorizes nothing. That is also M4.
- **The code is the model.** The Rust that Perch's smart account, the grant signer, the agent host and the relay run is proven equal to the Lean model the theorems are about (M1 for rule matching and attenuation, M2 for signers). Soroban's own behaviour enters through Lean models that are tested against the host (M5).

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

- a `Rule` has a `scope : Ctx → Bool` and a list of conditions `Ctx → Bool`, plus the signers and threshold of [Milestone 2](#milestone-2-signers);
- `Rule.allows` is the scope, every condition and the signer requirement;
- `RuleSet.allows` holds when some rule allows the context;
- `RuleSet.allowsAll` holds when every context is allowed;
- `narrower rs' rs` says every context `rs'` allows, `rs` allows, under the same authenticated signers.

`Model/Attenuation.lean` defines the steps and nothing else. Milestone 1's
three are: drop a rule, add a condition to a rule, and restrict a rule's
scope. Each names its rule by position and fails with `noSuchRule` out of
range.

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

- `allows(rules, context, authenticated)` and `allows_all(rules, contexts, authenticated)` evaluate a rule set;
- `drop_rule`, `add_cond` and `remove_functions` are Milestone 1's attenuation steps. Each reads a slice of rules and returns a new `Vec<Rule>` or `AttenuationError::NoSuchRule`.

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
- **New rule fields** (caps) extend `Rule` and `Chain.Rule`, as signers do in Milestone 2. Keeping `Rule.denote` a generic rule keeps every attenuation theorem.
- **Stateful checks** stay pure in `rule-eval`, as the spending-cap check does. The function takes the state as data and returns the new state or an error, and the shell does the storage.

## Milestone 2: signers

A rule names the signers that may authorize its calls and how many of them
must. The design is the same in Rust (`crates/rule-eval/src/signer.rs`), the
chain vocabulary (`Chain.Signer`) and the generic model (`Rule.signed`).

### Signers and the requirement

- A signer is `Delegated(address)` or `External(verifier, key)`, OpenZeppelin's two smart-account signer kinds: an address that authorizes for itself, or a key checked by a verifier contract. Addresses are their `ScAddress` XDR. Signers compare exactly, constructor first: `Delegated(x)` never equals `External(x, ...)`, and bytes compare with no prefix or extension match.
- A `Rule` has `signers`, a list of signers, and `threshold`, a `u32`.
- Evaluation takes the authorization's authenticated signers, one list for the whole batch: `allows(rules, context, authenticated)` and `allows_all(rules, contexts, authenticated)`. Authenticating the signatures is the shell's job. `rule-eval` receives the signers that passed.
- The signer requirement holds when at least `threshold` distinct rule signers appear in `authenticated`. Each rule signer counts once, at its first position in the rule's list, so a signer repeated in either list never counts twice. In the model the count is `(signers.eraseDups.filter (· ∈ auth)).length`, since `eraseDups` keeps first occurrences.
- Threshold 0 is no requirement. "All signers must sign" is a threshold equal to the number of distinct signers. A threshold above that number is never met, so the rule allows nothing.
- The requirement is one more conjunct of `Rule.allows`, after the scope and the conditions.

### Attenuation

There are five attenuation steps and nothing else: the three of Milestone 1 and these two.

- `remove_signers(rules, i, signers)` removes every occurrence of each listed signer from rule `i`'s signers. The threshold is unchanged, so the requirement only gets harder to meet.
- `raise_threshold(rules, i, k)` sets rule `i`'s threshold to `k`. It refuses with `AttenuationError::ThresholdLowered` when `k` is below the current threshold.

Both refuse an index out of range with `NoSuchRule`, and never panic. The
index is checked first, so `raise_threshold` on a missing rule is
`NoSuchRule` whatever `k`.

### Theorems

- `narrower` quantifies over authenticated signer lists as well as contexts, and every Milestone 1 theorem holds under that definition.
- `removeSigners_narrower` and `raiseThreshold_narrower`: each signer step yields a narrower rule set. `Derives.narrower` covers chains of all five steps.
- `allows_of_subset`, `allowsAll_of_subset`: authenticating more signers never turns an allow into a refusal.
- `allows_congr`, `allowsAll_congr`, `allows_eraseDups`, `allows_congr_signers`: the verdict depends only on which signers are in each list, so repeats and order in either list change nothing.
- `signed_of_threshold_zero`, `signed_iff_of_threshold_eq`, `allows_false_of_lt`: threshold 0, all signers, and a threshold above the signers (on the translation: `rule_allows_threshold_zero`, `signers_met_all_iff`, `rule_allows_false_of_lt`).
- `Signer.delegated_ne_external`, `signer_eq_iff`, `signer_eq_delegated_external`: signers compare exactly.

Each property holds on the model, the chain vocabulary and the translation of
`rule-eval` (`RuleCore.Extracted`).

### In the restricted subset

`signers_met(signers, threshold, authenticated)` compares `threshold as usize`
with a count. The count loop walks the rule's signers once. At position `i` it
asks `signer_in_first(signers[i], signers, i)`, a scan of the signers before
`i`, and `signer_in(signers[i], authenticated)`, and adds one when the first
answer is no and the second is yes. The count grows at most once per position,
so it stays at most `i` and its increment cannot overflow. `raise_threshold`
reads the rule through `rules.get(index)`. In Lean, `loop_count` gives what a
counting loop returns, and `countFrom_first` equates counting at first
occurrences with `eraseDups`.

### OpenZeppelin's rules, as input for M4

OpenZeppelin's smart account (`packages/accounts` of
[OpenZeppelin/stellar-contracts](https://github.com/OpenZeppelin/stellar-contracts/tree/ddc327eb92d63709436da3a8455f641c2d5476c5/packages/accounts/src),
read at commit `ddc327eb`) checks signers in two ways:

- **A context rule without policies requires all of its signers.** `get_validated_context_by_id` filters the rule's signers to those present among the authenticated ones and refuses unless every one is (`rule_signers.len() != matched_signers.len()`). Here that is a threshold equal to the number of distinct signers.
- **A rule with a `simple_threshold` policy requires `k` of them.** Its `enforce` checks `authenticated_signers.len() >= threshold` over the same matched signers. Here that is a threshold of `k`. OpenZeppelin refuses to install a threshold of 0 or one above the rule's signer count; this repository accepts both, as no requirement and as a rule that allows nothing.

The mapping is not exact in every respect. These differences are recorded for
M4 and not decided here:

- OpenZeppelin's caller names one rule per context (`context_rule_ids`). Here a context is allowed when some rule allows it.
- OpenZeppelin has rule kinds this model does not have: a `Default` context type that matches any contract, contract-creation rules, and `valid_until` expiry.
- OpenZeppelin finds duplicate external signers through the verifier's canonical key (`batch_canonicalize_key`). Here two external signers are the same signer only when their bytes are equal.
- The `weighted_threshold` policy gives signers weights, and `spending_limit` caps amounts. There is no counterpart to weights here; spending caps are the other half of M2.

## Milestone 2: spending caps

A cap bounds what one rule may spend: at most `limit` within `period`
consecutive ledgers, Perch's `periodLedgers`. The check is
`crates/rule-eval/src/cap.rs`, its model `formal/RuleCore/Model/Cap.lean`, and
its theorems `formal/RuleCore/Theorems/Cap.lean`. The check is a function of
its own: `Rule`, `allows` and the attenuation steps do not mention caps.

### The record and the check

- A `SpendRecord` holds the history, a list of `SpendEntry { ledger: u32, amount: i128 }` in the order the spends were made, and `total: i128`.
- `CapParams { limit: i128, period: u32 }` is a cap. `params_valid` holds when `limit > 0` and `period > 0`, which is what installing a cap requires.
- `check_spend(record, limit, period, now, amount)` returns the record after a spend of `amount` at ledger `now`, or a `CapError`. In order:
  1. a negative amount is refused (`NegativeAmount`);
  2. a zero amount passes and returns the record unchanged;
  3. a ledger earlier than that of the newest recorded entry is refused (`LedgerBeforeNewest`);
  4. the entries at the front of the history whose ledger is at most `now.saturating_sub(period)` are evicted, and their amounts are taken off the total;
  5. the spend is refused when the remaining total plus the amount exceeds `limit` (`LimitExceeded`);
  6. the spend is refused when the history left after eviction holds `MAX_HISTORY_ENTRIES` (1000) entries (`HistoryFull`);
  7. otherwise `(now, amount)` is appended and the total increased.
- Every sum is checked. One that does not fit in an `i128` is refused with `Overflow`.
- The check is pure. The shell loads the record, passes the current ledger sequence, and stores the returned record only on `Ok`. A refusal returns no record, so the stored one stays as it was. A failed Soroban invocation rolls back the same way.

### Mirroring Perch

Perch and Nido pin OpenZeppelin's `stellar-accounts` 0.7.1 through the fork
`theahaco/stellar-contracts-OZ` at commit `33726766` (Perch's `Cargo.toml`
line 62, locked at `Cargo.lock` line 2856). Its spending-limit policy is
[`packages/accounts/src/policies/spending_limit.rs`](https://github.com/theahaco/stellar-contracts-OZ/blob/33726766a1fd5e7e3d2977d79f64ee29e1ea3ca9/packages/accounts/src/policies/spending_limit.rs):

- `enforce` (lines 222–302) refuses a negative amount (line 246), returns early on a zero amount (line 256), evicts (lines 259–264), then compares `cached_total_spent + amount > spending_limit` (line 268), then `spending_history.len() >= MAX_HISTORY_ENTRIES` (line 272), and then appends (lines 277–279);
- `cleanup_old_entries` (lines 540–561) takes `cutoff_ledger = current_ledger.saturating_sub(period_ledgers)` (line 545) and pops entries from the front while `entry.ledger_sequence <= cutoff_ledger` (line 552), summing what it removes;
- `MAX_HISTORY_ENTRIES` is 1000 (line 158), and installation refuses `spending_limit <= 0 || period_ledgers == 0` (line 428).

`check_spend` follows the same steps in the same order. It differs in three ways:

- **The clock check** (step 3) is added. OpenZeppelin reads `e.ledger().sequence()` and never compares it with the history.
- **Overflow** is a typed refusal. OpenZeppelin's arithmetic uses plain operators under `overflow-checks = true`, so an overflowing sum traps. Both refuse the spend.
- **Purity.** OpenZeppelin mutates the stored data and panics to refuse. `check_spend` returns the new record or an error.

What OpenZeppelin's `enforce` checks besides the cap is not part of
`check_spend`: a non-empty signer set, and a `transfer` call whose argument 2
is an `i128`. Matching the call belongs to the rule (its scope and conditions),
and signers to [Milestone 2: signers](#milestone-2-signers).

### The time model

Time is discrete and passed in. The check takes the current ledger sequence as
an argument and refuses a positive spend at a ledger earlier than that of the
newest recorded entry. No theorem therefore assumes anything about the clock.
A run is any list of calls `(now, amount)`, with ledgers in any order, and the
theorems hold for every run.

### Theorems

`Params.check` is the model of `check_spend`, and `Params.run` runs a list of
calls, keeping the record after a refusal. `Params.recorded` lists the spends a
run recorded: the accepted calls with a positive amount.

- **Window safety** (`window_le_limit`): from the empty record, for every run and every ledger `t`, the recorded spends whose ledger is after `t - period` and at most `t` sum to at most the limit.
- **Consecutive windows**: every window of `period` consecutive ledgers starting at ledger 1 or later sums to at most the limit (`period_le_limit_of_pos`). When every call is at ledger 1 or later, every window does (`period_le_limit`).
- **Refinement**: the stored history is the recorded spends that eviction left at the last recorded spend's ledger, followed by that spend, and the stored total is their sum (`run_history`, `run_total`). With a nonzero period and that spend at ledger 1 or later, the history is exactly the recorded spends in the window at its ledger (`run_eq_window`).
- **Refusal changes nothing** (`step_of_error`, `run_cons_of_error`). In Rust, `check_spend` borrows the record and returns a new one.
- **The clock check** (`check_ledgerBeforeNewest_iff`, `beforeNewest_eq_false_iff`).
- **Narrowing is trace inclusion**: every run a narrower cap accepts from a valid record, the wider cap accepts too. A lower limit and a longer period are both narrower (`Params.accepts_of_narrower`, `accepts_of_limit_le`, `accepts_of_period_le`), and so is adding a cap where there was none (`capAccepts_of_capNarrower`).
- **Validity and the bound**: the check keeps a record valid (in ledger order, with positive amounts and a total that is their sum: `run_valid`), and a record never holds more than 1000 entries (`run_history_length_le`).
- **On the translation**: `check_spend_eq` proves that the extracted `check_spend` returns `ok` of the model's check on every input, so it terminates and never panics. It needs no stated bound. `runSpends_eq` carries the result to runs, and `runSpends_window` and `runSpends_length_le` state the refinement and the bound for the record the Rust code computes.

### Edges

- **Ledger 0.** For every `now < period`, `now.saturating_sub(period)` is 0, so an entry at ledger 0 is evicted by the next spend even inside its window. Two spends of the whole limit at ledger 0 are both accepted (`period_ledger_zero`). OpenZeppelin behaves the same way, and `check_spend` keeps it. This is a rule to state, not a bug: Stellar's ledgers start at 1 (`GENESIS_LEDGER_SEQ = 1`, [stellar-core `src/ledger/LedgerManagerImpl.cpp` line 112](https://github.com/stellar/stellar-core/blob/b8c4f12d6f1159d67be8743c87a3c7df839ae7f4/src/ledger/LedgerManagerImpl.cpp#L112)), and contracts run in ledgers after the genesis ledger. Window safety in eviction's window holds without the rule. The statement over every window of consecutive ledgers takes it as a hypothesis ([`TRUSTED.md`](TRUSTED.md#ledgers-start-at-1)).
- **A zero amount over a lowered limit.** A zero amount passes whatever the total, even a total above a limit lowered over an existing record. OpenZeppelin's `set_spending_limit` lowers the limit and keeps the history, and its comment at lines 249–253 gives this reason. Perch's wrapper does not expose `set_spending_limit`. This is not a bug: a zero spend records nothing, so no window gains anything. For a cap installed over an existing record, `window_le_limit_of_valid` bounds every window that holds a spend made under the new cap. Windows that hold only earlier spends keep the bound they were made under.
- **The history bound.** A spend under the limit is refused when the history left after eviction holds 1000 entries. The bound only refuses, so the safety theorems are unaffected. Within one window, 1000 spends of any size block further spends until eviction makes room. Upstream OpenZeppelin ([`ddc327eb`](https://github.com/OpenZeppelin/stellar-contracts/blob/ddc327eb92d63709436da3a8455f641c2d5476c5/packages/accounts/src/policies/spending_limit.rs), lines 161–169) has since lowered the bound to 815, because a `SpendingLimitData` of 816 entries serializes past mainnet's `contractDataEntrySizeBytes` of 65,536 bytes. At the revision Perch pins it is 1000, and `rule-eval` follows that pin. A record the shell cannot store fails its write, which refuses the transaction.
- **Eviction stops at the first entry kept.** On a record the check builds, the history is in ledger order, so this evicts exactly the entries at or before the cutoff (`dropWhile_eq_filter`). On a record built some other way, an entry after the cutoff shields the entries behind it. The equivalence covers every record. The window theorems are stated for valid ones.
- **Caps that are not valid to install.** `check_spend` does not check its parameters. With `limit <= 0` every positive spend is refused. With `period == 0` the cutoff is `now`, so each spend is checked alone. The window theorems need only `limit >= 0`.

### In the restricted subset

- `evict` is one `while i < history.len()` loop. It returns at the first entry after the cutoff, or with `Eviction::Overflow` when `i128::checked_add` of the evicted amounts fails. A private enum, `Eviction`, carries the result, and `check_spend` names the error.
- `before_newest` reads `history[len - 1]` under `len > 0`.
- `entries_from` copies the history from the first entry kept. It pushes fewer than 1000 entries before the new one, so no push can reach `Vec`'s bound, and no stated rule is needed.
- The other arithmetic is `u32::saturating_sub` for the cutoff, `i128::checked_sub` and `i128::checked_add` for the totals, and `len - kept_from` on `usize` under `kept_from <= len`.

## Later milestones

These are design notes for work that is not built. Where the brief leaves a
choice open, it is listed under [Open questions](#open-questions) and not
decided here.

### M2: caps on rules

A rule gains an optional cap, and its record is stored per rule.

- **Evaluation.** A capped rule allows a call when it matches and `check_spend` accepts the call's amount. The amount is the argument the rule names, an `i128`, so the conditions already read it.
- **Attenuation.** "Add a cap" and "lower a cap" become steps. `capNarrower` and `capAccepts_of_capNarrower` are the narrowing they rest on: every run a narrower cap accepts, the wider cap accepts, and a rule without a cap accepts every run.

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

1. **M4: rule mapping.** Whether Perch's compiled rules (OpenZeppelin context rules plus policies) map onto this rule model without loss, or need a richer condition set.
2. **M5: host versions.** How the Lean Soroban models are kept in step with new `soroban-env-host` versions.
