# Architecture

## Exact authorization-entry roots

Ordinary rules may additionally require an exact `AuthRoot` contract/function
pair. This is the first context of the current account's host-authenticated
entry, not the transaction root or an arbitrary ancestor. The Rust first pass
derives it through `context::entry_root`, implemented with the pinned
extraction's modeled `get(0)` operation. It conjoins `rule_allows_in` with the
existing expiry and generation checks before validating signer coverage or
charging any caps. No caller-supplied root parameter reaches `authorize`.

The generic model adds `authRoot : Option (Ctx → Bool)` and `Rule.allowsIn`;
chain denotation restricts it to exact byte comparisons. The first pass uses
`a.contexts.head?`, and `RuleSet.allowsBatch` uses that same head for the whole
batch. Local `allows`/`allowsAll` deliberately remain weaker screening views.
In particular, the existing Soroban shell model's `checkRules` containment
result is local screening; the new stateful root theorem is
`Chain.RuleSet.authorize_exactRoot`. The host model's preorder-head result
supplies the separate host-order fact. Real account integration must preserve
that ordering and invoke the complete evaluator.

The optional root is structural data in Rust and document/chain denotations.
All copy, lowering and attenuation equivalence proofs retain it. Self-admin
lowering and generated recovery rules remain unrestricted; input validators
must reject root-bearing self-admin documents. Generic `Rule.Refines` now
requires root-aware implication for every root. `AuthRoot.narrows_iff` proves
that unrestricted-to-exact or an identical exact pair is precisely safe for
this component, and `withRoot_traceNarrower` lifts that to complete traces.

`accepts_allowsBatch`, `mem_charged_root`, and the extracted
`accepts_allows_batch`/`charged_root` results connect accepted traces and every
charge to the selected rule's root requirement. The regenerated extracted
`authorize` and `runAuthorizations` agree with this model; the existing exact
spending/window and failed-batch theorems are rechecked against these changed
definitions. A game-only win authenticates and spends no transfer cap; a loss
charges transfers in the same entry; a direct transfer or a game root in a
separate entry cannot satisfy the restricted transfer rule.

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
| Scoped documents | Grants the owner issues under the admin document, one per agent or app ([scoped documents](#scoped-documents)). | An agent or an app. |
| Delegated grants | What a holder narrows and passes on under a scope, with budgets on the delegation tree: the grant signer. | Whoever the holder delegates to. |

Each link of the chain is a theorem about rule sets, or about the code that
builds, stores and checks them:

- **Grant inside scope.** A delegated grant is reached from its scope by attenuation steps, so it allows only what the scope allows, under any signers. Milestones 1 and 2 prove this for rule matching and signer requirements (`Derives.narrower`, `Derives.allows_all`), and for spending caps on rules as trace inclusion: every run of authorizations a derived rule set accepts from empty records, its root accepts from its own ([Milestone 2: caps on rules](#milestone-2-caps-on-rules)). Milestone 3 bounds what is spent under each grant on the delegation tree: from a tree with nothing spent, the total successfully spent at or under any node never exceeds its allowance, however the allowances below it oversubscribe it (`spentUnder_le_allowance`, [Milestone 3: the budget tree](#milestone-3-the-budget-tree)).
- **Scope inside the owner's authority.** The rules a document lowers to allow exactly what the document says, the recovery rule over-approximated, and a scoped document lowers to rules that reach none of the account, its recovery controller or its ZK adapter and pool, under any attenuation (`Doc.lower_authorize`, `Doc.lowerScoped_attenuateAll_excluded`, [Milestone 4: documents, scopes and the generation](#milestone-4-documents-scopes-and-the-generation)). The rule model the lowering targets is [Milestone 4: the rule model Perch lowers to](#milestone-4-the-rule-model-perch-lowers-to).
- **Recovery.** Every scoped rule carries the generation it was issued under, the generation advances only when a recovery completes, and `authorize` refuses a rule issued under another generation, so after a completed recovery every grant attenuated from an earlier scoped document authorizes nothing while the admin rules authorize as before (`Account.issued_stale`, `Account.adminRules_authorize_generation`).
- **The chain composes.** Anything `authorize` accepts under a grant attenuated from a scoped document's rules is allowed by that document, touches no excluded contract, and is made in the generation the document was issued under, on the model and on the translated Rust functions (`Account.chain`, `Extracted.chain`). [What does not compose](#what-does-not-compose) lists the links that rest on the shell.
- **The code is the model.** The Rust that Perch's smart account, the grant signer, the agent host and the relay run is proven equal to the Lean model the theorems are about (M1 for rule matching and attenuation, M2 for signers, spending caps and the stateful `authorize`, M3 for the budget tree, M4 for the lowering).
- **The host lets through only what the rules allow.** Soroban's own behaviour enters through Lean models of soroban-env-host 29.0.1, tested against that host. In the models, every call the host lets through on an account's signature is a context of the signed tree the account's `__check_auth` received, and so is allowed by every rule set that `__check_auth` checks with `rule-eval` (`Tx.run_authorized_allowed`, [Milestone 5: the Soroban facade](#milestone-5-the-soroban-facade)).

## Dependency direction

```
contract shells (Perch's account, the grant signer)
  ├── rule-eval            pure evaluator, no dependencies
  └── soroban-facade       SDK subset as plain data; converts contexts for rule-eval
        ├── rule-eval
        └── soroban-sdk 29 (feature `sdk`, the real implementation)
```

- `crates/rule-eval` depends on nothing: no crates, and no `std` (it uses only `core` and `alloc`). It holds the evaluator and the lowering of Perch's documents ([where the lowering lives](#where-the-lowering-lives)).
- `soroban-facade` never appears in `rule-eval`, and `rule-eval` never sees a Soroban type. The facade converts the host's contexts into `rule-eval`'s plain data (`Val`, `Context`), and a shell calls the evaluator with them.
- Only contract shells use the facade. Its `sdk` feature, the real implementation, is the only code in the repository that touches soroban-sdk; without it the facade has no dependency but `rule-eval`.
- `conformance/host` drives the host for the tests; nothing depends on it.
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
creation. [Milestone 4](#milestone-4-the-rule-model-perch-lowers-to) extends
the vocabulary: a rule's functions may be a wildcard, a rule may carry a last
ledger and a generation, there are two more conditions, and strings are a
value constructor of their own.

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
- **New rule fields** extend `Rule` and `Chain.Rule`, as signers and caps do in Milestone 2. Keeping `Rule.denote` a generic rule keeps every attenuation theorem.
- **Stateful checks** stay pure in `rule-eval`, as `check_spend` and `authorize` do. The function takes the state as data and returns the new state or an error, and the shell does the storage.

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

Signers add two attenuation steps to the three of Milestone 1; [Milestone 2: caps on rules](#milestone-2-caps-on-rules) adds three more, and nothing else is a step.

- `remove_signers(rules, i, signers)` removes every occurrence of each listed signer from rule `i`'s signers. The threshold is unchanged, so the requirement only gets harder to meet.
- `raise_threshold(rules, i, k)` sets rule `i`'s threshold to `k`. It refuses with `AttenuationError::ThresholdLowered` when `k` is below the current threshold.

Both refuse an index out of range with `NoSuchRule`, and never panic. The
index is checked first, so `raise_threshold` on a missing rule is
`NoSuchRule` whatever `k`.

### Theorems

- `narrower` quantifies over authenticated signer lists as well as contexts, and every Milestone 1 theorem holds under that definition.
- `removeSigners_narrower` and `raiseThreshold_narrower`: each signer step yields a narrower rule set. `Derives.narrower` covers chains of all eight steps.
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

### OpenZeppelin's rules and what Perch installs

OpenZeppelin's smart account (`packages/accounts` of
[OpenZeppelin/stellar-contracts](https://github.com/OpenZeppelin/stellar-contracts/tree/ddc327eb92d63709436da3a8455f641c2d5476c5/packages/accounts/src),
read at commit `ddc327eb`) checks signers in two ways:

- **A context rule without policies requires all of its signers.** `get_validated_context_by_id` filters the rule's signers to those present among the authenticated ones and refuses unless every one is (`rule_signers.len() != matched_signers.len()`). Here that is a threshold equal to the number of distinct signers.
- **A rule with a `simple_threshold` policy requires `k` of them.** Its `enforce` checks `authenticated_signers.len() >= threshold` over the same matched signers. Here that is a threshold of `k`. OpenZeppelin refuses to install a threshold of 0 or one above the rule's signer count; this repository accepts both, as no requirement and as a rule that allows nothing.

OpenZeppelin has more than this model expresses:

- its caller names one rule per context (`context_rule_ids`); here `allows` and `allows_all` accept a context when some rule allows it, and `authorize` takes one rule per context as OpenZeppelin does ([Milestone 2: caps on rules](#milestone-2-caps-on-rules));
- a `Default` context type that matches any contract, and contract-creation rules, which have no counterpart here; its `valid_until` expiry is [Milestone 4](#milestone-4-the-rule-model-perch-lowers-to)'s;
- duplicate external signers found through the verifier's canonical key (`batch_canonicalize_key`) when a rule is installed, where here two external signers are the same signer only when their bytes are equal;
- the `weighted_threshold` policy, which gives signers weights and has no counterpart here, and `spending_limit`, whose counterpart is a rule's cap.

What Perch installs on that smart account stays within this model, so its
lowering ([Milestone 4: documents, scopes and the generation](#milestone-4-documents-scopes-and-the-generation))
needs none of them. Read at
Perch `dff2a73` (the `bitswell-hq/stellar-registry__perch` fork) and
OpenZeppelin `stellar-accounts` at the fork commit Perch pins
(`theahaco/stellar-contracts-OZ@33726766`, Perch `Cargo.toml` line 61):

- **OpenZeppelin compares signers exactly when it checks an authorization, and Perch refuses keys that are not canonical.** At check time `get_validated_context_by_id` matches rule signers against the authenticated ones with `all_signers.contains(s)`, exact `Signer` equality (`smart_account/storage.rs` lines 313–314); the canonical comparison runs only when a rule is installed. Perch's document compiler refuses a key that is not already in its verifier-canonical form (`crates/perch-doc-compiler/src/lib.rs` lines 537–550). So among the rules Perch installs, byte equality of external keys is signer identity, as it is here.
- **Perch emits no `Default`, contract-creation or weighted rules.** Every rule it installs is `ContextRuleType::CallContract` of the scoped contract or of the account itself (`crates/perch-smart-account/src/rules.rs` lines 171–175, and the constructor's admin rule); thresholds are its interpreter's `MinSigners`, and `simple_threshold` and `weighted_threshold` appear only as golden XDR vectors.
- **Perch emits `valid_until`.** It lowers a rule's `not-after-ledger X` to `valid_until = X - 1` (`crates/perch-compile/src/lib.rs` line 256), and drops rules already expired when it installs a document (`crates/perch-smart-account/src/rules.rs` lines 127–129).
- **`apply_scope`, cross-token caps and per-rule generations do not exist in Perch at that commit.** It has one document per account, applied with `apply_doc`; validation refuses a cap whose token is not the rule's own contract (`CapTokenMismatch`, `crates/perch-ir/src/validate.rs` line 998); and its `recovery_generation` (`crates/perch-smart-account/src/lib.rs` lines 386–389) is account-level and only makes pending upgrades stale.

## Milestone 2: spending caps

A cap bounds what one rule may spend: at most `limit` within `period`
consecutive ledgers, Perch's `periodLedgers`. The check is
`crates/rule-eval/src/cap.rs`, its model `formal/RuleCore/Model/Cap.lean`, and
its theorems `formal/RuleCore/Theorems/Cap.lean`. The check works on one
record; [Milestone 2: caps on rules](#milestone-2-caps-on-rules) puts caps on
rules and charges them through `authorize`.

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

## Milestone 2: caps on rules

A rule may carry a spending cap, and `authorize` checks an authorization the
way OpenZeppelin's smart account does: one chosen rule per context, every
chosen rule allowing its context, and each capped rule's record charged with
`check_spend`. The code is `crates/rule-eval/src/authorize.rs` and the cap
steps in `attenuate.rs`; the model is `formal/RuleCore/Model/Authorize.lean`
and the cap steps in `Model/Attenuation.lean`; the theorems are
`Theorems/Authorize.lean` and, on the translation,
`Theorems/ExtractedAuthorize.lean`.

### The cap and the check

- A `Rule` has `cap: Option<Cap>`, where `Cap { limit: i128, period: u32, amount_arg: u32 }` caps spends at `limit` within `period` consecutive ledgers and names the argument that holds a call's amount. `cap_valid` holds when `limit > 0` and `period > 0`, what `params_valid` requires of a cap's parameters.
- `allows` and `allows_all` do not read the cap. They stay the cap-free view of a rule set, and every Milestone 1 theorem about them is unchanged.
- `authorize(rules, records, contexts, choices, authenticated, now, generation)` returns the records after the authorization, or a `Refusal` that changes nothing. `records[j]` is the record of `rules[j]`, one per rule, and `choices[i]` is the rule chosen for `contexts[i]`. In order:
  1. `choices` must hold one index per context (`ChoicesMismatch`), and `records` one record per rule (`RecordsMismatch`);
  2. in context order, every chosen rule must exist (`NoSuchRule`), be unexpired at `now` (`Expired`), carry the current `generation` when it carries one (`StaleGeneration`), and allow its context under `authenticated` (`NotAllowed`); expiry and generation are [Milestone 4](#milestone-4-the-rule-model-perch-lowers-to)'s;
  3. every authenticated signer must be a signer of some chosen rule (`UnauthorizedSigner`), also Milestone 4's;
  4. in context order, for every chosen rule with a cap, the context's argument at `amount_arg` must be an `I128` (`NoAmount`) and is charged to that rule's record with `check_spend` at ledger `now` (`Cap(e)` when the check refuses). Each charge starts from the record the charges before it left, so two contexts choosing one rule accumulate within the batch.
- A rule without a cap reads no amount and keeps its record. A refusal returns no records: the shell stores the result only on `Ok`, so the charges of a refused batch's earlier contexts are discarded with it, as a failed Soroban invocation rolls back.

### Mirroring OpenZeppelin

At the fork commit Perch pins (`theahaco/stellar-contracts-OZ@33726766`),
[`smart_account/storage.rs`](https://github.com/theahaco/stellar-contracts-OZ/blob/33726766a1fd5e7e3d2977d79f64ee29e1ea3ca9/packages/accounts/src/smart_account/storage.rs)
carries the rule choice in `AuthPayload::context_rule_ids` (lines 133–138),
aligned by index with the authorization contexts and bound into the digest the
signers sign (line 498). `do_check_auth` (lines 466–525) refuses a length
mismatch first (line 472), validates every context against its chosen rule
(lines 477–485), refuses any authenticated signer outside the chosen rules
(lines 504–507), and only then enforces each rule's policies in context order
(lines 511–522). `authorize` keeps that order: its second step is the
validation, its third the signer check and its fourth the enforcement, so a
batch with both a disallowed context and an exceeded cap is refused with
`NotAllowed`. The spending-limit
policy stores one record per context rule (`SpendingLimitStorageKey::AccountContext`,
[`policies/spending_limit.rs`](https://github.com/theahaco/stellar-contracts-OZ/blob/33726766a1fd5e7e3d2977d79f64ee29e1ea3ca9/packages/accounts/src/policies/spending_limit.rs)
line 236) and writes it after each enforcement (line 281), so two contexts on
one rule accumulate there too. Binding the choices into the signed digest is the
shell's job: `authorize` receives the choices the signatures covered.

### Attenuation

These three steps join the five of Milestones 1 and 2, and
[Milestone 4](#milestone-4-the-rule-model-perch-lowers-to) adds two more. Each
refuses an index out of range with `NoSuchRule` before anything else.

- `add_cap(rules, i, cap)` gives rule `i` the cap. It refuses a rule that already has one (`CapPresent`) and a cap that is not valid (`InvalidCap`).
- `lower_cap_limit(rules, i, limit)` sets the limit of rule `i`'s cap. It refuses a rule without a cap (`NoCap`), a limit above the current one (`LimitRaised`), and a limit that is not positive (`InvalidCap`).
- `lengthen_cap_period(rules, i, period)` sets the period of rule `i`'s cap. It refuses a rule without a cap (`NoCap`) and a period below the current one (`PeriodShortened`).

The steps never make a valid cap invalid (`attenuate_capsValid`). `authorize`
does not check validity: a root rule set is installed by the shell, which
checks its caps, and the cap check behaves monotonically in its parameters
whether or not they are valid, so narrowing holds for every cap.

### Narrowing as trace inclusion

`TraceNarrower rs' rs f` says: every run of authorizations that `rs'` accepts,
each authorization in turn from `rs'`'s empty records, `rs` accepts from its
own empty records, with each choice `j` renumbered to `f j`. Each side keeps
its own records. The renumbering is the one the steps induce:
`dropRule i` moves every rule after `i` down by one, so `f j` is `j` below `i`
and `j + 1` from `i` on (`Attenuation.source`); every other step keeps each
index; a list of steps composes them (`Attenuation.chainSource`).

The proof goes through `Refines rs' rs f`: `f` sends the rules of `rs'` one to
one to rules of `rs`, each rule of `rs'` allows no more than its image, its
cap is at least as narrow, reading the same amount with a lower or equal limit
and a longer or equal period, or there is a cap where the image has none, it
is current (unexpired and not stale) at no ledger and in no generation where
its image is not, and it lists no signer its image does not. Along
a run, the history of each image's record stays a suffix of the record it
corresponds to (`check_of_narrower_suffix`, the single step of the cap trace
inclusion), so every charge `rs'` accepts, `rs` accepts. Each step refines
along its renumbering, refinement composes, and so every chain of steps is
trace inclusion (`attenuateAll_traceNarrower`).

### Theorems

- **Soundness** (`authorize_allowsAll`, `authorize_chosen`): an accepted authorization's every context is allowed by the rule chosen for it, so the rule set allows the batch under its signers.
- **Refusals change nothing** (`step_of_error`): a run keeps the records after a refused authorization.
- **One record per capped rule** (`run_get`, `run_get_of_cap_none`): after any run, the stored record of a capped rule is the cap check's own run over the calls the run charged to that rule, and a rule without a cap keeps its record.
- **Window safety** (`RuleSet.window_le_limit`, `RuleSet.period_le_limit_of_pos`, `RuleSet.period_le_limit`): from empty records, for every capped rule with a non-negative limit and every run, the spends recorded for that rule in every window of eviction, and in every window of `period` consecutive ledgers from ledger 1 on, sum to at most its limit.
- **The stored record is the in-window spends** (`RuleSet.run_eq_window`), and never holds more than 1000 entries (`RuleSet.run_history_length_le`).
- **Narrowing** (`attenuate_traceNarrower`, `attenuateAll_traceNarrower`, `TraceNarrower.trans`), and each cap step leaves every `allows` verdict as it was (`addCap_narrower`, `lowerCapLimit_narrower`, `lengthenCapPeriod_narrower`).
- **On the translation**: `authorize_eq` proves that the translated `authorize` returns `ok` of the model's result on every input, so it terminates and never panics; `add_cap_eq`, `lower_cap_limit_eq` and `lengthen_cap_period_eq` do the same for the steps. `authorize_allows_all`, `runAuthorizations_window`, `runAuthorizations_window_le_limit`, `runAuthorizations_length_le`, `StepAlong.traceNarrower` and `DerivesAlong.traceNarrower` carry the theorems to the Rust functions.

### Edges

- **Renumbered choices are `u32`s.** On the translation, a renumbered run exists only when every renumbered index fits a `u32`. A rule set of more than `2^32` rules that drops a rule has rules no `u32` choice can name in the root, and the Rust statement says nothing about runs that choose them. The model's statement has no such limit.
- **Ledger 0** behaves as in [Milestone 2: spending caps](#edges): only the statement over every window of consecutive ledgers needs every authorization at ledger 1 or later.
- **Records of rules without a cap** are carried and returned unchanged. A shell may store only the records of capped rules and pass empty ones for the rest.

### In the restricted subset

- The validation and the charging are each one `while i < contexts.len()` loop. A choice is read with `choices.get(i)`, a rule with `rules.get(index)`, and a context with `contexts[i]` under `i < contexts.len()`.
- The charging pass copies the records once and charges in place through `out.get_mut(index)`. Aeneas models `get_mut` on a `Vec` as `DerefMut` to a slice and `<[T]>::get_mut`, which returns the element and a function writing a new one back at the index.
- `charge_all_loop_eq` and `check_choices_loop_eq` prove that the loops compute the model's `foldlM` of `charge` and `forM` of `checkChoice` over the contexts with their choices.

### Caps on rules and OpenZeppelin's metering

- **OpenZeppelin's spending-limit policy meters only `transfer` at argument 2.** At Perch's pin, `enforce` accepts a call only when its function is `transfer` and its argument 2 is an `i128`, and refuses every other context with `NotAllowed` (`policies/spending_limit.rs` lines 242–244, 298 and 301); it also refuses an empty set of authenticated signers (line 232). Here a cap names its argument (`amount_arg`), and which functions a rule covers is its function list, so a policy-capped OpenZeppelin rule corresponds to a rule whose functions are `["transfer"]`, with the condition that argument 2 is an `i128`, and whose cap reads argument 2. The lowering builds exactly that ([the lowering](#the-lowering)).
- **The history bound differs between upstream and Perch's pin.** Upstream OpenZeppelin bounds the history at 815 entries ([`stellar-contracts@ddc327eb`](https://github.com/OpenZeppelin/stellar-contracts/blob/ddc327eb92d63709436da3a8455f641c2d5476c5/packages/accounts/src/policies/spending_limit.rs) line 169), and Perch's pin at 1000 (line 158 of the fork). `rule-eval` follows the pin, so a record past 815 entries is one the pin accepts and upstream refuses.

## Milestone 3: the budget tree

Allowances sit on the delegation tree. Each grant a holder delegates is a node
with an allowance, and a spend under a grant is charged to its node and to
every node above it. The code is `crates/rule-eval/src/budget.rs`, the model
`formal/RuleCore/Model/Budget.lean`, the theorems `Theorems/Budget.lean` and,
on the translation, `Theorems/ExtractedBudget.lean`.

### The tree

- A tree is a slice of `Node { parent: Option<u32>, allowance: i128, spent: i128 }`. `parent` is the index of the node's parent, or `None` for a root; `spent` is what has been spent at or under the node. A tree may have several roots.
- A tree is well formed (`tree_valid`) when every node's parent index is below its own index and no allowance or spent amount is negative. Parent indices below their own make the tree acyclic by construction: each step of the walk from a node to its root moves to a smaller index, so the walk ends within as many steps as the tree has nodes.
- Every operation first checks the whole tree and refuses one that is not well formed with `Malformed`, whatever its other arguments.
- Well-formedness says nothing about how allowances relate. A node's spent amount may even start above its allowance; then no spend through it, not even a zero one, passes until a refill covers it.

### The operations

Each takes the tree as a slice and returns a new `Vec<Node>` or a `BudgetError`.

- `spend(tree, node, amount)` charges `node` and every ancestor up to its root by `amount`. In order, it refuses a malformed tree (`Malformed`), a node out of range (`NoSuchNode(node)`) and a negative amount (`NegativeAmount`). It then walks the chain from `node` and checks every node on it: a node can take the amount when `spent + amount` fits in an `i128` and is at most its allowance, so an overflowing sum counts as overdrawn. The first node that cannot is named in the refusal, `Overdrawn(j)`, counting from the spender; it is the node a refill request goes to. Only when every node on the chain can take the amount does `spend` build the new tree: a copy with the amount added to each node of the chain. A refusal returns no tree, so the input is unchanged by construction.
- `delegate(tree, parent, allowance)` appends a child of `parent` with `allowance` and nothing spent, at index `tree.len()`. It refuses a malformed tree, a parent out of range (`NoSuchNode(parent)`), a negative allowance (`NegativeAmount`), and a tree that already holds `MAX_NODES` nodes (`TreeFull`). `MAX_NODES` is `u32::MAX`, so every node a delegation appends has an index that fits in a `u32`.
- `refill(tree, node, amount)` raises `node`'s allowance by `amount`. It refuses a malformed tree, a node out of range, a negative amount, which would lower the allowance (`NegativeAmount`), and a raised allowance that does not fit in an `i128` (`Overflow`). A refill is the owner's action, not a holder's: the shell accepts one only on the owner's authority.

### Oversubscription

`delegate` does not compare a child's allowance with its parent's, so the
allowances of a node's children may sum to more than its own. Two children of
a root with allowance 10 may hold 8 each; once one has spent 8, the other's
spend of 3 is refused at the root, which has 2 left, and its spend of 2 passes.
The bound on each node holds because every spend under it is charged to it,
not because its children's allowances fit inside its own.

### Amounts and indices in Lean and Rust

Amounts, allowances and spent amounts are `i128` in Rust and integers in the
model; node indices are `u32` in Rust and natural numbers in the model. The
denotation (`Equiv/DenoteBudget.lean`) takes each to its value. The model's
sums are `Cap.addI128`, Rust's `i128::checked_add`, so the model refuses an
overflowing spend or refill exactly where Rust does. The model also has trees
no Rust value denotes, with indices of `2^32` or more or amounts outside the
`i128` range; its theorems hold for those too, and the equivalence says
nothing about them. Every Rust input denotes a model input, so the equivalence
and the theorems carried to the translation cover every Rust input. Indices are
widened with `as usize`, lossless because `usize` has at least 32 bits, and
`MAX_NODES` keeps every tree `delegate` pushes onto below `Usize.max`, so no
stated rule is needed.

### Theorems

`Tree.run` runs a list of spends, delegations and refills, keeping the tree on
a refusal and logging each successful spend; `Tree.Within t i a` says `a` is
`i` or one of its ancestors, and `spentUnder t log a` totals the logged spends
made at or under `a`.

- **Charging** (`spend_ok_charges`, `spend_ok_unchanged`, `spend_ok_length`, `spend_ok_parentOf`, `spend_ok_allowance`): a successful spend adds the amount to the spender and every ancestor and changes nothing else.
- **Refusals change nothing** (`step_of_error`, `run_cons_of_error`).
- **The named node** (`spend_overdrawn`): it is on the spender's chain and cannot take the amount, and every node before it on the chain can.
- **Refusing only what it must** (`spend_accepts_iff`, `spend_error_overdrawn`): on a well-formed tree, a spend of a non-negative amount at an existing node succeeds exactly when every node on its chain can take it.
- **Delegation and refills** (`delegate_ok_iff`, `refill_ok_iff`): what each appends or raises, and nothing else.
- **Invariants** (`run_valid`, `run_withinAllowance`, and the single-operation versions): every operation keeps the tree well formed and every spent amount within its allowance.
- **Budget safety** (`spent_run`, `spentUnder_eq_spent`, `spentUnder_le_allowance`): after any run, each node's spent amount is what it started with plus the total successfully spent at or under it, so from a well-formed tree with nothing spent that total is the node's spent amount and never exceeds its allowance. The theorem has no hypothesis on allowances.
- **On the translation**: `spend_eq`, `delegate_eq` and `refill_eq` prove that each translated operation returns `ok` of the model's result on every input, so it terminates and never panics. `runBudget_eq` carries this to runs of the Rust functions, and `runBudget_spentUnder_le_allowance`, `budget_spend_charges`, `budget_spend_overdrawn` and `budget_spend_accepts_iff` state the theorems for the code.

### Edges

- **`TreeFull`** needs a tree of `u32::MAX` nodes, so no test or vector reaches it; `delegate_eq` covers it.
- **A zero spend** passes when every node on the chain has spent at most its allowance, and charges nothing.
- **The walk's other refusals.** The checking walk refuses `Malformed` when it meets a parent index that is not below the current one, a missing node, or runs out of steps. On a well-formed tree none of these happens (`walk_error`), and `spend` checks well-formedness first, so `spend` never returns them from the walk.
- **Cost.** Each operation checks the whole tree, and each that succeeds copies it, so it is linear in the tree's size; the walk is linear in the spender's depth.

### The shell's part

The operations are pure. Linking an authorization to a node is the shell's job:
the grant signer (M6) decides which node an authorization's spend is charged
to and how much it spends, calls `spend`, and stores the returned tree only on
`Ok`, as a failed Soroban invocation rolls back. It accepts a refill only on
the owner's authority, and storing the tree in a contract is the shell's too.
None of this is built here.

### In the restricted subset

- `tree_valid` is one `while i < tree.len()` loop over the nodes.
- The checking walk (`check_chain`) and the charging walk (`charged`) are each one `while step < tree.len()` loop. The current node is read with `tree.get(current as usize)`, and a parent index not below the current one ends the walk, so every step moves to a smaller index. `check_chain_loop_eq` proves the checking walk is the model's `Tree.walk` with the steps left as fuel.
- `charged` copies the tree and walks the chain again, writing each charged node back through `out.get_mut(current as usize)`. Its `checked_add` cannot fail after the check: the walk found the same sum fits at each node it visits (`charged_loop_eq`).
- `refill` rebuilds the tree in one loop, replacing the node at its index, as `raise_threshold` does for a rule. `delegate` copies the tree and pushes the new node.

## Milestone 4: the rule model Perch lowers to

M4 proves Perch's document lowering sound. Each construct Perch's lowering
emits needs a counterpart that gives the same verdict on every input, so the
rule model is extended with exactly those constructs. Every Milestone 1 to 3
theorem keeps holding, and `allows` and `allows_all` stay the view without
time or generation that `authorize` refines. The document model, the lowering
and its theorems build on this ([Milestone 4: documents, scopes and the generation](#milestone-4-documents-scopes-and-the-generation)). The code is spread over `rule.rs`, `val.rs`,
`bytes.rs`, `attenuate.rs` and `authorize.rs`; the model over
`Model/RuleSet.lean`, `Model/Attenuation.lean`, `Model/Authorize.lean` and
`Vocab/Chain.lean`.

### The function wildcard

- A rule's functions are `Functions::Only(list)`, the functions listed, or `Functions::AnyExcept(list)`, every function except those listed. Perch's rule without a function list, every function on its contract, is `AnyExcept` of the empty list (`Functions.any`). Every applied Perch document holds one: its admin rule.
- The wildcard is a chain-vocabulary construct. The generic model's scope is unchanged: a rule's denoted scope is its contract and `f ∈ functions`, with membership read per constructor (`Functions.Mem`).
- `remove_functions(rules, i, fs)` removes `fs` from a list; on a wildcard it adds `fs` to the functions it excludes, so a removal is never refused and the rule then matches exactly the functions it matched but those. It still denotes restricting the scope to calls of functions not in `fs`, as in Milestone 1.
- `restrict_functions(rules, i, fs)`, a step of its own, restricts rule `i`'s functions to those also in `fs`: a list keeps the functions also named, in its own order; a wildcard becomes the list of the named functions it does not exclude. It denotes restricting the scope to calls of functions in `fs`, the generic `restrictScope`, so it narrows.
- On the translation, `remove_functions` on a wildcard appends to a vector, whose length Aeneas's model bounds at `Usize.max`; its equivalence takes the stated rule `FunctionsRoomAt`, which every list meets ([`TRUSTED.md`](TRUSTED.md#functionsroom)).

### Expiry

- A rule carries `valid_until: Option<u32>`, its last ledger. `authorize` refuses a chosen rule whose last ledger is before `now` (`Expired`), exactly OpenZeppelin's `if valid_until < e.ledger().sequence()` at Perch's pin (`smart_account/storage.rs` line 282): the rule authorizes at its last ledger and is refused one ledger later.
- `lower_valid_until(rules, i, v)`, a step, gives rule `i` the last ledger `v`, or moves its last ledger earlier, and refuses to move it later (`ValidUntilRaised`). `allows` does not read the last ledger, so the step leaves every verdict as it was; it narrows as trace inclusion, since a rule refines another only when it is unexpired at no ledger where the other has expired.

### Generations

- A rule carries `generation: Option<u64>`, the generation it was issued under, `None` for an admin rule, and `authorize` takes the account's current generation. A chosen rule issued under another generation is refused (`StaleGeneration`).
- Once the current generation is not `g`, a rule issued under `g` authorizes nothing: no accepted authorization chooses it (`authorize_not_chosen_of_stale`), and a rule set issued under `g` accepts only an empty batch (`authorize_contexts_nil_of_stale`).
- No attenuation step changes a rule's generation: each rule after a step, or after any chain of steps, carries the generation of the root rule it comes from (`attenuate_generation`, `attenuateAll_generation`), so everything derived from a scoped rule set issued under `g` is issued under `g` (`attenuateAll_generation_eq`).
- The lowering stamps every scoped rule with the generation it is issued under, and the account's generation advances only when a recovery completes ([the generation](#the-generation)).

### Signers outside the chosen rules

`authorize` refuses an authorization in which an authenticated signer is a
signer of no chosen rule (`UnauthorizedSigner`), as OpenZeppelin's
`do_check_auth` does after validating every context and before enforcing any
policy (`smart_account/storage.rs` lines 504–507 at Perch's pin). The check
compares signers exactly, as the signer requirement does. It only refuses more:
`allows`, which has no chosen rules, does not make it, and every batch
`authorize` accepts, `allows_all` still allows.

### Conditions and strings

- `Cond::ArgIn(i, values)` holds when argument `i` exists and equals one of `values`, each compared as `ArgEq` compares (`val_in`). It is Perch's `string-in`, a disjunction over one argument that one rule's conjunctive conditions cannot otherwise express without splitting the rule, which would give each part its own spend record.
- `Val::String(bytes)` is a string argument, as its bytes, distinct from every other constructor: a `Symbol` or `Bytes` value with the same bytes is a different value.
- `Cond::ArgStrPrefix(i, prefix)` holds when argument `i` is a `String` whose first bytes are exactly `prefix` (`bytes_starts_with`). It is Perch's `string-prefix`, which reads only `ScVal::String` arguments.

### Theorems

- **Every Milestone 1 to 3 theorem holds of the extended model.** A statement about a rule's functions reads them as the set `Functions` denotes (`Rule.allows_false_of_functions_nil` takes `functions = .only []`; `rule_allows_call` names `functions_match`). `authorize_eq_ok_iff`, `checkChoice_ok_iff` and `Rule.Refines` include the expiry, generation and signer checks.
- **Conditions** (`Cond.argIn_holds_iff`, `Cond.argIn_holds_iff_argEq`, `Cond.argStrPrefix_holds_iff`) and **strings** (`Val.string_ne_symbol`, `Cond.argStrPrefix_kind`, `Cond.argStrPrefix_false_of_symbol`, `Cond.argEq_string_false_of_symbol`).
- **The wildcard** matches every function of its contract (`Rule.allows_call_any`); removing and restricting keep exactly the expected functions (`Functions.mem_remove`, `Functions.mem_restrict`).
- **`restrict_functions` and `lower_valid_until` narrow** (`restrictFunctions_narrower`, `lowerValidUntil_narrower`), every chain of all ten chain steps stays inside its root, and each step and chain is trace inclusion (`attenuate_traceNarrower`, `attenuateAll_traceNarrower`, through `lowerValidUntil_refines`).
- **The refusals**: an accepted authorization chooses no expired rule (`authorize_validUntil`), no rule of another generation (`authorize_generation`), and authenticates no signer outside its chosen rules (`authorize_signers`); `authorize` stays sound (`authorize_allowsAll`).
- **On the translation**: `authorize_eq`, `restrict_functions_eq`, `lower_valid_until_eq`, `remove_functions_eq`, `cond_holds_eq`, `val_in_eq`, `bytes_starts_with_eq` and `functions_match_eq` prove that each of these functions returns `ok` of the model's result, termination included; `authorize_valid_until`, `authorize_generation`, `authorize_not_chosen_of_stale`, `authorize_contexts_nil_of_stale`, `authorize_signers`, `StepAlong.generation` and `DerivesAlong.generation_eq` carry these theorems to the Rust functions.

### In the restricted subset

- `bytes_starts_with` is one loop over the prefix, reading the string's byte with `get`; `val_in` is one loop over the values; `bytes_list_within` and `bytes_list_extend` each build a vector in one loop.
- The signer check is two functions of one loop each: `signers_chosen` over the authenticated signers, and `signer_chosen` over the choices, reading each rule with `rules.get`.
- Expiry, staleness and `lower_valid_until`'s refusal are matches on an `Option` field, each in a function of its own, so the step keeps one building loop.

## Milestone 4: documents, scopes and the generation

Perch lowers an owner's document to the rules its smart account installs on
OpenZeppelin's. This milestone models the document, states what it means on
chain, lowers it in Rust and in Lean, proves the two lowerings equal and the
lowered rules equal to the document's meaning, defines scoped documents and
the generation, and proves the containment chain. The code is
`crates/rule-eval/src/document.rs`, `lowering.rs` and `scoped.rs`; the model
`formal/RuleCore/Vocab/Document.lean`, `Vocab/Lowering.lean` and
`Vocab/Account.lean`; the theorems `Theorems/Lowering.lean`,
`Theorems/Scoped.lean` and, on the translation, `Theorems/ExtractedLowering.lean`.

### The document

A `Doc` is the part of a Perch policy document that Perch's lowering reads, as
plain data. Its types mirror `perch_ir`'s (`crates/perch-ir/src/doc.rs` of
`bitswell-hq/stellar-registry__perch` at `dff2a73`) without depending on Perch:

- declared signers, each an id and an OpenZeppelin signer;
- rules, each with a scope (a contract, or the account itself for `SelfAdmin`), principals (`All` of some ids, or `Threshold` of some ids and `m`), an optional function list, optional argument predicates (`IsSelf`, `AddressEq`, `StringIn`, `StringPrefix`, `U32Eq`), an optional not-after ledger and an optional cap (a limit and a period);
- an optional recovery configuration, reduced to the contracts it names: the controller and, for a zero-knowledge factor, its adapter and pool.

Identifiers are bytes: an address is its `ScAddress` XDR, a key its decoded
bytes, a function name or a string its bytes. Decoding strkeys and hex is the
caller's job. What the lowering never reads is left out: a document's version
and network, rule names, a cap's token, which Perch's validation makes the
rule's own contract (`CapTokenMismatch`, `crates/perch-ir/src/validate.rs`
line 998), and the rest of the recovery configuration. Self-authenticating
principals, which Perch's lowering refuses, and cross-token caps, which its
validation refuses, are not part of the subset.

`Doc.Valid` is what the theorems take of a document: the signers an `all` rule
names are distinct and fewer than `2^32`, and no not-after ledger is 0. Every
document Perch's validation and document compiler accept meets it
(`DuplicatePrincipalSigner`, `DuplicateSignerId` and `DuplicateSignerKey` at
`validate.rs` lines 718, 737, 766 and 824; `MAX_DOC_SIGNERS`, at most 8, in
`crates/perch-doc-compiler/src/lib.rs` line 57; `ZeroNotAfterLedger` at
`validate.rs` line 971).

### What a document means

`Doc.allows` (without time, generation or caps) and `Doc.authorize` (through an
authorization) are written from Perch's specification as Perch and OpenZeppelin
implement it, at Perch `dff2a73` and `theahaco/stellar-contracts-OZ@33726766`,
the revision Perch pins, and without reference to the lowering:

- a rule applies to calls to its scope's contract, the account for a self-admin scope (OpenZeppelin's `CallContract` context rule type);
- its functions are those it lists, or every function when it lists none (Perch's `FnIn` leaf, absent for a rule without a function list);
- a capped rule allows only a `transfer` whose argument 2 is an `i128`: OpenZeppelin's spending-limit policy meters exactly those calls and refuses every other (`policies/spending_limit.rs` lines 242–245 and 297–301);
- each predicate holds of the argument at its index as Perch's program leaves read it (`crates/perch-program/src/leaf.rs`): `IsSelf` and `AddressEq` an address equal to the account or to the one named, `U32Eq` the `u32` named, given as the `ScVal` XDR of it, `StringIn` a string of at most 256 bytes equal to one of the values, so a longer value never matches, and `StringPrefix` a string that starts with the prefix;
- `All` needs every named signer authenticated, `Threshold(_, m)` at least `m` of them, each counted once;
- a rule with not-after ledger `X` authorizes at ledger `now` only when `now < X`.

`Doc.authorize` checks an authorization as OpenZeppelin's `do_check_auth` does
over the rules Perch installs for the document: the document's rules, then the
recovery rule when it configures recovery (`crates/perch-smart-account/src/rules.rs`
lines 135–164). Every chosen rule must be live at the ledger, belong to the
generation a scoped document was issued under, and allow its context; every
authenticated signer must be named by a chosen rule; and each capped rule's
spend is charged with the cap model of [Milestone 2](#milestone-2-spending-caps).
The recovery rule is checked by the recovery controller against its own
state, which the meaning takes as a parameter.

### The lowering

`lower(d, account)` returns one rule per document rule, in order, then the
recovery rule when `d` configures recovery:

| Document | Lowered rule |
| --- | --- |
| scope `Contract(a)`, `SelfAdmin` | contract `a`, the account |
| no function list, a function list | the wildcard `AnyExcept([])`, `Only` of the list |
| a cap | functions `Only(["transfer"])` when the rule's functions cover `transfer` and `Only([])` otherwise; the condition `ArgI128AtMost(2, i128::MAX)`, which holds exactly when argument 2 is an `i128`; the cap `{limit, period, amount_arg: 2}` |
| `IsSelf`, `AddressEq(a)` at `i` | `ArgEq(i, Address(account))`, `ArgEq(i, Address(a))` |
| `U32Eq(v)` at `i` | `ArgEq(i, Other(u32_xdr(v)))`, where `u32_xdr(v)` is the discriminant `SCV_U32` (3) and the value, each as four big-endian bytes (`stellar-xdr` 30.0.0, `src/generated/sc_val_type.rs` line 81 and `src/generated.rs` line 821) |
| `StringIn(vs)`, `StringPrefix(p)` at `i` | `ArgIn(i, ...)` of the values of at most 256 bytes as strings, `ArgStrPrefix(i, p)` |
| `All(ids)`, `Threshold(ids, m)` | the signers declared under the ids, in order, an id no signer is declared under naming none; threshold their number, or `m` |
| not-after ledger `X` | `valid_until = X - 1`, OpenZeppelin's last ledger (`crates/perch-compile/src/lib.rs` line 256) |
| a recovery configuration | the recovery rule: the account's `apply_doc`, no conditions, no signers, threshold 0 |

No rule the admin document lowers to carries a generation. The recovery rule is
the one construct that is not exact: on chain the recovery controller allows
only the completion of an authorized recovery attempt through it
(`perch-recovery/src/contract.rs` lines 150–169), and the lowered rule allows
every `apply_doc` on the account, which is a sound over-approximation of that
check. The exact check stays with the controller.

### Compile soundness

For every valid document, stated over every context, signer list, ledger,
generation and run:

- **Without time or caps** (`Doc.lowerRule_allows`, `Doc.lowerRules_allows`, `Doc.lower_allows`, `Doc.lower_allows_of_recovery_none`): each lowered rule allows exactly what its document rule allows; the admin document's lowering allows what the document allows or what the recovery rule allows (`recoveryRule_allows`), and exactly what the document allows when it configures no recovery.
- **Through `authorize`** (`Doc.lower_authorize`, `Doc.lower_authorize_of_recovery_none`): on every authorization the lowering accepts exactly when the document accepts, with the recovery controller's check read as every call to `apply_doc` (`applyDocCheck`), and returns the same records. A run of authorizations is a sequence of these, so the lowering and the document accept the same runs with the same records.
- **The over-approximation** (`Doc.authorize_mono`, `Doc.lower_authorize_of_check`): whatever the document accepts under a controller check that accepts only `apply_doc` calls, the lowering accepts with the same records.
- **On the translation** (`lower_eq`, `lower_scoped_eq`, `excluded_eq`): the translated functions return `ok` of the model's lowering on every input, so they terminate and never panic, under the stated rule `LowerRoom` ([`TRUSTED.md`](TRUSTED.md#lowerroom)); `Extracted.lower_allows` and `Extracted.lower_authorize` state the soundness of the translated `lower` followed by the translated `allows` and `authorize`.

The statement covers the rule set the lowering returns. That Perch's
`apply_doc` installs exactly that set, through its reconcile, stays Perch's to
show, as Perch's own `docs/verification/PLAN.md` records under "Not modeled".

### Scoped documents

Perch has one document per account, applied with `apply_doc`. A scoped
document is defined here: a document the owner issues under the admin document
as a grant to an agent or an app. It has the admin document's form and no
recovery configuration. `lower_scoped(d, account, excluded, generation)` lowers
it like the admin document, with each rule carrying `generation`, and refuses
it with `RecoveryConfigured` when it configures recovery and with
`ExcludedScope` when any rule has a self-admin scope or a contract scope on the
account or on a contract of `excluded`. `excluded(admin, account)` is the
excluded set the admin document gives: the account, its recovery controller,
and its zero-knowledge factor's adapter and pool.

This is stricter than what Perch refuses in an admin document, where only the
document's own adapter and pool are refused and a rule may be scoped to the
controller so that the account can act as a guardian
(`validate.rs` lines 1016–1035; `docs/recovery/spec.md` D12). A grant needs
the stricter rule: the account's `execute` calls any contract as the account,
so a scoped rule on the account would be a universal grant, and the account
authorizes `apply_doc` through any ordinary rule scoped to it.

- **Compile soundness** (`Doc.lowerScoped_allows`, `Doc.lowerScoped_authorize`): a scoped document's lowering allows exactly what it allows, and through `authorize` accepts exactly what it accepts in the generation it was issued under, with the same records.
- **Exclusion** (`Doc.lowerScoped_contract`, `Doc.lowerScoped_allows_excluded`, `Doc.lowerScoped_attenuateAll_excluded`): every rule a scoped document lowers to applies to a contract that is neither the account nor in the excluded set, so no such rule set allows a call to one under any signers, and neither does any rule set a chain of attenuation steps derives from it.

### The generation

`Account` models the counter: an address, the admin document and a `u64`
generation. Two events change it. `applyDoc d` applies a new admin document and
keeps the generation. `completeRecovery target` applies the recovery's target
and advances the generation by one; it is the one event that advances it, and
at `u64::MAX` it is refused instead of wrapping to a generation an earlier
scoped document may carry. `Account.issue` lowers a scoped document under the
current admin document's excluded set and the current generation.

- Every scoped rule carries the generation it was issued under, and no admin rule carries one (`Doc.lowerScoped_generation`, `Doc.lower_generation`); a rule set without generations authorizes the same in every generation (`RuleSet.authorize_generation_none`).
- A run keeps the address and advances the generation by exactly the recoveries it completes (`Account.run_address`, `Account.run_generation`).
- After a run that completes a recovery, every grant attenuated from a scoped document issued before it accepts only the empty batch, while the admin rules authorize as before (`Account.issued_stale`, `Account.adminRules_authorize_generation`).

### The chain

`Account.chain`: anything `authorize` accepts under a grant attenuated from the
rules a valid scoped document was issued as

1. is allowed by that scoped document,
2. touches neither the account nor its recovery controller, ZK adapter or pool,
3. and is made in the generation the document was issued under.

`Account.chain_trace` adds the caps: every run the grant accepts from empty
records, the scoped rules accept, with each choice renumbered, and the scoped
rules accept exactly what the scoped document does. `Account.chain_after_recovery`:
once the account completes a recovery, the grant accepts only the empty batch.
`Extracted.chain` and `Extracted.chain_trace` state the same of the translated
`excluded`, `lower_scoped`, attenuation steps and `authorize`: the composition
is proven on the Rust functions themselves.

### What does not compose

- **The recovery rule** allows more in the model than on chain. It sits in the admin layer, and no scoped rule reaches the account, so the chain below the admin document is unaffected; compile soundness for the admin document is an inclusion for that one rule.
- **Exclusion is checked when a scoped document is issued**, against the admin document of that moment. A later admin document, applied with `applyDoc`, may name as its controller, adapter or pool a contract that a live scoped rule reaches. The generation does not advance on `applyDoc`, so it does not end that rule. The shell must refuse such an admin document or end the scoped documents it would expose.
- **The account model has no Rust counterpart.** On the translation, the generation `authorize` receives is the shell's; the chain holds for whatever generation the shell passes, and the recovery corollary needs the shell to keep the counter as the model does.
- **Validity is a hypothesis.** That Perch's validation guarantees `Doc.Valid` is read from Perch's source, not proven, and that the meaning describes Perch on chain is part of the specification ([`TRUSTED.md`](TRUSTED.md#the-documents-meaning)).

### The shell's part of the lowering

A shell that uses the lowering:

- decodes strkeys to `ScAddress` XDR, hex keys to bytes and decimal limits to `i128` before lowering, and gives a `u32` argument to `rule-eval` as `Val::Other` of `u32_xdr` of it;
- installs exactly the rules `lower` returns, and maps each OpenZeppelin rule id to the index of its rule;
- never lets an authorization choose the recovery rule without the recovery controller's check;
- keeps the account-level checks Perch makes before evaluating rules, the reserved-name guard and the freeze while a protected recovery is authorized, which only refuse more.

### What Perch adds in M6

- `apply_scope`: lower a scoped document with `lower_scoped` under `excluded` of its current admin document and its current generation, and install the scoped rules beside the admin document's.
- A generation that advances by one, checked, only when a recovery completes (`SyncOutcome::Completed`), passed to `authorize`. Perch's `recovery_generation` (`crates/perch-smart-account/src/lib.rs` lines 386–389) also advances on recovery reconfiguration, controller switches and executed upgrades, and is read only to make pending upgrades stale.
- A refusal of an admin document whose excluded set names a contract a live scoped rule reaches.
- Lowering with `rule-eval`'s `lower` in its document compiler, or checking its own plan against it, and running the document traces through `compile_doc`, `apply_doc` and `check_auth`.

### Where the lowering lives

The lowering is three modules of `rule-eval` (`document`, `lowering`,
`scoped`), in the restricted subset and with no dependencies. Aeneas translates
one crate per run: a crate of its own would carry its own translation of the
`rule-eval` types it builds, and the instances Aeneas generates for those
types are named after the types alone (`instDiscriminantSignerIsize`), so the
two translations cannot be loaded into one Lean environment. In one crate the
lowering returns the evaluator's own types, and the chain composes on the
translated functions. The modules use `rule-eval`'s public types and its
crate-private byte and signer copies, so a crate of their own is a directory
move plus making those copies public, once one crate's translation can import
another's.

### In the restricted subset

- Each loop is one `while i < s.len()`: resolving an id (`resolve`), the signers under the ids (`named`), the string filter (`strings_within`), the conditions (`lower_args`), the rules (`lower_rules`) and the excluded check (`any_excluded`). `loop_find`, `loop_build` and `loop_any` prove them.
- The names `transfer` and `apply_doc` are byte-string literals copied with `bytes_copy`; `u32_xdr` builds an array of the discriminant and the four bytes of the value, each a division or remainder by a constant cast to `u8` below 256.
- An `All` rule's threshold is its signer count, cast to `u32` under `count <= u32::MAX as usize`; a not-after ledger's last ledger is `u32::saturating_sub(1)`.
- The lowering pushes one more rule than the document has for the recovery rule, and one more condition than a capped rule's predicates for the amount condition; the stated rule `LowerRoom` bounds both.

### Conformance

`conformance/vectors/documents` holds document traces: a document, the account,
optionally the admin document it is issued under and the generation, the
rules the model lowers it to, and authorizations, each with the document's own
verdict and records. The verdicts come from `Doc.authorize`, the meaning, not
from the lowering, so an implementation that lowers the document and checks
the authorizations with its own evaluator should reach them. Every document is
one Perch's validation accepts, and no authorization chooses the recovery
rule. Perch runs them in M6.

## Milestone 5: the Soroban facade

`crates/soroban-facade` gives contract shells the part of soroban-sdk they
use as plain data and two small interfaces, and `formal/RuleCore/Soroban/`
models what they rely on from soroban-env-host 29.0.1. The facade's real
implementation builds against soroban-sdk 29.0.1, which fixes
soroban-env-host 29.0.1 and stellar-xdr 28.0.0 (protocol 29): the protocol
mainnet runs, and the SDK Perch moves to as the first step of M6. A shell
passes the facade its SDK's `Env`, so a shell and the facade share one SDK
major.

### The facade

- **Plain data.** `Val` is `Void`, `Bool`, `U32`, `U64`, `I128`, `Bytes`, `String`, `Symbol`, `Address`, `Vec`, `Map`, or `Other` of the `ScVal` XDR of any other kind (`i32`, `i64`, `u128`, `u256`, `i256`, a time point, a duration, an error). `Address` is an account key, a contract id or a muxed account. `xdr::encode` and `xdr::decode` write and read their XDR; `decode` reads one whole value or nothing, and refuses the `ScVal`s no contract holds as a value (a contract instance, the ledger keys, and claimable balance and liquidity pool addresses, which the host refuses) and the executable tag (CAP-85), which the facade does not model.
- **Storage.** The `Storage` trait is a contract's own storage by `Durability` (persistent, temporary, instance): `get`, `has`, `set` and `remove`. Every method refuses a key that holds a muxed address (`Val::storable`) with `Refusal::MuxedAddress` and changes nothing.
- **`require_auth`.** The `Auth` trait. On the host a refusal aborts the call, so the real implementation returns only `Ok`, or a refusal for a muxed address, which is no `Address` on the host.
- **Authorization contexts.** `AuthContext` is one context `__check_auth` receives: a call (contract, function, arguments) or a creation (executable, salt, constructor arguments). An `Executable` is uploaded Wasm by its hash, or an external reference (CAP-85): the Wasm hash a contract, the owner, keeps under an executable tag, by the owner and the tag's string. `auth_contexts` reads them from the value the host passes, the `contracttype` encoding of SDK 29's `Vec<auth::Context>`, and returns every context or nothing: one context the facade cannot read refuses the whole batch, and nothing panics.
- **`PlainHost`** implements both traits as plain data, for testing a shell without a host: storage as a map, and `require_auth` against the addresses a test has authorized.
- **`SdkHost`**, behind the `sdk` feature, implements them over soroban-sdk. Values cross between the facade and the SDK as XDR: a facade value is encoded by the facade and deserialized by the host (`FromXdr`), and a host value is serialized by the host (`ToXdr`) and decoded by the facade. A facade value whose XDR `decode` does not read back, such as an `Other` holding an executable tag, is refused (`Refusal::Undecodable`) before it reaches the host. Its surface is storage by durability, `Address::require_auth`, `Bytes` and the host's serialization; `SdkHost::auth_contexts` reads `__check_auth`'s third argument given as a raw value, so an undecodable context is the facade's refusal, not the SDK's trap. [`TRUSTED.md`](TRUSTED.md#sdk-items-the-real-implementation-calls) lists every SDK item it calls.

The restricted subset binds `rule-eval` alone. The facade uses ordinary Rust
(derived traits, iterators), is `no_std` with `alloc`, forbids unsafe code,
and builds for native and `wasm32v1-none` with and without `sdk`.

### The conversion

`to_rule_eval` turns an `AuthContext` into `rule-eval`'s `Context`, a
denotation of the same kind as `Equiv/Denote.lean`, written in Lean as
`AuthFn.toChain` and `Val.toChain`:

- a call becomes a call of the contract's `ScAddress` XDR, the function name and each argument read;
- an argument that is an `i128`, a `u64`, a `bool`, bytes, a string or a symbol stays one; an address becomes `Address` of its `ScAddress` XDR; every other value becomes `Other` of its full `ScVal` XDR, so a `u32` is exactly the `u32_xdr` Perch's lowering compares a `u32` with;
- a creation becomes a creation, which no rule allows, of the executable's identity (`Executable::id`, `Executable.id`): the Wasm hash, or for an external reference the `ScVal` XDR of the reference, which is longer than any hash (`Executable.id_externalRef_length`).

The theorems show that `rule-eval` reads a value as one of its constructors
only when it is one, and an address's XDR only when it is that address
(`Val.toChain_eq_address_xdr_iff`, `Address.xdr_injective`), so a rule's
condition on an argument pins down the host's value. The facade is not
translated to Lean; the value and context vectors test its XDR, its reading
and its conversion against the model, and the host harness tests them
against what the host passes ([`TRUSTED.md`](TRUSTED.md#the-facades-conversion)).

### The Lean models

`formal/RuleCore/Soroban/` is written from soroban-env-host 29.0.1's source
and is trusted specification ([`TRUSTED.md`](TRUSTED.md#the-soroban-models)).

- **Storage as a map** (`Storage.lean`). A `Store` maps a slot, a contract, a durability and a key, to a value; each contract and each durability is its own map. `Op.apply` is `get`, `has`, `set` and `remove`, refusing a key holding a muxed address anywhere in it, as the host's storage-key conversion does (CAP-67). Keys and values are facade values, so no key is an executable tag, the one key the host treats apart (CAP-85: persistent only, a Wasm hash as its value, never removed). Instance storage is part of the store: host 29.0.1 keeps a call's instance writes in its frame and writes them back before a re-entrant `__check_auth` of the same contract and when the call returns (host #1617, from protocol 25), and no other frame can see them, so a single store gives the same observations.
- **Signed trees and matching** (`Auth.lean`). An `Entry` is an address's signed `Invocation` tree with a nonce, a last valid ledger, a signature and `Credentials`: `address` (`SOROBAN_CREDENTIALS_ADDRESS`), `addressV2` or `withDelegates` (CAP-71). A `Tracker` follows the host's `AccountAuthorizationTracker`: the nodes already matched, one match state per frame on the call stack, and whether the entry was authenticated. `Tracker.extend` matches a `require_auth` of the top frame against the first unmatched child of the deepest matched node on the stack, or against the root when no frame on the stack matched it.
- **Calls, rollback and authorization** (`Host.lean`). A `Call` runs `Step`s; `execCall` pushes a frame, and when the call fails puts back the store, the used nonces and every tracker as they were at the push, so a caught failure (`try_call`) leaves the caller to go on and an uncaught one fails it. A call of a contract already on the call stack fails before its frame. `requireAuth` holds when the frame's direct caller is the address (the invoker rule); otherwise the first tracker of the address that matches decides, a root matching only while no other tracker of the address is active and unmatched in this frame (the host's guard against joining disjoint entries into one call tree). The first match authenticates the entry: the address's `__check_auth` runs with the payload, the signature and the tree's contexts in preorder, then the signature must not have expired, then the nonce is consumed. `__check_auth` is refused when the account is on the call stack below the current frame; a delegate's is called with the top-level payload and contexts and its own signature, is refused when the delegate is on the call stack, and each listed delegate may be used once. An `Event` log records every `__check_auth` call, read and `require_auth` that held, and is never rolled back.
- **What `__check_auth` receives.** `Entry.preimage` is what the payload hashes: the ledger's network id, the address when the credentials bind it (`addressV2` and `withDelegates`), the nonce, the last valid ledger and the whole tree; `Invocation.preorder` is the contexts, and `AuthFn.toVal` the form the host passes each one in, with a creation's `Executable` as `Wasm` and the hash or `ExternalRef` and the owner and tag, which `contextsOfVal` reads back.
- **A shell's rule check** is an account step: `checkRules rules authenticated` fails unless `rule-eval`'s rule set allows every received context (`Chain.RuleSet.allowsAll` over `AuthFn.toChain`). It is what a shell's `__check_auth` does with the facade and `rule-eval`, and it is how the models meet the evaluator.

### Theorems

`Theorems/Soroban.lean` proves, on the models:

- storage is a map, with durabilities and contracts apart, and a muxed key is refused changing nothing;
- `rule-eval`'s reading of a context is exact: creations are creations, a `u32` is `u32Xdr`, constructors and addresses are read only for themselves;
- the host's encoding of contexts reads back as the same contexts, creations from uploaded Wasm and from an external reference alike;
- every `__check_auth` call receives its payload's tree in preorder, root first, so never an empty batch, and a delegate receives the authenticated entry's payload and contexts (`Tx.run_checkAuth_contexts`, `authenticate_checkAuth`);
- **the containment link**: every `require_auth` an entry satisfies is for a node of the entry's tree, and every rule set the address's `__check_auth` checks allows that node's context (`Tx.run_authorized_allowed`). With `allows_all_eq`, the translated `allows_all` gives the same verdict;
- `__check_auth` reads the store as the requiring call left it, its own instance writes included (`authenticate_store`, `runAccount_get`);
- a failed call or transaction leaves storage and the used nonces as they were (`execCall_fail`, `Tx.run_fail`).

The containment link needs three facts that are not theorems: that the
models describe the host (tested below), that the shell's `__check_auth`
checks its contexts with `rule-eval` before accepting, and that it reads them
with the facade.

### The vectors and the harness

`conformance/generator` computes the Soroban vectors with the models
(`conformance/vectors/soroban`): value vectors with their XDR, `rule-eval`'s
reading and whether they may be keys; context vectors with what the model
reads; storage traces; and host traces, each a set of account programs and
transactions of call trees and signed entries with the model's outcome,
events and storage. The named host traces are the host's own cases: an exact
tree; mismatched arguments; a replayed nonce; an expired signature and one
valid in its last ledger; a refusing `__check_auth`; a nested tree with one
`__check_auth`; a nested call missing from the tree; disjoint entries; a tree
rooted below the top call; a signed node that never runs; two
`require_auth`s in one frame with one entry and with two; two signers;
address-bound payloads; delegation, nested delegation and its refusals; the
invoker rule; an account deeper on the call stack; re-entrant instance
storage both ways; rollback of an error and a trap, caught and uncaught; an
authorized call rolled back with its nonce and its match; a re-entrant call;
a muxed key; and accounts that check their contexts with `rule-eval`.
Randomized traces add call trees with their entries changed.

`conformance/host` replays them on the host. Each contract of a trace is a
native test contract that runs what the trace says: before each call the
harness hands the callee the body the trace gives that call, so two calls of
one context may run different bodies. Each transaction's
entries are installed with `set_auths` and its top call is invoked with
`try_invoke_contract`, so the host runs its enforcing authorization: it calls
`__check_auth`, consumes nonces, checks expiry and matches trees. The harness
compares outcomes, every event (each `__check_auth`'s payload against SHA-256
of the model's preimage, its signature, and its contexts as the host's value,
as the facade's real implementation reads them and as `rule-eval` reads
those) and storage after each transaction; it compares refusals as refusals,
since the host reports every refusal to the caller as the same error. With the
`facade` feature, which the pinned crate turns on, storage, `require_auth`,
the reading of contexts and the account's rule check go through
`soroban-facade`'s real implementation and `rule-eval`, so each host trace
also tests the shell's path from the host's contexts to the evaluator's
verdict.

The harness also reads every context vector with the SDK's `auth::Context`,
the type a shell's `__check_auth` takes its contexts as: the SDK reads a
vector exactly when the model does, and writes what it read back as the same
XDR. And it checks that the facade's real implementation refuses an
executable tag as a key or a value, which the host itself would take.

The harness source (`conformance/host/src`, `conformance/host/tests`) is one
crate per host version, named `soroban-host-p<protocol>` with its library
named `harness`:

| Entry | SDK | Host | Protocol | Lock | Through |
| --- | --- | --- | --- | --- | --- |
| `p29` | soroban-sdk 29.0.1 | soroban-env-host 29.0.1 | 29 | the workspace's, shared with the facade | the facade's real implementation (`facade`, on by default), and the SDK directly (`--no-default-features`) |
| `p30` | soroban-sdk 30.0.0-rc.1 | soroban-env-host 30.0.0 | 30 | its own (`[workspace]` in its `Cargo.toml`) | the SDK directly |

A crate whose SDK is not the facade's leaves `facade` off, since the facade's
real implementation takes soroban-sdk 29.0.1's `Env`. Running `p29` both ways
separates a facade difference from a host difference: the two SDK runs differ
only in the host. Each crate names `soroban-env-host` at the version its SDK
fixes, so the harness can turn the host's diagnostic events off (they are no
part of what it compares, and with them on, a native contract's storage call
refused for a muxed key spends the host's shadow budget and testutils' next
record of the authorizations panics, on both hosts). Neither entry needs a
`cfg` gate in the shared source or a lock pin beyond its SDK.

`host.yml` runs three checks on every pull request and push to `main`, each
with no condition and no allowed failure: `Host 29.0.1 (facade)`,
`Host 29.0.1 (SDK)` and `Host 30.0.0 (SDK)`. Each lints the harness with
clippy and replays every Soroban vector, seed traces included. Every vector
agrees on both hosts: no host behaviour the vectors exercise changed from
29.0.1 to 30.0.0.

### The host's own tests

`conformance/generator/Conformance/Soroban/Seed.lean` transcribes the
authorization and storage tests of soroban-env-host 29.0.1 into traces of
the existing formats, in `conformance/vectors/soroban/seed/host` and
`seed/storage`:

- `src/test/auth.rs`: every case of `AuthTest::tree_test_enforcing` and its two variants (addresses passed with duplicates, addresses read from storage), parsed from the test source with each setup tree, signed tree and expected `success`, and the `verify_nonces_consumed` after it; and `test_out_of_order_auth`. A host test's Stellar-account signers become contract accounts whose `__check_auth` accepts, so the case still tests the matching; the credentials alternate `ADDRESS_V2` and `ADDRESS` as in the test. `tree_fn`'s `require_auth_for_args(addr, [])` is a `require_auth` in a call with no arguments, which has the same context.
- `src/test/auth_delegation.rs`: each case whose test account only checks its payload or contexts and delegates (`BuiltinDelegated`), as a trace of its own, since each case gives its accounts their own programs. The payload and contexts the account checks are checked on every `__check_auth` event instead.
- `src/test/storage.rs`: the storage operations of `test_storage` on each durability and of `test_storage_mix`, and the muxed-address cases.
- `src/test/invoker_auth.rs` and `src/test/frame.rs`: nothing; every test there is about `authorize_as_current_contract` or a host-internal function.

Each case keeps the host test's own expectation. `gen-vectors` runs every
trace on the model and writes nothing when the model's outcome for a case,
or a nonce count, differs from the host test's; otherwise each trace carries
the model's outcome, events and storage like any other, and the harness
replays it on every host entry. `seed/coverage.json` records, for each of the
74 tests of the five files, whether the traces express it, how many of its
cases, how many agree, and why each case or test left out is outside the
models:

| | Tests | Cases |
| --- | --- | --- |
| In the five files | 74 | |
| Expressed | 27 | 155 of their 213 |
| The model agrees with the host test | | 155 |
| The model disagrees | | 0 |
| Outside the models | 47 | 58 more in the expressed tests |

The cases outside are recording authorization, `authorize_as_current_contract`,
`require_auth` inside `__check_auth`, `require_auth_for_args` with other
arguments, accounts whose `__check_auth` branches on storage or calls other
contracts, `get_delegated_signers`, Stellar-account signers and delegates,
the host's validation of the delegate list (order, duplicates, depth), test
accounts comparing their payload or contexts with values the test computed,
time to live, footprints, size limits, a muxed key in instance storage, and
host-internal functions. The transcription is of 29.0.1; a later host's tests
are read as a diff against it when the window moves.

### What the models leave out

Time to live, archival and restoration; footprints, fees and resources; the
checks stellar-core makes before the host runs a transaction (which protocol
admits which credentials, frozen keys); Stellar accounts' ed25519 signatures
and source-account credentials (only contract accounts authenticate);
`require_auth` inside `__check_auth`, `require_auth_for_args` and
`authorize_as_current_contract`; contract creation as a call (a creation
context is data the facade reads); executable tags (CAP-85), which the facade
refuses; a muxed key in instance storage, which host 29.0.1 refuses only when
it writes the instance back at the end of the call; and every protocol but
29 (the vectors also run on host 30.0.0, which tests the models at protocol
30 as far as they reach). The vectors stay inside this domain
(`Trace.inDomain`): contract accounts, valid symbols, maps keyed in the host's
order, and transactions within 16 ledgers, so temporary entries and used
nonces stay live.

### Keeping the models in step with the host

A model is only as current as the host version it is tested against. As
built:

- one pin, soroban-sdk 29.0.1 with soroban-env-host 29.0.1 (protocol 29, the protocol mainnet runs), which the facade and the shells build against;
- the same vectors on a window of two hosts, the pin's and the next release's (29.0.1 and 30.0.0, `host.yml`), so a host change shows as a failing check before the network adopts it, since stellar-core releases a host before the network votes its protocol in;
- the host's own authorization and storage tests of the pin's release, transcribed once as seed traces ([above](#the-hosts-own-tests));
- models parameterised by protocol only when a theorem must hold across a protocol change.

A bump is a pull request, and it must pass every check:

- **Moving the window** (a new next release, such as 31.x): add `conformance/host/p31` as a copy of `p30` with its package name, its SDK and host pins and a fresh `Cargo.lock` (`cargo generate-lockfile`), add its entry to `host.yml`'s matrix, and drop the oldest entry that is not the pin. A pre-release SDK becomes the release by changing the pin in place. If a vector fails on the new entry, the pull request reports it as a host behaviour change against the pinned protocol's models; the vector and the model stay as they are until the pin moves.
- **Moving the pin** (the network's protocol advances): point the facade, `p29`'s successor and the workspace lock at the new SDK, read the host's history between the two releases for the files the models are written from, and record each change and its effect on the models, as below. A failing vector means changing the model and its proofs, or not moving. Transcribe the new release's tests as a diff of the five test files against the transcribed release, with the coverage updated.

#### The host changes of protocol 30

Read from soroban-env-host 30.0.0 against 29.0.1: `auth.rs`, `storage.rs`,
`host/frame.rs`, `host/data_helper.rs`, `builtin_contracts/account_contract.rs`
and `builtin_contracts/common_types.rs` are unchanged, so matching, rollback
and storage are the same source.

| Change | Model in scope | Effect |
| --- | --- | --- |
| CAP-84: `SC_ADDRESS_TYPE_MUXED_CONTRACT`, an address type (`host/conversion.rs`, `host.rs`, `builtin_contracts/base_types.rs`), refused in storage keys as a muxed account is | Values; storage key domain | Outside the facade's values: the facade's reader reads no muxed contract, so a context or value holding one is refused before `rule-eval` sees it. The storage model is unchanged. |
| ML-DSA signature verification and its cost types (`crypto/ml_dsa.rs`, `budget.rs`) | None | New host functions no model uses. |
| testutils' default ledger protocol 30 | None | The entry runs at protocol 30 (`the_host_runs_the_pinned_protocol`). |

Every vector, the seed traces included, agrees on 30.0.0.

#### The host changes of protocols 28 and 29

Read from soroban-env-host's history between v27.0.1 and v29.0.1 (`auth.rs`,
`storage.rs`, `host/frame.rs`, `host/data_helper.rs` and the built-in account
contract) and from the CAPs of each protocol, with what each does to the
models:

| Change | Model in scope | Effect |
| --- | --- | --- |
| CAP-85 (p28): `ContractExecutable::ExternalRef` in creation contexts, as `Vec[ExternalRef, {owner, tag}]` | What `__check_auth` receives | `AuthFn.create` carries an `Executable`, Wasm or external reference; `Executable.ofVal` and the facade read both; `rule-eval` reads a creation of `Executable.id`. Proven: `Executable.ofVal_toVal`, `AuthFn.ofVal_toVal`, `AuthFn.allows_create`. |
| CAP-85 (p28): executable tags (`SCV_EXECUTABLE_TAG`) as storage keys, persistent only, valued with an uploaded Wasm hash, never removed | Storage | Outside the facade's values: `decode` reads none, and the real implementation refuses one before the host does. The storage model is unchanged. |
| CAP-85 (p28): recording-mode authorization of external-reference creations | None | Recording mode (simulation) is not the enforcing path the models describe. |
| CAP-86 (p28): sparse `Symbol`-keyed map host functions | None | The facade reads contexts itself; the harness shows SDK 29 reads exactly the context vectors the model reads. |
| CAP-83 (p28): validators vote to drop a transaction set | None | Consensus, outside the host. |
| Host #1729 (p29): `extend_ttl` clamps `extend_to` instead of failing | None | Time to live is not modelled. |
| Host #1698 (p28): ledger entries decoded lazily in the end-to-end path | None | Same observations; the storage traces pass on 29.0.1. |
| Host #1716 (p28): VM linear memory refunded | None | Resources are not modelled. |
| Host #1720 (p29): native test contracts get their own Wasm entries and roll back constructor failures | None | Test-only; the harness's native contracts replay every host trace unchanged. |

Credentials (`address`, `addressV2`, `withDelegates`), tree matching and
rollback are the same at 29.0.1 as at 27.0.1.

#### Existing Soroban verification tools

Each entry below cites the vendor's own docs or source code, at the versions
and commits linked. None of these tools produces a kernel-checked proof, and
each works on a different object from this repository.

- **Certora Sunbeam** (the Certora Prover for Soroban), at release 8.20.3.
  - *Technique.* It compiles a contract's WebAssembly to Certora's intermediate language, TAC, and discharges verification conditions with SMT solvers. A result is verified, violated, a timeout or unknown ([Certora: formally verifying WebAssembly](https://www.certora.com/blog/formally-verifying-webassembly)).
  - *Specifications* are Rust functions marked `#[rule]` that use the CVLR macros `cvlr_assert!`, `cvlr_assume!` and `cvlr_satisfy!` ([Sunbeam usage](https://docs.certora.com/en/latest/docs/sunbeam/usage.html)), with Soroban helpers such as `is_auth` ([cvlr-soroban](https://github.com/Certora/cvlr-soroban/blob/70a9ddfcc4fd4ca49ba5c8866a863f0f37b4b61b/cvlr-soroban/src/auth.rs)).
  - *Host model* ([`wasm/host/soroban`](https://github.com/Certora/CertoraProver/tree/4ef546d00cd67d333914845dead2d72081e1f014/src/main/kotlin/wasm/host/soroban)):
    - contract data is a map from a key and its storage type to a value; TTLs are not modelled;
    - `require_auth` succeeds only where an uninterpreted per-address authorization predicate holds;
    - a host function without a model, such as `require_auth_for_args`, `authorize_as_curr_contract`, `delegate_account_auth` or a cross-contract call, returns an unconstrained value and never refuses.
- **Runtime Verification Komet**, a K semantics of Soroban over KWasm, at v0.1.89.
  - *Technique.* It executes a contract's WebAssembly. `komet test` fuzzes property functions written in Rust, and `komet prove` runs them symbolically over all inputs ([Komet](https://github.com/runtimeverification/komet), [Komet docs](https://docs.runtimeverification.com/komet)).
  - *Host model* ([soroban-semantics](https://github.com/runtimeverification/komet/tree/a078e296621a4f52fd1497fed64435e9948cc830/src/komet/kdist/soroban-semantics)):
    - instance, persistent and temporary storage, with TTLs;
    - cross-contract calls;
    - rollback: the world state is pushed on each call, restored when the call fails, and dropped when it succeeds;
    - `require_auth` and `authorize_as_curr_contract` always succeed (`host/address.md`: "the auth system is out of scope for now"), and no `__check_auth` is called.
- **Galois Formal VerSo** proves properties of Soroban contracts at the MIR level with SAW and crux-mir. Its README describes it as early-stage, supporting a small part of the Soroban API at SDK 0.8.4 ([formal-verso](https://github.com/GaloisInc/formal-verso/tree/68c261bfeb56de03ff2308b57250a16c0ded7a33)). Its Cryptol model of `require_auth` (`lib/Auth.cry`) is limited to one signed call-graph fragment of one node, matched by function name with the arguments ignored, and SAW checks that matching keeps the model well formed. The model has no signature payload, nonces or `__check_auth`, and is not compared with the host.
- **CoinFabrik Scout**, a static analyser of Soroban Rust source built from lint detectors, at 0.3.17 for soroban-sdk 28 ([scout-audit](https://github.com/CoinFabrik/scout-audit/tree/f99a7982e2fd62c79f6e1a8db27bfad900c43802)). It finds known bug patterns, authorization ones among them, and proves nothing.
- **OpenZeppelin Soroban Security Detectors SDK**, a framework for detectors over a contract's syntax tree, with prebuilt checks for improper TTL extension, contract panics and unsafe use of temporary storage, and a `soroban-scanner` command ([soroban-security-detectors-sdk](https://github.com/OpenZeppelin/soroban-security-detectors-sdk/tree/f3888e0619c8cb6a718ee48c69cfe6daa527ed00)). It finds patterns and proves nothing.
- **Flux refinement types** through [soroban-flux](https://github.com/nidohq/soroban-flux/tree/f3d61774bcc6f68a5fc9a3db67cc8d5fab43c0f6). Flux checks refinement-type signatures of Rust functions with an SMT solver. It checks library code without macros, and a contract's `#[contractimpl]` functions stay trusted. Its README describes it as a feasibility spike against soroban-sdk 26.
- **soroban-sdk testutils** run contracts against the real `soroban-env-host` in tests ([`Env`](https://docs.rs/soroban-sdk/latest/soroban_sdk/struct.Env.html)). `set_auths` installs signed authorization entries and runs the host's own authorization, `mock_all_auths` makes every `require_auth` succeed, `auths()` returns the authorization trees of the last call, and `try_invoke_contract_check_auth` calls `__check_auth` directly. Each test writes a snapshot of its authorizations, ledger state and events (`testutils::Snapshot`), and Stellar documents differential testing with those snapshots ([test snapshots](https://developers.stellar.org/docs/build/guides/testing/differential-tests-with-test-snapshots)) and fuzzing with cargo-fuzz on top of testutils ([fuzzing guide](https://developers.stellar.org/docs/build/guides/testing/fuzzing)).

This repository differs from all of these in four ways.

- **The proofs are Lean proofs**, checked by Lean's kernel, about a function's behaviour on every input. The specification is a readable model, not a set of properties.
- **The object is a pure function**, the rule evaluator, translated from its MIR through Charon and Aeneas. Whole contracts and their compiled WebAssembly are not the object, so rustc's back end is trusted ([`TRUSTED.md`](TRUSTED.md#rustc)), where Sunbeam and Komet check the WebAssembly itself.
- **The host enters through small Lean models** of storage, rollback, `require_auth` matching and `__check_auth`'s input, and each model is tested against `soroban-env-host`. Formal VerSo's model of `require_auth` is the nearest counterpart. It matches one signed node by function name, without arguments, and has no signature payload, nonces, delegated signers or `__check_auth` input; none of the tools above tests a model of the host against the host.
- **The tools can complement each other.** A contract shell that uses `rule-eval` can also be checked with Sunbeam or Komet. Those tools would cover the shell's storage and call handling, and this repository covers the rule check.

## Later milestones

These are design notes for work that is not built. Where the brief leaves a
choice open, it is listed under [Open questions](#open-questions) and not
decided here.

### M6: adoption

Perch first moves to soroban-sdk 29, the facade's SDK, on its own fork. It
then moves its pure rule check behind `rule-eval` in small pull requests, and
adds what [Milestone 4](#what-perch-adds-in-m6) leaves to it.
Each one is pinned by a differential test against Perch's current behaviour:
the conformance vectors, plus recorded verdicts of the code being replaced.
The grant signer moves last, onto the budget tree of M3. Each consumer runs
the conformance vectors in its own CI, so a change to the model shows up as a
failing vector in every consumer.

## Open questions

No question is open.
