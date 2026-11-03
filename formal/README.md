# formal

The Lean model of rule evaluation, the Lean translation of `crates/rule-eval`,
and the theorems relating them. The Lake package is `rule-core`
(MIT OR Apache-2.0); its one library is `RuleCore`, rooted at `RuleCore.lean`.

| Directory | Contents |
| --- | --- |
| `RuleCore/Model/` | The generic model: rules with their signers, threshold and optional cap, rule sets, `narrower`, and the nine attenuation steps, over any context and signer type. `Cap.lean` models spending caps: the spend record, the check, runs and windows. `Authorize.lean` models `authorize`, its runs, and narrowing as trace inclusion. `Budget.lean` models the budget tree: spends, delegations, refills and their runs. |
| `RuleCore/Vocab/` | The chain vocabulary (contexts, values, conditions, signers, caps, rules, authorizations) and its denotation into the generic model; Perch's documents, their meaning and validity (`Document.lean`), the lowering and scoped documents (`Lowering.lean`), and the account's generation (`Account.lean`). |
| `RuleCore/Extracted/` | `RuleEval.lean`, the translation of `crates/rule-eval`, the lowering included, that Charon and Aeneas generate. Never edited by hand. |
| `RuleCore/Equiv/` | Denotations from the translated types to the chain vocabulary, the cap model (`DenoteCap.lean`), the budget model (`DenoteBudget.lean`) and the document vocabulary (`DenoteDocument.lean`), and theorems that the translated functions compute the model's results (`Cap.lean` for the cap check, `Authorize.lean` for `authorize`, `Budget.lean` for the budget operations, `Lowering.lean` for the lowering). |
| `RuleCore/Theorems/` | The theorems below, including the model's theorems carried over to the translation (`Extracted.lean`, `ExtractedCap.lean`, `ExtractedAuthorize.lean`, `ExtractedBudget.lean`, `ExtractedLowering.lean`), the cap theorems (`Cap.lean`), the authorization theorems (`Authorize.lean`), the budget theorems (`Budget.lean`), compile soundness (`Lowering.lean`), scoped documents, the generation and the chain (`Scoped.lean`), and kernel-checked examples of concrete verdicts. |
| `RuleCore/Axioms.lean` | The axioms each theorem depends on, pinned under `#guard_msgs`. |

## Building

```sh
cd formal
lake exe cache get   # Mathlib's prebuilt oleans
lake build
```

`lean-toolchain` pins `leanprover/lean4:v4.35.0`, the Lean release of Aeneas
commit `ab34bd28458a08c150b7cbf1873e59af74588138`'s Lean backend. elan installs
it on the first `lake` call.

The package has one Lake dependency, Aeneas's Lean library
(`backends/lean` of Aeneas at that same commit), which the translation is
written against: its `Result` monad, its `loop` combinator and its models of the
Rust library items the evaluator calls. It brings Mathlib and Mathlib's own
dependencies; `lake-manifest.json` pins all of them. `lake exe cache get`
fetches Mathlib's prebuilt oleans, and Lake fetches Aeneas's from its release
archive.

CI (`.github/workflows/lean.yml`) rejects `sorry`, `admit`, `partial`,
`unsafe`, `native_decide`, `implemented_by`, `extern` and `axiom` anywhere in
the Lean sources, the generated translation included, checks that
`RuleCore.lean` imports every module, fetches the Mathlib cache, runs
`lake build`, and then checks that every theorem `claims.yaml` cites is a
theorem of the built package (`tools/check-claims --theorems lean`).

## The generic model

`RuleCore/Model/RuleSet.lean` holds the readable model, generic in the context
type `Ctx` and the signer type `Sig` (with decidable equality):

```lean
structure RuleCap (Ctx : Type) where
  params : Cap.Params         -- at most `limit` within `period` ledgers
  amount : Ctx → Option Int   -- the amount a context spends, if it names one

structure Rule (Ctx Sig : Type) where
  scope : Ctx → Bool          -- contract and function match
  conds : List (Ctx → Bool)   -- conditions on this call's arguments
  signers : List Sig          -- the signers that count towards the threshold
  threshold : Nat             -- how many distinct signers must be authenticated
  cap : Option (RuleCap Ctx) := none  -- the rule's spending cap, if it has one
  validUntil : Option Nat := none     -- the last ledger it authorizes in, if any
  generation : Option Nat := none     -- the generation it was issued under, if any

def Rule.present (r : Rule Ctx Sig) (auth : List Sig) : List Sig :=
  r.signers.eraseDups.filter (· ∈ auth)

def Rule.signed (r : Rule Ctx Sig) (auth : List Sig) : Bool :=
  decide (r.threshold ≤ (r.present auth).length)

def Rule.allows (r : Rule Ctx Sig) (c : Ctx) (auth : List Sig) : Bool :=
  r.scope c && r.conds.all (· c) && r.signed auth

def RuleSet (Ctx Sig : Type) := List (Rule Ctx Sig)

def RuleSet.allows (rs : RuleSet Ctx Sig) (c : Ctx) (auth : List Sig) : Bool :=
  rs.any (·.allows c auth)

def RuleSet.allowsAll (rs : RuleSet Ctx Sig) (cs : List Ctx) (auth : List Sig) : Bool :=
  cs.all (rs.allows · auth)

def RuleSet.narrower (rs' rs : RuleSet Ctx Sig) : Prop :=
  ∀ c auth, rs'.allows c auth = true → rs.allows c auth = true
```

`auth` is the list of signers the authorization authenticated, one list for a
whole batch. `eraseDups` keeps each signer at its first position, so a signer
listed twice in a rule, or authenticated twice, counts once. A threshold of 0 is
no requirement. `Rule.allows` reads neither the cap nor the last ledger nor
the generation; `Rule.expired now` and `Rule.stale gen` are what `authorize`
checks of the last two. `RuleSet` is a plain
definition, so `RuleSet.rules` and `RuleSet.ofRules` convert to and from the
underlying list for list notation.

`RuleCore/Model/Attenuation.lean` defines the attenuation steps. Each names a
rule by its position and returns the new rule set, or
`AttenuationError.noSuchRule` when the position is not below the number of
rules:

* `RuleSet.dropRule i` removes rule `i`.
* `RuleSet.addCond i p` appends condition `p` to rule `i`.
* `RuleSet.restrictScope i s` restricts rule `i`'s scope to the contexts that
  also satisfy `s`.
* `RuleSet.removeSigners i ss` removes every signer in `ss` from rule `i`'s
  signers and keeps its threshold.
* `RuleSet.raiseThreshold i k` sets rule `i`'s threshold to `k`, and is refused
  with `AttenuationError.thresholdLowered` when `k` is below the current
  threshold.
* `RuleSet.addCap i k` gives rule `i` the cap `k`, refused with `capPresent`
  when the rule has a cap and with `invalidCap` when `k`'s parameters are not
  valid.
* `RuleSet.lowerCapLimit i limit` sets the limit of rule `i`'s cap, refused
  with `noCap`, with `limitRaised` above the current limit, and with
  `invalidCap` when `limit` is not positive.
* `RuleSet.lengthenCapPeriod i period` sets the period of rule `i`'s cap,
  refused with `noCap` and with `periodShortened` below the current period.
* `RuleSet.lowerValidUntil i v` sets rule `i`'s last ledger to `v`, refused
  with `validUntilRaised` when the rule has a last ledger before `v`.

No step changes a rule's generation. `Attenuation` names one step, `RuleSet.attenuate` applies one,
`RuleSet.attenuateAll` applies a list in order, and `RuleSet.Derives root rs`
says `rs` is reachable from `root` by zero or more steps. Nothing else is an
attenuation step.

## The chain vocabulary

`RuleCore/Vocab/Chain.lean` (namespace `RuleCore.Chain`) is the vocabulary the
Rust evaluator implements:

* `Bytes` is `List UInt8`. Contract ids, function names and byte payloads are
  compared exactly: equal length and equal bytes, no prefix match, no
  normalization.
* `Val` is `i128 (BitVec 128) | u64 UInt64 | bool Bool | bytes Bytes |
  address Bytes | symbol Bytes | string Bytes | other Bytes`, where `other`
  carries the argument's full XDR. `i128` values compare as signed integers.
  Values of different constructors are never equal: a `string` is never a
  `symbol`, whatever the bytes.
* `Context` is `call contract function args` or `create wasmHash`.
* `Signer` is `delegated address` (an address, as its `ScAddress` XDR) or
  `external verifier key` (a verifier contract's address and a key), compared
  exactly, constructor first.
* `Cond` is `argEq index val` (argument `index` exists and equals `val`),
  `argI128AtMost index n` (argument `index` exists, is an `i128`, and is at
  most `n`), `argIn index vals` (argument `index` exists and is one of
  `vals`) or `argStrPrefix index pre` (argument `index` is a `string` whose
  bytes start with `pre`, `pre <+: v`). A missing argument makes every
  condition false, and another constructor makes `argI128AtMost` and
  `argStrPrefix` false.
* `Functions` is `anyExcept removed` (every function not in `removed`) or
  `only listed` (the functions in `listed`); `Functions.any` is
  `anyExcept []`, and `f ∈ fs` is membership read per constructor.
  `Functions.remove fs gs` drops `gs` from a list and adds them to a
  wildcard's `removed`; `Functions.restrict fs gs` keeps a list's functions
  also in `gs`, and turns a wildcard into the list of `gs` it does not
  exclude.
* `Cap` is `{ limit, period, amountArg }`: an `i128` limit, a `UInt32` period
  and the index of the argument holding a call's amount. `Cap.params` reads
  it as the cap model's `⟨limit.toInt, period.toNat⟩`, `Cap.amount` reads a
  call's argument at `amountArg` when it is an `i128`, and `Cap.valid` is
  `Params.valid` of its parameters.
* `Rule` is `{ contract, functions, conds, signers, threshold, cap,
  validUntil, generation }`, the last two an optional `UInt32` and `UInt64`,
  and `RuleSet` is `List Rule`. A rule whose functions are the empty list
  allows nothing; the wildcard allows every function of its contract.
* `RuleSet.allows rs c auth` and `RuleSet.allowsAll rs cs auth` take the
  authenticated signers `auth`.
* `RuleSet.dropRule i`, `RuleSet.addCond i cond`,
  `RuleSet.removeFunctions i fs`, `RuleSet.restrictFunctions i fs`,
  `RuleSet.removeSigners i ss`, `RuleSet.raiseThreshold i k`,
  `RuleSet.addCap i k`, `RuleSet.lowerCapLimit i limit`,
  `RuleSet.lengthenCapPeriod i period` and `RuleSet.lowerValidUntil i v` are
  the attenuation operations.
  `removeFunctions` and `removeSigners` remove every occurrence of every
  function in `fs` or signer in `ss` and keep the rest in order; `dropRule`
  keeps the remaining rules in their order; `addCond` appends;
  `raiseThreshold` refuses to lower a threshold. Each returns the new rule set,
  or `AttenuationError.noSuchRule` when `i` is not below the number of rules.
* Argument and rule indices and thresholds are `UInt32`, as in the Rust
  evaluator, read as list positions and counts through `toNat`.

`Rule.denote` gives each rule's meaning as a generic `Rule Context`: its scope
matches a call to the rule's contract and one of its functions, and each
condition reads the arguments of the call it is evaluated against. Every scope
and every condition is false on a creation. `allows`, `allowsAll` and
`narrower` on chain rule sets are the generic ones on the denotation, and
`Attenuation.denote` maps each chain step to the generic step of the same kind
at position `i.toNat`: `removeFunctions i fs` denotes
`restrictScope i.toNat (notCalling fs)`, `restrictFunctions i fs` denotes
`restrictScope i.toNat (calling fs)`, `lowerValidUntil i v` denotes
`lowerValidUntil i.toNat v.toNat`, and the signer steps denote the
generic steps of the same name, as do the cap steps, with the cap denoted by
`Cap.denote` and the limit and period read through `toInt` and `toNat`. A chain
rule's signers and threshold are the generic rule's, its cap the denoted cap,
and its last ledger and generation the generic rule's, read through `toNat`.
`Authorization` is `{ contexts, choices, auth, now, generation }` with `UInt32`
choices and ledger and a `UInt64` generation, and `RuleSet.authorize` is the
generic authorization of the denotation, those read through `toNat`.

## The extracted evaluator

`tools/extract.sh` regenerates `RuleCore/Extracted/RuleEval.lean`: Charon
translates `crates/rule-eval` to LLBC (`--preset=aeneas --error-on-warnings`)
and Aeneas translates the LLBC to Lean (`-backend lean -warnings-as-errors`).
Both tools come from the repository's flake, which pins Aeneas
`ab34bd28458a08c150b7cbf1873e59af74588138`, the Charon commit it fixes
(`7b462d9159db2ed3015162352183906a30bfafc6`) and the Rust nightly Charon reads
MIR with (`nightly-2026-09-17`). The script needs Nix with flakes; without
Nix it runs in the `nixos/nix` image (see the script's header). CI
(`.github/workflows/extraction.yml`) runs `tools/extract.sh --check`, which
regenerates the file and fails if it differs from the committed one.

Aeneas puts the items of each module of the crate in a namespace named after
the module: `rule_eval.rule.Rule`, `rule_eval.rule_set.allows`,
`rule_eval.attenuate.drop_rule`, `rule_eval.signer.signers_met`. Each `while`
loop becomes a `loop` over a body
that returns `cont` to go round again or `done` to exit. `loop` is a
`partial_fixpoint`, so it may diverge, and every function returns a `Result`
that may fail. A theorem that a translated function returns `ok v` therefore
says it terminates, does not fail, and returns `v`.

## Equivalence

`RuleCore/Equiv/Denote.lean` maps the translated types to the chain
vocabulary. The denotations are part of the specification. Each is structural:
a byte string (`Vec<u8>`, a structure over `List Std.U8`) is the `Bytes` of the
same bytes; an `i128` is its bit vector, a `u64` and a `u32` the `UInt64` and
`UInt32` with the same bit vector; `Val`, `Context`, `Cond`, `Functions` and
`Signer` map each constructor to the constructor of the same name; `Rule` maps
each field to the field of the same name, its optional `valid_until` and
`generation` to the optional denoted `UInt32` and `UInt64`; a slice or vector of rules or signers is the list
of its elements' denotations (`denoteRules`, `denoteSigners`);
a `Cap` is the chain cap of the same limit, period and argument index
(`denoteCap`), and a rule's optional cap the optional denoted cap;
each `AttenuationError` constructor is the error of the same name, and a Rust
`Result` of an attenuation step is the `Except` with the denoted payload
(`denoteOutcome`). Every denotation is injective (`denoteVal_injective`,
`denoteContext_injective`, `denoteCond_injective`, `denoteFunctions_injective`,
`denoteSigner_injective`,
`denoteSigners_injective`, `denoteCap_injective`, `denoteRule_injective`,
`denoteRules_injective`, `denoteOutcome_injective`).

On every input, the translated functions return `ok` of the model's result on
the denotations:

* `allows_eq`: `allows rules c authenticated = ok ((denoteRules rules).allows (denoteContext c) (denoteSigners authenticated))`.
* `allows_all_eq`: `allows_all rules cs authenticated = ok ((denoteRules rules).allowsAll (cs.map denoteContext) (denoteSigners authenticated))`.
* `signers_met_eq`, `signed_count_eq`: the signer requirement and the count of
  distinct authenticated rule signers are the model's.
* `functions_match_eq`, `val_in_eq`, `bytes_starts_with_eq`: a rule's
  functions, `ArgIn`'s membership and `ArgStrPrefix`'s prefix test are the
  model's.
* `drop_rule_eq`, `restrict_functions_eq`, `remove_signers_eq`,
  `raise_threshold_eq`: the step returns `ok res` with `denoteOutcome res` the
  model's `dropRule`, `restrictFunctions`, `removeSigners` or
  `raiseThreshold` of the denotations, `noSuchRule` and `thresholdLowered`
  included.
* `add_cond_eq`, `remove_functions_eq`: the same for `addCond`, under the
  stated rule `CondRoom`, and for `removeFunctions`, under the stated rule
  `FunctionsRoomAt`, which every rule with a function list meets
  (`functionsRoom_only`).
* `add_cap_eq`, `lower_cap_limit_eq`, `lengthen_cap_period_eq`,
  `lower_valid_until_eq`: the same for the cap steps and the last-ledger step,
  every refusal included.

The signer count is a fourth loop shape, `loop_count`: a counter that grows by
at most one per position, so it stays at most the position and its increment
cannot overflow. `countFrom_first` shows that counting each signer at its first
position, when it is authenticated, is the length of the model's
`present` list.

### The rules `add_cond` and `remove_functions` need

Aeneas's model of `Vec::push` fails once the vector holds `Usize.max`
elements. Every push in the evaluator but two appends to a vector holding at
most one element per position of a slice already walked, so it cannot reach
that bound. The exceptions are `add_cond`, which appends to the condition
vector of the rule at `index`, and `remove_functions` on a wildcard, which
appends the removed functions to the ones it excludes (`bytes_list_extend`). `add_cond_eq` therefore takes
`CondRoom rules index`: the rule at `index`, when there is one, holds fewer
than `Usize.max` conditions. `add_cond_full` shows the rule is exact: on a rule
already holding `Usize.max` conditions, the translated `add_cond` fails with
`maximumSizeExceeded`. In Rust a `Vec<Cond>` never reaches that length: a
`Vec` holds at most `isize::MAX` bytes. The theorems about the translation do
not depend on `CondRoom`: an `add_cond` that returned `Ok` had room
(`add_cond_room`). `remove_functions_eq` likewise takes
`FunctionsRoomAt rules index functions`: a wildcard at `index` excludes, with
`functions`, at most `Usize.max` names. `remove_functions_full` shows that rule
is exact, and `remove_functions_room` reads it off a step that returned `Ok`.

## Spending caps

`RuleCore/Model/Cap.lean` models the spending-cap check of `crates/rule-eval`'s
`cap` module. Ledgers are natural numbers and amounts integers. `addI128` and
`subI128` are `i128::checked_add` and `i128::checked_sub`, and `now - period`
is truncated subtraction, which is `u32::saturating_sub`.

* `Entry` is `{ ledger, amount }` and `Record` is `{ history, total }`;
  `Record.empty` has no entries and total 0.
* `Params` is `{ limit, period }`, and `Params.valid` holds for `limit > 0` and
  `period > 0`.
* `evict cutoff h removed` drops entries from the front of `h` while their
  ledger is at most `cutoff`, adding their amounts to `removed` with `addI128`.
* `Params.check p r now amount` is the check: `negativeAmount` for a negative
  amount; `r` itself for a zero amount; `ledgerBeforeNewest` when `now` is
  earlier than the ledger of the history's last entry; then eviction at
  `now - p.period`, `overflow` for a sum outside `i128`, `limitExceeded` when the
  kept total plus the amount exceeds the limit, `historyFull` when the kept
  entries number `maxHistory` (1000), and otherwise the kept entries followed by
  `(now, amount)`, with their total.
* A run is a list of `Call`s `{ now, amount }`. `Params.run` keeps the record
  after a refused call, `Params.runAll` fails at the first refusal, and
  `Params.Accepts p r calls` says every call is accepted. `Params.recorded`
  lists the spends a run recorded, the accepted calls with a positive amount.
* `Params.inWindow p t e` holds when `t - period < e.ledger ≤ t`: the window
  eviction leaves at `t`. `Params.inPeriodFrom p s e` holds when
  `s ≤ e.ledger < s + period`: `period` consecutive ledgers from `s`.
* `Params.narrower q p` is `q.limit ≤ p.limit ∧ p.period ≤ q.period`, and
  `capNarrower` extends it to a rule that may have no cap.
* `Record.Valid r`: the history is in ledger order, its amounts are positive,
  and the total is their sum and at most `i128Max`.

`RuleCore/Equiv/DenoteCap.lean` maps `SpendEntry`, `SpendRecord`, `CapParams`
and `CapError` field for field and constructor for constructor, a `u32` to its
value as a natural number and an `i128` to its value as an integer. Every
denotation is injective. `check_spend_eq` proves that the translated
`check_spend` returns `ok` of `Params.check` on the denotations, on every input
and with no stated bound: every push copies from a slice or follows the
history-bound check. The eviction loop, whose state carries the running total
of the evicted amounts, has its own induction (`evict_loop_eq`).

## Authorization

`RuleCore/Model/Authorize.lean` models `authorize`. An `Authorization` is a
batch of contexts, the index of the rule chosen for each (`choices`), the
authenticated signers, the ledger `now` and the current `generation`;
`records` holds one `Cap.Record` per rule.

* `RuleSet.authorize rs records a` refuses `choicesMismatch` and
  `recordsMismatch` for lists of the wrong length, then runs
  `RuleSet.checkChoice` on every context with its choice (`noSuchRule`,
  `expired`, `staleGeneration`, `notAllowed`), then `RuleSet.checkSigners`
  (`unauthorizedSigner` when an authenticated signer is a signer of no chosen
  rule, `RuleSet.signerChosen`), then folds `RuleSet.charge` over them in
  order: a context
  whose chosen rule has a cap must name an amount under it (`noAmount`) and is
  charged to the rule's record with `Cap.Params.check` (`cap e`).
* `RuleSet.step` keeps the records after a refusal, `RuleSet.run` folds it over
  a list of authorizations, `RuleSet.authorizeAll` fails at the first refusal
  and `RuleSet.Accepts` says every authorization is accepted.
* `Authorization.charges a k j` lists the calls `a` charges to rule `j` under
  its cap `k`, `RuleSet.charged` those of every accepted authorization of a
  run, and `RuleSet.spent` the positive ones as entries.
* `RuleSet.TraceNarrower rs' rs f`: every run `rs'` accepts from its empty
  records, `rs` accepts from its own, each choice `j` renumbered to `f j`.
  `Attenuation.source` is the renumbering a step induces and
  `Attenuation.chainSource` its composition along a list of steps.
* `RuleSet.capsValid`: every cap of the rule set is valid.

`RuleCore/Equiv/Authorize.lean` maps `Refusal` constructor for constructor,
`authorize`'s result to the `Except` of the denoted records, and its arguments
to the chain authorization of their denotations (`denoteAuthorization`), and
proves `authorize_eq`: on every input, the translated `authorize` returns `ok`
of `Chain.RuleSet.authorize` on the denotations. Its loops have their own
inductions (`check_choices_loop_eq`, `signer_chosen_eq`, `signers_chosen_eq`,
`charge_all_loop_eq`); expiry and staleness are `expired_eq` and `stale_eq`;
the charge writes through `get_mut` (`slice_get_mut_eq`).

## Budgets

`RuleCore/Model/Budget.lean` models the `budget` module. Indices are natural
numbers and amounts integers; sums are `Cap.addI128`, `i128::checked_add`.

* `Node` is `{ parent, allowance, spent }`, with `parent : Option Nat`, and a
  `Tree` is a list of nodes. `Node.valid i n` holds when `n`'s parent index is
  below `i` and its allowance and spent amount are not negative, and
  `Tree.valid` when every node is valid at its position.
* `Node.fits n amount` holds when `addI128 n.spent amount` is some total at
  most `n.allowance`.
* `Tree.walk t amount fuel i` walks from `i` toward its root, refusing
  `overdrawn i` at the first node that cannot take the amount and returning the
  walked nodes otherwise; `Tree.charge t path amount` adds the amount to the
  nodes of `path`.
* `Tree.spend t i amount` refuses `malformed`, `noSuchNode i` and
  `negativeAmount` in that order, then walks with the tree's length as fuel and
  charges the path. `Tree.delegate t p allowance` refuses `malformed`,
  `noSuchNode p`, `negativeAmount` and `treeFull` (at `maxNodes`, `u32::MAX`
  nodes), and otherwise appends `⟨some p, allowance, 0⟩`. `Tree.refill t i
  amount` refuses `malformed`, `noSuchNode i`, `negativeAmount` and `overflow`,
  and otherwise raises node `i`'s allowance.
* An `Op` is a spend, a delegation or a refill. `Tree.run` applies a list of
  them, keeping the tree after a refusal and logging each successful spend.
  `Tree.Within t i a` holds when `a` is `i` or one of its ancestors, and
  `spentUnder t log a` totals the logged spends made at or under `a`.

`RuleCore/Equiv/DenoteBudget.lean` maps `Node` and `BudgetError` field for
field and constructor for constructor, a `u32` to its value and an `i128` to its
value. Every denotation is injective. `spend_eq`, `delegate_eq` and
`refill_eq` prove that each translated operation returns `ok` of the model's on
the denotations, on every input and with no stated bound. The walks carry a
current index and a step count, and each has its own induction on the steps
left (`check_chain_loop_eq`, `charged_loop_eq`); the charging walk writes
through `get_mut`.

## Documents

`RuleCore/Vocab/Document.lean` models the part of a Perch policy document that
Perch's lowering reads, in namespace `RuleCore.Document`:

* a `Doc` is declared signers (`SignerDecl`, an id and a chain signer), rules
  and an optional `Recovery` (a controller and an optional `ZkFactor` of an
  adapter and a pool);
* a `Rule` has a `Scope` (`contract a` or `selfAdmin`), `Principals` (`all ids`
  or `threshold ids m`), optional functions, optional argument constraints
  (`ArgConstraint`, an index and a `Pred`: `isSelf`, `addressEq`, `stringIn`,
  `stringPrefix`, `u32Eq`), an optional not-after ledger and an optional `Cap`
  of a limit and a period.

Its meaning is written without reference to the lowering. `Doc.named d p` is
the signers declared under `p`'s ids, the first declaration of each, and
`Doc.signed` the requirement: every named signer for `all`, at least `m` of
them, each once, for `threshold`. `Rule.covers` is the contract, the functions
and, for a capped rule, `transfer`; `Rule.argsHold` every predicate
(`Pred.holds`) and, for a capped rule, an `i128` at argument 2;
`Doc.ruleAllows` all three and `Doc.allows` some rule. `Doc.installed` is the
document's rules then the recovery rule when it configures recovery, and
`Doc.authorize d acct ctl issued records a` checks an authorization over them
(`Doc.validates`, `Doc.signerChosen`, `Doc.charge`), with `ctl` the recovery
controller's check and `issued` the generation of a scoped document; it returns
the records or `none`. `Doc.Valid` is what the theorems take of a document.

`RuleCore/Vocab/Lowering.lean` is the lowering: `Doc.lowerRule`, `Doc.lowerRules`,
`recoveryRule`, `Doc.lower`, `Doc.excluded` and `Doc.lowerScoped`, with
`applyDocCheck` the controller's check as the recovery rule reads it.
`RuleCore/Vocab/Account.lean` models the account's generation: `Account`,
`Event` (`applyDoc`, `completeRecovery`), `Account.step`, `Account.run`,
`Account.completions`, `Account.issue` and `Account.adminRules`.

`RuleCore/Equiv/DenoteDocument.lean` maps the translated document types
constructor for constructor and field for field; every denotation is
injective. `lower_eq`, `lower_scoped_eq` and `excluded_eq` prove that the
translated lowering returns `ok` of the model's, under the stated rule
`LowerRoom`.

## Theorems

Generic model (`RuleCore`):

| Theorem | Statement |
| --- | --- |
| `RuleSet.narrower_refl` | Every rule set is narrower than itself. |
| `RuleSet.narrower_trans` | If `rs''` is narrower than `rs'` and `rs'` narrower than `rs`, then `rs''` is narrower than `rs`. |
| `RuleSet.dropRule_narrower` | If dropping rule `i` from `rs` gives `rs'`, then `rs'` is narrower than `rs`. |
| `RuleSet.addCond_narrower` | If adding a condition to rule `i` of `rs` gives `rs'`, then `rs'` is narrower than `rs`. |
| `RuleSet.restrictScope_narrower` | If restricting rule `i`'s scope in `rs` gives `rs'`, then `rs'` is narrower than `rs`. |
| `RuleSet.attenuate_narrower` | Any single attenuation step yields a narrower rule set. |
| `RuleSet.Derives.narrower` | Every rule set derived from a root by attenuation steps is narrower than the root. |
| `RuleSet.attenuateAll_derives`, `RuleSet.attenuateAll_narrower` | Applying a list of steps is such a derivation, so its result is narrower than the root. |
| `RuleSet.allowsAll_of_narrower` | If `rs'` is narrower than `rs` and `rs'` allows a batch, then `rs` allows that batch. |
| `RuleSet.removeSigners_narrower`, `RuleSet.raiseThreshold_narrower` | If removing signers from rule `i`, or raising its threshold, gives `rs'`, then `rs'` is narrower than `rs`. |
| `RuleSet.dropRule_eq_error_iff`, `RuleSet.addCond_eq_error_iff`, `RuleSet.restrictScope_eq_error_iff`, `RuleSet.removeSigners_eq_error_iff`, `RuleSet.raiseThreshold_eq_noSuchRule_iff` | A step is refused with `noSuchRule` exactly when its position is not below the number of rules. |
| `RuleSet.raiseThreshold_eq_thresholdLowered_iff` | `raiseThreshold i k` is refused with `thresholdLowered` exactly when rule `i` exists and `k` is below its threshold. |
| `Rule.allows_iff`, `RuleSet.allows_iff`, `RuleSet.allowsAll_iff` | A rule allows a context iff its scope matches, every condition holds and its signer requirement holds; a rule set allows a context iff some rule does; a batch is allowed iff every context in it is. |
| `RuleSet.allowsAll_nil` | Every rule set allows the empty batch. |
| `Rule.allows_of_allows_addCond`, `Rule.allows_of_allows_restrictScope`, `Rule.allows_of_allows_removeSigners`, `Rule.allows_of_allows_threshold_le` | A rule with an added condition, a restricted scope, fewer signers or a higher threshold allows only what the original rule allows. |
| `Rule.signed_of_signed_removeSigners` | Removing signers only makes the signer requirement harder to meet. |
| `Rule.signed_iff`, `Rule.mem_present`, `Rule.nodup_present` | The requirement holds iff at least `threshold` distinct rule signers are authenticated; `present` holds exactly the rule signers that are, without repeats. |
| `Rule.signed_of_threshold_zero`, `Rule.allows_of_threshold_zero` | Threshold 0 is no requirement: the verdict is the scope and conditions alone. |
| `Rule.signed_iff_of_threshold_eq` | A threshold equal to the number of distinct signers is met iff every rule signer is authenticated. |
| `Rule.signed_false_of_lt`, `Rule.allows_false_of_lt` | A threshold above the number of distinct signers is never met, so the rule allows nothing. |
| `Rule.signed_of_subset`, `Rule.allows_of_subset`, `RuleSet.allows_of_subset`, `RuleSet.allowsAll_of_subset`, `Rule.present_length_le_of_subset` | Authenticating more signers never turns an allow into a refusal. |
| `Rule.signed_congr`, `RuleSet.allows_congr`, `RuleSet.allowsAll_congr`, `RuleSet.allows_eraseDups` | The verdict depends only on which signers are authenticated, not on their order or repeats. |
| `Rule.signed_congr_signers`, `Rule.allows_congr_signers`, `Rule.signed_eraseDups_signers` | Nor on the order or repeats of the rule's own signers. |
| `nodup_eraseDups`, `length_eq_of_nodup_of_mem_iff` | `eraseDups` leaves no repeats; two lists without repeats and with the same members have the same length. |
| `RuleSet.modifyRule_narrower` | Replacing one rule by a rule that allows no more yields a narrower rule set. |
| `RuleSet.modifyRule_eq_error_iff` | Replacing rule `i` is refused with `noSuchRule` exactly when `i` is not below the number of rules. |
| `RuleSet.rules_ofRules` | The rules of `ofRules l` are `l`. |
| `RuleSet.addCap_narrower`, `RuleSet.lowerCapLimit_narrower`, `RuleSet.lengthenCapPeriod_narrower`, `RuleSet.set_cap_narrower` | Each cap step yields a narrower rule set: changing only a rule's cap leaves every verdict as it was. |
| `RuleSet.addCap_eq_noSuchRule_iff`, `RuleSet.lowerCapLimit_eq_noSuchRule_iff`, `RuleSet.lengthenCapPeriod_eq_noSuchRule_iff` | A cap step is refused with `noSuchRule` exactly when its position is not below the number of rules. |
| `RuleSet.addCap_eq_capPresent_iff`, `RuleSet.addCap_eq_invalidCap_iff`, `RuleSet.lowerCapLimit_eq_noCap_iff`, `RuleSet.lowerCapLimit_eq_limitRaised_iff`, `RuleSet.lowerCapLimit_eq_invalidCap_iff`, `RuleSet.lengthenCapPeriod_eq_noCap_iff`, `RuleSet.lengthenCapPeriod_eq_periodShortened_iff` | Each other refusal of a cap step happens exactly in the case it names. |

Authorization (`RuleCore`, `RuleCore/Theorems/Authorize.lean`):

| Theorem | Statement |
| --- | --- |
| `RuleSet.authorize_eq_ok_iff`, `RuleSet.checkChoice_ok_iff`, `RuleSet.checkSigners_ok_iff`, `RuleSet.signerChosen_iff` | An accepted authorization, pass by pass: the lengths match, every chosen rule exists, is current and allows its context, every authenticated signer is a signer of a chosen rule, and the charges build the new records. |
| `RuleSet.authorize_current`, `RuleSet.authorize_validUntil`, `Rule.expired_eq_false_iff`, `Authorization.map_snd_chosen` | An accepted authorization chooses no rule whose last ledger is before its ledger. |
| `RuleSet.authorize_generation`, `RuleSet.authorize_not_chosen_of_stale`, `RuleSet.authorize_contexts_nil_of_stale`, `Rule.stale_eq_false_iff` | It chooses no rule issued under another generation: once the generation is not `g`, a rule issued under `g` authorizes nothing, and a rule set issued under `g` accepts only an empty batch. |
| `RuleSet.authorize_signers` | Every authenticated signer of an accepted authorization is a signer of a chosen rule. |
| `RuleSet.attenuate_generation`, `RuleSet.attenuateAll_generation`, `RuleSet.attenuateAll_generation_eq` | No step changes a rule's generation; a rule set derived from one issued under `g` is issued under `g`. |
| `RuleSet.authorize_chosen`, `RuleSet.authorize_allowsAll` | An accepted authorization's every context is allowed by the rule chosen for it, so the rule set allows the batch under its signers. |
| `RuleSet.authorize_length`, `RuleSet.charge_length`, `RuleSet.foldlM_charge_length` | An accepted authorization keeps one record per rule. |
| `RuleSet.step_of_error` | A refused authorization leaves the records as they were. |
| `RuleSet.charge_get_ne`, `RuleSet.charge_get_capped`, `RuleSet.charge_of_cap_none`, `RuleSet.foldlM_charge_get`, `RuleSet.foldlM_charge_get_of_cap_none` | A charge touches only the chosen rule's record, through the cap check when the rule has a cap. |
| `RuleSet.run_get`, `RuleSet.runAll_charged`, `RuleSet.spent_eq_recorded`, `RuleSet.run_get_of_cap_none`, `RuleSet.mem_charged` | After a run, a capped rule's record is the cap check's run over the calls charged to it, every one of which it accepted; a rule without a cap keeps its record. |
| `RuleSet.window_le_limit`, `RuleSet.period_le_limit_of_pos`, `RuleSet.period_le_limit` | From empty records, the spends a run records for a capped rule with a non-negative limit sum to at most the limit in every window of eviction, in every window of `period` ledgers from ledger 1 on, and in every window when every authorization is at ledger 1 or later. |
| `RuleSet.run_eq_window`, `RuleSet.run_history_length_le` | From empty records, the stored record is the spends in the window at the last spend's ledger with their sum as total, and holds at most `maxHistory` entries. |
| `RuleSet.Refines.traceNarrower`, `RuleSet.Refines.authorize`, `RuleSet.Refines.authorizeAll`, `RuleSet.Refines.charge`, `RuleSet.Refines.foldlM_charge`, `RuleSet.RecordsRel.empty` | A rule set whose rules, renumbered one to one, each allow no more, carry a cap at least as narrow, are current no more often and list no other signer accepts no run of authorizations its image does not. |
| `RuleSet.attenuate_refines`, `RuleSet.attenuateAll_refines`, `RuleSet.dropRule_refines`, `RuleSet.modifyRule_refines`, `RuleSet.raiseThreshold_refines`, `RuleSet.addCap_refines`, `RuleSet.lowerCapLimit_refines`, `RuleSet.lengthenCapPeriod_refines`, `RuleSet.lowerValidUntil_refines`, `RuleSet.Refines.set`, `RuleSet.Refines.refl`, `RuleSet.Refines.trans`, `Rule.Refines.refl`, `Rule.Refines.trans`, `Rule.Refines.of_eq`, `Rule.refines_addCond`, `Rule.refines_restrictScope`, `Rule.refines_removeSigners`, `RuleCap.NarrowerOpt.refl`, `RuleCap.NarrowerOpt.trans` | Each of the nine steps, and every list of them, refines along the renumbering it induces. |
| `RuleSet.attenuate_traceNarrower`, `RuleSet.attenuateAll_traceNarrower` | Each step, and every chain of steps, is narrowing as trace inclusion, each side from its own empty records, with the choices renumbered. |
| `RuleSet.TraceNarrower.refl`, `RuleSet.TraceNarrower.trans`, `Authorization.renumber_renumber`, `Authorization.chosen_renumber` | Trace inclusion is reflexive and composes, with the renumberings composed. |
| `Attenuation.source_dropRule`, `Attenuation.source_eq_of_ne_dropRule` | `dropRule i` sends `j` to `j` below `i` and to `j + 1` from `i` on; every other step keeps each index. |
| `RuleSet.attenuate_capsValid`, `RuleSet.attenuateAll_capsValid`, `RuleSet.capsValid_set` | The steps keep every cap valid. |
| `Cap.run_of_runAll`, `Cap.recorded_of_runAll`, `Cap.runAll_append`, `Cap.run_append`, `Cap.check_of_narrower_suffix` | Runs of the cap check that accept every call, and one check under a narrower cap. |
| `forM_except_ok_iff`, `foldlM_except_cons`, `foldlM_except_append`, `Authorization.map_fst_chosen`, `Authorization.length_chosen`, `RuleSet.run_nil`, `RuleSet.run_cons`, `RuleSet.emptyRecords_length`, `RuleSet.emptyRecords_get`, `Authorization.charges_eq` | The lemmas these rest on. |

Chain vocabulary (`RuleCore.Chain`):

| Theorem | Statement |
| --- | --- |
| `Rule.allows_create`, `RuleSet.allows_create` | No rule and no rule set allows a contract creation. |
| `RuleSet.allowsAll_false_of_create_mem` | A batch containing a contract creation is denied. |
| `Cond.argEq_kind` | If `argEq i val` holds on a call's arguments, argument `i` exists and has `val`'s constructor. |
| `Cond.argEq_false_of_kind_ne` | If argument `i` has a constructor other than `val`'s, `argEq i val` is false, whatever its payload. |
| `Cond.argEq_bytes_false_of_other` | An `other` argument never satisfies `argEq i (bytes b)`, even when its XDR is exactly `b`. |
| `Val.ne_of_kind_ne` | Values of different constructors are not equal. |
| `Cond.argEq_holds_iff`, `Cond.argI128AtMost_holds_iff` | `argEq i val` holds iff argument `i` is `val`; `argI128AtMost i n` holds iff argument `i` is an `i128` whose signed value is at most `n`'s. |
| `Cond.holds_false_of_length_le` | A condition on an index at or past the end of the arguments is false. |
| `Rule.allows_false_of_functions_nil` | A rule whose functions are the empty list allows nothing. |
| `Rule.allows_call_any`, `Functions.mem_any`, `Functions.mem_remove`, `Functions.mem_restrict`, `Rule.mem_restrictFunctions` | The wildcard matches every function of its contract; removing and restricting functions keep exactly the expected ones. |
| `Cond.argIn_holds_iff`, `Cond.argIn_holds_iff_argEq`, `Cond.argStrPrefix_holds_iff` | `argIn` holds exactly when `argEq` holds for one of its values; `argStrPrefix` exactly when the argument is a string starting with the prefix. |
| `Val.string_ne_symbol`, `Cond.argEq_string_false_of_symbol`, `Cond.argStrPrefix_kind`, `Cond.argStrPrefix_false_of_kind_ne`, `Cond.argStrPrefix_false_of_symbol` | A string is never a symbol; `argStrPrefix` holds only on strings. |
| `RuleSet.restrictFunctions_narrower`, `RuleSet.lowerValidUntil_narrower`, `RuleSet.denote_restrictFunctions`, `RuleSet.denote_lowerValidUntil`, `RuleSet.lowerValidUntil_eq_validUntilRaised_iff` | The two Milestone 4 steps narrow, denote the generic steps, and refuse exactly where stated. |
| `RuleSet.authorize_validUntil`, `RuleSet.authorize_generation`, `RuleSet.authorize_not_chosen_of_stale`, `RuleSet.authorize_contexts_nil_of_stale`, `RuleSet.authorize_signers`, `RuleSet.attenuate_generation`, `RuleSet.attenuateAll_generation`, `RuleSet.attenuateAll_generation_eq` | The expiry, generation and signer theorems, and generation preservation, on chain rule sets. |
| `RuleCore.Bytes.eq_iff` | Two byte strings are equal iff they have the same length and the same byte at every index. |
| `RuleCore.Bytes.append_ne_self` | A byte string is not equal to itself extended by a non-empty suffix. |
| `Rule.contract_eq_of_allows` | A rule allows a call only if the call's contract equals the rule's contract and its function is in the rule's function list. |
| `Rule.allows_extension_false`, `Rule.allows_prefix_false` | A call to a proper extension or a proper prefix of the rule's contract id is denied. |
| `Rule.allows_call_iff`, `Rule.allows_iff`, `RuleSet.allows_iff`, `RuleSet.allowsAll_iff`, `Rule.signed_iff` | Each verdict stated in the vocabulary's terms. |
| `Rule.mem_present` | A rule signer counts only when exactly that signer is authenticated. |
| `Signer.delegated_ne_external`, `Signer.delegated_eq_iff`, `Signer.external_eq_iff`, `Signer.delegated_append_ne` | Signers compare exactly, constructor first: a delegated signer is never an external one, whatever their bytes, and no prefix or extension of an address matches. |
| `Rule.signed_of_threshold_zero`, `Rule.allows_of_threshold_zero`, `Rule.signed_iff_of_threshold_eq`, `Rule.allows_false_of_lt` | Threshold 0, a threshold of all signers, and a threshold above them, in the vocabulary's terms. |
| `Rule.allows_of_subset`, `RuleSet.allows_of_subset`, `RuleSet.allowsAll_of_subset` | Authenticating more signers never turns an allow into a refusal. |
| `RuleSet.allows_congr`, `RuleSet.allowsAll_congr`, `RuleSet.allows_eraseDups`, `Rule.allows_congr_signers`, `Rule.allows_eraseDups_signers` | Repeats and order in either signer list do not change the verdict. |
| `RuleSet.dropRule_narrower`, `RuleSet.addCond_narrower`, `RuleSet.removeFunctions_narrower`, `RuleSet.removeSigners_narrower`, `RuleSet.raiseThreshold_narrower`, `RuleSet.attenuate_narrower` | Each chain attenuation operation yields a narrower rule set. |
| `RuleSet.narrower_refl`, `RuleSet.narrower_trans` | `narrower` on chain rule sets is reflexive and transitive. |
| `RuleSet.Derives.narrower`, `RuleSet.attenuateAll_derives`, `RuleSet.attenuateAll_narrower` | Every chain rule set derived from a root by attenuation steps is narrower than the root. |
| `RuleSet.allowsAll_of_narrower` | A narrower chain rule set allows a batch only if its ancestor does. |
| `Rule.denote_addCond`, `Rule.denote_removeFunctions`, `Rule.denote_removeSigners`, `RuleSet.denote_modifyRule`, `RuleSet.denote_dropRule`, `RuleSet.denote_addCond`, `RuleSet.denote_removeFunctions`, `RuleSet.denote_removeSigners`, `RuleSet.denote_raiseThreshold`, `RuleSet.denote_attenuate` | Each chain operation commutes with the denotation: the denotation of its result is the generic step's result on the denotation. |
| `Rule.mem_removeFunctions`, `Rule.mem_removeSigners` | After removing `fs` or `ss`, a function or signer is in a rule's list iff it was before and is not in the removed list. |
| `RuleSet.dropRule_eq_error_iff`, `RuleSet.addCond_eq_error_iff`, `RuleSet.removeFunctions_eq_error_iff`, `RuleSet.removeSigners_eq_error_iff`, `RuleSet.raiseThreshold_eq_noSuchRule_iff`, `RuleSet.modifyRule_eq_error_iff` | A chain operation is refused with `noSuchRule` exactly when its index is not below the number of rules. |
| `RuleSet.raiseThreshold_eq_thresholdLowered_iff` | `raiseThreshold` is refused with `thresholdLowered` exactly when the rule exists and the new threshold is below its own. |
| `RuleSet.rules_denote` | The rules of a chain rule set's denotation are the denotations of its rules. |
| `RuleSet.addCap_narrower`, `RuleSet.lowerCapLimit_narrower`, `RuleSet.lengthenCapPeriod_narrower` | Each chain cap step yields a narrower rule set. |
| `RuleSet.denote_addCap`, `RuleSet.denote_lowerCapLimit`, `RuleSet.denote_lengthenCapPeriod`, `RuleSet.denote_attenuateAll`, `Cap.valid_denote` | Each chain cap step, and each list of steps, commutes with the denotation. |
| `RuleSet.authorize_allowsAll` | A chain rule set that accepts an authorization allows its batch under its signers. |
| `RuleSet.attenuate_traceNarrower`, `RuleSet.attenuateAll_traceNarrower`, `Attenuation.source_denote_dropRule`, `Attenuation.source_denote_of_ne` | Each chain step, and every chain of steps, is trace inclusion on the denotations, along the renumbering `dropRule` induces. |
| `RuleSet.attenuate_capsValid`, `RuleSet.attenuateAll_capsValid` | The chain steps keep every cap valid. |
| `RuleSet.emptyRecords_denote`, `RuleSet.authorizeAll_denote` | The chain's empty records and runs are the generic ones of the denotation. |

Equivalence (`RuleCore.Equiv`), on every input of the translated functions:

| Theorem | Statement |
| --- | --- |
| `allows_eq` | `allows rules c authenticated` returns `ok` of the chain `RuleSet.allows` on the denotations: it terminates, does not fail, and agrees with the model. |
| `allows_all_eq` | `allows_all rules cs authenticated` returns `ok` of the chain `RuleSet.allowsAll` on the denotations. |
| `rule_allows_eq`, `conds_hold_eq`, `cond_holds_eq`, `val_eq_eq` | `rule_allows`, `conds_hold`, `cond_holds` and `val_eq` return `ok` of the model's `Rule.allows`, all of the conditions, `Cond.holds` and value equality on the denotations. |
| `signers_met_eq`, `signed_count_eq` | `signers_met` returns `ok` of the model's signer requirement, and `signed_count` of the number of distinct authenticated rule signers. |
| `signer_eq_eq`, `signer_in_eq`, `signer_in_first_eq`, `any_signer_eq_mem` | `signer_eq` is equality of the denoted signers; `signer_in` is membership of the denotation, and `signer_in_first x list before` membership among the first `before` signers. |
| `bytes_eq_eq`, `bytes_in_eq` | `bytes_eq a b` returns `ok` of whether `a` and `b` hold the same bytes; `bytes_in x list` returns `ok` of whether some element of `list` does. |
| `drop_rule_eq`, `restrict_functions_eq`, `remove_signers_eq`, `raise_threshold_eq`, `lower_valid_until_eq` | The step returns `ok res`, and `denoteOutcome res` is the chain `RuleSet.dropRule`, `RuleSet.restrictFunctions`, `RuleSet.removeSigners`, `RuleSet.raiseThreshold` or `RuleSet.lowerValidUntil` on the denotations, every refusal included. |
| `add_cond_eq`, `remove_functions_eq` | Under `CondRoom rules index`, `add_cond` returns `ok res`, and under `FunctionsRoomAt rules index functions` `remove_functions` does, and `denoteOutcome res` is the chain `RuleSet.addCond` or `RuleSet.removeFunctions` on the denotations. `remove_functions_full` and `remove_functions_room` show the rule exact; `functionsRoom_only` shows every list meets it. |
| `functions_match_eq`, `val_in_eq`, `bytes_starts_with_eq`, `functions_without_eq`, `functions_within_eq`, `bytes_list_within_eq`, `bytes_list_extend_eq` | A rule's functions, `ArgIn` and `ArgStrPrefix`, and the function-set operations the steps use, are the model's. |
| `add_cond_full` | On a rule holding `Usize.max` conditions, `add_cond` fails with `maximumSizeExceeded`. |
| `drop_rule_ok`, `drop_rule_err`, `remove_functions_ok`, `remove_functions_err`, `remove_signers_ok`, `remove_signers_err`, `add_cond_ok`, `add_cond_err`, `raise_threshold_ok`, `raise_threshold_err`, `raise_threshold_lowered` | The rules each step returns when the index is in range, `Err NoSuchRule` when it is not, and `Err ThresholdLowered` when `raise_threshold` would lower the threshold. |
| `bytes_copy_eq`, `bytes_copy_deref`, `bytes_list_copy_deref`, `val_copy_eq`, `cond_copy_eq`, `conds_copy_deref`, `signer_copy_eq`, `signers_copy_deref`, `rule_copy_eq` | Each copy returns `ok` of its input. |
| `bytes_list_without_eq`, `rule_without_functions_eq`, `signers_without_eq`, `rule_without_signers_eq`, `denote_filter_inList`, `denote_filter_signerInList` | Removing functions or signers keeps, in order, the elements not in the removed list; the rule it builds denotes the chain `Rule.removeFunctions` or `Rule.removeSigners`. |
| `denoteVal_injective`, `denoteContext_injective`, `denoteCond_injective`, `denoteSigner_injective`, `denoteSigners_injective`, `denoteRule_injective`, `denoteRules_injective`, `denoteOutcome_injective`, `denoteBytes_injective`, `denoteU32_injective`, `denoteU64_injective`, `denoteError_injective` | Each denotation is injective. |
| `loop_any`, `loop_all`, `loop_build`, `loop_build_fail`, `loop_count` | What a scanning, building or counting loop returns, from what one round of its body returns. |
| `countFrom_first`, `countFrom_first_from`, `countFrom_map` | Counting each element at its first position, when it satisfies a predicate, counts the elements of `eraseDups` that do. |
| `push_eq`, `push_full`, `incr_eq`, `incr_eq_of_le`, `index_usize_eq`, `slice_get_eq` | `Vec::push` succeeds below `Usize.max` elements and fails at it; the loop counter's and the signer count's increments and in-range indexing succeed; `get` is the list lookup. |
| `add_cap_eq`, `lower_cap_limit_eq`, `lengthen_cap_period_eq` | Each cap step returns `ok res`, and `denoteOutcome res` is the chain step on the denotations, every refusal included. |
| `add_cap_ok`, `lower_cap_limit_ok`, `lengthen_cap_period_ok`, `loop_set_eq`, `cap_valid_eq`, `cap_copy_eq`, `cap_option_copy_eq` | The rules each cap step returns when it is taken; the loop that rebuilds every rule and changes one; `cap_valid` is `Cap.valid`; the cap copies return their input. |
| `authorize_eq` | `authorize rules records contexts choices authenticated now generation` returns `ok res`, and `denoteAuthorized res` is the chain `RuleSet.authorize` on the denotations, every refusal included. |
| `expired_eq`, `stale_eq`, `signer_chosen_eq`, `signers_chosen_eq` | Expiry, staleness and the signer check are the model's. |
| `check_choices_loop_eq`, `charge_all_loop_eq`, `records_copy_eq`, `records_copy_loop_eq`, `spend_amount_eq`, `slice_get_mut_eq`, `slice_len_bne_any`, `list_set_opt_some` | The first pass is the model's `forM` of `checkChoice`, the second its `foldlM` of `charge`; the records copy returns the records; `spend_amount` is the cap's amount; `get_mut` returns the element and writes back at its index. |
| `chosen_denoteAuthorization`, `chosenOf_drop`, `chosenOf_drop_nil`, `denoteRules_rules_get`, `denoteRule_denote_cap`, `denoteCap_params`, `except_error_bind`, `except_ok_bind` | The model read on the denotations. |
| `denoteCap_injective`, `denoteRefusal_injective`, `denoteAuthorized_injective` | The new denotations are injective. |

The model's theorems carried over to the translation
(`RuleCore.Extracted`), stated on the translated functions alone. `Narrower
rs' rs` says every context the translated `allows` accepts under `rs'` and some
authenticated signers, it accepts under `rs` and the same signers; `Step rs
rs'` says one of the ten translated attenuation steps on `rs` returned `Ok`
of the rules of `rs'`; `Derives root rs` is zero or more steps.

| Theorem | Statement |
| --- | --- |
| `drop_rule_narrower`, `add_cond_narrower`, `remove_functions_narrower`, `restrict_functions_narrower`, `remove_signers_narrower`, `raise_threshold_narrower`, `add_cap_narrower`, `lower_cap_limit_narrower`, `lengthen_cap_period_narrower`, `lower_valid_until_narrower`, `Step.narrower` | Each translated attenuation step that returns `Ok` yields a narrower rule set. |
| `Narrower.refl`, `Narrower.trans` | `Narrower` is reflexive and transitive. |
| `Derives.narrower` | Any chain of translated steps stays inside its root. |
| `allows_all_of_narrower`, `Derives.allows_all` | A narrower rule set accepts a batch only if its ancestor does. |
| `narrower_of_denote` | The model's `narrower` on the denotations gives `Narrower`. |
| `add_cond_room` | An `add_cond` that returned `Ok` had room for the condition. |
| `remove_functions_room` | A `remove_functions` that returned `Ok` had room for the removed functions. |
| `allows_create`, `allows_all_create` | No rule set allows a contract creation; a batch containing one is denied. |
| `val_eq_iff` | `val_eq a b` returns `ok true` exactly when `a = b`. |
| `val_eq_kind`, `val_eq_other_bytes`, `val_eq_string_symbol` | `val_eq` holds only for values of the same constructor; an `Other` value never equals a `Bytes` value, nor a `String` a `Symbol`, whatever the bytes. |
| `cond_holds_argIn_iff`, `cond_holds_argStrPrefix_iff` | `ArgIn` holds exactly when `ArgEq` holds for one of its values; `ArgStrPrefix` exactly when the argument is a `String` starting with the prefix. |
| `cond_holds_argEq_iff`, `cond_holds_argEq_kind`, `cond_holds_argEq_false_of_kind_ne` | `ArgEq index v` holds exactly when argument `index` exists and is `v`, so only for an argument of `v`'s constructor. |
| `bytes_eq_iff` | Two byte strings compare equal exactly when they hold the same bytes. |
| `rule_allows_call`, `functions_match_only_iff`, `functions_match_anyExcept_iff` | A rule allows a call only if the call's contract is the rule's contract and its functions match its function: exactly one listed function, or for a wildcard any function it does not exclude. |
| `rule_allows_extension_false`, `rule_allows_prefix_false` | A call to a proper extension or a proper prefix of the rule's contract id is denied. |
| `signer_eq_iff`, `signer_eq_delegated_external` | `signer_eq a b` returns `ok true` exactly when `a = b`; a `Delegated` signer never equals an `External` one, whatever their bytes. |
| `allows_of_subset`, `allows_all_of_subset`, `denoteSigners_subset` | Authenticating more signers never turns an allow into a refusal. |
| `allows_congr`, `allows_all_congr`, `rule_allows_congr_signers`, `denoteSigners_mem_iff` | Repeats and order in the authenticated signers, or in a rule's signers, do not change the verdict. |
| `rule_allows_threshold_zero`, `signers_met_all_iff`, `rule_allows_false_of_lt` | With threshold 0 a rule's verdict does not depend on the authenticated signers; a threshold equal to the number of distinct signers is met exactly when every signer is authenticated; a threshold above it allows nothing. |

Spending caps (`RuleCore.Cap`):

| Theorem | Statement |
| --- | --- |
| `check_negative`, `check_zero` | A negative amount is refused; a zero amount returns the record unchanged, whatever its total. |
| `check_ledgerBeforeNewest_iff`, `beforeNewest_eq_false_iff` | A positive spend is refused with `ledgerBeforeNewest` iff `now` is earlier than the ledger of the newest entry; on a history in ledger order, iff some entry is after `now`. |
| `check_valid`, `check_pos_ok` | On a valid record, the check keeps the entries after `now - period` and refuses with `overflow`, `limitExceeded` or `historyFull` exactly as the kept total and count say. |
| `evict_eq`, `evict_error`, `dropWhile_eq_filter` | Eviction on positive amounts drops the entries at or before the cutoff and sums them, and only ever fails with `overflow`; on a history in ledger order, the kept entries are the entries after the cutoff. |
| `step_of_error`, `run_cons_of_error` | A refused call leaves the record as it was. |
| `Record.empty_valid`, `check_preserves_valid`, `run_valid` | The empty record is valid, and the check keeps a record valid. |
| `window_le_limit` | From the empty record, for every run and ledger `t`, the recorded spends in the window at `t` sum to at most the limit. |
| `window_le_limit_of_valid` | From any valid record, every window holding a spend the run recorded sums to at most the limit. |
| `period_le_limit_of_pos`, `period_le_limit`, `inPeriodFrom_eq_inWindow` | Every window of `period` consecutive ledgers from ledger 1 or later sums to at most the limit, and every window does when every call is at ledger 1 or later. |
| `period_ledger_zero` | Two spends of the whole limit at ledger 0 are both recorded under a valid cap. |
| `run_history`, `run_total`, `run_eq_window`, `run_eq_of_recorded_nil`, `mem_recorded` | The stored history is the recorded spends eviction left at the last spend's ledger, followed by that spend, and the total is their sum; with a nonzero period and that spend at ledger 1 or later, exactly the recorded spends in its window. |
| `run_history_length_le` | A record never holds more than `maxHistory` entries. |
| `Params.accepts_of_narrower`, `accepts_of_limit_le`, `accepts_of_period_le`, `capAccepts_of_capNarrower` | Every run a narrower cap accepts from a valid record, the wider one accepts; a rule without a cap accepts every run. |
| `run_spec`, `RunInv.start`, `RunInv.step_pos`, `accepts_of_narrower_suffix`, `filter_cutoff_suffix` | The invariants these rest on: the windows of the recorded spends at ledgers the clock check lets through are the record's, and a narrower cap's history ends with the wider cap's. |

The cap check on the translation (`RuleCore.Extracted`):

| Theorem | Statement |
| --- | --- |
| `runSpends_eq` | A run of the translated `check_spend`, keeping the record after a refusal, returns `ok` of a record denoting `Params.run`. |
| `runSpends_window`, `runSpends_length_le` | From the empty record, that record holds the recorded spends in its window and at most `MAX_HISTORY_ENTRIES` entries. |
| `check_spend_negative`, `check_spend_zero`, `check_spend_before_newest` | The translated check refuses a negative amount, returns the record unchanged on a zero amount, and refuses a positive spend before the newest recorded ledger. |
| `empty_record_denote` | The empty record denotes the model's. |

`authorize` on the translation (`RuleCore.Extracted`,
`Theorems/ExtractedAuthorize.lean`). `runAuthorizations` runs the translated
`authorize`, keeping the records after a refusal; `emptyRecords rules` is one
empty record per rule; `TraceNarrower rules' rules f` says every run `rules'`
accepts from its empty records, `rules` accepts from its own with each choice
renumbered by `f` (`Renumbered`); `StepAlong rs rs' f` is one translated step
with its renumbering and `DerivesAlong root rs f` a chain of them.

| Theorem | Statement |
| --- | --- |
| `authorize_allows_all` | An `authorize` that returned `Ok` means the translated `allows_all` accepts the same batch under the same signers. |
| `authorize_valid_until`, `authorize_generation`, `authorize_not_chosen_of_stale`, `authorize_contexts_nil_of_stale`, `authorize_signers` | An `authorize` that returned `Ok` chose no expired rule and no rule of another generation, and authenticated no signer outside its chosen rules. |
| `StepAlong.generation`, `DerivesAlong.generation`, `DerivesAlong.generation_eq` | No translated step changes a rule's generation. |
| `runAuthorizations_eq`, `authorizeAll_eq`, `accepts_iff` | A run of the translated `authorize` returns `ok` of records denoting the model's run, and accepts a run exactly when the model does. |
| `runAuthorizations_of_err` | A refused authorization leaves the records as they were. |
| `runAuthorizations_window`, `runAuthorizations_window_le_limit`, `runAuthorizations_length_le` | From empty records, a capped rule's stored record is the in-window spends with their sum as total, every window of its spends sums to at most its limit, and it holds at most `MAX_HISTORY_ENTRIES` entries. |
| `traceNarrower_of_denote`, `StepAlong.denote_step`, `StepAlong.denote_traceNarrower`, `StepAlong.traceNarrower`, `DerivesAlong.traceNarrower`, `DerivesAlong.derives` | Each translated step, and every chain of them, is trace inclusion along its renumbering; a chain is also a `Derives`. |
| `emptyRecords_denote`, `emptyRecords_denote_rules`, `emptyRecords_length`, `renumbered_denote`, `renumbered_map` | The empty records and renumbered runs, read on the denotations. |

Budgets (`RuleCore.Budget`, `Theorems/Budget.lean`), in namespace `Tree`:

| Theorem | Statement |
| --- | --- |
| `spend_ok_iff` | A spend succeeds exactly on a well-formed tree, at an existing node, with a non-negative amount and a walk that reaches the root, and returns the charged tree. |
| `spend_ok_charges`, `spend_ok_unchanged`, `spend_ok_length`, `spend_ok_parentOf`, `spend_ok_allowance` | A successful spend adds the amount to the spender and every ancestor and changes nothing else. |
| `spend_overdrawn`, `walk_overdrawn` | The node an `overdrawn` refusal names is on the spender's chain and cannot take the amount, and every node before it on the chain can. |
| `spend_accepts_iff`, `spend_error_overdrawn`, `walk_total`, `walk_error` | On a well-formed tree, a spend of a non-negative amount at an existing node succeeds exactly when every node on its chain can take it, and is otherwise refused as `overdrawn`. |
| `delegate_ok_iff`, `refill_ok_iff` | What a successful delegation appends and a successful refill raises. |
| `step_of_error`, `run_cons_of_error`, `logged_of_error` | A refused operation leaves the tree as it was and logs nothing. |
| `spend_valid`, `delegate_valid`, `refill_valid`, `run_valid` | Every operation and run keeps the tree well formed. |
| `spend_withinAllowance`, `delegate_withinAllowance`, `refill_withinAllowance`, `run_withinAllowance` | Every operation and run keeps every spent amount within its allowance. |
| `run_extends` | A run never removes a node or changes an existing node's parent. |
| `spent_run`, `spentUnder_eq_spent` | After any run, each node's spent amount is its starting one plus the total successfully spent at or under it; from a tree with nothing spent, it is that total. |
| `spentUnder_le_allowance` | From a well-formed tree with nothing spent, after any run the total successfully spent at or under each node is at most its allowance. |
| `mem_walk`, `walk_fits`, `within_of_walk`, `within_root`, `within_step`, `le_of_within`, `within_antisymm`, `within_trans`, `parent_lt` | The walk returns exactly the spender and its ancestors, each able to take the amount, and the ancestor relation on a well-formed tree. |

Budgets on the translation (`RuleCore.Extracted`,
`Theorems/ExtractedBudget.lean`). `runBudget` runs the translated `spend`,
`delegate` and `refill`, keeping the tree after a refusal and logging each
successful spend.

| Theorem | Statement |
| --- | --- |
| `runBudget_eq` | A run returns `ok` of a tree and a log denoting the model's run. |
| `runBudget_valid`, `runBudget_withinAllowance` | A run keeps the tree well formed and every spent amount within its allowance. |
| `runBudget_spentUnder_eq_spent`, `runBudget_spentUnder_le_allowance` | From a well-formed tree with nothing spent, the total successfully spent at or under each node is its spent amount and at most its allowance. |
| `budget_spend_charges`, `budget_spend_unchanged` | A successful translated spend charges exactly the spender and its ancestors. |
| `budget_spend_overdrawn`, `budget_spend_accepts_iff` | An `Overdrawn` refusal names the first node on the chain that cannot take the amount; on a well-formed tree a spend of a non-negative amount at an existing node succeeds exactly when every node on its chain can take it. |
| `budget_delegate_appends`, `budget_refill_raises` | What a successful translated delegation appends and refill raises. |

Documents (`RuleCore.Document`, `Theorems/Lowering.lean` and `Theorems/Scoped.lean`):

| Theorem | Statement |
| --- | --- |
| `Doc.lowerRule_allows`, `Doc.lowerRules_allows` | For a valid rule or document, each lowered rule allows exactly what its document rule allows, and the lowered rules what the document allows, whatever generation they carry. |
| `Doc.lower_allows`, `Doc.lower_allows_of_recovery_none` | The admin document's lowering allows what the document allows or what the recovery rule allows; exactly what the document allows with no recovery configured. |
| `recoveryRule_allows` | The recovery rule allows every call to the account's `apply_doc`, under any signers, and nothing else. |
| `Doc.lower_authorize`, `Doc.authorize_lowerAll`, `Doc.lower_authorize_of_recovery_none` | On every authorization the lowering accepts exactly when the document accepts, with the recovery controller's check read as `applyDocCheck`, and returns the same records. |
| `Doc.authorize_mono`, `Doc.lower_authorize_of_check`, `Doc.authorize_of_recovery_none` | The document's acceptance grows with the controller's check, so whatever it accepts under a check allowing only `apply_doc`, the lowering accepts; without recovery the check is not read. |
| `Doc.checkChoice_lower`, `Doc.signerChosen_lower`, `Doc.charge_lower`, `Doc.foldlM_charge_lower`, `Doc.authorize_eq_some_iff` | Pass by pass, the lowered rules' `authorize` and the document's check agree. |
| `Rule.mem_lowerFunctions`, `Rule.covers_iff`, `Pred.lower_holds`, `amountCond_holds`, `Rule.lowerConds_all`, `Rule.signed_lowerRule` | The lowered functions, conditions and signer requirement are the document rule's. |
| `Doc.lowerScoped_eq_ok`, `Doc.lowerScoped_allows`, `Doc.lowerScoped_authorize` | An accepted scoped lowering is the document's rules lowered with the generation, and allows and accepts exactly what the scoped document does in that generation. |
| `Doc.lowerScoped_contract`, `Doc.lowerScoped_allows_excluded`, `Doc.lowerScoped_attenuateAll_excluded`, `Doc.mem_excluded` | No scoped rule, nor any rule set attenuated from scoped rules, allows a call to the account or to a contract of the excluded set, which holds the account, the controller, the adapter and the pool. |
| `Doc.lowerScoped_generation`, `Doc.lower_generation`, `RuleSet.authorize_generation_none` | Scoped rules carry their generation, admin rules none, and rules without one authorize the same in every generation. |
| `Account.run_address`, `Account.run_generation`, `Account.issued_stale`, `Account.adminRules_authorize_generation` | A run advances the generation by exactly the recoveries it completes; after one, a grant attenuated from an earlier scoped document accepts only the empty batch, and the admin rules authorize as before. |
| `Account.chain`, `Account.chain_trace`, `Account.chain_after_recovery` | The containment chain: what a grant accepts is allowed by its scoped document, touches no excluded contract and is in the issue's generation; the grant's runs are the scoped rules' runs; a completed recovery ends the grant. |

The lowering on the translation (`RuleCore.Extracted`, `Theorems/ExtractedLowering.lean`):

| Theorem | Statement |
| --- | --- |
| `lower_allows`, `lower_allows_of_recovery_none`, `lower_authorize` | The translated `allows` and `authorize` on the rules the translated `lower` returns give the document's verdicts, with the same records. |
| `lower_scoped_allows`, `lower_scoped_authorize`, `lower_scoped_model` | The same for a scoped document the translated `lower_scoped` accepts. |
| `lower_scoped_allows_excluded`, `derives_allows_excluded` | No rule set the translated `lower_scoped` returns, or translated steps derive from it, allows a call to the account or an excluded contract. |
| `lower_scoped_generation`, `lower_generation` | Scoped rules carry their generation; admin rules carry none. |
| `chain`, `chain_trace` | The containment chain on the translated `excluded`, `lower_scoped`, attenuation steps and `authorize`. |

The empty batch is allowed by every rule set (`RuleCore.RuleSet.allowsAll_nil`;
chain `allowsAll` is the generic one on the denotation, and the translated
`allows_all` is the chain one, by `allows_all_eq`). A
Soroban authorization tree always has a root context, so a batch collected from
one is never empty; a caller that builds batches some other way must reject the
empty batch itself.

No rule set allows a creation in the chain vocabulary because every chain scope
is false on a creation. The generic model makes no such claim: a generic scope
is an arbitrary predicate.

## Axioms

`RuleCore/Axioms.lean` imports `RuleCore` and runs `#print axioms` on every
exported theorem (every theorem written in the sources that is not private)
under `#guard_msgs`, so a new theorem or a change in any theorem's axioms fails
the build until the record is updated. It also checks every theorem in the
package, generated ones included, against the permitted axioms `propext`,
`Quot.sound` and `Classical.choice`.

The chain theorems depend on `Classical.choice` through Lean core's proof that
`BEq` on `List UInt8` is lawful, which the decision procedure for list
membership (`function ∈ r.functions`, and a signer's membership among the
authenticated ones) uses. The translated definitions depend
on `Classical.choice` through Aeneas's library (`#print axioms
rule_eval.rule_set.allows` lists it), so the theorems about them do too. No
theorem depends on an axiom Aeneas's library declares.
