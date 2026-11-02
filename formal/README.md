# formal

The Lean model of rule evaluation, the Lean translation of `crates/rule-eval`,
and the theorems relating them. The Lake package is `rule-core`
(MIT OR Apache-2.0); its one library is `RuleCore`, rooted at `RuleCore.lean`.

| Directory | Contents |
| --- | --- |
| `RuleCore/Model/` | The generic model: rules with their signers and threshold, rule sets, `narrower`, and the five attenuation steps, over any context and signer type. |
| `RuleCore/Vocab/` | The chain vocabulary (contexts, values, conditions, signers, rules) and its denotation into the generic model. |
| `RuleCore/Extracted/` | `RuleEval.lean`, the translation of `crates/rule-eval` that Charon and Aeneas generate. Never edited by hand. |
| `RuleCore/Equiv/` | Denotations from the translated types to the chain vocabulary, and theorems that the translated functions compute the model's results. |
| `RuleCore/Theorems/` | The theorems below, including the model's theorems carried over to the translation (`Extracted.lean`), and kernel-checked examples of concrete verdicts. |
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
structure Rule (Ctx Sig : Type) where
  scope : Ctx → Bool          -- contract and function match
  conds : List (Ctx → Bool)   -- conditions on this call's arguments
  signers : List Sig          -- the signers that count towards the threshold
  threshold : Nat             -- how many distinct signers must be authenticated

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
no requirement. `RuleSet` is a plain definition, so `RuleSet.rules` and
`RuleSet.ofRules` convert to and from the underlying list for list notation.

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

`Attenuation` names one step, `RuleSet.attenuate` applies one,
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
  address Bytes | symbol Bytes | other Bytes`, where `other` carries the
  argument's full XDR. `i128` values compare as signed integers. Values of
  different constructors are never equal.
* `Context` is `call contract function args` or `create wasmHash`.
* `Signer` is `delegated address` (an address, as its `ScAddress` XDR) or
  `external verifier key` (a verifier contract's address and a key), compared
  exactly, constructor first.
* `Cond` is `argEq index val` (argument `index` exists and equals `val`) or
  `argI128AtMost index n` (argument `index` exists, is an `i128`, and is at
  most `n`). A missing argument or another constructor makes the condition
  false.
* `Rule` is `{ contract, functions, conds, signers, threshold }` and `RuleSet`
  is `List Rule`. A rule with an empty function list allows nothing.
* `RuleSet.allows rs c auth` and `RuleSet.allowsAll rs cs auth` take the
  authenticated signers `auth`.
* `RuleSet.dropRule i`, `RuleSet.addCond i cond`,
  `RuleSet.removeFunctions i fs`, `RuleSet.removeSigners i ss` and
  `RuleSet.raiseThreshold i k` are the attenuation operations.
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
`restrictScope i.toNat (notCalling fs)`, and the signer steps denote the
generic steps of the same name. A chain rule's signers and threshold are the
generic rule's.

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
`UInt32` with the same bit vector; `Val`, `Context`, `Cond` and `Signer` map
each constructor to the constructor of the same name; `Rule` maps each field to
the field of the same name; a slice or vector of rules or signers is the list
of its elements' denotations (`denoteRules`, `denoteSigners`);
`AttenuationError::NoSuchRule` and `AttenuationError::ThresholdLowered` are
`AttenuationError.noSuchRule` and `AttenuationError.thresholdLowered`, and a
Rust `Result` of an attenuation step is the `Except` with the denoted payload
(`denoteOutcome`). Every denotation is injective (`denoteVal_injective`,
`denoteContext_injective`, `denoteCond_injective`, `denoteSigner_injective`,
`denoteSigners_injective`, `denoteRule_injective`, `denoteRules_injective`,
`denoteOutcome_injective`).

On every input, the translated functions return `ok` of the model's result on
the denotations:

* `allows_eq`: `allows rules c authenticated = ok ((denoteRules rules).allows (denoteContext c) (denoteSigners authenticated))`.
* `allows_all_eq`: `allows_all rules cs authenticated = ok ((denoteRules rules).allowsAll (cs.map denoteContext) (denoteSigners authenticated))`.
* `signers_met_eq`, `signed_count_eq`: the signer requirement and the count of
  distinct authenticated rule signers are the model's.
* `drop_rule_eq`, `remove_functions_eq`, `remove_signers_eq`,
  `raise_threshold_eq`: the step returns `ok res` with `denoteOutcome res` the
  model's `dropRule`, `removeFunctions`, `removeSigners` or `raiseThreshold` of
  the denotations, `noSuchRule` and `thresholdLowered` included.
* `add_cond_eq`: the same for `addCond`, under the stated rule `CondRoom`.

The signer count is a fourth loop shape, `loop_count`: a counter that grows by
at most one per position, so it stays at most the position and its increment
cannot overflow. `countFrom_first` shows that counting each signer at its first
position, when it is authenticated, is the length of the model's
`present` list.

### The rule `add_cond` needs

Aeneas's model of `Vec::push` fails once the vector holds `Usize.max`
elements. Every push in the evaluator but one appends to a vector holding at
most one element per position of a slice already walked, so it cannot reach
that bound. The exception is `add_cond`, which appends to the condition
vector of the rule at `index`. `add_cond_eq` therefore takes
`CondRoom rules index`: the rule at `index`, when there is one, holds fewer
than `Usize.max` conditions. `add_cond_full` shows the rule is exact: on a rule
already holding `Usize.max` conditions, the translated `add_cond` fails with
`maximumSizeExceeded`. In Rust a `Vec<Cond>` never reaches that length: a
`Vec` holds at most `isize::MAX` bytes. The theorems about the translation do
not depend on `CondRoom`: an `add_cond` that returned `Ok` had room
(`add_cond_room`).

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
| `Rule.allows_false_of_functions_nil` | A rule with an empty function list allows nothing. |
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

Equivalence (`RuleCore.Equiv`), on every input of the translated functions:

| Theorem | Statement |
| --- | --- |
| `allows_eq` | `allows rules c authenticated` returns `ok` of the chain `RuleSet.allows` on the denotations: it terminates, does not fail, and agrees with the model. |
| `allows_all_eq` | `allows_all rules cs authenticated` returns `ok` of the chain `RuleSet.allowsAll` on the denotations. |
| `rule_allows_eq`, `conds_hold_eq`, `cond_holds_eq`, `val_eq_eq` | `rule_allows`, `conds_hold`, `cond_holds` and `val_eq` return `ok` of the model's `Rule.allows`, all of the conditions, `Cond.holds` and value equality on the denotations. |
| `signers_met_eq`, `signed_count_eq` | `signers_met` returns `ok` of the model's signer requirement, and `signed_count` of the number of distinct authenticated rule signers. |
| `signer_eq_eq`, `signer_in_eq`, `signer_in_first_eq`, `any_signer_eq_mem` | `signer_eq` is equality of the denoted signers; `signer_in` is membership of the denotation, and `signer_in_first x list before` membership among the first `before` signers. |
| `bytes_eq_eq`, `bytes_in_eq` | `bytes_eq a b` returns `ok` of whether `a` and `b` hold the same bytes; `bytes_in x list` returns `ok` of whether some element of `list` does. |
| `drop_rule_eq`, `remove_functions_eq`, `remove_signers_eq`, `raise_threshold_eq` | The step returns `ok res`, and `denoteOutcome res` is the chain `RuleSet.dropRule`, `RuleSet.removeFunctions`, `RuleSet.removeSigners` or `RuleSet.raiseThreshold` on the denotations, `noSuchRule` and `thresholdLowered` included. |
| `add_cond_eq` | Under `CondRoom rules index`, `add_cond` returns `ok res`, and `denoteOutcome res` is the chain `RuleSet.addCond` on the denotations. |
| `add_cond_full` | On a rule holding `Usize.max` conditions, `add_cond` fails with `maximumSizeExceeded`. |
| `drop_rule_ok`, `drop_rule_err`, `remove_functions_ok`, `remove_functions_err`, `remove_signers_ok`, `remove_signers_err`, `add_cond_ok`, `add_cond_err`, `raise_threshold_ok`, `raise_threshold_err`, `raise_threshold_lowered` | The rules each step returns when the index is in range, `Err NoSuchRule` when it is not, and `Err ThresholdLowered` when `raise_threshold` would lower the threshold. |
| `bytes_copy_eq`, `bytes_copy_deref`, `bytes_list_copy_deref`, `val_copy_eq`, `cond_copy_eq`, `conds_copy_deref`, `signer_copy_eq`, `signers_copy_deref`, `rule_copy_eq` | Each copy returns `ok` of its input. |
| `bytes_list_without_eq`, `rule_without_functions_eq`, `signers_without_eq`, `rule_without_signers_eq`, `denote_filter_inList`, `denote_filter_signerInList` | Removing functions or signers keeps, in order, the elements not in the removed list; the rule it builds denotes the chain `Rule.removeFunctions` or `Rule.removeSigners`. |
| `denoteVal_injective`, `denoteContext_injective`, `denoteCond_injective`, `denoteSigner_injective`, `denoteSigners_injective`, `denoteRule_injective`, `denoteRules_injective`, `denoteOutcome_injective`, `denoteBytes_injective`, `denoteU32_injective`, `denoteU64_injective`, `denoteError_injective` | Each denotation is injective. |
| `loop_any`, `loop_all`, `loop_build`, `loop_build_fail`, `loop_count` | What a scanning, building or counting loop returns, from what one round of its body returns. |
| `countFrom_first`, `countFrom_first_from`, `countFrom_map` | Counting each element at its first position, when it satisfies a predicate, counts the elements of `eraseDups` that do. |
| `push_eq`, `push_full`, `incr_eq`, `incr_eq_of_le`, `index_usize_eq`, `slice_get_eq` | `Vec::push` succeeds below `Usize.max` elements and fails at it; the loop counter's and the signer count's increments and in-range indexing succeed; `get` is the list lookup. |

The model's theorems carried over to the translation
(`RuleCore.Extracted`), stated on the translated functions alone. `Narrower
rs' rs` says every context the translated `allows` accepts under `rs'` and some
authenticated signers, it accepts under `rs` and the same signers; `Step rs
rs'` says one of the translated `drop_rule`, `add_cond`, `remove_functions`,
`remove_signers` and `raise_threshold` on `rs` returned `Ok` of the rules of
`rs'`; `Derives root rs` is zero or more steps.

| Theorem | Statement |
| --- | --- |
| `drop_rule_narrower`, `add_cond_narrower`, `remove_functions_narrower`, `remove_signers_narrower`, `raise_threshold_narrower`, `Step.narrower` | Each translated attenuation step that returns `Ok` yields a narrower rule set. |
| `Narrower.refl`, `Narrower.trans` | `Narrower` is reflexive and transitive. |
| `Derives.narrower` | Any chain of translated steps stays inside its root. |
| `allows_all_of_narrower`, `Derives.allows_all` | A narrower rule set accepts a batch only if its ancestor does. |
| `narrower_of_denote` | The model's `narrower` on the denotations gives `Narrower`. |
| `add_cond_room` | An `add_cond` that returned `Ok` had room for the condition. |
| `allows_create`, `allows_all_create` | No rule set allows a contract creation; a batch containing one is denied. |
| `val_eq_iff` | `val_eq a b` returns `ok true` exactly when `a = b`. |
| `val_eq_kind`, `val_eq_other_bytes` | `val_eq` holds only for values of the same constructor; an `Other` value never equals a `Bytes` value, whatever the bytes. |
| `cond_holds_argEq_iff`, `cond_holds_argEq_kind`, `cond_holds_argEq_false_of_kind_ne` | `ArgEq index v` holds exactly when argument `index` exists and is `v`, so only for an argument of `v`'s constructor. |
| `bytes_eq_iff` | Two byte strings compare equal exactly when they hold the same bytes. |
| `rule_allows_call` | A rule allows a call only if the call's contract is the rule's contract and its function is in the rule's function list. |
| `rule_allows_extension_false`, `rule_allows_prefix_false` | A call to a proper extension or a proper prefix of the rule's contract id is denied. |
| `signer_eq_iff`, `signer_eq_delegated_external` | `signer_eq a b` returns `ok true` exactly when `a = b`; a `Delegated` signer never equals an `External` one, whatever their bytes. |
| `allows_of_subset`, `allows_all_of_subset`, `denoteSigners_subset` | Authenticating more signers never turns an allow into a refusal. |
| `allows_congr`, `allows_all_congr`, `rule_allows_congr_signers`, `denoteSigners_mem_iff` | Repeats and order in the authenticated signers, or in a rule's signers, do not change the verdict. |
| `rule_allows_threshold_zero`, `signers_met_all_iff`, `rule_allows_false_of_lt` | With threshold 0 a rule's verdict does not depend on the authenticated signers; a threshold equal to the number of distinct signers is met exactly when every signer is authenticated; a threshold above it allows nothing. |

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
