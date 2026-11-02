# formal

The Lean model of rule evaluation and its theorems. The Lake package is
`rule-core` (MIT OR Apache-2.0); its one library is `RuleCore`, rooted at
`RuleCore.lean`.

| Directory | Contents |
| --- | --- |
| `RuleCore/Model/` | The generic model: rules, rule sets, `narrower`, and the three attenuation steps, over any context type. |
| `RuleCore/Vocab/` | The chain vocabulary (contexts, values, conditions, rules) and its denotation into the generic model. |
| `RuleCore/Theorems/` | The theorems below, and kernel-checked examples of concrete verdicts. |
| `RuleCore/Axioms.lean` | The axioms each theorem depends on, pinned under `#guard_msgs`. |

## Building

```sh
cd formal
lake build
```

`lean-toolchain` pins `leanprover/lean4:v4.35.0`, the Lean release of Aeneas
commit `ab34bd28458a08c150b7cbf1873e59af74588138`'s Lean backend. elan installs
it on the first `lake` call. The package has no Lake dependencies.

CI (`.github/workflows/lean.yml`) rejects `sorry`, `admit`, `partial`,
`unsafe`, `native_decide`, `implemented_by`, `extern` and `axiom` anywhere in
the Lean sources, checks that `RuleCore.lean` imports every module, and runs
`lake build`.

## The generic model

`RuleCore/Model/RuleSet.lean` holds the readable model, generic in the context
type `Ctx`:

```lean
structure Rule (Ctx : Type) where
  scope : Ctx → Bool          -- contract and function match
  conds : List (Ctx → Bool)   -- conditions on this call's arguments

def Rule.allows (r : Rule Ctx) (c : Ctx) : Bool :=
  r.scope c && r.conds.all (· c)

def RuleSet (Ctx : Type) := List (Rule Ctx)

def RuleSet.allows (rs : RuleSet Ctx) (c : Ctx) : Bool :=
  rs.any (·.allows c)

def RuleSet.allowsAll (rs : RuleSet Ctx) (cs : List Ctx) : Bool :=
  cs.all rs.allows

def RuleSet.narrower (rs' rs : RuleSet Ctx) : Prop :=
  ∀ c, rs'.allows c = true → rs.allows c = true
```

`RuleSet` is a plain definition, so `RuleSet.rules` and `RuleSet.ofRules`
convert to and from the underlying list for list notation.

`RuleCore/Model/Attenuation.lean` defines the attenuation steps. Each names a
rule by its position and returns the new rule set, or
`AttenuationError.noSuchRule` when the position is not below the number of
rules:

* `RuleSet.dropRule i` removes rule `i`.
* `RuleSet.addCond i p` appends condition `p` to rule `i`.
* `RuleSet.restrictScope i s` restricts rule `i`'s scope to the contexts that
  also satisfy `s`.

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
* `Cond` is `argEq index val` (argument `index` exists and equals `val`) or
  `argI128AtMost index n` (argument `index` exists, is an `i128`, and is at
  most `n`). A missing argument or another constructor makes the condition
  false.
* `Rule` is `{ contract, functions, conds }` and `RuleSet` is `List Rule`. A
  rule with an empty function list allows nothing.
* `RuleSet.dropRule i`, `RuleSet.addCond i cond` and
  `RuleSet.removeFunctions i fs` are the attenuation operations.
  `removeFunctions` removes every occurrence of every function in `fs` and
  keeps the remaining functions in their order; `dropRule` keeps the remaining
  rules in their order; `addCond` appends. Each returns the new rule set, or
  `AttenuationError.noSuchRule` when `i` is not below the number of rules.
* Argument and rule indices are `UInt32`, as in the Rust evaluator, read as
  list positions through `toNat`.

`Rule.denote` gives each rule's meaning as a generic `Rule Context`: its scope
matches a call to the rule's contract and one of its functions, and each
condition reads the arguments of the call it is evaluated against. Every scope
and every condition is false on a creation. `allows`, `allowsAll` and
`narrower` on chain rule sets are the generic ones on the denotation, and
`Attenuation.denote` maps each chain step to the generic step of the same kind
at position `i.toNat`: `removeFunctions i fs` denotes
`restrictScope i.toNat (notCalling fs)`.

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
| `RuleSet.dropRule_eq_error_iff`, `RuleSet.addCond_eq_error_iff`, `RuleSet.restrictScope_eq_error_iff` | A step is refused with `noSuchRule` exactly when its position is not below the number of rules. |
| `Rule.allows_iff`, `RuleSet.allows_iff`, `RuleSet.allowsAll_iff` | A rule allows a context iff its scope matches and every condition holds; a rule set allows a context iff some rule does; a batch is allowed iff every context in it is. |
| `RuleSet.allowsAll_nil` | Every rule set allows the empty batch. |
| `Rule.allows_of_allows_addCond`, `Rule.allows_of_allows_restrictScope` | A rule with an added condition, or a restricted scope, allows only contexts the original rule allows. |
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
| `Rule.allows_call_iff`, `Rule.allows_iff`, `RuleSet.allows_iff`, `RuleSet.allowsAll_iff` | Each verdict stated in the vocabulary's terms. |
| `RuleSet.dropRule_narrower`, `RuleSet.addCond_narrower`, `RuleSet.removeFunctions_narrower`, `RuleSet.attenuate_narrower` | Each chain attenuation operation yields a narrower rule set. |
| `RuleSet.narrower_refl`, `RuleSet.narrower_trans` | `narrower` on chain rule sets is reflexive and transitive. |
| `RuleSet.Derives.narrower`, `RuleSet.attenuateAll_derives`, `RuleSet.attenuateAll_narrower` | Every chain rule set derived from a root by attenuation steps is narrower than the root. |
| `RuleSet.allowsAll_of_narrower` | A narrower chain rule set allows a batch only if its ancestor does. |
| `Rule.denote_addCond`, `Rule.denote_removeFunctions`, `RuleSet.denote_modifyRule`, `RuleSet.denote_dropRule`, `RuleSet.denote_addCond`, `RuleSet.denote_removeFunctions`, `RuleSet.denote_attenuate` | Each chain operation commutes with the denotation: the denotation of its result is the generic step's result on the denotation. |
| `Rule.mem_removeFunctions` | After removing `fs`, a function is in a rule's list iff it was before and is not in `fs`. |
| `RuleSet.dropRule_eq_error_iff`, `RuleSet.addCond_eq_error_iff`, `RuleSet.removeFunctions_eq_error_iff`, `RuleSet.modifyRule_eq_error_iff` | A chain operation is refused with `noSuchRule` exactly when its index is not below the number of rules. |
| `RuleSet.rules_denote` | The rules of a chain rule set's denotation are the denotations of its rules. |

The empty batch is allowed by every rule set (`RuleCore.RuleSet.allowsAll_nil`;
chain `allowsAll` is the generic one on the denotation). A
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
membership (`function ∈ r.functions`) uses.
