# Trusted

The theorems in `formal/` are checked by Lean's kernel. What they say about
`crates/rule-eval` holds only as far as everything below holds. Nothing in
this repository checks these items. `claims.yaml` lists each of them as an
`assumed` claim, and every proven claim that rests on one names it under
`assumes`.

## rustc

The theorems are about the MIR that Charon reads from rustc
`nightly-2026-09-17` (`rust-toolchain.toml`). Deployed code is what rustc's
back end produces from that MIR, for native targets and for `wasm32v1-none`.
CI also builds the crate with stable 1.99.0. Two things are trusted here:
the back end preserves the MIR's behaviour, and the stable compiler gives the
crate the same meaning as the nightly. Nothing here checks the compiled
binary or the WebAssembly against the Lean translation.

`overflow-checks = true` in the `release` and `contract` profiles makes
overflowing arithmetic trap, as Aeneas's model of it fails. The evaluator's
only arithmetic is the loop counter's `i += 1`, under `i < s.len()` (in
`authorize`'s first and third passes, under `i < contexts.len()`), and the signer count's
`count += 1`, which runs at most once per position of its loop, so `count`
stays at most `i`. The equivalence theorems prove that neither
overflows. The spending-cap check sums with `i128::checked_add` and
`i128::checked_sub`, which return `None` instead of trapping, and takes its
cutoff with `u32::saturating_sub`. Its two subtractions on `usize`, `len - 1`
and `len - kept_from`, run under `len > 0` and `kept_from <= len`, and
`check_spend_eq` proves that neither fails. The budget operations' walks count
their steps with `step += 1` under `step < tree.len()`, and they sum amounts
with `i128::checked_add`; `spend_eq` proves that the counter never overflows.
The lowering divides a `u32` by 16,777,216, 65,536 and 256 and takes it modulo
256, none of which can fail, and narrows only where the value fits: a byte of
a `u32` after a division or remainder that leaves less than 256, and a signer
count cast to `u32` under `count <= u32::MAX as usize`. `u32_xdr_eq` and
`threshold_of_eq` prove the values. A last ledger is `u32::saturating_sub`.

## Charon

Charon `7b462d9159db2ed3015162352183906a30bfafc6` (`charon cargo
--preset=aeneas --error-on-warnings`) is trusted to translate the crate's MIR
to LLBC faithfully. `flake.lock` pins this commit, and the flake checks that
it equals Aeneas's `charon-pin`.

## Aeneas

Aeneas `ab34bd28458a08c150b7cbf1873e59af74588138` (`aeneas -backend lean
-warnings-as-errors`) is trusted to translate the LLBC to Lean faithfully. Its
output is `formal/RuleCore/Extracted/RuleEval.lean`, which CI regenerates and
compares on every change. Aeneas names each module's namespace after the
module, so in the crate no parameter or local variable carries a module's
name.

## Aeneas's Lean library

The translation is written against `backends/lean` of the same Aeneas commit
(`formal/lakefile.toml`). The proofs use the library's definitions and are
checked by the kernel, so what is trusted is that those definitions model
Rust. No theorem of the package depends on an axiom the library declares.
`RuleCore/Axioms.lean` checks every theorem against `propext`, `Quot.sound`
and `Classical.choice`.

### Result and loop

- `Result`: a translated function returns `ok v`, `fail e` (a panic) or `div`
  (divergence). The equivalence theorems state `ok`, so they rule out both
  panics and divergence. What is trusted is that every panic the Rust code
  can reach is a `fail` in the model.
- `loop`: each `while` loop becomes `loop` over a body that returns `cont` or
  `done`. `loop` is defined by `partial_fixpoint`, so it may diverge. Its
  meaning is trusted to be the Rust loop's. `partial_fixpoint` is a
  kernel-checked construction, distinct from the `partial` keyword that CI
  rejects.

### Rust library items the evaluator calls

The translation calls each item below, and the library's Lean definition of
each is trusted to match the Rust item.

| Rust | Lean (Aeneas library) | Model |
| --- | --- | --- |
| `u8`, `u32`, `u64`, `i128`, `usize` | `Std.U8`, `Std.U32`, `Std.U64`, `Std.I128`, `Std.Usize` | Bounded integers. `usize` has `System.Platform.numBits` bits, which Lean fixes only as 32 or 64. The proofs hold for both widths, so they cover `wasm32v1-none` and 64-bit native targets. |
| `Result<T, E>` (`Ok`, `Err`) | `core.result.Result` | The two-constructor inductive. |
| `&[T]` | `Slice` | A list of at most `Usize.max` elements. |
| `Vec<T>` | `alloc.vec.Vec` | A list of at most `Usize.max` elements. |
| `Vec::new` | `alloc.vec.Vec.new` | The empty vector. |
| `Vec::push` | `alloc.vec.Vec.push` | Appends. Fails with `maximumSizeExceeded` when the vector already holds `Usize.max` elements. Allocation failure, which aborts in Rust, is outside the model. |
| `Vec::len` | `alloc.vec.Vec.len` | The list's length. |
| `Deref` of `Vec<T>` to `&[T]` | `alloc.vec.Vec.deref` | The same list. |
| `DerefMut` of `Vec<T>` to `&mut [T]` | `alloc.vec.Vec.deref_mut` | The same list, and a function that rebuilds the vector from the slice written back. Called in `authorize` to charge a record in place, and in the budget's charging walk to charge a node of the copied tree. |
| `<[T]>::len` | `Slice.len` | The list's length. |
| `s[i]` on a slice (`Index<usize>`) | `Slice.index_usize` | Element `i`, or `fail` when `i` is out of range. |
| `<[T]>::get(i)` | `core.slice.Slice.get` with `core.slice.index.SliceIndexUsizeSlice` | `some` element `i`, or `none` when `i` is out of range. Called on a rule's arguments (a condition's, and a cap's amount), on a string argument's bytes in `bytes_starts_with`, on the rules in `raise_threshold`, the cap steps, `lower_valid_until` and both of `authorize`'s passes over choices, on an authorization's choices, and on the tree's nodes in the budget's walks and in `refill`. |
| `<[T]>::get_mut(i)` | `core.slice.Slice.get_mut` with `core.slice.index.SliceIndexUsizeSlice` | `some` element `i` and a function that writes a new element back at `i` (`Slice.set_opt`), or `none` and the slice unchanged when `i` is out of range. Called in `authorize` on the copied records, and in the budget's charging walk on the copied tree. |
| `u32 as usize` | `UScalar.cast` | The same value. Lossless because `usize` has at least 32 bits. Widens indices (an authorization's choices, a cap's `amount_arg` and the budget's node and parent indices included), in `signers_met` the threshold, and `u32::MAX` into `MAX_NODES` and in the lowering's `threshold_of`. |
| `u32 as u8`, `usize as u32` | `UScalar.cast` | The value modulo `2^8` or `2^32`. The lowering casts only a `u32` below 256 and a signer count of at most `u32::MAX`, so no value changes. |
| `/` and `%` on `u32` | `UScalar.div`, `UScalar.rem` | The quotient and the remainder, `fail` on a zero divisor. `u32_xdr` divides and takes remainders by the constants 16,777,216, 65,536 and 256. |
| `[u8; N]` and `[Vec<u8>; 1]` literals, and their coercion to slices | `Array.make`, `Array.to_slice` | An array of the listed elements, and the slice of the same list. The lowering builds the names `transfer` and `apply_doc`, a `u32`'s XDR and the recovery rule's function list from them. |
| `i128::MAX` | `core.num.I128.MAX` | `2^127 - 1`. The lowering's amount condition bounds argument 2 by it. |
| `u32::MAX` | `core.num.U32.MAX` | `2^32 - 1`. |
| `i += 1`, `count += 1` and `step += 1` on `usize` | `+` on `Usize` | Checked addition: `fail` on overflow. |
| `len - 1` and `len - kept_from` on `usize` | `-` on `Usize` | Checked subtraction: `fail` when the result would be negative. |
| `<`, `<=`, `>`, `>=`, `==`, `!=` on `usize` | the order and equality of `Usize` | On the values. The lowering compares a string's length with 256 and a signer count with `u32::MAX`. |
| `!=` on `u8` | equality of `U8` | On the values. |
| `==` and `!=` on `u64` | equality of `U64` | On the values. `!=` compares a rule's generation with the current one in `authorize`. |
| `==`, `<`, `<=`, `>` and `>=` on `i128` | equality and order of `I128` | On the values, as signed integers. `lower_cap_limit` compares limits with `>` and `<= 0`, `cap_valid` the limit with `> 0`, and `tree_valid` each allowance and spent amount with `>= 0`. |
| `i128::checked_add`, `i128::checked_sub` | `I128.checked_add`, `I128.checked_sub` | `some` of the sum or difference when it lies between `i128::MIN` and `i128::MAX`, `none` otherwise. |
| `Option<T>` (`Some`, `None`) | Lean's `Option` | The two-constructor inductive. |
| `u32::saturating_sub` | `core.num.U32.saturating_sub` | The difference when it is not negative, `0` otherwise. The cap check takes its cutoff with it, and the lowering a last ledger. |
| `usize::BITS` | `core.num.Usize.BITS` | `System.Platform.numBits`, as a `U32`. |
| `<`, `>` and `>=` on `u32` | the order of `U32` | On the values. `lengthen_cap_period` compares periods with `<`, `cap_valid` the period with `> 0`, `authorize` a rule's last ledger with the current one with `<`, `lower_valid_until` a new last ledger with the current one with `>`, and the budget's walks a parent index with the current one with `>=`. |
| `const _: () = assert!(usize::BITS >= 32)` | `massert` | `ok ()` when the condition holds, `fail` otherwise. |

`==` on `bool` and `!` translate to Lean's own `Bool` equality and negation,
which need no library model. Copying a rule's `Option<u32>` last ledger and
`Option<u64>` generation copies the value. Writing through a mutable borrow
(`*record = next` in `authorize`, `c.limit = limit` and `c.period = period` in
the cap steps, `r.valid_until = Some(valid_until)` in `lower_valid_until`)
translates to functional updates and backward functions in the generated Lean,
not to library items. So does `m.spent = spent` in the budget's charging walk
and `n.allowance = allowance` in `refill`.

## Lean's kernel

Lean `v4.35.0` (`formal/lean-toolchain`, which the flake checks against
Aeneas's Lean backend) is trusted to check proofs correctly. The theorems also
trust the three axioms they may use: `propext`, `Quot.sound` and
`Classical.choice`.

## The denotation functions

`formal/RuleCore/Equiv/Denote.lean` maps each translated type to the chain
vocabulary of `formal/RuleCore/Vocab/Chain.lean`, and these maps are part of
the specification. The equivalence theorems prove that the translated code
computes the chain model's results on the denotations. That those results are
what the Rust values mean rests on the denotations. Each denotation is
structural:

- a byte string is the same bytes;
- an integer is its bit vector;
- each enum constructor maps to the constructor of the same name, so `Signer::Delegated` is `Signer.delegated` and `Signer::External` is `Signer.external`, `Val::String` is `Val.string`, `Cond::ArgIn` and `Cond::ArgStrPrefix` are `Cond.argIn` and `Cond.argStrPrefix`, `Functions::AnyExcept` and `Functions::Only` are `Functions.anyExcept` and `Functions.only`, and each `AttenuationError` is the error of the same name;
- each struct field maps to the field of the same name, so a rule's `threshold` is the same `u32`, a `Cap`'s `limit` the same `i128` and its `amount_arg` the chain cap's `amountArg`, a rule's optional cap the optional denoted cap, and its optional `valid_until` and `generation` the chain rule's optional `validUntil` (`u32`) and `generation` (`u64`);
- a slice or vector maps to the list of its elements' denotations, so the authenticated signers are the list of their denotations.

The chain vocabulary gives a cap its meaning (`Chain.Cap.denote`): its
parameters are the cap model's `⟨limit, period⟩`, the limit read as a signed
integer, and the amount a call spends is its argument at `amountArg` when that
argument is an `i128`. It gives a rule's functions their meaning
(`Functions.Mem`): a list matches the functions it lists, and `anyExcept`
every function it does not list. It reads a rule's last ledger and
generation, and an authorization's ledger and generation, as natural numbers.
Those readings are part of the specification as well.

`formal/RuleCore/Equiv/DenoteCap.lean` maps the types of the `cap` module to
the cap model of `formal/RuleCore/Model/Cap.lean` in the same way:

- a `u32` ledger or period is its value as a natural number, and an `i128` amount, total or limit its value as an integer;
- `SpendEntry`, `SpendRecord` and `CapParams` map each field to the field of the same name, and the history to the list of its entries' denotations;
- each `CapError` constructor maps to the constructor of the same name.

`formal/RuleCore/Equiv/Authorize.lean` maps the types of the `authorize`
module the same way:

- each `Refusal` constructor maps to the constructor of the same name (`Expired` to `expired`, `StaleGeneration` to `staleGeneration`, `UnauthorizedSigner` to `unauthorizedSigner`), and `Refusal::Cap(e)` to `Refusal.cap` of the denoted `CapError`;
- a result of `authorize` is the `Except` of the denoted records or refusal;
- `authorize`'s contexts, choices, authenticated signers, ledger and generation are the chain vocabulary's authorization of their denotations.

`formal/RuleCore/Equiv/DenoteBudget.lean` maps the types of the `budget`
module to the budget model of `formal/RuleCore/Model/Budget.lean` the same way:

- a `u32` node or parent index is its value as a natural number, and an `i128` allowance, spent amount or amount its value as an integer;
- `Node` maps each field to the field of the same name, the optional parent to the optional value, and a tree to the list of its nodes' denotations;
- each `BudgetError` constructor maps to the constructor of the same name, with its index's value, and a result of `spend`, `delegate` or `refill` is the `Except` of the denoted tree or error.

`formal/RuleCore/Equiv/DenoteDocument.lean` maps the types of the `document`
and `scoped` modules to the document vocabulary of
`formal/RuleCore/Vocab/Document.lean` the same way:

- each enum constructor maps to the constructor of the same name (`Scope::SelfAdmin` to `selfAdmin`, `Pred::U32Eq` to `u32Eq`, `ScopeError::ExcludedScope` to `excludedScope`);
- each struct field maps to the field of the same name (`period_ledgers` to `periodLedgers`, `not_after_ledger` to `notAfterLedger`), an optional field to the optional denoted value, and a vector to the list of its elements' denotations;
- a result of `lower_scoped` is the `Except` of the denoted rules or error.

Each one is proven injective, so two Rust values that differ never have the
same meaning.

## The document's meaning

`formal/RuleCore/Vocab/Document.lean` says what a document means:
`Doc.allows` without time, generation or caps, and `Doc.authorize` through an
authorization, as OpenZeppelin's `do_check_auth` checks the rules Perch
installs for the document. The compile-soundness theorems prove the lowering
equal to this meaning, so that the lowering allows what a document says rests
on the meaning saying what Perch's installed rules do on chain. It is written
from Perch `dff2a73` (`bitswell-hq/stellar-registry__perch`) and OpenZeppelin
`stellar-accounts` at `theahaco/stellar-contracts-OZ@33726766`, the revision
Perch pins, and it is part of the specification, as the denotations are. Three
of its readings come from outside the document:

- a shell gives a `u32` argument as `Val::Other` of its `ScVal` XDR, and `u32Xdr` is that XDR;
- a capped rule's spends are charged with the cap model, which mirrors OpenZeppelin's spending-limit policy with the differences `ARCHITECTURE.md` records;
- the recovery rule's calls are checked by the recovery controller against its own state, which the meaning takes as a parameter `ctl`. The lowering's recovery rule allows every `apply_doc` on the account, which over-approximates every controller check that allows only `apply_doc` calls (`Doc.lower_authorize_of_check`).

## The Soroban models

`formal/RuleCore/Soroban/` models the part of Soroban the contract shells rely
on: values and their XDR (`Val.lean`), contract storage as a finite map
(`Storage.lean`), authorization contexts, the form the host passes them in
and what `rule-eval` reads of them (`Context.lean`), signed authorization
trees, credentials and the host's matching of `require_auth` (`Auth.lean`),
and calls, rollback, `require_auth` and `__check_auth` (`Host.lean`). They are
written from `soroban-env-host` 29.0.1 (`auth.rs`, `host/frame.rs`,
`host.rs`, `host/conversion.rs`, `host/data_helper.rs`,
`builtin_contracts/account_contract.rs` and
`builtin_contracts/common_types.rs`)
and they are part of the specification, as the denotations are. The theorems
in `RuleCore.Theorems.Soroban` are about the models; that they describe the
host rests on the models, and nothing proves the models equal to the host.
The host harness tests them against the host on every change
([the host harness](#the-host-harness)), at the pin, soroban-env-host 29.0.1,
and at the next release, 30.0.0, with the model's own vectors and with the
host's own authorization and storage tests transcribed into the same form
(`conformance/vectors/soroban/seed`, whose `coverage.json` lists each host test
the models leave out and why).

The models leave out, and nothing here tests:

- time to live, archival and automatic restoration of entries, footprints, fees and resources;
- the checks stellar-core makes on a transaction before the host runs it, such as which protocol admits which credentials and frozen keys (CAP-77);
- Stellar accounts' ed25519 signatures, source-account credentials, `require_auth` inside `__check_auth`, `require_auth_for_args`, `authorize_as_current_contract` and contract creation as a call (a creation context is modelled, and the facade reads it, as data);
- a key holding a muxed address in instance storage, which host 29.0.1 refuses only when it writes the instance back at the end of the call (the facade refuses every such key at once);
- executable tags (CAP-85), which the host takes as values and treats apart as storage keys, and which the facade refuses as keys and as values;
- every protocol but 29. The vectors also run on soroban-env-host 30.0.0 (protocol 30), which tests the models there as far as the vectors reach; nothing models a change between protocols.

## soroban-sdk and soroban-env-host

`crates/soroban-facade`'s real implementation and the host harness build
against soroban-sdk 29.0.1, which fixes soroban-env-host 29.0.1 and
stellar-xdr 28.0.0 (protocol 29, the protocol mainnet runs), as `Cargo.lock`
records. The harness also builds, in `conformance/host/p30`, against
soroban-sdk 30.0.0-rc.1, which fixes soroban-env-host 30.0.0 and stellar-xdr
30.0.0 (protocol 30, the next), as that crate's own `Cargo.lock` records.

| Host tested | SDK | stellar-xdr | Protocol | Through |
| --- | --- | --- | --- | --- |
| soroban-env-host 29.0.1 | soroban-sdk 29.0.1 | 28.0.0 | 29 | the facade's real implementation, and the SDK directly |
| soroban-env-host 30.0.0 | soroban-sdk 30.0.0-rc.1 | 30.0.0 | 30 | the SDK directly |

The harness drives each host through
soroban-sdk's testutils: native test contracts (`ContractFunctionSet`),
`set_auths` and `try_invoke_contract`. That path shares storage, rollback
within a transaction and enforcing authorization with the host function
stellar-core calls (`e2e_invoke::invoke_host_function`), and it is trusted to
behave as that path does for what the vectors exercise. A contract built at
the pin runs on the host the network's protocol selects, which is why the
vectors run on the next host as well as the pin's.

Building the facade's real implementation for `wasm32v1-none` outside
stellar-cli needs `SOROBAN_SDK_BUILD_SYSTEM_SUPPORTS_SPEC_SHAKING_V2` set,
which CI sets for that build alone: soroban-sdk 29 refuses a wasm build
without it, since it relies on the build system to shake a contract's spec.
The facade exports no contract functions; a shell builds through stellar-cli.

### SDK items the real implementation calls

`SdkHost` (`crates/soroban-facade/src/sdk.rs`) is the only code in the
repository that calls the SDK. At soroban-sdk 29.0.1 it calls:

| Item | Use |
| --- | --- |
| `Env::storage`, and `Storage::persistent`, `Storage::temporary`, `Storage::instance` | The storage of each durability. |
| `get`, `has`, `set` and `remove` of `Persistent`, `Temporary` and `Instance`, on `Val` keys and values | The four storage operations. |
| `Address::require_auth` | `require_auth`. |
| `soroban_sdk::Val` | The host's value. |
| `Bytes::from_slice`, `Bytes::len`, `Bytes::copy_into_slice` | Moving XDR between the host and the facade. |
| `xdr::ToXdr::to_xdr` (the host's `serialize_to_bytes`) | A host value's `ScVal` XDR. |
| `xdr::FromXdr::from_xdr` for `Val` and for `Address` (the host's `deserialize_from_bytes`) | The host value of a facade value, and the host address of a facade address. |

The facade's own XDR writer and reader stand between these and its plain
values, and a value whose XDR the reader does not read back is refused before
`from_xdr`. The host traps on XDR it cannot represent as a value, as it does
for any contract.

## The facade's conversion

`crates/soroban-facade` is not translated to Lean. Its XDR writer
(`xdr::encode`) is meant to be `Val.xdr`, its reading of contexts
(`auth_contexts`) `contextsOfVal`, and its conversion to `rule-eval`'s types
(`val_to_rule_eval`, `to_rule_eval`) `Val.toChain` and `AuthFn.toChain`; the
value and context vectors check each one against the model, and the host
harness checks them against what the host gives `__check_auth` and against
each SDK's reading of every context vector. Nothing proves them equal.

## The host harness

`conformance/host` replays the Soroban vectors on the host. Five of its parts
are trusted:

- the signature payload it expects is SHA-256 (the `sha2` crate) of `stellar-xdr`'s encoding of the `HashIdPreimage` it builds from the model's preimage and the ledger's network id;
- values pass between the vectors, the facade and the host through the facade's XDR and `stellar-xdr`'s reading and writing of it;
- its native contracts run each step of a call or of `__check_auth` as the model's step says, and record what they see;
- its reading of the context vectors takes each SDK's `auth::Context` (`TryFromVal` and `IntoVal`) as the reading a shell's `__check_auth` makes, and a trap while reading as a refusal, as it is in a contract;
- it turns the host's diagnostic events off. They are no part of what the harness compares, and with them on, a native contract's storage call refused for a muxed key leaves the host's shadow budget spent and testutils' next record of the authorizations panics (`Error(Budget, ExceededLimit)`), on both hosts.

A mistake in any of them shows up as a failing vector, unless it hides a
difference between the model and the host in the same way on both sides.

## Stated rules

The theorems take these as given about their inputs or callers.

### CondRoom

`add_cond_eq`, the equivalence for `add_cond`, assumes `CondRoom rules index`:
the rule at `index`, if there is one, holds fewer than `Usize.max` conditions.
That is the bound in Aeneas's model of `Vec::push`. `add_cond_full` proves the
bound exact: on a rule already holding `Usize.max` conditions, the translated
`add_cond` fails. In Rust a `Vec<Cond>` holds at most `isize::MAX` bytes, so it
never reaches that length. The theorems stated on the translation alone do not
assume `CondRoom`, because an `add_cond` that returned `Ok` had room
(`add_cond_room`).

### FunctionsRoom

`remove_functions_eq`, the equivalence for `remove_functions`, assumes
`FunctionsRoomAt rules index functions`: when the rule at `index` is a
wildcard, `AnyExcept(removed)`, the functions it excludes and the ones removed
number at most `Usize.max` together, so the vector holding both fits Aeneas's
model of `Vec`. Every rule whose functions are a list meets it
(`functionsRoom_only`): removing functions from a list never grows it.
`remove_functions_full` proves the rule exact: on a wildcard without that room,
the translated step fails. In Rust a `Vec<Vec<u8>>` holds at most
`isize::MAX` bytes, so two of them never hold `Usize.max` names between them.
The theorems stated on the translation alone do not assume it, because a
`remove_functions` that returned `Ok` had room (`remove_functions_room`).

### LowerRoom

`lower_eq` and `lower_scoped_eq`, the equivalences for the lowering, assume
`LowerRoom doc`: a document configuring recovery has fewer than `Usize.max`
rules, and each capped rule fewer than `Usize.max` argument predicates. That is
the bound in Aeneas's model of `Vec::push`, which the lowering calls once more
than the rules for the recovery rule and once more than the predicates for a
capped rule's amount condition. `lower_full` proves the rule exact for the
rules: on a document configuring recovery with `Usize.max` rules, the
translated `lower` fails. In Rust a `Vec<DocRule>` or `Vec<ArgConstraint>`
holds at most `isize::MAX` bytes, so it never reaches that length.

### The empty batch

Every rule set, the empty one included, allows the empty batch
(`RuleCore.RuleSet.allowsAll_nil`), because that is how `List.all` and
`allows_all`'s loop behave. A Soroban authorization tree always has a root
context, so a batch collected from one is never empty: in the Soroban model,
every `__check_auth` call receives its tree's contexts in preorder, root first
(`RuleCore.Soroban.Tx.run_checkAuth_contexts`), and the host harness tests
that the host passes exactly those. A caller that builds batches some other
way must reject the empty batch itself. `authorize` accepts
an empty batch only when it authenticates no signer, since no rule is chosen.

### No creation is a vocabulary property

No chain rule set allows a contract creation, because every chain scope is
false on a creation (`RuleCore.Chain.RuleSet.allows_create`). The generic
model makes no such claim: a generic scope is an arbitrary predicate. The
no-creation guarantee therefore covers rule sets built in the chain vocabulary,
which is the vocabulary `rule-eval` implements.

### Ledgers start at 1

`period_le_limit`, which bounds every window of `period` consecutive ledgers,
assumes that every call is made at ledger 1 or later. Stellar's ledgers start
at 1: the genesis ledger has sequence 1 (`GENESIS_LEDGER_SEQ`,
[stellar-core `src/ledger/LedgerManagerImpl.cpp` line 112](https://github.com/stellar/stellar-core/blob/b8c4f12d6f1159d67be8743c87a3c7df839ae7f4/src/ledger/LedgerManagerImpl.cpp#L112)),
and a contract runs in a later ledger, so `e.ledger().sequence()` is never 0.
Without the rule the statement is false. For `now < period` the cutoff
`now.saturating_sub(period)` is 0 and evicts entries at ledger 0, so two spends
of the whole limit at ledger 0 are both accepted (`period_ledger_zero`). The
window that eviction leaves at each ledger is bounded without the rule
(`window_le_limit`), and so is every window starting at ledger 1 or later
(`period_le_limit_of_pos`).

## The conformance encoding

The vectors in `conformance/vectors`, the cap traces in
`conformance/vectors/caps`, the authorization traces in
`conformance/vectors/authorize`, the budget traces in
`conformance/vectors/budget`, the document traces in
`conformance/vectors/documents` and the Soroban vectors in
`conformance/vectors/soroban` are computed by the Lean model and written as
JSON by the generator's own encoder (`conformance/generator/Conformance/Json.lean`,
`Conformance/Caps.lean`, `Conformance/Authorize.lean`, `Conformance/Budget.lean`,
`Conformance/Documents.lean` and `Conformance/Soroban/`). The Rust runner
decodes them into `rule-eval`'s and `soroban-facade`'s types
(`conformance/runner/src/lib.rs`, `src/caps.rs`, `src/authorize.rs`,
`src/budget.rs`, `src/documents.rs` and `src/soroban.rs`). Neither the
encoding nor the decoding is verified. A mismatch in either one shows up as a
failing vector, unless both get the same field wrong in the same way.
