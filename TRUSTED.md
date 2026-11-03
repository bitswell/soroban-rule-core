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
`authorize`'s two passes, under `i < contexts.len()`), and the signer count's
`count += 1`, which runs at most once per position of its loop, so `count`
stays at most `i`. The equivalence theorems prove that neither
overflows. The spending-cap check sums with `i128::checked_add` and
`i128::checked_sub`, which return `None` instead of trapping, and takes its
cutoff with `u32::saturating_sub`. Its two subtractions on `usize`, `len - 1`
and `len - kept_from`, run under `len > 0` and `kept_from <= len`, and
`check_spend_eq` proves that neither fails. The budget operations' walks count
their steps with `step += 1` under `step < tree.len()`, and they sum amounts
with `i128::checked_add`; `spend_eq` proves that the counter never overflows.

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
| `<[T]>::get(i)` | `core.slice.Slice.get` with `core.slice.index.SliceIndexUsizeSlice` | `some` element `i`, or `none` when `i` is out of range. Called on a rule's arguments (a condition's, and a cap's amount), on the rules in `raise_threshold`, the cap steps and `authorize`, on an authorization's choices, and on the tree's nodes in the budget's walks and in `refill`. |
| `<[T]>::get_mut(i)` | `core.slice.Slice.get_mut` with `core.slice.index.SliceIndexUsizeSlice` | `some` element `i` and a function that writes a new element back at `i` (`Slice.set_opt`), or `none` and the slice unchanged when `i` is out of range. Called in `authorize` on the copied records, and in the budget's charging walk on the copied tree. |
| `u32 as usize` | `UScalar.cast` | The same value. Lossless because `usize` has at least 32 bits. Widens indices (an authorization's choices, a cap's `amount_arg` and the budget's node and parent indices included), in `signers_met` the threshold, and `u32::MAX` into `MAX_NODES`. |
| `u32::MAX` | `core.num.U32.MAX` | `2^32 - 1`. |
| `i += 1`, `count += 1` and `step += 1` on `usize` | `+` on `Usize` | Checked addition: `fail` on overflow. |
| `len - 1` and `len - kept_from` on `usize` | `-` on `Usize` | Checked subtraction: `fail` when the result would be negative. |
| `<`, `<=`, `>=`, `==`, `!=` on `usize` | the order and equality of `Usize` | On the values. |
| `!=` on `u8` | equality of `U8` | On the values. |
| `==` on `u64` | equality of `U64` | On the values. |
| `==`, `<`, `<=`, `>` and `>=` on `i128` | equality and order of `I128` | On the values, as signed integers. `lower_cap_limit` compares limits with `>` and `<= 0`, `cap_valid` the limit with `> 0`, and `tree_valid` each allowance and spent amount with `>= 0`. |
| `i128::checked_add`, `i128::checked_sub` | `I128.checked_add`, `I128.checked_sub` | `some` of the sum or difference when it lies between `i128::MIN` and `i128::MAX`, `none` otherwise. |
| `Option<T>` (`Some`, `None`) | Lean's `Option` | The two-constructor inductive. |
| `u32::saturating_sub` | `core.num.U32.saturating_sub` | The difference when it is not negative, `0` otherwise. |
| `usize::BITS` | `core.num.Usize.BITS` | `System.Platform.numBits`, as a `U32`. |
| `<`, `>` and `>=` on `u32` | the order of `U32` | On the values. `lengthen_cap_period` compares periods with `<`, `cap_valid` the period with `> 0`, and the budget's walks a parent index with the current one with `>=`. |
| `const _: () = assert!(usize::BITS >= 32)` | `massert` | `ok ()` when the condition holds, `fail` otherwise. |

`==` on `bool` translates to Lean's own `Bool` equality, which needs no
library model. Writing through a mutable borrow (`*record = next` in
`authorize`, `c.limit = limit` and `c.period = period` in the cap steps)
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
- each enum constructor maps to the constructor of the same name, so `Signer::Delegated` is `Signer.delegated` and `Signer::External` is `Signer.external`, and each `AttenuationError` is the error of the same name;
- each struct field maps to the field of the same name, so a rule's `threshold` is the same `u32`, a `Cap`'s `limit` the same `i128` and its `amount_arg` the chain cap's `amountArg`, and a rule's optional cap the optional denoted cap;
- a slice or vector maps to the list of its elements' denotations, so the authenticated signers are the list of their denotations.

The chain vocabulary gives a cap its meaning (`Chain.Cap.denote`): its
parameters are the cap model's `⟨limit, period⟩`, the limit read as a signed
integer, and the amount a call spends is its argument at `amountArg` when that
argument is an `i128`. That reading is part of the specification as well.

`formal/RuleCore/Equiv/DenoteCap.lean` maps the types of the `cap` module to
the cap model of `formal/RuleCore/Model/Cap.lean` in the same way:

- a `u32` ledger or period is its value as a natural number, and an `i128` amount, total or limit its value as an integer;
- `SpendEntry`, `SpendRecord` and `CapParams` map each field to the field of the same name, and the history to the list of its entries' denotations;
- each `CapError` constructor maps to the constructor of the same name.

`formal/RuleCore/Equiv/Authorize.lean` maps the types of the `authorize`
module the same way:

- each `Refusal` constructor maps to the constructor of the same name, and `Refusal::Cap(e)` to `Refusal.cap` of the denoted `CapError`;
- a result of `authorize` is the `Except` of the denoted records or refusal;
- `authorize`'s contexts, choices, authenticated signers and ledger are the chain vocabulary's authorization of their denotations.

`formal/RuleCore/Equiv/DenoteBudget.lean` maps the types of the `budget`
module to the budget model of `formal/RuleCore/Model/Budget.lean` the same way:

- a `u32` node or parent index is its value as a natural number, and an `i128` allowance, spent amount or amount its value as an integer;
- `Node` maps each field to the field of the same name, the optional parent to the optional value, and a tree to the list of its nodes' denotations;
- each `BudgetError` constructor maps to the constructor of the same name, with its index's value, and a result of `spend`, `delegate` or `refill` is the `Except` of the denoted tree or error.

Each one is proven injective, so two Rust values that differ never have the
same meaning.

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

### The empty batch

Every rule set, the empty one included, allows the empty batch
(`RuleCore.RuleSet.allowsAll_nil`), because that is how `List.all` and
`allows_all`'s loop behave. A Soroban authorization tree always has a root
context, so a batch collected from one is never empty. A caller that builds
batches some other way must reject the empty batch itself.

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
`conformance/vectors/authorize` and the budget traces in
`conformance/vectors/budget` are computed by the Lean model and written as
JSON by the generator's own encoder (`conformance/generator/Conformance/Json.lean`,
`Conformance/Caps.lean`, `Conformance/Authorize.lean` and
`Conformance/Budget.lean`). The Rust runner decodes them into `rule-eval`'s
types (`conformance/runner/src/lib.rs`, `src/caps.rs`, `src/authorize.rs` and
`src/budget.rs`). Neither the
encoding nor the decoding is verified. A mismatch in either one shows up as a
failing vector, unless both get the same field wrong in the same way.
