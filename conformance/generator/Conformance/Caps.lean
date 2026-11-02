import Conformance.Random
import RuleCore.Model.Cap

/-!
# Cap traces

A `Trace` is the specification of one cap trace: a cap, a starting record and
a list of calls. `Trace.toJson` runs the calls through the Lean model's
`RuleCore.Cap.Params.check`, each on the record the calls before it left (the
same record after a refusal), and writes every call with its expected outcome:
the record after it, or the refusal.

The named traces exercise each refusal, the inclusive limit, eviction at and
beside the cutoff, the cutoff saturating at ledger 0, the history bound, each
checked sum, a lowered limit over an existing record, the clock check and
invalid caps. The randomized traces draw caps, starting ledgers and calls from
small universes that include the `u32` and `i128` extremes, with ledgers that
mostly advance by less than a period and sometimes go back.
-/

namespace Conformance.Caps

open RuleCore.Cap
open Conformance.Random (Gen Rng below pick next)

/-- The version of the cap trace format in `conformance/README.md`. -/
def formatVersion : Nat := 1

/-- The seed of the committed randomized traces is the vectors' seed; this is
their number. -/
def defaultCount : Nat := 50

def u32Max : Nat := 2 ^ 32 - 1

structure Trace where
  /-- The file name, without `.json`. -/
  name : String
  description : String
  params : Params
  start : Record := .empty
  calls : List Call

/-! ## Encoding -/

def encodeAmount (n : Int) : Json := .str (toString n)

def encodeLedger (n : Nat) : Json := .num n

def encodeEntry (e : Entry) : Json :=
  .obj [("ledger", encodeLedger e.ledger), ("amount", encodeAmount e.amount)]

def encodeRecord (r : Record) : Json :=
  .obj [("history", .arr (r.history.map encodeEntry)), ("total", encodeAmount r.total)]

def encodeCapError : CapError → Json
  | .negativeAmount => .str "negative_amount"
  | .ledgerBeforeNewest => .str "ledger_before_newest"
  | .overflow => .str "overflow"
  | .limitExceeded => .str "limit_exceeded"
  | .historyFull => .str "history_full"

/-- Each call with the model's outcome, applied to the record the calls before
it left. -/
def callsJson (p : Params) : Record → List Call → List Json
  | _, [] => []
  | r, k :: ks =>
    let call (expected : Json) : Json :=
      .obj [("now", encodeLedger k.now), ("amount", encodeAmount k.amount),
        ("expected", expected)]
    match p.check r k.now k.amount with
    | .ok r' => call (tagged "ok" (encodeRecord r')) :: callsJson p r' ks
    | .error e => call (tagged "error" (encodeCapError e)) :: callsJson p r ks

def Trace.toJson (t : Trace) : Json :=
  .obj [
    ("format", .num formatVersion),
    ("name", .str t.name),
    ("description", .str t.description),
    ("limit", encodeAmount t.params.limit),
    ("period", encodeLedger t.params.period),
    ("params_valid", .bool t.params.valid),
    ("start", encodeRecord t.start),
    ("calls", .arr (callsJson t.params t.start t.calls))]

def inI128 (n : Int) : Bool := decide (i128Min ≤ n ∧ n ≤ i128Max)

def inU32 (n : Nat) : Bool := decide (n ≤ u32Max)

/-- Every ledger, period and amount of the trace fits the Rust types: `u32`
and `i128`. -/
def Trace.inRange (t : Trace) : Bool :=
  inI128 t.params.limit && inU32 t.params.period && inI128 t.start.total &&
    t.start.history.all (fun e => inU32 e.ledger && inI128 e.amount) &&
    t.calls.all (fun k => inU32 k.now && inI128 k.amount)

/-! ## Named traces -/

def call (now : Nat) (amount : Int) : Call := ⟨now, amount⟩

/-- A record of `n` entries of amount 1 at ledger `ledger`. -/
def ones (n ledger : Nat) : Record :=
  ⟨List.replicate n ⟨ledger, 1⟩, n⟩

def named : List Trace := [
  { name := "cap-within-limit"
    description := "Spends at successive ledgers are recorded until their total reaches the limit; the next is refused."
    params := ⟨100, 10⟩
    calls := [call 1 40, call 2 30, call 3 30, call 4 1] },
  { name := "cap-limit-inclusive"
    description := "A spend taking the total exactly to the limit passes; one more is refused, and so is a single spend over the limit."
    params := ⟨100, 10⟩
    calls := [call 1 101, call 1 100, call 1 1, call 2 1] },
  { name := "cap-window-slides"
    description := "Entries at or before now - period are evicted: at ledger 20 with period 10, ledger 10 is evicted and ledger 11 kept."
    params := ⟨100, 10⟩
    calls := [call 10 30, call 11 30, call 12 30, call 19 11, call 19 10, call 20 41, call 20 30,
      call 21 31, call 1000 100] },
  { name := "cap-refusal-keeps-record"
    description := "A refused spend leaves the record as it was, its eviction included."
    params := ⟨100, 10⟩
    calls := [call 10 60, call 11 40, call 20 80, call 20 1, call 21 61] },
  { name := "cap-negative-amount"
    description := "A negative amount is refused, before the clock check."
    params := ⟨100, 10⟩
    calls := [call 5 10, call 6 (-1), call 0 (-1), call 6 i128Min, call 6 10] },
  { name := "cap-zero-amount"
    description := "A zero amount passes and changes nothing: at any ledger, before the newest entry, and when the total already exceeds the limit."
    params := ⟨50, 10⟩
    start := ⟨[⟨5, 80⟩], 80⟩
    calls := [call 6 0, call 0 0, call u32Max 0, call 6 1] },
  { name := "cap-lowered-limit"
    description := "Over a record built under a higher limit, a positive spend is refused until eviction brings the total plus the amount within the lowered limit."
    params := ⟨50, 10⟩
    start := ⟨[⟨1, 30⟩, ⟨3, 30⟩], 60⟩
    calls := [call 4 1, call 11 20, call 11 21, call 12 1, call 13 30, call 13 1] },
  { name := "cap-ledger-before-newest"
    description := "A positive spend at a ledger earlier than the newest entry is refused; the newest ledger itself and later ones pass."
    params := ⟨100, 10⟩
    calls := [call 9 10, call 8 1, call 0 1, call 9 1, call 10 1, call 9 1] },
  { name := "cap-same-ledger"
    description := "Several spends in one ledger are each recorded and count together against the limit."
    params := ⟨10, 5⟩
    calls := [call 7 3, call 7 3, call 7 4, call 7 1, call 12 10] },
  { name := "cap-ledger-zero"
    description := "At ledger 0 the cutoff saturates to 0 and evicts entries at ledger 0, so each spend of the whole limit at ledger 0 is recorded alone."
    params := ⟨100, 10⟩
    calls := [call 0 100, call 0 100, call 0 100, call 1 1] },
  { name := "cap-saturating-cutoff"
    description := "Before ledger period the cutoff is 0: an entry at ledger 0 is evicted, one at ledger 1 is kept."
    params := ⟨100, 10⟩
    start := ⟨[⟨0, 60⟩, ⟨1, 40⟩], 100⟩
    calls := [call 5 61, call 5 60, call 6 1] },
  { name := "cap-u32-extremes"
    description := "The largest ledger and period: at ledger u32::MAX with period u32::MAX the cutoff is 0."
    params := ⟨100, u32Max⟩
    start := ⟨[⟨0, 50⟩, ⟨1, 50⟩], 100⟩
    calls := [call u32Max 51, call u32Max 50, call u32Max 1] },
  { name := "cap-period-one"
    description := "With period 1, each ledger is its own window."
    params := ⟨10, 1⟩
    calls := [call 1 10, call 1 1, call 2 10, call 4 10] },
  { name := "cap-history-fills"
    description := "A record holding 999 entries takes one more; at 1000 a spend under the limit is refused until eviction makes room."
    params := ⟨10000, 10⟩
    start := ones 999 1
    calls := [call 1 1, call 1 1, call 11 1] },
  { name := "cap-history-full-after-limit"
    description := "The limit is checked before the history bound."
    params := ⟨1000, 10⟩
    start := ones 1000 1
    calls := [call 1 1, call 2 1] },
  { name := "cap-overflow-total"
    description := "A new total that does not fit in an i128 is refused with overflow."
    params := ⟨i128Max, 10⟩
    start := ⟨[⟨1, i128Max - 1⟩], i128Max - 1⟩
    calls := [call 2 2, call 2 1, call 3 1] },
  { name := "cap-overflow-evicted"
    description := "Evicted amounts that do not sum within an i128 are refused with overflow; the record is not one the check builds."
    params := ⟨100, 10⟩
    start := ⟨[⟨1, i128Max⟩, ⟨2, 1⟩, ⟨30, 1⟩], 1⟩
    calls := [call 30 1, call 11 1] },
  { name := "cap-overflow-remaining"
    description := "A total minus the evicted amounts that does not fit in an i128 is refused with overflow; the record is not one the check builds."
    params := ⟨100, 10⟩
    start := ⟨[⟨1, 1⟩], i128Min⟩
    calls := [call 30 1] },
  { name := "cap-eviction-stops-at-first-kept"
    description := "Eviction walks from the front and stops at the first entry after the cutoff; the record is not one the check builds."
    params := ⟨100, 10⟩
    start := ⟨[⟨15, 10⟩, ⟨5, 10⟩, ⟨16, 10⟩], 30⟩
    calls := [call 20 1, call 26 1] },
  { name := "cap-invalid-limit"
    description := "A cap with limit 0 is not valid to install; under it every positive spend is refused and a zero spend passes."
    params := ⟨0, 10⟩
    calls := [call 1 1, call 1 0, call 2 1] },
  { name := "cap-invalid-period"
    description := "A cap with period 0 is not valid to install; under it the cutoff is now and every spend is checked alone."
    params := ⟨10, 0⟩
    calls := [call 1 10, call 1 10, call 2 10, call 2 11] },
  { name := "cap-empty-run"
    description := "A trace with no calls."
    params := ⟨1, 1⟩
    calls := [] }
]

/-! ## Randomized traces -/

def limits : List Int := [0, 1, 5, 10, 100, i128Max]
def periods : List Nat := [0, 1, 2, 3, 10, u32Max]
def starts : List Nat := [0, 0, 1, 2, 5, 100, u32Max - 3]

def amount (limit : Int) : Gen Int := do
  pick [-1, 0, 1, 1, 2, 3, limit / 2, limit / 2, limit, min (limit + 1) i128Max, i128Max, i128Min]

/-- The next ledger: usually a step forward of less than about a period,
sometimes the same ledger, sometimes back, never past `u32::MAX`. -/
def step (period now : Nat) : Gen Nat := do
  let r ← below 10
  if r < 2 then return now
  if r < 3 then return now - (← below 3)
  let d ← below (min period 20 + 3)
  return min (now + d) u32Max

def calls (limit : Int) (period : Nat) : Nat → Nat → Gen (List Call)
  | 0, _ => return []
  | n + 1, now => do
    let now' ← step period now
    let a ← amount limit
    let rest ← calls limit period n now'
    return ⟨now', a⟩ :: rest

def trace (seed : UInt64) (k : Nat) : Trace :=
  let g : Gen Trace := do
    let limit ← pick limits
    let period ← pick periods
    let start ← pick starts
    let n ← below 12
    let cs ← calls limit period (n + 1) start
    return {
      name := s!"cap-random-{if k < 10 then "0" else ""}{k}"
      description := s!"Randomized trace {k} of seed {seed}."
      params := ⟨limit, period⟩
      calls := cs }
  (g.run ⟨seed + UInt64.ofNat k⟩).1

def traces (seed : UInt64) (count : Nat) : List Trace :=
  named ++ (List.range count).map (trace seed)

end Conformance.Caps
