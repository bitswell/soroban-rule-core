/-!
# Spending caps

A cap bounds what one rule may spend within a rolling window of ledgers: at
most `limit` within `period` consecutive ledgers. The rule keeps a `Record`:
the spends still inside the window, in the order they were made, and their
total. `Params.check` takes the record, the current ledger `now` and the amount
of a new spend, and returns the record after the spend or a `CapError`.

The check mirrors `enforce` and `cleanup_old_entries` of the spending-limit
policy in OpenZeppelin's `stellar-accounts`, at the revision Perch pins:

1. a negative amount is refused (`negativeAmount`);
2. a zero amount passes and changes nothing;
3. the entries at the front of the history whose ledger is at most
   `now - period` are evicted, and their amounts taken off the total;
4. the spend is refused if the remaining total plus the amount exceeds the
   limit (`limitExceeded`);
5. the spend is refused if the remaining history already holds `maxHistory`
   entries (`historyFull`);
6. otherwise the entry `(now, amount)` is appended and the total increased.

Two refusals are added. Between steps 2 and 3, a spend is refused when `now`
is earlier than the ledger of the newest recorded entry
(`ledgerBeforeNewest`), so nothing about the ledger clock is assumed. Every sum
is computed as Rust's checked `i128` arithmetic computes it, and one that does
not fit in an `i128` is refused (`overflow`).

Ledgers are natural numbers, and `now - period` is truncated subtraction:
Rust's `u32::saturating_sub`. Amounts are integers, and `addI128` and
`subI128` are `i128::checked_add` and `i128::checked_sub`.

A run is a list of calls, each a ledger and an amount, applied in order.
`Params.run` keeps the record unchanged on a refused call; `Params.runAll` fails
with the first refusal, so `Params.Accepts` says a run is accepted call by
call. `Params.recorded` lists the spends a run records. `capAccepts` and
`capNarrower` extend acceptance and narrowing to a rule that may have no cap.
The theorems in `RuleCore.Theorems.Cap` are stated over these.
-/

namespace RuleCore.Cap

/-- The least `i128`. -/
def i128Min : Int := -2 ^ 127

/-- The greatest `i128`. -/
def i128Max : Int := 2 ^ 127 - 1

/-- `a + b` when it fits in an `i128`: Rust's `i128::checked_add`. -/
def addI128 (a b : Int) : Option Int :=
  if i128Min ≤ a + b ∧ a + b ≤ i128Max then some (a + b) else none

/-- `a - b` when it fits in an `i128`: Rust's `i128::checked_sub`. -/
def subI128 (a b : Int) : Option Int :=
  if i128Min ≤ a - b ∧ a - b ≤ i128Max then some (a - b) else none

/-- The most entries a record holds: a spend is refused when the history left
after eviction already holds this many. -/
def maxHistory : Nat := 1000

/-- One recorded spend: the ledger it was made in and its amount. -/
structure Entry where
  ledger : Nat
  amount : Int
  deriving DecidableEq, Repr

/-- What a capped rule has spent: its recorded spends in the order they were
made, and their total. -/
structure Record where
  history : List Entry
  total : Int
  deriving DecidableEq, Repr

/-- The record of a cap with no spends. -/
def Record.empty : Record := ⟨[], 0⟩

/-- A cap: at most `limit` spent within `period` consecutive ledgers. -/
structure Params where
  limit : Int
  period : Nat
  deriving DecidableEq, Repr

/-- Why a spend was refused. -/
inductive CapError where
  /-- The amount is negative. -/
  | negativeAmount
  /-- The current ledger is earlier than the ledger of the newest recorded
  spend. -/
  | ledgerBeforeNewest
  /-- A sum of amounts does not fit in an `i128`. -/
  | overflow
  /-- The spend would take the total within the window above the limit. -/
  | limitExceeded
  /-- The history left after eviction already holds `maxHistory` entries. -/
  | historyFull
  deriving DecidableEq, Repr

/-- Whether a cap may be installed: a positive limit and a nonzero period. -/
def Params.valid (p : Params) : Bool :=
  decide (0 < p.limit) && decide (0 < p.period)

/-- Whether `now` is earlier than the ledger of the last entry of `h`. -/
def beforeNewest (h : List Entry) (now : Nat) : Bool :=
  match h.getLast? with
  | some e => decide (now < e.ledger)
  | none => false

/-- Eviction at `cutoff`: the entries of `h` from the first one whose ledger is
after `cutoff` on, and `removed` plus the amounts of the entries before it,
summed one entry at a time with `addI128`. -/
def evict (cutoff : Nat) : List Entry → Int → Except CapError (List Entry × Int)
  | [], removed => .ok ([], removed)
  | e :: h, removed =>
    if cutoff < e.ledger then .ok (e :: h, removed)
    else
      match addI128 removed e.amount with
      | some removed' => evict cutoff h removed'
      | none => .error .overflow

/-- The record after a spend of `amount` at ledger `now`, or why the spend is
refused. -/
def Params.check (p : Params) (r : Record) (now : Nat) (amount : Int) :
    Except CapError Record :=
  if amount < 0 then .error .negativeAmount
  else if amount = 0 then .ok r
  else if beforeNewest r.history now then .error .ledgerBeforeNewest
  else
    match evict (now - p.period) r.history 0 with
    | .error e => .error e
    | .ok (kept, removed) =>
      match subI128 r.total removed with
      | none => .error .overflow
      | some remaining =>
        match addI128 remaining amount with
        | none => .error .overflow
        | some total =>
          if p.limit < total then .error .limitExceeded
          else if maxHistory ≤ kept.length then .error .historyFull
          else .ok { history := kept ++ [⟨now, amount⟩], total }

/-! ## Runs -/

/-- A call of a run: a spend of `amount` at ledger `now`. -/
structure Call where
  now : Nat
  amount : Int
  deriving DecidableEq, Repr

/-- The record after one call: the checked record, or the same record when
the check refuses. -/
def Params.step (p : Params) (r : Record) (k : Call) : Record :=
  match p.check r k.now k.amount with
  | .ok r' => r'
  | .error _ => r

/-- The record after every call of `calls`, each refused call leaving the
record as it was. -/
def Params.run (p : Params) (r : Record) (calls : List Call) : Record :=
  calls.foldl p.step r

/-- The spends a run records, in order: each call the check accepts with a
positive amount, as an entry. -/
def Params.recorded (p : Params) : Record → List Call → List Entry
  | _, [] => []
  | r, k :: ks =>
    match p.check r k.now k.amount with
    | .ok r' => (if 0 < k.amount then [⟨k.now, k.amount⟩] else []) ++ p.recorded r' ks
    | .error _ => p.recorded r ks

/-- Apply every call in order, failing with the first refusal. -/
def Params.runAll (p : Params) (r : Record) (calls : List Call) : Except CapError Record :=
  calls.foldlM (fun r k => p.check r k.now k.amount) r

/-- `p` accepts every call of `calls`, starting from `r`. -/
def Params.Accepts (p : Params) (r : Record) (calls : List Call) : Prop :=
  ∃ r', p.runAll r calls = .ok r'

/-- `q` is narrower than `p`: its limit is at most `p`'s and its period at
least `p`'s. -/
def Params.narrower (q p : Params) : Prop :=
  q.limit ≤ p.limit ∧ p.period ≤ q.period

/-- A rule's cap, if it has one, accepts every call of `calls` from `r`. A rule
without a cap checks no spend and accepts every run. -/
def capAccepts : Option Params → Record → List Call → Prop
  | none, _, _ => True
  | some p, r, calls => p.Accepts r calls

/-- Narrower on a rule's cap: any cap is narrower than none, and one cap is
narrower than another as `Params.narrower` says. Adding a cap and lowering one
are both steps to a narrower cap. -/
def capNarrower : Option Params → Option Params → Prop
  | _, none => True
  | none, some _ => False
  | some q, some p => q.narrower p

/-! ## Windows -/

/-- The total of the amounts of `es`. -/
def amountSum (es : List Entry) : Int :=
  (es.map (·.amount)).sum

/-- Entry `e` is in the window that eviction leaves at ledger `t`: its ledger
is after `t - period` and not after `t`. -/
def Params.inWindow (p : Params) (t : Nat) (e : Entry) : Bool :=
  decide (t - p.period < e.ledger) && decide (e.ledger ≤ t)

/-- Entry `e` is in the `period` consecutive ledgers starting at ledger `s`. -/
def Params.inPeriodFrom (p : Params) (s : Nat) (e : Entry) : Bool :=
  decide (s ≤ e.ledger) && decide (e.ledger < s + p.period)

/-- A record the check can have built: its history is in ledger order, its
amounts are positive, and its total is their sum and fits in an `i128`. -/
structure Record.Valid (r : Record) : Prop where
  sorted : r.history.Pairwise (fun a b => a.ledger ≤ b.ledger)
  pos : ∀ e ∈ r.history, 0 < e.amount
  total_eq : r.total = amountSum r.history
  total_le : r.total ≤ i128Max

end RuleCore.Cap
