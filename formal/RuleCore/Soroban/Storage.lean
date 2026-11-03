import RuleCore.Soroban.Val

/-!
# Storage as a map

Contract storage is a finite map from slots to values. A slot is a contract,
a durability and a key, so each contract has its own storage, and the same key
under two durabilities is two slots. `Store.set` replaces the slot's value,
`Store.remove` deletes it, and `Store.get` and `Store.has` read it. Each slot
appears at most once (`Store.set` and `Store.remove` drop every earlier entry
for the slot), and `get` reads the first entry for the slot.

`Op.apply` is an operation a contract makes on its own storage, as
`soroban-env-host` 27.0.1 performs it: `get` returns the value or nothing,
`has` whether there is one, `set` and `remove` change the map (removing an
absent key changes nothing). A key holding a muxed address is refused
(`Val.storable`), and the call making the operation fails. The host refuses
such a key at once in persistent and temporary storage; in instance storage it
refuses it when it writes the instance back, at the end of the call, and the
model leaves that case out (the vectors never use such a key in instance
storage).

Time to live and archival are not modelled: every entry stays live.
-/

namespace RuleCore.Soroban

/-- Where a value is kept: the contract, the durability and the key. -/
structure Slot where
  contract : Address
  durability : Durability
  key : Val
  deriving DecidableEq, Repr

/-- Contract storage, a finite map from slots to values. -/
abbrev Store := List (Slot × Val)

def Store.get (s : Store) (k : Slot) : Option Val :=
  (s.find? fun e => decide (e.1 = k)).map (·.2)

def Store.has (s : Store) (k : Slot) : Bool :=
  (s.get k).isSome

def Store.set (s : Store) (k : Slot) (v : Val) : Store :=
  (k, v) :: s.filter fun e => decide (e.1 ≠ k)

def Store.remove (s : Store) (k : Slot) : Store :=
  s.filter fun e => decide (e.1 ≠ k)

/-- An operation a contract makes on its own storage. -/
inductive Op where
  | get (d : Durability) (key : Val)
  | has (d : Durability) (key : Val)
  | set (d : Durability) (key val : Val)
  | remove (d : Durability) (key : Val)
  deriving DecidableEq, Repr

def Op.durability : Op → Durability
  | .get d _ | .has d _ | .set d _ _ | .remove d _ => d

def Op.key : Op → Val
  | .get _ k | .has _ k | .set _ k _ | .remove _ k => k

/-- What an operation returns. -/
inductive Obs where
  /-- What `get` read. -/
  | value (v : Option Val)
  /-- What `has` found. -/
  | present (b : Bool)
  /-- `set` or `remove` done. -/
  | done
  deriving DecidableEq, Repr

/-- The operation made by `contract` on store `s`: what it returns and the
store after it, or `none` when its key holds a muxed address. -/
def Op.apply (contract : Address) (s : Store) (op : Op) : Option (Obs × Store) :=
  if op.key.storable then
    let k : Slot := ⟨contract, op.durability, op.key⟩
    match op with
    | .get _ _ => some (.value (s.get k), s)
    | .has _ _ => some (.present (s.has k), s)
    | .set _ _ v => some (.done, s.set k v)
    | .remove _ _ => some (.done, s.remove k)
  else none

end RuleCore.Soroban
