import Conformance.Random
import Conformance.Soroban.Values

/-!
# Storage traces

A storage trace is a contract and a list of operations on its storage, each
with what the model's `Op.apply` returns for it on the store the operations
before it left: what `get` read, what `has` found, `set` and `remove` done, or
refused when the key holds a muxed address (which changes nothing).

The named traces cover each operation, the three durabilities keeping the
same key apart, overwriting, removing an absent key, keys of every kind and
muxed addresses in persistent and temporary keys. The randomized traces draw
operations over three durabilities and a small universe of keys and values.
-/

namespace Conformance.Soroban.Storage

open RuleCore RuleCore.Soroban
open Conformance.Soroban.Values
open Conformance.Random (Gen below pick listOf pad)

/-- The version of the storage trace format in `conformance/README.md`. -/
def formatVersion : Nat := 1

/-- The number of committed randomized traces, of the vectors' seed. -/
def defaultCount : Nat := 30

structure Trace where
  name : String
  description : String
  contract : Address
  ops : List Op

def encodeOp : Op → List (String × Json)
  | .get d k => [("op", .str "get")] ++ encodeSlot d k
  | .has d k => [("op", .str "has")] ++ encodeSlot d k
  | .set d k v => [("op", .str "set")] ++ encodeSlot d k ++ [("val", encodeValue v)]
  | .remove d k => [("op", .str "remove")] ++ encodeSlot d k

def encodeObs : Obs → Json
  | .value v => tagged "value" (encodeOption encodeValue v)
  | .present p => tagged "present" (.bool p)
  | .done => .str "done"

def opsJson (c : Address) : Store → List Op → List Json
  | _, [] => []
  | s, op :: ops =>
    let entry (expected : Json) : Json := .obj (encodeOp op ++ [("expected", expected)])
    match op.apply c s with
    | some (obs, s') => entry (encodeObs obs) :: opsJson c s' ops
    | none => entry (.str "refused") :: opsJson c s ops

def Trace.toJson (t : Trace) : Json :=
  .obj [
    ("format", .num formatVersion),
    ("name", .str t.name),
    ("description", .str t.description),
    ("contract", encodeAddress t.contract),
    ("ops", .arr (opsJson t.contract [] t.ops))]

/-- Whether every key and value can be written on the host: muxed keys only
in persistent or temporary storage (instance storage refuses them later, at
the end of the call, which the model leaves out). -/
def Trace.inDomain (t : Trace) : Bool :=
  t.ops.all fun op => op.key.storable || op.durability != .contractInstance

/-! ## Named traces -/

def k (s : String) : Val := .symbol (b s)
def muxed : Val := .address (.muxedAccount 7 (key32 1))

def named : List Trace := [
  { name := "storage-set-get-remove"
    description := "A value is read back, overwritten, removed, and removing it again changes nothing."
    contract := contract 0x10
    ops := [
      .get .persistent (k "a"), .has .persistent (k "a"),
      .set .persistent (k "a") (.u32 1), .get .persistent (k "a"), .has .persistent (k "a"),
      .set .persistent (k "a") (.u32 2), .get .persistent (k "a"),
      .remove .persistent (k "a"), .get .persistent (k "a"), .has .persistent (k "a"),
      .remove .persistent (k "a"), .get .persistent (k "a")] },
  { name := "storage-durabilities-apart"
    description := "The same key in persistent, temporary and instance storage is three slots."
    contract := contract 0x10
    ops := [
      .set .persistent (k "a") (.u32 1), .set .temporary (k "a") (.u32 2),
      .set .contractInstance (k "a") (.u32 3),
      .get .persistent (k "a"), .get .temporary (k "a"), .get .contractInstance (k "a"),
      .remove .temporary (k "a"),
      .get .persistent (k "a"), .get .temporary (k "a"), .get .contractInstance (k "a"),
      .has .temporary (k "a"), .has .contractInstance (k "a")] },
  { name := "storage-key-kinds"
    description := "Keys of every kind, each its own slot; a string and a symbol of the same bytes differ."
    contract := contract 0x11
    ops := [
      .set .persistent (.string (b "a")) (.u32 1), .set .persistent (.symbol (b "a")) (.u32 2),
      .set .persistent (.bytes (b "a")) (.u32 3), .set .persistent (.u32 1) (.u32 4),
      .set .persistent (.u64 1) (.u32 5), .set .persistent (i128 1) (.u32 6),
      .set .persistent .void (.u32 7), .set .persistent (.bool true) (.u32 8),
      .set .persistent (.address (contract 1)) (.u32 9),
      .set .persistent (.address (account 1)) (.u32 10),
      .set .persistent (.vec [.u32 1, k "x"]) (.u32 11),
      .set .persistent (.map [(.u32 1, .u32 2)]) (.u32 12),
      .get .persistent (.string (b "a")), .get .persistent (.symbol (b "a")),
      .get .persistent (.bytes (b "a")), .get .persistent (.u32 1), .get .persistent (.u64 1),
      .get .persistent (i128 1), .get .persistent .void, .get .persistent (.bool true),
      .get .persistent (.bool false),
      .get .persistent (.address (contract 1)), .get .persistent (.address (account 1)),
      .get .persistent (.vec [.u32 1, k "x"]), .get .persistent (.vec [k "x", .u32 1]),
      .get .persistent (.map [(.u32 1, .u32 2)])] },
  { name := "storage-values-of-every-kind"
    description := "Values of every kind are stored and read back unchanged."
    contract := contract 0x12
    ops :=
      (scalars.values.zipIdx.flatMap fun (v, i) =>
        [.set .temporary (.u32 (UInt32.ofNat i)) v, .get .temporary (.u32 (UInt32.ofNat i))]) ++
      ((addresses.values ++ containers.values ++ otherKinds.values).zipIdx.flatMap fun (v, i) =>
        [.set .persistent (.u32 (UInt32.ofNat i)) v, .get .persistent (.u32 (UInt32.ofNat i))]) },
  { name := "storage-muxed-keys-refused"
    description :=
      "A key holding a muxed address, alone or nested, is refused in persistent and temporary " ++
      "storage and changes nothing; a muxed address is a value like any other."
    contract := contract 0x13
    ops := [
      .set .persistent muxed (.u32 1), .get .persistent muxed, .has .temporary muxed,
      .remove .temporary muxed, .set .temporary (.vec [muxed]) (.u32 1),
      .set .persistent (.map [(.u32 1, muxed)]) (.u32 1),
      .set .persistent (k "m") muxed, .get .persistent (k "m"),
      .set .persistent (.address (account 1)) (.u32 1), .get .persistent (.address (account 1))] }]

/-! ## Randomized traces -/

def keys : List Val := [k "a", k "b", .u32 1, .string (b "a"), .address (contract 1), muxed]
def vals : List Val := [.u32 0, .u32 1, i128 (-1), .bool true, .symbol (b "v"), .vec [.u32 2], muxed]
def durabilities : List Durability := [.persistent, .temporary, .contractInstance]

instance : Inhabited Val := ⟨.void⟩
instance : Inhabited Durability := ⟨.persistent⟩

def op : Gen Op := do
  let d ← pick durabilities
  let key ← pick keys
  -- Instance storage refuses a muxed key only at the end of the call.
  let key := if d == .contractInstance && !key.storable then k "a" else key
  match ← below 6 with
  | 0 | 1 => return .set d key (← pick vals)
  | 2 => return .remove d key
  | 3 => return .has d key
  | _ => return .get d key

def trace (seed : UInt64) (n : Nat) : Trace :=
  let g : Gen Trace := do
    let ops ← listOf ((← below 25) + 5) op
    return {
      name := s!"storage-random-{pad 3 n}"
      description := s!"Randomized storage trace {n} of seed {seed}."
      contract := contract 0x20
      ops }
  (g.run ⟨seed + UInt64.ofNat n⟩).1

def traces (seed : UInt64) (count : Nat) : List Trace :=
  named ++ (List.range count).map (trace seed)

end Conformance.Soroban.Storage
