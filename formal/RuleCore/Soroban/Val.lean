import RuleCore.Vocab.Document

/-!
# Soroban values

The values a contract passes to the host and receives from it, as plain data:
the subset of Soroban's `ScVal` that `crates/soroban-facade` models
(protocol 29, `soroban-env-host` 29.0.1), and their XDR.

An address is a Stellar account (its ed25519 key), a contract (its id) or a
muxed account (an account key with a 64-bit id). A value is `void`, a `bool`,
a `u32`, a `u64`, an `i128`, bytes, a string, a symbol, an address, a vector,
a map, or `other`, which carries the full XDR of a value of any other type
(`i32`, `i64`, `u128`, `u256`, `i256`, a time point, a duration or an error).
Claimable balance and liquidity pool addresses (CAP-67) are no values a
contract holds: the host refuses them. An executable tag (CAP-85, protocol
28) is no value the facade models: it holds none and refuses one. A map's entries are in the host's key
order; a vector's are in order.

`Val.xdr` is the value's `ScVal` XDR and `Address.xdr` the address's
`ScAddress` XDR, as `stellar-xdr` 28.0.0 writes them: a four-byte big-endian
discriminant, then the payload; byte strings as a four-byte length, the bytes
and zero padding to a multiple of four; vectors and maps present, then their
length and their elements. `other` is its own XDR. The `u32` encoding is
`RuleCore.Document.u32Xdr`, the encoding Perch's lowering compares a `u32`
argument with.

A storage key may hold no muxed address anywhere in it (`Val.storable`): the
host refuses such a key (CAP-67).
-/

namespace RuleCore.Soroban

open RuleCore

inductive Address where
  /-- A Stellar account, by its ed25519 public key. -/
  | account (key : Bytes)
  /-- A contract, by its id. -/
  | contract (id : Bytes)
  /-- A muxed account: an account key and a 64-bit id. -/
  | muxedAccount (id : UInt64) (key : Bytes)
  deriving DecidableEq, Repr

inductive Val where
  | void
  | bool (b : Bool)
  | u32 (v : UInt32)
  | u64 (v : UInt64)
  | i128 (v : BitVec 128)
  | bytes (b : Bytes)
  | string (b : Bytes)
  | symbol (b : Bytes)
  | address (a : Address)
  | vec (items : List Val)
  | map (entries : List (Val × Val))
  /-- A value of a type the other constructors do not model, as its full XDR. -/
  | other (xdr : Bytes)
  deriving Repr

/-! ## Equality

Lean derives no `DecidableEq` for a nested inductive type, so it is written
out: two values are equal when they have the same constructor and equal
payloads. -/

mutual

def Val.decEq : (a b : Val) → Decidable (a = b)
  | .void, .void => isTrue rfl
  | .bool x, .bool y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Val.bool.inj e))
  | .u32 x, .u32 y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Val.u32.inj e))
  | .u64 x, .u64 y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Val.u64.inj e))
  | .i128 x, .i128 y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Val.i128.inj e))
  | .bytes x, .bytes y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Val.bytes.inj e))
  | .string x, .string y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Val.string.inj e))
  | .symbol x, .symbol y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Val.symbol.inj e))
  | .address x, .address y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Val.address.inj e))
  | .vec xs, .vec ys =>
    match Val.decEqList xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => h (Val.vec.inj e))
  | .map xs, .map ys =>
    match Val.decEqEntries xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => h (Val.map.inj e))
  | .other x, .other y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Val.other.inj e))
  | .void, .bool _ | .void, .u32 _ | .void, .u64 _ | .void, .i128 _ | .void, .bytes _
  | .void, .string _ | .void, .symbol _ | .void, .address _ | .void, .vec _ | .void, .map _
  | .void, .other _ | .bool _, .void | .bool _, .u32 _ | .bool _, .u64 _ | .bool _, .i128 _
  | .bool _, .bytes _ | .bool _, .string _ | .bool _, .symbol _ | .bool _, .address _
  | .bool _, .vec _ | .bool _, .map _ | .bool _, .other _ | .u32 _, .void | .u32 _, .bool _
  | .u32 _, .u64 _ | .u32 _, .i128 _ | .u32 _, .bytes _ | .u32 _, .string _ | .u32 _, .symbol _
  | .u32 _, .address _ | .u32 _, .vec _ | .u32 _, .map _ | .u32 _, .other _ | .u64 _, .void
  | .u64 _, .bool _ | .u64 _, .u32 _ | .u64 _, .i128 _ | .u64 _, .bytes _ | .u64 _, .string _
  | .u64 _, .symbol _ | .u64 _, .address _ | .u64 _, .vec _ | .u64 _, .map _ | .u64 _, .other _
  | .i128 _, .void | .i128 _, .bool _ | .i128 _, .u32 _ | .i128 _, .u64 _ | .i128 _, .bytes _
  | .i128 _, .string _ | .i128 _, .symbol _ | .i128 _, .address _ | .i128 _, .vec _
  | .i128 _, .map _ | .i128 _, .other _ | .bytes _, .void | .bytes _, .bool _ | .bytes _, .u32 _
  | .bytes _, .u64 _ | .bytes _, .i128 _ | .bytes _, .string _ | .bytes _, .symbol _
  | .bytes _, .address _ | .bytes _, .vec _ | .bytes _, .map _ | .bytes _, .other _
  | .string _, .void | .string _, .bool _ | .string _, .u32 _ | .string _, .u64 _
  | .string _, .i128 _ | .string _, .bytes _ | .string _, .symbol _ | .string _, .address _
  | .string _, .vec _ | .string _, .map _ | .string _, .other _ | .symbol _, .void
  | .symbol _, .bool _ | .symbol _, .u32 _ | .symbol _, .u64 _ | .symbol _, .i128 _
  | .symbol _, .bytes _ | .symbol _, .string _ | .symbol _, .address _ | .symbol _, .vec _
  | .symbol _, .map _ | .symbol _, .other _ | .address _, .void | .address _, .bool _
  | .address _, .u32 _ | .address _, .u64 _ | .address _, .i128 _ | .address _, .bytes _
  | .address _, .string _ | .address _, .symbol _ | .address _, .vec _ | .address _, .map _
  | .address _, .other _ | .vec _, .void | .vec _, .bool _ | .vec _, .u32 _ | .vec _, .u64 _
  | .vec _, .i128 _ | .vec _, .bytes _ | .vec _, .string _ | .vec _, .symbol _
  | .vec _, .address _ | .vec _, .map _ | .vec _, .other _ | .map _, .void | .map _, .bool _
  | .map _, .u32 _ | .map _, .u64 _ | .map _, .i128 _ | .map _, .bytes _ | .map _, .string _
  | .map _, .symbol _ | .map _, .address _ | .map _, .vec _ | .map _, .other _ | .other _, .void
  | .other _, .bool _ | .other _, .u32 _ | .other _, .u64 _ | .other _, .i128 _
  | .other _, .bytes _ | .other _, .string _ | .other _, .symbol _ | .other _, .address _
  | .other _, .vec _ | .other _, .map _ => isFalse (fun e => by cases e)

def Val.decEqList : (a b : List Val) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (fun e => by cases e)
  | x :: xs, y :: ys =>
    match Val.decEq x y, Val.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => h1 (List.cons.inj e).1)
    | _, isFalse h2 => isFalse (fun e => h2 (List.cons.inj e).2)

def Val.decEqEntries : (a b : List (Val × Val)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (fun e => by cases e)
  | (k1, v1) :: xs, (k2, v2) :: ys =>
    match Val.decEq k1 k2, Val.decEq v1 v2, Val.decEqEntries xs ys with
    | isTrue h1, isTrue h2, isTrue h3 => isTrue (h1 ▸ h2 ▸ h3 ▸ rfl)
    | isFalse h1, _, _ => isFalse (fun e => h1 (Prod.mk.inj (List.cons.inj e).1).1)
    | _, isFalse h2, _ => isFalse (fun e => h2 (Prod.mk.inj (List.cons.inj e).1).2)
    | _, _, isFalse h3 => isFalse (fun e => h3 (List.cons.inj e).2)

end

instance : DecidableEq Val := Val.decEq

/-- Where a contract keeps a value. -/
inductive Durability where
  | persistent
  | temporary
  /-- The contract instance's own storage. -/
  | contractInstance
  deriving DecidableEq, Repr

/-! ## XDR -/

/-- `n` modulo `2^32`, as four big-endian bytes. -/
def be32 (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 256 % 256),
    UInt8.ofNat (n % 256)]

/-- `n` modulo `2^64`, as eight big-endian bytes. -/
def be64 (n : Nat) : Bytes :=
  be32 (n / 4294967296 % 4294967296) ++ be32 (n % 4294967296)

/-- A 128-bit integer as sixteen big-endian bytes, two's complement: XDR's
`Int128Parts`, the high half then the low half. -/
def be128 (v : BitVec 128) : Bytes :=
  be64 (v.toNat / 18446744073709551616) ++ be64 (v.toNat % 18446744073709551616)

/-- XDR's variable-length opaque data: the length, the bytes and zero padding
to a multiple of four. -/
def xdrOpaque (b : Bytes) : Bytes :=
  be32 b.length ++ b ++ List.replicate ((4 - b.length % 4) % 4) 0

/-- The address's `ScAddress` XDR. -/
def Address.xdr : Address → Bytes
  | .account key => be32 0 ++ be32 0 ++ key
  | .contract id => be32 1 ++ id
  | .muxedAccount id key => be32 2 ++ be64 id.toNat ++ key

/-- Whether the address is a muxed account. -/
def Address.muxed : Address → Bool
  | .muxedAccount _ _ => true
  | _ => false

mutual

/-- The value's `ScVal` XDR. -/
def Val.xdr : Val → Bytes
  | .bool b => be32 0 ++ be32 (if b then 1 else 0)
  | .void => be32 1
  | .u32 v => RuleCore.Document.u32Xdr v
  | .u64 v => be32 5 ++ be64 v.toNat
  | .i128 v => be32 10 ++ be128 v
  | .bytes b => be32 13 ++ xdrOpaque b
  | .string b => be32 14 ++ xdrOpaque b
  | .symbol b => be32 15 ++ xdrOpaque b
  | .vec items => be32 16 ++ be32 1 ++ be32 items.length ++ Val.xdrList items
  | .map entries => be32 17 ++ be32 1 ++ be32 entries.length ++ Val.xdrEntries entries
  | .address a => be32 18 ++ a.xdr
  | .other x => x

def Val.xdrList : List Val → Bytes
  | [] => []
  | v :: vs => v.xdr ++ Val.xdrList vs

def Val.xdrEntries : List (Val × Val) → Bytes
  | [] => []
  | (k, v) :: es => k.xdr ++ v.xdr ++ Val.xdrEntries es

end

/-! ## Storage keys -/

mutual

/-- Whether the value may be a storage key: no muxed address occurs in it. -/
def Val.storable : Val → Bool
  | .address a => !a.muxed
  | .vec items => Val.storableList items
  | .map entries => Val.storableEntries entries
  | _ => true

def Val.storableList : List Val → Bool
  | [] => true
  | v :: vs => v.storable && Val.storableList vs

def Val.storableEntries : List (Val × Val) → Bool
  | [] => true
  | (k, v) :: es => k.storable && v.storable && Val.storableEntries es

end

end RuleCore.Soroban
