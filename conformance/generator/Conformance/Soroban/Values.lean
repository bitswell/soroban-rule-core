import Conformance.Soroban.Encode

/-!
# Value and context vectors

A value vector lists values, each with its `ScVal` XDR (`Val.xdr`), its
reading by `rule-eval` (`Val.toChain`) and whether it may be a storage key
(`Val.storable`). The values cover every constructor, the integer extremes,
byte strings of every padding length, the three kinds of address, nested
vectors and maps, and `other` values of every other fixed-size kind.

A context vector is one value as `__check_auth` would receive it, with what
the model reads of it (`contextsOfVal`): every context and its reading by
`rule-eval`, or nothing when one context cannot be read.
-/

namespace Conformance.Soroban.Values

open RuleCore RuleCore.Soroban

/-- The version of the value and context vector formats in
`conformance/README.md`. -/
def formatVersion : Nat := 1

structure ValueVector where
  name : String
  description : String
  values : List Val

structure ContextVector where
  name : String
  description : String
  value : Val

def ValueVector.toJson (v : ValueVector) : Json :=
  .obj [
    ("format", .num formatVersion),
    ("name", .str v.name),
    ("description", .str v.description),
    ("values", .arr (v.values.map fun x => .obj [
      ("value", encodeValue x),
      ("xdr", .str (hex x.xdr)),
      ("rule_eval", encodeVal x.toChain),
      ("storable", .bool x.storable)]))]

def ContextVector.toJson (v : ContextVector) : Json :=
  .obj [
    ("format", .num formatVersion),
    ("name", .str v.name),
    ("description", .str v.description),
    ("value", encodeValue v.value),
    ("xdr", .str (hex v.value.xdr)),
    ("expected", match contextsOfVal v.value with
      | some cs => .obj [
          ("contexts", .arr (cs.map encodeAuthFn)),
          ("rule_eval", .arr (cs.map (encodeContext ∘ AuthFn.toChain)))]
      | none => .null)]

/-! ## Universes -/

def b (s : String) : Bytes := Bytes.ofString s

/-- A 32-byte id ending in `n`. -/
def id32 (n : Nat) : Bytes := List.replicate 31 0 ++ [UInt8.ofNat n]

def key32 (n : Nat) : Bytes := List.replicate 32 (UInt8.ofNat n)

def contract (n : Nat) : Address := .contract (id32 n)
def account (n : Nat) : Address := .account (key32 n)

def i128 (n : Int) : Val := .i128 (BitVec.ofInt 128 n)

def i128Min : Int := -(2 ^ 127)
def i128Max : Int := 2 ^ 127 - 1

/-- `n` as `k` big-endian bytes. -/
def beBytes (k n : Nat) : Bytes :=
  (List.range k).reverse.map fun i => UInt8.ofNat (n / 256 ^ i % 256)

/-- An `other` value: a discriminant and a fixed-size payload. -/
def otherOf (disc : Nat) (payload : Bytes) : Val :=
  .other (be32 disc ++ payload)

/-! ## Value vectors -/

def scalars : ValueVector where
  name := "values-scalars"
  description := "void, both booleans, and u32, u64 and i128 at their extremes and in between."
  values := [
    .void, .bool false, .bool true,
    .u32 0, .u32 1, .u32 7, .u32 4294967295,
    .u64 0, .u64 1, .u64 18446744073709551615,
    i128 0, i128 1, i128 (-1), i128 100, i128 (-100), i128 i128Min, i128 i128Max,
    i128 (2 ^ 64), i128 (-(2 ^ 64))]

def byteStrings : ValueVector where
  name := "values-byte-strings"
  description :=
    "Bytes, strings and symbols of every padding length; a string and a symbol with the same " ++
    "bytes are different values."
  values := [
    .bytes [], .bytes [0], .bytes [1, 2], .bytes [1, 2, 3], .bytes [1, 2, 3, 4], .bytes [0xff],
    .bytes (id32 7),
    .string [], .string (b "a"), .string (b "ab"), .string (b "abc"), .string (b "abcd"),
    .string (b "transfer"),
    .symbol (b "a"), .symbol (b "ab"), .symbol (b "abc"), .symbol (b "abcd"),
    .symbol (b "transfer"), .symbol (b "apply_doc"),
    .symbol (b "a_symbol_of_thirty_two_letters_x")]

def addresses : ValueVector where
  name := "values-addresses"
  description :=
    "Accounts, contracts and muxed accounts; a muxed account is never a storage key, alone or " ++
    "inside a vector or a map."
  values := [
    .address (account 1), .address (account 0xff), .address (contract 1), .address (contract 0xa1),
    .address (.muxedAccount 0 (key32 1)), .address (.muxedAccount 18446744073709551615 (key32 2)),
    .vec [.address (contract 1), .address (.muxedAccount 7 (key32 1))],
    .map [(.u32 1, .address (.muxedAccount 7 (key32 1)))]]

def containers : ValueVector where
  name := "values-containers"
  description := "Empty and nested vectors and maps, with map keys in the host's order."
  values := [
    .vec [], .vec [.u32 1], .vec [.u32 1, .bool true, .symbol (b "x")],
    .vec [.vec [], .vec [.vec [.void]]],
    .map [], .map [(.u32 1, .u32 2)], .map [(.u32 1, .vec []), (.u32 2, .map [(.u32 3, .void)])],
    .vec [i128 (-1), .address (contract 2), .string (b "s"), .bytes [9]]]

def otherKinds : ValueVector where
  name := "values-other-kinds"
  description :=
    "Values of the kinds the facade does not model, each as its XDR: i32, i64, a time point, a " ++
    "duration, u128, u256, i256 and a contract error."
  values := [
    otherOf 4 (beBytes 4 7), otherOf 4 (beBytes 4 4294967295),
    otherOf 6 (beBytes 8 7), otherOf 7 (beBytes 8 1700000000), otherOf 8 (beBytes 8 60),
    otherOf 9 (beBytes 16 5), otherOf 11 (beBytes 32 5), otherOf 12 (beBytes 32 5),
    otherOf 2 (be32 0 ++ be32 3),
    .vec [otherOf 6 (beBytes 8 1), .u32 1]]

def valueVectors : List ValueVector := [scalars, byteStrings, addresses, containers, otherKinds]

/-! ## Context vectors -/

def callCtx (c : Address) (f : String) (args : List Val) : AuthFn :=
  .contract c (b f) args

def ctxs (fs : List AuthFn) : Val :=
  .vec (fs.map AuthFn.toVal)

def wasmHashOf (n : Nat) : Bytes := key32 n

def contextVectors : List ContextVector := [
  { name := "contexts-one-call"
    description := "One call, the shape a token transfer's authorization has."
    value := ctxs [callCtx (contract 1) "transfer" [.address (account 1), .address (account 2), i128 10]] },
  { name := "contexts-tree-in-preorder"
    description := "Three calls, each with arguments of a different kind."
    value := ctxs [
      callCtx (contract 2) "pay_nested" [.address (contract 0xa1), .u32 7],
      callCtx (contract 3) "pay" [.vec [.u32 1], .map [(.u32 1, .bool true)]],
      callCtx (contract 3) "run" []] },
  { name := "contexts-create"
    description := "Creations with and without constructor arguments; rule-eval reads them as creations."
    value := ctxs [
      .create (.wasm (wasmHashOf 1)) (key32 2) [],
      .create (.wasm (wasmHashOf 3)) (key32 4) [.u32 1, .symbol (b "init")]] },
  { name := "contexts-create-external-ref"
    description :=
      "Creations from an external reference (CAP-85), with and without constructor arguments; rule-eval reads them as creations of the reference's XDR."
    value := ctxs [
      .create (.externalRef (contract 7) (b "v1")) (key32 2) [],
      .create (.externalRef (contract 8) (b "release")) (key32 4) [.u32 1]] },
  { name := "contexts-other-arguments"
    description := "Arguments of kinds the facade carries as their XDR."
    value := ctxs [callCtx (contract 1) "f" [otherOf 6 (beBytes 8 1), otherOf 4 (beBytes 4 2)]] },
  { name := "contexts-empty"
    description := "No contexts; a host authorization tree never gives this, and rule-eval allows it."
    value := .vec [] },
  { name := "contexts-unknown-variant"
    description :=
      "A creation of a Stellar asset contract, an executable SDK 29's contexts do not have: the whole batch cannot be read."
    value := .vec [
      AuthFn.toVal (callCtx (contract 1) "f" []),
      .vec [sym "CreateContractHostFn",
        .map [(sym "executable", .vec [sym "StellarAsset"]),
          (sym "salt", .bytes (key32 2))]]] },
  { name := "contexts-external-ref-as-hash"
    description := "An external reference carrying a hash instead of an owner and a tag."
    value := .vec [.vec [sym "CreateContractHostFn",
      .map [(sym "executable", .vec [sym "ExternalRef", .bytes (key32 1)]),
        (sym "salt", .bytes (key32 2))]]] },
  { name := "contexts-unknown-name"
    description := "A context with a variant name SDK 29 does not have."
    value := .vec [.vec [sym "Invoke",
      .map [(sym "args", .vec []), (sym "contract", .address (contract 1)),
        (sym "fn_name", .symbol (b "f"))]]] },
  { name := "contexts-missing-field"
    description := "A call without its arguments."
    value := .vec [.vec [sym "Contract",
      .map [(sym "contract", .address (contract 1)), (sym "fn_name", .symbol (b "f"))]]] },
  { name := "contexts-fields-out-of-order"
    description := "A call whose fields are not in the order of their names."
    value := .vec [.vec [sym "Contract",
      .map [(sym "contract", .address (contract 1)), (sym "args", .vec []),
        (sym "fn_name", .symbol (b "f"))]]] },
  { name := "contexts-short-hash"
    description := "A creation whose Wasm hash has 31 bytes."
    value := .vec [.vec [sym "CreateContractHostFn",
      .map [(sym "executable", .vec [sym "Wasm", .bytes (List.replicate 31 1)]),
        (sym "salt", .bytes (key32 2))]]] },
  { name := "contexts-function-as-string"
    description := "A call whose function name is a string, not a symbol."
    value := .vec [.vec [sym "Contract",
      .map [(sym "args", .vec []), (sym "contract", .address (contract 1)),
        (sym "fn_name", .string (b "f"))]]] },
  { name := "contexts-not-a-vector"
    description := "One context given alone, not in a vector."
    value := AuthFn.toVal (callCtx (contract 1) "f" []) }]

end Conformance.Soroban.Values
