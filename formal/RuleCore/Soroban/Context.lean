import RuleCore.Soroban.Val

/-!
# Authorization contexts and their meaning for the evaluator

`AuthFn` is what a node of a signed authorization tree authorizes, and what
`__check_auth` receives as one context (SDK 27's `auth::Context`): a contract
call (the contract, the function, the arguments), or a contract creation from
uploaded Wasm (its hash, the salt and the constructor arguments, none for a
creation without a constructor call).

`AuthFn.toChain` is the context's meaning in the chain vocabulary that
`rule-eval` implements, a denotation of the same kind as `Equiv/Denote.lean`:

* a call is a chain call of the contract's `ScAddress` XDR, the function name
  and each argument's meaning;
* a creation is a chain creation of the Wasm hash, which no rule allows.

`Val.toChain` maps `i128`, `u64`, `bool`, bytes, strings and symbols to the
chain constructor of the same name, an address to `address` of its
`ScAddress` XDR, and every other value (`void`, `u32`, vectors, maps, `other`)
to `other` of its full `ScVal` XDR. So a `u32` argument is `other (u32Xdr v)`,
the reading Perch's lowering compares a `u32` with.

`crates/soroban-facade` implements this conversion (`to_rule_eval`). Decoding
the host's contexts into `AuthFn` values happens in the facade before it, and
a context the facade cannot decode makes it refuse the whole batch.
-/

namespace RuleCore.Soroban

open RuleCore

/-- What an authorization tree node authorizes: one context. -/
inductive AuthFn where
  /-- A call of `fn` on `contract` with `args`. -/
  | contract (contract : Address) (fn : Bytes) (args : List Val)
  /-- A creation from the Wasm with hash `wasmHash`, with `salt` and the
  constructor arguments `args`. -/
  | create (wasmHash : Bytes) (salt : Bytes) (args : List Val)
  deriving DecidableEq, Repr

/-! ## The form the host passes contexts in -/

def sym (s : String) : Val :=
  .symbol (Bytes.ofString s)

def isSym (v : Val) (s : String) : Bool :=
  decide (v = sym s)

/-- A context's `contracttype` encoding, the value the host passes it as: a
variant name and a map of its fields, in the order of their names. A creation
without constructor arguments is `CreateContractHostFn`, one with them
`CreateContractWithCtorHostFn`. -/
def AuthFn.toVal : AuthFn → Val
  | .contract c f args =>
    .vec [sym "Contract",
      .map [(sym "args", .vec args), (sym "contract", .address c), (sym "fn_name", .symbol f)]]
  | .create h s [] =>
    .vec [sym "CreateContractHostFn",
      .map [(sym "executable", .vec [sym "Wasm", .bytes h]), (sym "salt", .bytes s)]]
  | .create h s args =>
    .vec [sym "CreateContractWithCtorHostFn",
      .map [(sym "constructor_args", .vec args), (sym "executable", .vec [sym "Wasm", .bytes h]),
        (sym "salt", .bytes s)]]

/-- Bytes of length 32, as a `BytesN<32>` holds. -/
def bytes32 : Val → Option Bytes
  | .bytes b => if b.length = 32 then some b else none
  | _ => none

/-- The hash of a `ContractExecutable::Wasm`, the one executable SDK 27 has. -/
def wasmHash : Val → Option Bytes
  | .vec [n, h] => if isSym n "Wasm" then bytes32 h else none
  | _ => none

/-- Reads one context from the value the host passes, or nothing when the
value is not a context SDK 27 knows. -/
def AuthFn.ofVal : Val → Option AuthFn
  | .vec [n, .map [(k1, .vec args), (k2, .address c), (k3, .symbol f)]] =>
    if isSym n "Contract" && isSym k1 "args" && isSym k2 "contract" && isSym k3 "fn_name" then
      some (.contract c f args)
    else none
  | .vec [n, .map [(k1, e), (k2, s)]] =>
    if isSym n "CreateContractHostFn" && isSym k1 "executable" && isSym k2 "salt" then
      match wasmHash e, bytes32 s with
      | some h, some s => some (.create h s [])
      | _, _ => none
    else none
  | .vec [n, .map [(k1, .vec args), (k2, e), (k3, s)]] =>
    if isSym n "CreateContractWithCtorHostFn" && isSym k1 "constructor_args" &&
        isSym k2 "executable" && isSym k3 "salt" then
      match wasmHash e, bytes32 s with
      | some h, some s => some (.create h s args)
      | _, _ => none
    else none
  | _ => none

/-- Reads `__check_auth`'s contexts, given as one vector: every context, or
nothing when one of them cannot be read. -/
def contextsOfVal : Val → Option (List AuthFn)
  | .vec items => items.mapM AuthFn.ofVal
  | _ => none

/-! ## The evaluator's reading -/

/-- A value's meaning for the evaluator. -/
def Val.toChain : Val → Chain.Val
  | .i128 v => .i128 v
  | .u64 v => .u64 v
  | .bool b => .bool b
  | .bytes b => .bytes b
  | .string b => .string b
  | .symbol b => .symbol b
  | .address a => .address a.xdr
  | v => .other v.xdr

/-- A context's meaning for the evaluator. -/
def AuthFn.toChain : AuthFn → Chain.Context
  | .contract c f args => .call c.xdr f (args.map Val.toChain)
  | .create h _ _ => .create h

end RuleCore.Soroban
