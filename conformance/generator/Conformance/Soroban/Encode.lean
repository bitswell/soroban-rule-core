import Conformance.Json
import RuleCore.Soroban.Host

/-!
# Encoding the Soroban models

The JSON encoding of `RuleCore.Soroban`'s values, contexts, signed trees,
calls, account programs and events, as `conformance/README.md` describes it.
Integers that may not fit a double (`u64`, `i128`, nonces) are decimal
strings; byte strings are lowercase hexadecimal.
-/

namespace Conformance.Soroban

open RuleCore RuleCore.Soroban

def encodeAddress : Address → Json
  | .account k => tagged "account" (.str (hex k))
  | .contract i => tagged "contract" (.str (hex i))
  | .muxedAccount id k =>
    tagged "muxed_account" (.obj [("id", .str (toString id.toNat)), ("key", .str (hex k))])

mutual

def encodeValue : Val → Json
  | .void => tagged "void" .null
  | .bool b => tagged "bool" (.bool b)
  | .u32 v => tagged "u32" (.num v.toNat)
  | .u64 v => tagged "u64" (.str (toString v.toNat))
  | .i128 v => tagged "i128" (.str (toString v.toInt))
  | .bytes b => tagged "bytes" (.str (hex b))
  | .string b => tagged "string" (.str (hex b))
  | .symbol b => tagged "symbol" (.str (hex b))
  | .address a => tagged "address" (encodeAddress a)
  | .vec items => tagged "vec" (.arr (encodeValues items))
  | .map es => tagged "map" (.arr (encodeEntries es))
  | .other x => tagged "other" (.str (hex x))

def encodeValues : List Val → List Json
  | [] => []
  | v :: vs => encodeValue v :: encodeValues vs

def encodeEntries : List (Val × Val) → List Json
  | [] => []
  | (k, v) :: es => .arr [encodeValue k, encodeValue v] :: encodeEntries es

end

def encodeOption {α : Type} (f : α → Json) : Option α → Json
  | some a => f a
  | none => .null

def encodeDurability : Durability → Json
  | .persistent => .str "persistent"
  | .temporary => .str "temporary"
  | .contractInstance => .str "instance"

def encodeAuthFn : AuthFn → Json
  | .contract c f args =>
    tagged "contract" (.obj [
      ("contract", encodeAddress c),
      ("fn_name", .str (hex f)),
      ("args", .arr (encodeValues args))])
  | .create h s args =>
    tagged "create_contract" (.obj [
      ("wasm_hash", .str (hex h)),
      ("salt", .str (hex s)),
      ("constructor_args", .arr (encodeValues args))])

mutual

def encodeInvocation : Invocation → Json
  | .node f subs => .obj [("context", encodeAuthFn f), ("subs", .arr (encodeInvocations subs))]

def encodeInvocations : List Invocation → List Json
  | [] => []
  | i :: is => encodeInvocation i :: encodeInvocations is

end

mutual

def encodeDelegate : Delegate → Json
  | .mk a sig nested =>
    .obj [("address", encodeAddress a), ("signature", encodeValue sig),
      ("nested", .arr (encodeDelegates nested))]

def encodeDelegates : List Delegate → List Json
  | [] => []
  | d :: ds => encodeDelegate d :: encodeDelegates ds

end

def encodeCredentials : Credentials → Json
  | .address => .str "address"
  | .addressV2 => .str "address_v2"
  | .withDelegates ds => tagged "with_delegates" (.arr (encodeDelegates ds))

def encodeEntry (e : Entry) : Json :=
  .obj [
    ("address", encodeAddress e.address),
    ("nonce", .str (toString e.nonce)),
    ("expiration", .num e.expiration),
    ("signature", encodeValue e.signature),
    ("credentials", encodeCredentials e.credentials),
    ("root", encodeInvocation e.root)]

def encodePreimage (p : Preimage) : Json :=
  .obj [
    ("address", encodeOption encodeAddress p.address),
    ("nonce", .str (toString p.nonce)),
    ("expiration", .num p.expiration),
    ("invocation", encodeInvocation p.invocation)]

def encodeFailKind : FailKind → Json
  | .error => .str "error"
  | .trap => .str "trap"

def encodeSlot (d : Durability) (k : Val) : List (String × Json) :=
  [("durability", encodeDurability d), ("key", encodeValue k)]

mutual

def encodeStep : Step → Json
  | .get d k => tagged "get" (.obj (encodeSlot d k))
  | .has d k => tagged "has" (.obj (encodeSlot d k))
  | .put d k v => tagged "put" (.obj (encodeSlot d k ++ [("val", encodeValue v)]))
  | .remove d k => tagged "remove" (.obj (encodeSlot d k))
  | .requireAuth a => tagged "require_auth" (encodeAddress a)
  | .call c catches => tagged "call" (.obj [("callee", encodeCall c), ("catches", .bool catches)])
  | .fail k => tagged "fail" (encodeFailKind k)

def encodeSteps : List Step → List Json
  | [] => []
  | s :: ss => encodeStep s :: encodeSteps ss

def encodeCall : Call → Json
  | .mk c f args body =>
    .obj [
      ("contract", encodeAddress c),
      ("fn_name", .str (hex f)),
      ("args", .arr (encodeValues args)),
      ("body", .arr (encodeSteps body))]

end

def encodeAccountStep : AccountStep → Json
  | .get d k => tagged "get" (.obj (encodeSlot d k))
  | .put d k v => tagged "put" (.obj (encodeSlot d k ++ [("val", encodeValue v)]))
  | .remove d k => tagged "remove" (.obj (encodeSlot d k))
  | .checkRules rs auth =>
    tagged "check_rules" (.obj [("rules", encodeRuleSet rs), ("authenticated", encodeSigners auth)])
  | .delegate a => tagged "delegate" (encodeAddress a)
  | .fail k => tagged "fail" (encodeFailKind k)

def encodeVia : Via → Json
  | .invoker => .str "invoker"
  | .entry => .str "entry"

/-- An event. A `check_auth` event also carries its contexts as the value the
host passes them in and as `rule-eval` reads them. -/
def encodeEvent : Event → Json
  | .checkAuth a pre sig ctxs =>
    tagged "check_auth" (.obj [
      ("account", encodeAddress a),
      ("preimage", encodePreimage pre),
      ("signature", encodeValue sig),
      ("contexts", .arr (ctxs.map encodeAuthFn)),
      ("contexts_value", encodeValue (.vec (ctxs.map AuthFn.toVal))),
      ("rule_eval_contexts", .arr (ctxs.map (encodeContext ∘ AuthFn.toChain)))])
  | .read c d k v =>
    tagged "read" (.obj ([("contract", encodeAddress c)] ++ encodeSlot d k ++
      [("value", encodeOption encodeValue v)]))
  | .found c d k b =>
    tagged "found" (.obj ([("contract", encodeAddress c)] ++ encodeSlot d k ++
      [("present", .bool b)]))
  | .authorized a f via =>
    tagged "authorized" (.obj [("address", encodeAddress a), ("context", encodeAuthFn f),
      ("via", encodeVia via)])

end Conformance.Soroban
