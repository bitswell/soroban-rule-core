import Lean.Data.Json
import RuleCore.Vocab.Chain

/-!
# JSON encoding

A small JSON tree that keeps object fields in the order they are written, a
printer for it, and the encoding of the chain vocabulary described in
`conformance/README.md`.

The printer writes a value on one line when it fits within `width` columns and
otherwise puts each element or field on its own line, indented by two spaces,
so the committed vectors are stable and readable in a diff.
-/

namespace Conformance

open RuleCore RuleCore.Chain

inductive Json where
  | str (s : String)
  | num (n : Int)
  | bool (b : Bool)
  | arr (items : List Json)
  | obj (fields : List (String × Json))

/-- A JSON string literal, with Lean's JSON escaping. -/
def quote (s : String) : String :=
  Lean.Json.compress (.str s)

mutual

def Json.compact : Json → String
  | .str s => quote s
  | .num n => toString n
  | .bool b => toString b
  | .arr items => "[" ++ Json.compactItems items ++ "]"
  | .obj fields => "{" ++ Json.compactFields fields ++ "}"

def Json.compactItems : List Json → String
  | [] => ""
  | [x] => x.compact
  | x :: xs => x.compact ++ ", " ++ Json.compactItems xs

def Json.compactFields : List (String × Json) → String
  | [] => ""
  | [(k, v)] => quote k ++ ": " ++ v.compact
  | (k, v) :: kvs => quote k ++ ": " ++ v.compact ++ ", " ++ Json.compactFields kvs

end

/-- The line width the printer keeps one-line values within. -/
def width : Nat := 100

def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

mutual

/-- `j` printed with its enclosing block indented by `ind` spaces and its first
character at column `col`. -/
def Json.pretty (ind col : Nat) : Json → String
  | .arr items =>
    let c := (Json.arr items).compact
    if items.isEmpty || col + c.length ≤ width then c
    else "[\n" ++ Json.prettyItems (ind + 2) items ++ "\n" ++ spaces ind ++ "]"
  | .obj fields =>
    let c := (Json.obj fields).compact
    if fields.isEmpty || col + c.length ≤ width then c
    else "{\n" ++ Json.prettyFields (ind + 2) fields ++ "\n" ++ spaces ind ++ "}"
  | j => j.compact

def Json.prettyItems (ind : Nat) : List Json → String
  | [] => ""
  | [x] => spaces ind ++ x.pretty ind ind
  | x :: xs => spaces ind ++ x.pretty ind ind ++ ",\n" ++ Json.prettyItems ind xs

def Json.prettyFields (ind : Nat) : List (String × Json) → String
  | [] => ""
  | [(k, v)] => spaces ind ++ quote k ++ ": " ++ v.pretty ind (ind + (quote k).length + 2)
  | (k, v) :: kvs =>
    spaces ind ++ quote k ++ ": " ++ v.pretty ind (ind + (quote k).length + 2) ++ ",\n" ++
      Json.prettyFields ind kvs

end

/-- The document printed from column zero, ending with a newline. -/
def Json.render (j : Json) : String :=
  j.pretty 0 0 ++ "\n"

/-! ## The chain vocabulary -/

def hexDigit (n : Nat) : Char :=
  "0123456789abcdef".toList.getD n '0'

/-- A byte string as lowercase hexadecimal, two digits per byte. -/
def hex (b : Bytes) : String :=
  String.ofList (b.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

def tagged (tag : String) (j : Json) : Json :=
  .obj [(tag, j)]

def encodeBytesList (bs : List Bytes) : Json :=
  .arr (bs.map (.str ∘ hex))

/-- `i128` and `u64` are decimal strings, since many JSON readers hold numbers
as doubles. -/
def encodeVal : Val → Json
  | .i128 v => tagged "i128" (.str (toString v.toInt))
  | .u64 v => tagged "u64" (.str (toString v.toNat))
  | .bool v => tagged "bool" (.bool v)
  | .bytes v => tagged "bytes" (.str (hex v))
  | .address v => tagged "address" (.str (hex v))
  | .symbol v => tagged "symbol" (.str (hex v))
  | .other v => tagged "other" (.str (hex v))

def encodeContext : Context → Json
  | .call contract function args =>
    tagged "call" (.obj [
      ("contract", .str (hex contract)),
      ("function", .str (hex function)),
      ("args", .arr (args.map encodeVal))])
  | .create wasmHash => tagged "create" (.obj [("wasm_hash", .str (hex wasmHash))])

def encodeIndex (i : UInt32) : Json :=
  .num i.toNat

def encodeCond : Cond → Json
  | .argEq i val => tagged "arg_eq" (.obj [("index", encodeIndex i), ("value", encodeVal val)])
  | .argI128AtMost i n =>
    tagged "arg_i128_at_most" (.obj [("index", encodeIndex i), ("bound", .str (toString n.toInt))])

def encodeRule (r : Rule) : Json :=
  .obj [
    ("contract", .str (hex r.contract)),
    ("functions", encodeBytesList r.functions),
    ("conds", .arr (r.conds.map encodeCond))]

def encodeRuleSet (rs : RuleSet) : Json :=
  .arr (rs.map encodeRule)

def encodeStep : Attenuation → Json
  | .dropRule i => tagged "drop_rule" (.obj [("index", encodeIndex i)])
  | .addCond i cond => tagged "add_cond" (.obj [("index", encodeIndex i), ("cond", encodeCond cond)])
  | .removeFunctions i fs =>
    tagged "remove_functions" (.obj [("index", encodeIndex i), ("functions", encodeBytesList fs)])

def encodeError : AttenuationError → Json
  | .noSuchRule => .str "no_such_rule"

end Conformance
