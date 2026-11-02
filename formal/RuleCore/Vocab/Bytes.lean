/-!
# Byte strings

Contract ids, function names and the payloads of `bytes`, `address`, `symbol`
and `other` values are byte strings, compared exactly: two byte strings are
equal when they have the same length and the same byte at every index. No
prefix match, no normalization.

Byte strings are `List UInt8`. Aeneas translates a Rust `Vec<u8>` or `&[u8]`
to a structure over a `List` of bytes, so an equivalence proof relates the
two by that list.
-/

namespace RuleCore

/-- A byte string, compared by the derived `DecidableEq` of `List UInt8`. -/
abbrev Bytes := List UInt8

/-- The UTF-8 bytes of a string literal, for writing examples. -/
def Bytes.ofString (s : String) : Bytes := s.toUTF8.toList

end RuleCore
