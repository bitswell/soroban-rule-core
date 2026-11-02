import Conformance

/-!
# gen-vectors

`gen-vectors <dir> [--seed <n>] [--count <n>]` writes every named case and
`count` randomized cases of seed `seed` (by default the committed seed and
count) into `<dir>`, one `<name>.json` per case, after removing the `.json`
files already there.
-/

open Conformance

structure Options where
  dir : System.FilePath
  seed : UInt64 := Random.defaultSeed
  count : Nat := Random.defaultCount

def usage : String :=
  "usage: gen-vectors <dir> [--seed <n>] [--count <n>]"

def parseFlags (o : Options) : List String → Except String Options
  | [] => .ok o
  | "--seed" :: n :: rest =>
    match n.toNat? with
    | some v => parseFlags { o with seed := UInt64.ofNat v } rest
    | none => .error s!"--seed: not a number: {n}"
  | "--count" :: n :: rest =>
    match n.toNat? with
    | some v => parseFlags { o with count := v } rest
    | none => .error s!"--count: not a number: {n}"
  | flag :: _ => .error s!"unexpected argument: {flag}\n{usage}"

def parseArgs : List String → Except String Options
  | dir :: rest => parseFlags { dir } rest
  | [] => .error usage

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args with
    | .ok o => pure o
    | .error e => do IO.eprintln e; return 2
  let cases := Cases.all ++ Random.cases o.seed o.count
  let names := cases.map (·.name)
  if names.eraseDups.length ≠ names.length then
    IO.eprintln "two cases share a name"
    return 1
  IO.FS.createDirAll o.dir
  for entry in ← o.dir.readDir do
    if entry.path.extension == some "json" then
      IO.FS.removeFile entry.path
  for c in cases do
    IO.FS.writeFile (o.dir / s!"{c.name}.json") c.toJson.render
  IO.println s!"wrote {cases.length} vectors to {o.dir}"
  return 0
