import Conformance

/-!
# gen-vectors

`gen-vectors <dir> [--seed <n>] [--count <n>] [--cap-count <n>] [--auth-count <n>]
[--budget-count <n>]` writes every named case and `count` randomized cases of
seed `seed` (by default the committed seed and count) into `<dir>`, one
`<name>.json` per case, every named cap trace and `cap-count` randomized cap
traces of the same seed into `<dir>/caps`, every named authorization trace and
`auth-count` randomized authorization traces of the same seed into
`<dir>/authorize`, and every named budget trace and `budget-count` randomized
budget traces of the same seed into `<dir>/budget`, after removing the `.json`
files already in each.
-/

open Conformance

structure Options where
  dir : System.FilePath
  seed : UInt64 := Random.defaultSeed
  count : Nat := Random.defaultCount
  capCount : Nat := Caps.defaultCount
  authCount : Nat := Authorize.defaultCount
  budgetCount : Nat := Budget.defaultCount

def usage : String :=
  "usage: gen-vectors <dir> [--seed <n>] [--count <n>] [--cap-count <n>] [--auth-count <n>] " ++
    "[--budget-count <n>]"

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
  | "--cap-count" :: n :: rest =>
    match n.toNat? with
    | some v => parseFlags { o with capCount := v } rest
    | none => .error s!"--cap-count: not a number: {n}"
  | "--auth-count" :: n :: rest =>
    match n.toNat? with
    | some v => parseFlags { o with authCount := v } rest
    | none => .error s!"--auth-count: not a number: {n}"
  | "--budget-count" :: n :: rest =>
    match n.toNat? with
    | some v => parseFlags { o with budgetCount := v } rest
    | none => .error s!"--budget-count: not a number: {n}"
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
  let traces := Caps.traces o.seed o.capCount
  let traceNames := traces.map (·.name)
  if traceNames.eraseDups.length ≠ traceNames.length then
    IO.eprintln "two cap traces share a name"
    return 1
  for t in traces do
    unless t.inRange do
      IO.eprintln s!"{t.name}: a ledger, period or amount does not fit the Rust types"
      return 1
  let auths := Authorize.traces o.seed o.authCount
  let authNames := auths.map (·.name)
  if authNames.eraseDups.length ≠ authNames.length then
    IO.eprintln "two authorization traces share a name"
    return 1
  for t in auths do
    unless t.inRange do
      IO.eprintln s!"{t.name}: a ledger or amount does not fit the Rust types"
      return 1
  let budgets := Budget.traces o.seed o.budgetCount
  let budgetNames := budgets.map (·.name)
  if budgetNames.eraseDups.length ≠ budgetNames.length then
    IO.eprintln "two budget traces share a name"
    return 1
  for t in budgets do
    unless t.inRange do
      IO.eprintln s!"{t.name}: an index or amount does not fit the Rust types"
      return 1
  let capDir := o.dir / "caps"
  let authDir := o.dir / "authorize"
  let budgetDir := o.dir / "budget"
  for d in [o.dir, capDir, authDir, budgetDir] do
    IO.FS.createDirAll d
    for entry in ← d.readDir do
      if entry.path.extension == some "json" then
        IO.FS.removeFile entry.path
  for c in cases do
    IO.FS.writeFile (o.dir / s!"{c.name}.json") c.toJson.render
  for t in traces do
    IO.FS.writeFile (capDir / s!"{t.name}.json") t.toJson.render
  for t in auths do
    IO.FS.writeFile (authDir / s!"{t.name}.json") t.toJson.render
  for t in budgets do
    IO.FS.writeFile (budgetDir / s!"{t.name}.json") t.toJson.render
  IO.println s!"wrote {cases.length} vectors to {o.dir}, {traces.length} cap traces to {capDir}, {auths.length} authorization traces to {authDir} and {budgets.length} budget traces to {budgetDir}"
  return 0
