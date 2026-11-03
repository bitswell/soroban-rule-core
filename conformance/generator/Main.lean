import Conformance

/-!
# gen-vectors

`gen-vectors <dir> [--seed <n>] [--count <n>] [--cap-count <n>] [--auth-count <n>]
[--budget-count <n>] [--doc-count <n>] [--storage-count <n>] [--host-count <n>]` writes every named case and `count` randomized cases of
seed `seed` (by default the committed seed and count) into `<dir>`, one
`<name>.json` per case, every named cap trace and `cap-count` randomized cap
traces of the same seed into `<dir>/caps`, every named authorization trace and
`auth-count` randomized authorization traces of the same seed into
`<dir>/authorize`, every named budget trace and `budget-count` randomized
budget traces of the same seed into `<dir>/budget`, and every named document
trace and `doc-count` randomized document traces of the same seed into
`<dir>/documents`, the Soroban value and context vectors into
`<dir>/soroban/values` and `<dir>/soroban/contexts`, every named storage trace
and `storage-count` randomized storage traces of the same seed into
`<dir>/soroban/storage`, and every named host trace and `host-count`
randomized host traces of the same seed into `<dir>/soroban/host`, and the
traces transcribed from soroban-env-host's own tests into
`<dir>/soroban/seed/host` and `<dir>/soroban/seed/storage`, with their
coverage in `<dir>/soroban/seed/coverage.json`, after removing the `.json`
files already in each. It writes nothing when the model's outcome for a
transcribed case differs from the host test's.
-/

open Conformance

structure Options where
  dir : System.FilePath
  seed : UInt64 := Random.defaultSeed
  count : Nat := Random.defaultCount
  capCount : Nat := Caps.defaultCount
  authCount : Nat := Authorize.defaultCount
  budgetCount : Nat := Budget.defaultCount
  docCount : Nat := Documents.defaultCount
  storageCount : Nat := Soroban.Storage.defaultCount
  hostCount : Nat := Soroban.Host.defaultCount

def usage : String :=
  "usage: gen-vectors <dir> [--seed <n>] [--count <n>] [--cap-count <n>] [--auth-count <n>] " ++
    "[--budget-count <n>] [--doc-count <n>] [--storage-count <n>] [--host-count <n>]"

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
  | "--doc-count" :: n :: rest =>
    match n.toNat? with
    | some v => parseFlags { o with docCount := v } rest
    | none => .error s!"--doc-count: not a number: {n}"
  | "--storage-count" :: n :: rest =>
    match n.toNat? with
    | some v => parseFlags { o with storageCount := v } rest
    | none => .error s!"--storage-count: not a number: {n}"
  | "--host-count" :: n :: rest =>
    match n.toNat? with
    | some v => parseFlags { o with hostCount := v } rest
    | none => .error s!"--host-count: not a number: {n}"
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
  let docs := Documents.traces o.seed o.docCount
  let docNames := docs.map (·.name)
  if docNames.eraseDups.length ≠ docNames.length then
    IO.eprintln "two document traces share a name"
    return 1
  for t in docs do
    unless t.valid do
      IO.eprintln s!"{t.name}: a document is not valid"
      return 1
    if t.choosesRecovery then
      IO.eprintln s!"{t.name}: an authorization chooses the recovery rule"
      return 1
  let storages := Soroban.Storage.traces o.seed o.storageCount
  let storageNames := storages.map (·.name)
  if storageNames.eraseDups.length ≠ storageNames.length then
    IO.eprintln "two storage traces share a name"
    return 1
  for t in storages do
    unless t.inDomain do
      IO.eprintln s!"{t.name}: a muxed key is used in instance storage"
      return 1
  let hosts := Soroban.Host.traces o.seed o.hostCount
  let hostNames := hosts.map (·.name)
  if hostNames.eraseDups.length ≠ hostNames.length then
    IO.eprintln "two host traces share a name"
    return 1
  for t in hosts do
    unless t.inDomain do
      IO.eprintln s!"{t.name}: the harness cannot drive this trace on the host"
      return 1
  let seeds := Soroban.Seed.hostSeeds
  let seedStorages := Soroban.Seed.storageSeeds
  let seedNames := seeds.map (·.trace.name) ++ seedStorages.map (·.trace.name)
  if seedNames.eraseDups.length ≠ seedNames.length then
    IO.eprintln "two seed traces share a name"
    return 1
  for s in seeds do
    unless s.trace.inDomain do
      IO.eprintln s!"{s.trace.name}: the harness cannot drive this trace on the host"
      return 1
    unless s.expects.length == s.trace.txs.length do
      IO.eprintln s!"{s.trace.name}: one expectation for each transaction"
      return 1
  for s in seedStorages do
    unless s.trace.inDomain do
      IO.eprintln s!"{s.trace.name}: a muxed key is used in instance storage"
      return 1
  for e in Soroban.Seed.inconsistencies do
    IO.eprintln e
  unless Soroban.Seed.inconsistencies.isEmpty do
    return 1
  for (file, test, line) in Soroban.Seed.disagreements do
    IO.eprintln s!"{file} {test}, line {line}: the model's outcome differs from the host test's"
  unless Soroban.Seed.disagreements.isEmpty do
    return 1
  let capDir := o.dir / "caps"
  let authDir := o.dir / "authorize"
  let budgetDir := o.dir / "budget"
  let docDir := o.dir / "documents"
  let valueDir := o.dir / "soroban" / "values"
  let contextDir := o.dir / "soroban" / "contexts"
  let storageDir := o.dir / "soroban" / "storage"
  let hostDir := o.dir / "soroban" / "host"
  let seedDir := o.dir / "soroban" / "seed"
  let seedHostDir := seedDir / "host"
  let seedStorageDir := seedDir / "storage"
  for d in [o.dir, capDir, authDir, budgetDir, docDir, valueDir, contextDir, storageDir, hostDir,
      seedDir, seedHostDir, seedStorageDir] do
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
  for t in docs do
    IO.FS.writeFile (docDir / s!"{t.name}.json") t.toJson.render
  for v in Soroban.Values.valueVectors do
    IO.FS.writeFile (valueDir / s!"{v.name}.json") v.toJson.render
  for v in Soroban.Values.contextVectors do
    IO.FS.writeFile (contextDir / s!"{v.name}.json") v.toJson.render
  for t in storages do
    IO.FS.writeFile (storageDir / s!"{t.name}.json") t.toJson.render
  for t in hosts do
    IO.FS.writeFile (hostDir / s!"{t.name}.json") t.toJson.render
  for s in seeds do
    IO.FS.writeFile (seedHostDir / s!"{s.trace.name}.json") s.trace.toJson.render
  for s in seedStorages do
    IO.FS.writeFile (seedStorageDir / s!"{s.trace.name}.json") s.trace.toJson.render
  IO.FS.writeFile (seedDir / "coverage.json") Soroban.Seed.coverageJson.render
  IO.println s!"wrote {cases.length} vectors to {o.dir}, {traces.length} cap traces to {capDir}, {auths.length} authorization traces to {authDir}, {budgets.length} budget traces to {budgetDir}, {docs.length} document traces to {docDir}, {Soroban.Values.valueVectors.length + Soroban.Values.contextVectors.length} Soroban value and context vectors to {o.dir / "soroban"}, {storages.length} storage traces to {storageDir}, {hosts.length} host traces to {hostDir}, and {seeds.length} host and {seedStorages.length} storage traces transcribed from the host's tests to {seedDir}"
  return 0
