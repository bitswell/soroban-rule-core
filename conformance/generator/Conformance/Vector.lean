import Conformance.Json

/-!
# Vectors

A `Case` is the specification of one vector: a rule set, a batch of contexts,
the signers the batch's authorization authenticated, and attenuation step lists
to apply to the rule set. `Case.toJson` evaluates it with the Lean model
(`RuleSet.allows`, `RuleSet.allowsAll` and `RuleSet.attenuateAll` of
`RuleCore.Chain`) and writes the vector, inputs and expected results together.
-/

namespace Conformance

open RuleCore RuleCore.Chain

/-- The version of the vector format in `conformance/README.md`. -/
def formatVersion : Nat := 4

structure Case where
  /-- The file name, without `.json`. -/
  name : String
  description : String
  rules : RuleSet
  batch : List Context
  /-- The signers the authorization covering `batch` authenticated. -/
  authenticated : List Signer := []
  /-- Each list is applied to `rules` in order, stopping at the first refused
  step. -/
  attenuations : List (List Attenuation) := []

/-- The model's verdicts for `rs` on `batch` under `auth`: one per context,
and for the whole batch. -/
def verdicts (rs : RuleSet) (batch : List Context) (auth : List Signer) : List (String × Json) :=
  [("allows", .arr (batch.map fun c => .bool (rs.allows c auth))),
   ("allows_all", .bool (rs.allowsAll batch auth))]

def attenuationJson (rs : RuleSet) (batch : List Context) (auth : List Signer)
    (steps : List Attenuation) : Json :=
  let expected : Json :=
    match rs.attenuateAll steps with
    | .ok rs' => tagged "ok" (.obj ([("rules", encodeRuleSet rs')] ++ verdicts rs' batch auth))
    | .error e => tagged "error" (encodeError e)
  .obj [("steps", .arr (steps.map encodeStep)), ("expected", expected)]

def Case.toJson (c : Case) : Json :=
  .obj [
    ("format", .num formatVersion),
    ("name", .str c.name),
    ("description", .str c.description),
    ("rules", encodeRuleSet c.rules),
    ("batch", .arr (c.batch.map encodeContext)),
    ("authenticated", encodeSigners c.authenticated),
    ("expected", .obj (verdicts c.rules c.batch c.authenticated)),
    ("attenuations",
      .arr (c.attenuations.map (attenuationJson c.rules c.batch c.authenticated)))]

end Conformance
