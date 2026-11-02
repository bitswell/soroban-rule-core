import Lean
import RuleCore

/-!
# Axioms

Every theorem of the package depends on at most Lean's built-in axioms
`propext`, `Quot.sound` and `Classical.choice`: no `sorryAx`, no
`Lean.ofReduceBool`, nothing declared by the package.

`RuleCore.lean` imports every other module of the package, so importing it
here brings every theorem of the package into scope.

`#print_package_axioms` runs `#print axioms` on every exported theorem of the
package's modules (every theorem written in the sources that is not private),
in order of full name, and `#guard_msgs` pins the output. A new theorem, or a
change in any theorem's axioms, fails the build until the record below is
updated.

`#check_package_axioms` checks every theorem in the package's modules,
generated ones included (equation lemmas, injectivity lemmas, auxiliary
proofs), against the three permitted axioms and fails on any other.
-/

namespace RuleCore.Axioms

open Lean Elab Command

/-- The axioms a theorem of the package may depend on. -/
def permitted : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The theorems declared in the package's modules, in order of full name. With
`exported`, only those written in the sources and not private. -/
def packageTheorems (exported : Bool) : CommandElabM (Array Name) := do
  let env ← getEnv
  let mut names := #[]
  for (n, ci) in env.constants.map₁.toList do
    let .thmInfo _ := ci | continue
    let some idx := env.getModuleIdxFor? n | continue
    unless (env.header.moduleNames[idx.toNat]!).getRoot == `RuleCore do continue
    if exported then
      if isPrivateName n then continue
      if (← findDeclarationRanges? n).isNone then continue
    names := names.push n
  return names.qsort (·.toString < ·.toString)

/-- `#print axioms` for every exported theorem of the package. -/
elab "#print_package_axioms" : command => do
  for n in ← packageTheorems true do
    elabCommand (← `(command| #print axioms $(mkIdent n):ident))

/-- Fail unless every theorem of the package depends only on `permitted`. -/
elab "#check_package_axioms" : command => do
  for n in ← packageTheorems false do
    for a in ← collectAxioms n do
      unless permitted.contains a do
        throwError "{n} depends on {a}"

end RuleCore.Axioms

#guard_msgs in
#check_package_axioms

/--
info: 'RuleCore.Bytes.append_ne_self' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Bytes.eq_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argEq_bytes_false_of_other' depends on axioms: [propext]
---
info: 'RuleCore.Chain.Cond.argEq_false_of_kind_ne' depends on axioms: [propext]
---
info: 'RuleCore.Chain.Cond.argEq_holds_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.Cond.argEq_kind' depends on axioms: [propext]
---
info: 'RuleCore.Chain.Cond.argI128AtMost_holds_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.holds_false_of_length_le' depends on axioms: [propext]
---
info: 'RuleCore.Chain.Rule.allows_call_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_create' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_extension_false' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_false_of_functions_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_prefix_false' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.contract_eq_of_allows' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.denote_addCond' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.denote_removeFunctions' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.mem_removeFunctions' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.Derives.narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.addCond_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.RuleSet.addCond_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allowsAll_false_of_create_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allowsAll_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allowsAll_of_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allows_create' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allows_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuateAll_derives' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuateAll_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuate_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_addCond' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_attenuate' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_dropRule' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_modifyRule' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_removeFunctions' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.dropRule_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.RuleSet.dropRule_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.modifyRule_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.RuleSet.narrower_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.narrower_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.removeFunctions_eq_error_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.removeFunctions_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.rules_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Val.ne_of_kind_ne' does not depend on any axioms
---
info: 'RuleCore.Rule.allows_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.allows_of_allows_addCond' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.allows_of_allows_restrictScope' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.Derives.narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.addCond_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.addCond_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.allowsAll_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.allowsAll_nil' does not depend on any axioms
---
info: 'RuleCore.RuleSet.allowsAll_of_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.allows_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuateAll_derives' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.attenuateAll_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuate_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.dropRule_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.dropRule_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.modifyRule_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.modifyRule_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.narrower_refl' does not depend on any axioms
---
info: 'RuleCore.RuleSet.narrower_trans' does not depend on any axioms
---
info: 'RuleCore.RuleSet.restrictScope_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.restrictScope_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.rules_ofRules' does not depend on any axioms
-/
#guard_msgs in
#print_package_axioms
