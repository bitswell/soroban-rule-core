import Lean
import RuleCore

/-!
# Axioms

Every theorem of the package depends on at most Lean's built-in axioms
`propext`, `Quot.sound` and `Classical.choice`: no `sorryAx`, no
`Lean.ofReduceBool`, nothing declared by the package, and none of the axioms
Aeneas's Lean library declares. That covers the model's theorems, the
equivalence theorems and every theorem about the extracted evaluator.

`RuleCore.lean` imports every other module of the package, so importing it
here brings every theorem of the package into scope.

`#print_package_axioms` runs `#print axioms` on every exported theorem of the
package's modules (every theorem written in the sources that is not private),
in order of full name, and `#guard_msgs` pins the output. A new theorem, or a
change in any theorem's axioms, fails the build until the record below is
updated.

`#check_package_axioms` checks every theorem in the package's modules,
generated ones included (equation lemmas, injectivity lemmas, auxiliary
proofs, and anything in the Aeneas translation `RuleCore.Extracted.RuleEval`),
against the three permitted axioms and fails on any other.
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
info: 'RuleCore.Equiv.add_cond_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.add_cond_err' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.add_cond_full' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.add_cond_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.add_cond_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.allows_all_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.allows_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.any_bytes_eq_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.byte_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.bytesOf_inj' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.bytes_copy_deref' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_copy_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_eq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_eq_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_in_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_copy_deref' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_copy_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_without_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_without_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.cast_usize_val' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.chain_ruleSet_allows' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.chain_ruleSet_allowsAll' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.chain_rule_allows_call' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.cond_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.cond_holds_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.conds_copy_deref' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.conds_copy_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.conds_hold_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteBytes_inj' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteBytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteCond_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteContext_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteError_injective' does not depend on any axioms
---
info: 'RuleCore.Equiv.denoteOutcome_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteRule_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteRules_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteU32_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteU32_toNat' does not depend on any axioms
---
info: 'RuleCore.Equiv.denoteU64_inj' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteU64_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteVal_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denote_filter_inList' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.drop_rule_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.drop_rule_err' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.drop_rule_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.drop_rule_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.i128_bv_inj' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.i128_bv_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.incr_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.index_usize_eq' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.loop_all' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.loop_any' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.loop_build' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.loop_build_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.push_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.push_full' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.pushedFrom_eraseIdx' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.pushedFrom_eraseIdx_from' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.pushedFrom_filter' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.pushedFrom_map' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.pushedFrom_map_of' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.pushedFrom_set' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.pushedFrom_set_from' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_functions_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_functions_err' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_functions_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_functions_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.room_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.rule_allows_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.rule_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.rule_without_functions_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.slice_get_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.slice_len_bne' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.slice_len_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.slice_len_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.usize_val_eq_iff' does not depend on any axioms
---
info: 'RuleCore.Equiv.val_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.val_eq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vec_deref_val' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vec_eq_of_val' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vec_mk_deref' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vec_new_val' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.zip_all_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.Derives.allows_all' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.Derives.narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.Narrower.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.Narrower.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.Step.narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.add_cond_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.add_cond_room' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.allows_all_create' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.allows_all_of_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.allows_create' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.bytes_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.cond_holds_argEq_false_of_kind_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.cond_holds_argEq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.cond_holds_argEq_kind' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.drop_rule_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.narrower_of_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.remove_functions_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.rule_allows_call' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.rule_allows_extension_false' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.rule_allows_prefix_false' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.val_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.val_eq_kind' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.val_eq_other_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
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
