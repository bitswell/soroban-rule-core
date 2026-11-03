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
info: 'RuleCore.Attenuation.source_dropRule' depends on axioms: [propext]
---
info: 'RuleCore.Attenuation.source_eq_of_ne_dropRule' depends on axioms: [propext]
---
info: 'RuleCore.Authorization.charges_eq' does not depend on any axioms
---
info: 'RuleCore.Authorization.chosen_renumber' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Authorization.length_chosen' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Authorization.map_fst_chosen' depends on axioms: [propext]
---
info: 'RuleCore.Authorization.map_snd_chosen' depends on axioms: [propext]
---
info: 'RuleCore.Authorization.renumber_renumber' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.apply_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.apply_withinAllowance' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.delegate_ok_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.delegate_valid' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.delegate_withinAllowance' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.fits_iff' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.getElem?_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.getElem_of_getElem?' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.le_of_within' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.length_charge' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.logged_of_error' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.lt_length_of_getElem?' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.mem_walk' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.node_valid_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.nonneg_of_valid' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.parentOf_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.parent_lt' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.refill_ok_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.refill_valid' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.refill_withinAllowance' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.run_cons_of_error' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.run_extends' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.run_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.run_withinAllowance' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_accepts_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_error_overdrawn' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_ok_allowance' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_ok_charges' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_ok_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_ok_length' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_ok_parentOf' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_ok_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_overdrawn' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spend_withinAllowance' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spentUnder_append' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spentUnder_eq_spent' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spentUnder_le_allowance' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spentUnder_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spentUnder_single' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.spent_run' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.step_extends' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.step_of_error' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.step_spent' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.step_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.step_withinAllowance' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Budget.Tree.validFrom_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.valid_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.valid_set' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.walk_error' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.walk_fits' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.walk_overdrawn' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.walk_succ' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.walk_total' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.withinAllowance_iff' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.within_antisymm' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Budget.Tree.within_of_walk' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.within_root' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.within_step' depends on axioms: [propext]
---
info: 'RuleCore.Budget.Tree.within_trans' depends on axioms: [propext]
---
info: 'RuleCore.Bytes.append_ne_self' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Bytes.eq_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Cap.Params.accepts_of_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.Params.narrower_refl' depends on axioms: [propext]
---
info: 'RuleCore.Cap.Params.narrower_trans' depends on axioms: [propext]
---
info: 'RuleCore.Cap.Record.Valid.pos' does not depend on any axioms
---
info: 'RuleCore.Cap.Record.Valid.sorted' does not depend on any axioms
---
info: 'RuleCore.Cap.Record.Valid.total_eq' does not depend on any axioms
---
info: 'RuleCore.Cap.Record.Valid.total_le' does not depend on any axioms
---
info: 'RuleCore.Cap.Record.empty_history' does not depend on any axioms
---
info: 'RuleCore.Cap.Record.empty_valid' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Cap.RunInv.le' does not depend on any axioms
---
info: 'RuleCore.Cap.RunInv.start' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Cap.RunInv.step_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.RunInv.valid' does not depend on any axioms
---
info: 'RuleCore.Cap.RunInv.window' does not depend on any axioms
---
info: 'RuleCore.Cap.accepts_cons_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Cap.accepts_of_limit_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.accepts_of_narrower_suffix' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.accepts_of_period_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.addI128_eq_none' depends on axioms: [propext]
---
info: 'RuleCore.Cap.addI128_eq_some' depends on axioms: [propext]
---
info: 'RuleCore.Cap.amountSum_append' depends on axioms: [propext]
---
info: 'RuleCore.Cap.amountSum_cons' depends on axioms: [propext]
---
info: 'RuleCore.Cap.amountSum_filter_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.amountSum_nil' does not depend on any axioms
---
info: 'RuleCore.Cap.amountSum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.amountSum_suffix_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.beforeNewest_concat' depends on axioms: [propext]
---
info: 'RuleCore.Cap.beforeNewest_eq_false_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Cap.beforeNewest_nil' does not depend on any axioms
---
info: 'RuleCore.Cap.capAccepts_of_capNarrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.check_ledgerBeforeNewest_iff' depends on axioms: [propext]
---
info: 'RuleCore.Cap.check_negative' depends on axioms: [propext]
---
info: 'RuleCore.Cap.check_of_narrower_suffix' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.check_pos_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.check_preserves_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.check_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.check_zero' depends on axioms: [propext]
---
info: 'RuleCore.Cap.dropWhile_eq_filter' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Cap.evict_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.evict_error' depends on axioms: [propext]
---
info: 'RuleCore.Cap.filter_cutoff_suffix' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Cap.filter_cutoff_window' depends on axioms: [propext]
---
info: 'RuleCore.Cap.filter_inPeriodFrom_period_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.filter_window_eq_cutoff' depends on axioms: [propext]
---
info: 'RuleCore.Cap.i128Max_pos' does not depend on any axioms
---
info: 'RuleCore.Cap.i128Min_neg' does not depend on any axioms
---
info: 'RuleCore.Cap.inPeriodFrom_eq_inWindow' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.mem_recorded' depends on axioms: [propext]
---
info: 'RuleCore.Cap.period_le_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.period_le_limit_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.period_ledger_zero' does not depend on any axioms
---
info: 'RuleCore.Cap.recorded_nil' does not depend on any axioms
---
info: 'RuleCore.Cap.recorded_of_runAll' depends on axioms: [propext]
---
info: 'RuleCore.Cap.runAll_append' depends on axioms: [propext]
---
info: 'RuleCore.Cap.runAll_cons' depends on axioms: [propext]
---
info: 'RuleCore.Cap.runAll_nil' does not depend on any axioms
---
info: 'RuleCore.Cap.run_append' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Cap.run_cons' does not depend on any axioms
---
info: 'RuleCore.Cap.run_cons_of_error' depends on axioms: [propext]
---
info: 'RuleCore.Cap.run_eq_of_recorded_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.run_eq_window' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.run_history' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.run_history_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.run_nil' does not depend on any axioms
---
info: 'RuleCore.Cap.run_of_runAll' depends on axioms: [propext]
---
info: 'RuleCore.Cap.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.run_total' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.run_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.step_of_error' depends on axioms: [propext]
---
info: 'RuleCore.Cap.subI128_eq_some' depends on axioms: [propext]
---
info: 'RuleCore.Cap.window_le_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Cap.window_le_limit_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Attenuation.source_denote_dropRule' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Attenuation.source_denote_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Cap.valid_denote' depends on axioms: [propext]
---
info: 'RuleCore.Chain.Cond.argEq_bytes_false_of_other' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argEq_false_of_kind_ne' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argEq_holds_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argEq_kind' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argEq_string_false_of_symbol' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argI128AtMost_holds_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argIn_holds_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argIn_holds_iff_argEq' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argStrPrefix_false_of_kind_ne' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argStrPrefix_false_of_symbol' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argStrPrefix_holds_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.argStrPrefix_kind' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Cond.holds_false_of_length_le' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Functions.mem_any' depends on axioms: [propext]
---
info: 'RuleCore.Chain.Functions.mem_anyExcept' does not depend on any axioms
---
info: 'RuleCore.Chain.Functions.mem_only' does not depend on any axioms
---
info: 'RuleCore.Chain.Functions.mem_remove' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Functions.mem_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_call_any' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_call_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_congr_signers' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_create' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_eraseDups_signers' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_extension_false' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_false_of_functions_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_false_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_of_threshold_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.allows_prefix_false' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.contract_eq_of_allows' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.denote_addCond' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.denote_removeFunctions' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.denote_removeSigners' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.denote_restrictFunctions' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.mem_present' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.mem_removeFunctions' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.mem_removeSigners' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Rule.mem_restrictFunctions' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.signed_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.signed_iff_of_threshold_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Rule.signed_of_threshold_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.Derives.narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.addCap_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.addCond_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.RuleSet.addCond_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allowsAll_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allowsAll_false_of_create_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allowsAll_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allowsAll_of_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allowsAll_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allows_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allows_create' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allows_eraseDups' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allows_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.allows_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuateAll_capsValid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuateAll_derives' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuateAll_generation' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuateAll_generation_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuateAll_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuateAll_traceNarrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuate_capsValid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuate_generation' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuate_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.attenuate_traceNarrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.authorizeAll_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.authorize_allowsAll' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.authorize_contexts_nil_of_stale' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.authorize_generation' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.authorize_not_chosen_of_stale' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.authorize_signers' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.authorize_validUntil' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_addCap' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_addCond' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_attenuate' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_attenuateAll' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_dropRule' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_get' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_lengthenCapPeriod' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_lowerCapLimit' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_lowerValidUntil' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_modifyRule' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_raiseThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_removeFunctions' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_removeSigners' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.denote_restrictFunctions' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.dropRule_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.RuleSet.dropRule_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.emptyRecords_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.lengthenCapPeriod_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.lowerCapLimit_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.lowerValidUntil_eq_noSuchRule_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.RuleSet.lowerValidUntil_eq_validUntilRaised_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.lowerValidUntil_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.modifyRule_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.RuleSet.narrower_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.narrower_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.raiseThreshold_eq_noSuchRule_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.RuleSet.raiseThreshold_eq_thresholdLowered_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.raiseThreshold_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.removeFunctions_eq_error_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.removeFunctions_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.removeSigners_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.RuleSet.removeSigners_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.restrictFunctions_eq_error_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.restrictFunctions_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.RuleSet.rules_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Chain.Signer.delegated_append_ne' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Chain.Signer.delegated_eq_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.Signer.delegated_ne_external' does not depend on any axioms
---
info: 'RuleCore.Chain.Signer.external_eq_iff' depends on axioms: [propext]
---
info: 'RuleCore.Chain.Val.ne_of_kind_ne' does not depend on any axioms
---
info: 'RuleCore.Chain.Val.string_ne_symbol' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.add_cap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.add_cap_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
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
info: 'RuleCore.Equiv.any_signer_eq_mem' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.any_val_eq_mem' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.authorize_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.before_newest_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
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
info: 'RuleCore.Equiv.bytes_list_extend_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_extend_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_extend_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_extend_loop_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_within_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_within_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_without_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_list_without_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.bytes_starts_with_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.cap_copy_eq' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.cap_option_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.cap_valid_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.cast_usize_val' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.chain_ruleSet_allows' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.chain_ruleSet_allowsAll' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.chain_rule_allows_call' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.charge_all_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.charge_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.charge_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.charge_set' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.charged_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.check_chain_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.check_choices_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.check_spend_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.checked_add_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.checked_add_none' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.checked_add_some' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.checked_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.checked_sub_none' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.checked_sub_some' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.chosenOf_drop' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.chosenOf_drop_nil' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.chosen_denoteAuthorization' depends on axioms: [propext]
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
info: 'RuleCore.Equiv.countFrom_first' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.countFrom_first_from' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.countFrom_map' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.delegate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteAuthorized_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteBudgetError_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteBudget_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteBytes_inj' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteBytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteCapError_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteCap_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteCap_params' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteCond_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteContext_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteEntry_injective' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.denoteError_injective' does not depend on any axioms
---
info: 'RuleCore.Equiv.denoteFunctions_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteNode_injective' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.denoteOutcome_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteParams_injective' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.denoteRecord_history' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteRecord_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteRecord_total' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteRefusal_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteRule_denote_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteRule_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteRules_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteRules_rules_get' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteSigner_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteSigners_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteSpend_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denoteTree_drop' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteTree_injective' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.denoteU32_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteU32_toNat' does not depend on any axioms
---
info: 'RuleCore.Equiv.denoteU64_inj' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteU64_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.denoteU64_toNat' does not depend on any axioms
---
info: 'RuleCore.Equiv.denoteVal_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denote_filter_inList' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denote_filter_inList_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.denote_filter_signerInList' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.drop_rule_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.drop_rule_err' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.drop_rule_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.drop_rule_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.empty_record_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.entries_from_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.entries_from_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.entry_copy_eq' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.evict_body_end' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.evict_body_next' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.evict_body_overflow' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.evict_body_stop' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.evict_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.except_error_bind' does not depend on any axioms
---
info: 'RuleCore.Equiv.except_map_cons_unit' does not depend on any axioms
---
info: 'RuleCore.Equiv.except_ok_bind' does not depend on any axioms
---
info: 'RuleCore.Equiv.expired_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.extends_validity_eq' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.fits_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.functionsRoom_only' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.functions_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.functions_match_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.functions_within_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.functions_without_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.functions_without_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.getElem?_denoteTree' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.i128_bv_inj' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.i128_bv_injective' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.i128_max_eq' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.i128_min_eq' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.i128_val_injective' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.incr_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.incr_eq_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.index_usize_eq' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.length_denoteTree' depends on axioms: [propext]
---
info: 'RuleCore.Equiv.lengthen_cap_period_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.lengthen_cap_period_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.list_set_opt_some' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.loop_all' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.loop_any' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.loop_build' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.loop_build_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.loop_count' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.loop_set_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.lower_cap_limit_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.lower_cap_limit_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.lower_valid_until_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.lower_valid_until_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.max_history_lt_usize' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.max_history_val' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.max_nodes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.max_nodes_le_usize' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.node_copy_eq' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.node_valid_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.nodes_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.nodes_copy_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.params_valid_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
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
info: 'RuleCore.Equiv.raise_threshold_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.raise_threshold_err' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.raise_threshold_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.raise_threshold_lowered' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.raise_threshold_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.record_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.records_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.records_copy_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.refill_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.refill_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_functions_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_functions_err' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_functions_full' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_functions_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_functions_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_functions_room' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_signers_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_signers_err' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_signers_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.remove_signers_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.restrict_functions_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.restrict_functions_err' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.restrict_functions_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.restrict_functions_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.room_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.rule_allows_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.rule_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.rule_within_functions_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.rule_without_functions_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.rule_without_functions_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.rule_without_signers_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.saturating_sub_val' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Equiv.signed_count_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signed_count_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signer_chosen_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signer_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signer_eq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signer_in_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signer_in_first_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signers_chosen_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signers_copy_deref' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signers_copy_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signers_met_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signers_without_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.signers_without_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.slice_get_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.slice_get_mut_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.slice_len_bne' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.slice_len_bne_any' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.slice_len_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.slice_len_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.spend_amount_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.spend_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.stale_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.tree_valid_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.tree_valid_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.u32_val_injective' does not depend on any axioms
---
info: 'RuleCore.Equiv.usize_val_eq_iff' does not depend on any axioms
---
info: 'RuleCore.Equiv.val_copy_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.val_eq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.val_in_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vals_copy_deref' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vals_copy_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vec_deref_val' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vec_eq_of_val' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vec_mk_deref' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vec_new_val' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.vec_val_set_opt' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Equiv.zip_all_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.Derives.allows_all' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.Derives.narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.DerivesAlong.derives' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.DerivesAlong.generation' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.DerivesAlong.generation_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.DerivesAlong.traceNarrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.Narrower.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.Narrower.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.Step.narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.StepAlong.denote_step' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.StepAlong.denote_traceNarrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.StepAlong.generation' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.StepAlong.traceNarrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.add_cap_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.add_cond_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.add_cond_room' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.allows_all_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.allows_all_create' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.allows_all_of_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.allows_all_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.allows_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.allows_create' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.allows_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.authorizeAll_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.authorize_allows_all' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.authorize_contexts_nil_of_stale' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.authorize_generation' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.authorize_not_chosen_of_stale' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.authorize_signers' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.authorize_valid_until' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.budget_delegate_appends' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.budget_refill_raises' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.budget_spend_accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.budget_spend_charges' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.budget_spend_overdrawn' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.budget_spend_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.bytes_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.check_spend_before_newest' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.check_spend_negative' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.check_spend_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.cond_holds_argEq_false_of_kind_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.cond_holds_argEq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.cond_holds_argEq_kind' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.cond_holds_argIn_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.cond_holds_argStrPrefix_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.denoteRules_get' depends on axioms: [propext]
---
info: 'RuleCore.Extracted.denoteSigners_mem_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Extracted.denoteSigners_subset' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Extracted.drop_rule_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.emptyRecords_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.emptyRecords_denote_rules' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.emptyRecords_length' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.empty_record_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.functions_match_anyExcept_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.functions_match_only_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.lengthen_cap_period_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.lower_cap_limit_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.lower_valid_until_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.narrower_of_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.raise_threshold_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.remove_functions_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.remove_signers_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.renumbered_denote' depends on axioms: [propext]
---
info: 'RuleCore.Extracted.renumbered_map' depends on axioms: [propext]
---
info: 'RuleCore.Extracted.restrict_functions_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.rule_allows_call' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.rule_allows_congr_signers' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.rule_allows_extension_false' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.rule_allows_false_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.rule_allows_prefix_false' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.rule_allows_threshold_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runAuthorizations_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runAuthorizations_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runAuthorizations_of_err' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runAuthorizations_window' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runAuthorizations_window_le_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runBudget_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runBudget_spentUnder_eq_spent' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runBudget_spentUnder_le_allowance' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runBudget_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runBudget_withinAllowance' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runSpends_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runSpends_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.runSpends_window' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.signer_eq_delegated_external' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.signer_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.signers_met_all_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.spend_ok_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.traceNarrower_of_denote' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.val_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.val_eq_kind' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.val_eq_other_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Extracted.val_eq_string_symbol' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.Refines.of_eq' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.Refines.refl' depends on axioms: [propext]
---
info: 'RuleCore.Rule.Refines.trans' depends on axioms: [propext]
---
info: 'RuleCore.Rule.allows_congr_signers' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.allows_false_of_lt' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.allows_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.allows_of_allows_addCond' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.allows_of_allows_removeSigners' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.allows_of_allows_restrictScope' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.allows_of_allows_threshold_le' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.allows_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.allows_of_threshold_zero' depends on axioms: [propext]
---
info: 'RuleCore.Rule.expired_eq_false_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.mem_present' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.nodup_present' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.present_length_le_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.refines_addCond' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.refines_removeSigners' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.refines_restrictScope' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.signed_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.signed_congr_signers' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.signed_eraseDups_signers' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.signed_false_of_lt' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.signed_iff' depends on axioms: [propext]
---
info: 'RuleCore.Rule.signed_iff_of_threshold_eq' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.Rule.signed_of_signed_removeSigners' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.signed_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.Rule.signed_of_threshold_zero' depends on axioms: [propext]
---
info: 'RuleCore.Rule.stale_eq_false_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleCap.NarrowerOpt.refl' depends on axioms: [propext]
---
info: 'RuleCore.RuleCap.NarrowerOpt.trans' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.Derives.narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.RecordsRel.empty' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.RecordsRel.narrowLen' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.RecordsRel.rel' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.RecordsRel.wideLen' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.Refines.authorize' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.Refines.authorizeAll' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.Refines.charge' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.Refines.foldlM_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.Refines.refl' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.Refines.set' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.Refines.traceNarrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.Refines.trans' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.TraceNarrower.refl' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.TraceNarrower.trans' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.addCap_eq_capPresent_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.addCap_eq_invalidCap_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.addCap_eq_noSuchRule_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.addCap_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.addCap_refines' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.addCond_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.addCond_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.allowsAll_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.allowsAll_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.allowsAll_nil' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.allowsAll_of_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.allowsAll_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.allows_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.allows_eraseDups' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.allows_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.allows_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuateAll_capsValid' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuateAll_derives' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.attenuateAll_generation' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuateAll_generation_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuateAll_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuateAll_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuateAll_traceNarrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuate_capsValid' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuate_generation' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuate_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuate_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.attenuate_traceNarrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.authorize_allowsAll' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.authorize_chosen' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.authorize_contexts_nil_of_stale' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.authorize_current' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.authorize_eq_ok_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.authorize_generation' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.authorize_length' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.authorize_not_chosen_of_stale' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.authorize_signers' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.authorize_validUntil' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.capsValid_set' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.charge_get_capped' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.charge_get_ne' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.charge_length' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.charge_of_cap_none' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.checkChoice_ok_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.checkSigners_ok_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.dropRule_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.dropRule_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.dropRule_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.emptyRecords_get' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.emptyRecords_length' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.foldlM_charge_get' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.foldlM_charge_get_of_cap_none' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.foldlM_charge_length' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.lengthenCapPeriod_eq_noCap_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.lengthenCapPeriod_eq_noSuchRule_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.lengthenCapPeriod_eq_periodShortened_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.lengthenCapPeriod_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.lengthenCapPeriod_refines' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.lowerCapLimit_eq_invalidCap_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.lowerCapLimit_eq_limitRaised_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.lowerCapLimit_eq_noCap_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.lowerCapLimit_eq_noSuchRule_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.lowerCapLimit_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.lowerCapLimit_refines' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.lowerValidUntil_eq_noSuchRule_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.lowerValidUntil_eq_validUntilRaised_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.lowerValidUntil_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.lowerValidUntil_refines' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.mem_charged' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.modifyRule_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.modifyRule_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.modifyRule_refines' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.narrower_refl' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.narrower_trans' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.period_le_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.period_le_limit_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.raiseThreshold_eq_noSuchRule_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.raiseThreshold_eq_thresholdLowered_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.raiseThreshold_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.raiseThreshold_refines' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.removeSigners_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.removeSigners_narrower' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.restrictScope_eq_error_iff' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.restrictScope_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.rules_ofRules' does not depend on any axioms
---
info: 'RuleCore.RuleSet.runAll_charged' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.run_cons' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.run_eq_window' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.run_get' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.run_get_of_cap_none' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.run_history_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.RuleSet.run_nil' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.set_cap_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.set_validUntil_narrower' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.signerChosen_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.spent_eq_recorded' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.RuleSet.step_of_error' depends on axioms: [propext]
---
info: 'RuleCore.RuleSet.window_le_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.foldlM_except_append' depends on axioms: [propext]
---
info: 'RuleCore.foldlM_except_cons' depends on axioms: [propext]
---
info: 'RuleCore.forM_except_ok_iff' depends on axioms: [propext, Quot.sound]
---
info: 'RuleCore.length_eq_of_nodup_of_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: 'RuleCore.nodup_eraseDups' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print_package_axioms
