-- A stand-in for formal/RuleCore/Axioms.lean: only its #print_package_axioms
-- record matters to the checker. `Fixture.only_in_a_comment` is named here and
-- nowhere in the record.

/--
info: 'Fixture.narrower_trans' does not depend on any axioms
---
info: 'Fixture.allows_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print_package_axioms
