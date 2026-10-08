import ProofAudit

#assert_standard_axioms True.intro
#assert_standard_axioms propext
#assert_standard_axioms Classical.choice
#assert_standard_axioms Quot.sound

axiom unexpected_axiom : False

theorem transitive_unproved : True := False.elim unexpected_axiom

/-- error: transitive_unproved depends on unexpected axioms: [unexpected_axiom] -/
#guard_msgs in
#assert_standard_axioms transitive_unproved

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem incomplete_proof : False := by sorry

/-- error: incomplete_proof depends on unexpected axioms: [sorryAx] -/
#guard_msgs in
#assert_standard_axioms incomplete_proof
