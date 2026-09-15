import Imscribing.IUTT

/-! Dependency audit for every theorem in IUTT.lean.
Run lake env lean Imscribing/IUTT_Audit.lean.
The audit reports foundations explicitly; no theorem may depend on sorryAx.
-/

#print axioms Imscribing.IUTT.sixteen_states
#print axioms Imscribing.IUTT.support_union
#print axioms Imscribing.IUTT.support_intersection
#print axioms Imscribing.IUTT.binary_recovery
#print axioms Imscribing.IUTT.binary_disjoint
#print axioms Imscribing.IUTT.ternary_recovery
#print axioms Imscribing.IUTT.ternary_disjoint
#print axioms Imscribing.IUTT.polarity_involution
#print axioms Imscribing.IUTT.identity_transport
#print axioms Imscribing.IUTT.theta_terminal
#print axioms Imscribing.IUTT.discrepancy_terminal
#print axioms Imscribing.IUTT.unequal_branches_recover
#print axioms Imscribing.IUTT.erasure_idempotent
#print axioms Imscribing.IUTT.erasure_fixed_iff
#print axioms Imscribing.IUTT.theta_shadow
#print axioms Imscribing.IUTT.discrepancy_shadow
#print axioms Imscribing.IUTT.four_preimages_of_falsity
#print axioms Imscribing.IUTT.erasure_not_injective
#print axioms Imscribing.IUTT.no_erasure_decoder
#print axioms Imscribing.IUTT.four_retraction
#print axioms Imscribing.IUTT.erasure_is_four_projection
#print axioms Imscribing.IUTT.boolean_shadow_lands_in_centre
#print axioms Imscribing.IUTT.boolean_shadow_not_injective
#print axioms Imscribing.IUTT.coreflection
#print axioms Imscribing.IUTT.reflection
#print axioms Imscribing.IUTT.contradictory_closure_not_boolean
#print axioms Imscribing.IUTT.information_closure_properties
#print axioms Imscribing.IUTT.alien_not_ring_hom
#print axioms Imscribing.IUTT.non_explosion
#print axioms Imscribing.IUTT.update_preserves_state
#print axioms Imscribing.IUTT.terminal_scalar
#print axioms Imscribing.IUTT.branches_reconnect
#print axioms Imscribing.IUTT.finite_terminal_has_no_successor
#print axioms Imscribing.IUTT.finite_no_return
#print axioms Imscribing.IUTT.boundary_return
#print axioms Imscribing.IUTT.reconnection_return_triple
#print axioms Imscribing.IUTT.phase_twelve
#print axioms Imscribing.IUTT.invariant_nat_shift
#print axioms Imscribing.IUTT.phase_invariant_iff_constant
#print axioms Imscribing.IUTT.phase_dependent_example
#print axioms Imscribing.IUTT.Filtration.degree_mem
#print axioms Imscribing.IUTT.Filtration.degree_le_iff
#print axioms Imscribing.IUTT.evaluation_no_factor
#print axioms Imscribing.IUTT.same_blind_value
#print axioms Imscribing.IUTT.different_weighted_values
#print axioms Imscribing.IUTT.weighted_does_not_factor
#print axioms Imscribing.IUTT.degree_atOne
#print axioms Imscribing.IUTT.degree_atTwo
#print axioms Imscribing.IUTT.filtered_nonvacuity
#print axioms Imscribing.IUTT.tensor_same_shadow
#print axioms Imscribing.IUTT.tensor_different_weights
#print axioms Imscribing.IUTT.tensor_weighted_no_factor
#print axioms Imscribing.IUTT.tensor_degree_agrees
#print axioms Imscribing.IUTT.tensor_positions
