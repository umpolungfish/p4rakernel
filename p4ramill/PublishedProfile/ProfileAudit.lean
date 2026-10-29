import InjectionConnection
import NavierStokes.LocalResidualFlatness

/-! Audit the selected cancellation schedule, assembled endpoint witness,
actual whole-space candidate and local injection bridge together. -/

#print axioms NavierStokes.LocalResidualFlatness.selected_schedule
#print axioms NavierStokes.ActualCandidateAssembly.selected_witness
#print axioms NavierStokesR3.ActualCandidate.selected_candidate_one
#print axioms InjectionConnection.residual_eq_published
#print axioms InjectionConnection.injection_eq_published_force
#print axioms InjectionConnection.actual_profile_smooth_injection
