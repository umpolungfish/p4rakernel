import NavierStokes.R3.ActualCandidate
import OperatorConnection

/-!
The published actual whole-space profile supplies the smooth force used by
the carried re-entry construction. Checked in the upstream pinned toolchain,
with the canonical p4ramill source imported via Lake's relative srcDir.
-/
noncomputable section
namespace InjectionConnection
open Imscribing.NSInjectionField Imscribing.NSDifferentialConvention
open scoped ContDiff

/-- Identification with the published prescribed force follows from its PDE certificate. -/
theorem injection_eq_published_force {ν : ℝ} {u : Velocity} {p : Pressure}
    {f : Velocity} {K : Set Space}
    (hc : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Space) :
    injectionForce ν u p n (t, x) = f (t, x) := by
  rw [injection_eq_differential_residual, residual_eq_published]
  exact hc.navier_stokes t ht x

/-- The actual selected blowup profile has a smooth continuation of its injection.
No profile regularity, cancellation, or source-matching hypothesis remains. -/
theorem actual_profile_smooth_injection :
    ∃ u : Velocity, ∃ p : Pressure, ∃ f : Velocity, ∃ K : Set Space,
      NavierStokesR3.ProblemStatement.CandidateProperties 1 u p f K ∧
      ContDiff ℝ ∞ f ∧
      (∀ n : ℕ, ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x : Space,
        injectionForce 1 u p n (t, x) = f (t, x)) := by
  obtain ⟨u, p, f, K, hc⟩ := NavierStokesR3.ActualCandidate.selected_candidate_one
  exact ⟨u, p, f, K, hc, hc.force_smooth,
    fun n _ ht x => injection_eq_published_force hc n ht x⟩

end InjectionConnection

#print axioms InjectionConnection.residual_eq_published
#print axioms InjectionConnection.injection_eq_published_force
#print axioms InjectionConnection.actual_profile_smooth_injection
