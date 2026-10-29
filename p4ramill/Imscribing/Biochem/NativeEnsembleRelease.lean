import Imscribing.Biochem.PrimaLogicaMechanicalGlut
import Imscribing.Paraconsistent.TemporalSemantics

enable_trilattice

/-! Re-entry of the retained release coordinate into the existing native
two-preference realization. This is an explicit realization of the ensemble
continuation, with both source supports and the banked preference retained.
The quadratic completion determines its force readout at the new boundary. -/
namespace Imscribing.Biochem.NativeEnsembleRelease

noncomputable def center (p n z : ℝ) : ℝ :=
  Real.sqrt (n * (p * n + z ^ 2) / (p + n))

theorem center_squared (p n z : ℝ) (hp : 0 < p) (hn : 0 < n) :
    center p n z ^ 2 = n * (p * n + z ^ 2) / (p + n) := by
  apply Real.sq_sqrt
  positivity

theorem prepared_center (p n : ℝ) (hp : 0 < p) (hn : 0 < n) :
    center p n n = n := by
  unfold center
  have h : n * (p * n + n ^ 2) / (p + n) = n ^ 2 := by
    field_simp
  rw [h, Real.sqrt_sq (le_of_lt hn)]

/-- Both opposed preferences remain in the same potential. Their current
separation is the completion of the retained accessible and banked strain. -/
theorem complete_joint_potential (p n z r q : ℝ) (hn : n ≠ 0)
    (hq : (p + n) * q ^ 2 = n * (p * n + z ^ 2)) :
    p * r ^ 2 / 2 + n * (r - (p + n) * q / n) ^ 2 / 2 =
      (p + n) * (r - q) ^ 2 / 2 + p ^ 2 * n / 2 + p * z ^ 2 / 2 := by
  field_simp
  linear_combination p * hq

theorem retained_bank_and_accessible (p n z : ℝ) :
    p ^ 2 * n / 2 + p * z ^ 2 / 2 = p * (p * n + z ^ 2) / 2 := by ring

theorem force_changes_with_retained_center (p n r a b : ℝ) :
    (p + n) * (r - a) - (p + n) * (r - b) = (p + n) * (b - a) := by ring

/-- The whole conformation's current distance determines the internal
release target. Bank boundaries restrict this target in execution. -/
theorem joint_release_minimum (p n r q : ℝ) (hn : n ≠ 0) (hk : p + n ≠ 0) :
    (p + n) * (r - q) ^ 2 / 2 + p * (p + n) * q ^ 2 / (2 * n) =
      (p + n) ^ 2 / (2 * n) * (q - r * n / (p + n)) ^ 2 + p * r ^ 2 / 2 := by
  field_simp
  <;> ring

theorem different_release_is_a_necessary_distinction (p n r a b : ℝ)
    (hp : 0 < p) (hn : 0 < n) (different : a ≠ b) :
    (p + n) * (r - a) ≠ (p + n) * (r - b) := by
  intro same
  have h : (p + n) * (b - a) = 0 := by
    rw [← force_changes_with_retained_center p n r a b, same]
    ring
  rcases mul_eq_zero.mp h with zero | zero
  · linarith
  · exact different (by linarith)

#print axioms center_squared
#print axioms prepared_center
#print axioms complete_joint_potential
#print axioms force_changes_with_retained_center
#print axioms joint_release_minimum
#print axioms different_release_is_a_necessary_distinction
end Imscribing.Biochem.NativeEnsembleRelease
