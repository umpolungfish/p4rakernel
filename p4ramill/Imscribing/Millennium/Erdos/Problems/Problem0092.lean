import Mathlib

/-!
# Erdős problem #92

Prize: $500.  Status as catalogued: **DISPROVED**.

Erdős conjectured a bound on the minimum number of distances from a point to all others
in a set of n points. This was disproved by showing configurations where some point
has many distances.
-/

open scoped BigOperators
open Finset

/-- The number of distances from x to other points in A. -/
def distances_from (x : ℝ × ℝ) (A : Finset (ℝ × ℝ)) : Finset ℝ :=
  (A.image (fun y => dist x y)).filter (fun d => d ≠ 0)

/-- The minimum over x ∈ A of |distances_from x A|. -/
def min_distances (A : Finset (ℝ × ℝ)) : ℕ :=
  A.image (fun x => distances_from x A) |>.image Finset.card |>.min' (by sorry)

/-- Erdős' conjecture was false: there exist configurations where the minimum is large. -/
theorem erdos_problem_92 :
    ¬ (∀ A : Finset (ℝ × ℝ), ∃ x ∈ A, min_distances A ≤ (A.card : ℕ) ^ (1 / Real.log (Real.log (A.card : ℕ)))) := by sorry

/-- Counterexample using a regular polygon or grid. -/
lemma erdos_problem_92_counterexample :
    ∃ (A : Finset (ℝ × ℝ)), ∀ C > 0, ∀ᶠ N in Filter.atTop, (A.card : ℕ) = N →
      min_distances A > C * N ^ (1 / Real.log (Real.log N)) := by sorry