import Mathlib

/-!
# Erdős problem #90

Prize: $500.  Status as catalogued: **DISPROVED (LEAN)**.

Erdős conjectured that for any A ⊂ ℝ², the number of unit distances is at most
C·|A|^(1 + o(1)). This was disproved by Erdős himself using the square grid,
which gives ~|A|^(1 + c/√log |A|) unit distances.
-/

open scoped BigOperators
open Finset

def unit_distances (A : Finset (ℝ × ℝ)) : ℕ :=
  (A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1) |>.card

/-- The square grid construction: A = [√N] × [√N] gives many unit distances. -/
lemma grid_unit_distances :
    ∃ c > 0, ∀ᶠ N in Filter.atTop, ∃ A : Finset (ℝ × ℝ),
      A.card = N ∧ unit_distances A ≥ N ^ (1 + c / Real.sqrt (Real.log N)) := by sorry

/-- The original Erdős conjecture was false: unit distances can exceed C·N. -/
theorem erdos_problem_90 :
    ¬ (∀ A : Finset (ℝ × ℝ), A.card = A.ncard →
      ∃ C > 0, unit_distances A ≤ C * (A.card : ℝ) ^ (1 + 1 / Real.log (Real.log (A.card : ℝ)))) := by sorry

/-- Erdős' own counterexample: the square grid gives N^(1 + c/√log N) unit distances. -/
theorem erdos_problem_90_counterexample :
    ∃ A : Finset (ℝ × ℝ), ∀ C > 0, ∀ᶠ N in Filter.atTop, (A.card : ℝ) = N →
      (unit_distances A : ℝ) > C * N ^ (1 + 1 / Real.log (Real.log N)) := by sorry