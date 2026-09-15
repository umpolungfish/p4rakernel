import Mathlib

/-!
# Erdős problem #89

Prize: $500.  Status as catalogued: **OPEN**.

For A ⊂ ℝ² with |A| = n, let g(A) be the number of distinct distances.
Erdős conjectured g(A) ≥ c·n / √log n for some c > 0.

This is equivalent to Problem #95 in a different formulation.
-/

open scoped BigOperators
open Finset

def distances (A : Finset (ℝ × ℝ)) : Finset ℝ :=
  (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)

/-- Guth–Katz: g(A) ≥ C·n / log n for some C > 0.
This implies the weaker bound g(A) ≥ C·n / √log n. -/
theorem guth_katz_implies_erdos89 :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, ∀ A : Finset (ℝ × ℝ),
      A.card = n → C * (n / Real.sqrt (Real.log n)) ≤ (distances A).card := by sorry

/-- The original Erdős problem #89 statement. -/
theorem erdos_problem_89
    (A : Finset (ℝ × ℝ))
    (h_distinct : A.card = A.ncard) :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, A.card = n → C * (n / Real.sqrt (Real.log n)) ≤ (distances A).card := by
  sorry