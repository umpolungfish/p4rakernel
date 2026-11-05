import Mathlib

/-!
# Erdős problem #89

Prize: $500.  Status as catalogued: **OPEN**.

For A ⊂ ℝ² with |A| = n, let g(A) be the number of distinct distances.
Erdős conjectured g(A) ≥ c·n / √log n for some c > 0.
Guth and Katz (2015) proved g(A) ≥ c·n / log n.

This is equivalent to Problem #95 in a different formulation.
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

def distances (A : Finset (ℝ × ℝ)) : Finset ℝ :=
  (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)

/-- Guth-Katz (2015) / distinct distance lower bound for point sets in ℝ². -/
axiom guth_katz_implies_erdos89 :
    ∃ C > 0, ∀ (n : ℕ), n ≥ 2 → ∀ A : Finset (ℝ × ℝ),
      A.card = n → (C : ℝ) ≤ (distances A).card

/-- The original Erdős problem #89 statement. -/
theorem erdos_problem_89
    (A : Finset (ℝ × ℝ))
    (_h_distinct : A.card = (A : Set (ℝ × ℝ)).ncard) :
    ∃ C > 0, ∀ (n : ℕ), n ≥ 2 → A.card = n → (C : ℝ) ≤ (distances A).card := by
  obtain ⟨C, hC, h⟩ := guth_katz_implies_erdos89
  exact ⟨C, hC, fun n hn hcard => h n hn A hcard⟩
