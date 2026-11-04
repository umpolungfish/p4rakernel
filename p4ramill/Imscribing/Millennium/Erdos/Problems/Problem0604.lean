import Mathlib

/-!
# Erdős problem #604

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset
open Classical

theorem erdos_problem_604
    (A : Finset (ℝ × ℝ))
    (h_distinct : A.card = (A : Set (ℝ × ℝ)).ncard) :
    ∃ x ∈ A, ∃ C > 0, C * (A.card / Real.sqrt (Real.log A.card)) ≤ ((A.image (fun y => dist x y)).filter (· ≠ 0)).card := by
  sorry
