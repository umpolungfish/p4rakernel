import Mathlib

/-!
# Erdős problem #107

Prize: $500.  Status as catalogued: **FALSIFIABLE**.

"FALSIFIABLE" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_107
    (f : ℕ → ℕ)
    (h_f : ∀ n, f n = sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x y z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬Collinear x y z) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent B }) :
    f n = 2^(n - 2) + 1 := by
  sorry
