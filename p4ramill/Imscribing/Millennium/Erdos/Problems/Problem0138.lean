import Mathlib

/-!
# Erdős problem #138

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_138
    (W : ℕ → ℕ)
    (h_W : ∀ k, W k = sInf { N | ∀ c : Fin N → Fin 2, ∃ a d : ℕ, d ≥ 1 ∧ a + k * d ≤ N ∧ ∀ i < k, c (a + i * d) = c a }) :
    Filter.Tendsto (fun k => (W k)^(1/k : ℝ)) Filter.atTop Filter.atTop := by
  sorry
