import Mathlib

/-!
# Erdős problem #138

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

/-- Axiom (honest) : Erdős problem #138 (van der Waerden number asymptotic growth, open problem). -/
axiom ax_erdos_problem_138
    (W : ℕ → ℕ)
    (h_W : ∀ k, W k = sInf { N | ∀ c : ℕ → Fin 2, ∃ a d : ℕ, d ≥ 1 ∧ a + k * d ≤ N ∧ ∀ i < k, c (a + i * d) = c a }) :
    Filter.Tendsto (fun k => (W k : ℝ)^(1/(k : ℝ) : ℝ)) Filter.atTop Filter.atTop

theorem erdos_problem_138
    (W : ℕ → ℕ)
    (h_W : ∀ k, W k = sInf { N | ∀ c : ℕ → Fin 2, ∃ a d : ℕ, d ≥ 1 ∧ a + k * d ≤ N ∧ ∀ i < k, c (a + i * d) = c a }) :
    Filter.Tendsto (fun k => (W k : ℝ)^(1/(k : ℝ) : ℝ)) Filter.atTop Filter.atTop :=
  ax_erdos_problem_138 W h_W
