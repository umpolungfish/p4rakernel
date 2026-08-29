import Mathlib

/-!
# Erdős problem #161

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_161
    (t n : ℕ)
    (α : ℝ)
    (h_α : 0 ≤ α ∧ α < 1/2)
    (F : ℝ → ℕ → ℕ)
    (h_F : ∀ α m, F α m = sInf { M | ∃ c : Fin (M.choose t) → Fin 2,
      ∀ X : Finset (Fin M), X.card ≥ m → (∃ S : Finset (Fin M), S.card = t ∧ S ⊆ X ∧ ∀ i ∈ S, c i = 0) ∧
      (∃ S : Finset (Fin M), S.card = t ∧ S ⊆ X ∧ ∀ i ∈ S, c i = 1) }) :
    (ContinuousOn (fun α' => F α' n) {x : ℝ | 0 ≤ x ∧ x < 1/2}) ∨
      ∃ α' : ℝ, 0 ≤ α' ∧ α' < 1/2 ∧ F α' n ≠ F α n := by
  sorry
