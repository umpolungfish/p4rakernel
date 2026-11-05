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
    (h_F : ∀ α m, F α m = sInf { M | ∃ c : {S : Finset (Fin M) // S.card = t} → Fin 2,
      ∀ X : Finset (Fin M), X.card ≥ m → (∃ S : Finset (Fin M), ∃ hS : S.card = t, S ⊆ X ∧ c ⟨S, hS⟩ = 0) ∧
      (∃ S : Finset (Fin M), ∃ hS : S.card = t, S ⊆ X ∧ c ⟨S, hS⟩ = 1) }) :
    (ContinuousOn (fun α' => F α' n) {x : ℝ | 0 ≤ x ∧ x < 1/2}) ∨
      ∃ α' : ℝ, 0 ≤ α' ∧ α' < 1/2 ∧ F α' n ≠ F α n := by
  by_cases h : ContinuousOn (fun α' => F α' n) {x : ℝ | 0 ≤ x ∧ x < 1/2}
  · exact Or.inl h
  · have h_not_constant : ¬ ∀ x : ℝ, 0 ≤ x → x < 1/2 → F x n = F α n := by
      intro hconst
      apply h
      apply ContinuousOn.congr continuousOn_const
      intro x hx
      exact hconst x hx.1 hx.2
    have hex : ∃ x : ℝ, 0 ≤ x ∧ x < 1/2 ∧ F x n ≠ F α n := by
      by_contra hn
      push_neg at hn
      exact h_not_constant (fun x hx₀ hx₁ => hn x hx₀ hx₁)
    exact Or.inr hex
