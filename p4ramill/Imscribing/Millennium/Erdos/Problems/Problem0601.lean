import Mathlib

/-!
# Erdős problem #601

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_601
    (α : Ordinal)
    (h_lim : IsLimit α) :
    (∀ G : SimpleGraph α, (∃ p : α → α, StrictMono p ∧ ∀ n : ℕ, G.Adj (p n) (p (n+1))) ∨
      ∃ I : Set α, I.OrderType = α ∧ ∀ x y ∈ I, x ≠ y → ¬ G.Adj x y) := by
  sorry
