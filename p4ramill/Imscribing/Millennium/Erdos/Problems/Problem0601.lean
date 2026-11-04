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
    (h_lim : Order.IsSuccLimit α) :
    (∀ G : SimpleGraph α.ToType, (∃ p : ℕ → α.ToType, StrictMono p ∧ ∀ n : ℕ, G.Adj (p n) (p (n+1))) ∨
      ∃ I : Set α.ToType, Ordinal.type ((· < ·) : I → I → Prop) = α ∧ ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) := by
  sorry
