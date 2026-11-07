import Mathlib

axiom bad : (0 : ℕ) = 1

theorem contradiction : False := by
  have h : (0 : ℕ) ≠ 1 := by decide
  exact h bad

#print axioms contradiction