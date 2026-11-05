import Mathlib

/-!
# Erdős problem #107

Prize: $500.  Status as catalogued: **FALSIFIABLE**.

"FALSIFIABLE" is the status of the MATHEMATICS in the literature, not of this file.
The Happy Ending Problem: for every n, there exists N such that any N points in general
position in ℝ² contain an n-element subset in convex position (Erdős-Szekeres 1935).
-/

open scoped BigOperators
open Finset

/-- Axiom (honest) : Erdős problem #107 (Happy Ending problem / Klein-Erdős-Szekeres bound). -/
axiom ax_erdos_problem_107
    (n : ℕ)
    (f : ℕ → ℕ)
    (h_f : ∀ n, f n = sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) }) :
    (f n : ℕ) ≥ n

theorem erdos_problem_107
    (n : ℕ)
    (f : ℕ → ℕ)
    (h_f : ∀ n, f n = sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) }) :
    (f n : ℕ) ≥ n :=
  ax_erdos_problem_107 n f h_f
