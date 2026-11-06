import Mathlib

/-!
# Erdős problem #107 — the Happy Ending problem

Prize: $500. The statement is open; the database calls it falsifiable because
a finite counterexample could refute it. No theorem below is claimed to solve
the general problem.

For `n ≥ 3`, the target is the exact equality `f n = 2^(n - 2) + 1`. The
previous file used an axiom to prove only `f n ≥ n`, which is not the target.
-/

open scoped BigOperators
open Finset
open EuclideanGeometry

namespace Erdos107

/-- A finite point set has no three distinct collinear points. -/
def GeneralPosition (A : Finset (ℝ × ℝ)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
    x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))

/-- The point set contains an `n`-point convex polygon. -/
def HasConvexNGon (n : ℕ) (A : Finset (ℝ × ℝ)) : Prop :=
  ∃ B : Finset (ℝ × ℝ), B ⊆ A ∧ B.card = n ∧
    ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ))

/-- Point counts for which every general-position configuration contains an
`n`-gon. -/
def cardSet (n : ℕ) : Set ℕ :=
  {N | ∀ A : Finset (ℝ × ℝ), A.card = N → GeneralPosition A → HasConvexNGon n A}

/-- The least number of points forcing a convex `n`-gon. -/
noncomputable def f (n : ℕ) : ℕ := sInf (cardSet n)

/-- The exact Erdős–Szekeres assertion in problem #107. -/
def ErdosProblem107Statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → f n = 2 ^ (n - 2) + 1

end Erdos107
