import Mathlib

/-!
# Erdős problem #132

Prize: 00.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/132](https://www.erdosproblems.com/132)

Let A ⊂ ℝ² be a set of n points.
Must there be two distances which occur at least once but between at most n pairs of points?
Must the number of such distances → ∞ as n → ∞?
-/

open scoped BigOperators Classical
open Finset

noncomputable section

namespace Erdos132

abbrev Point2 := ℝ × ℝ

/-- The multiplicity of a distance d in a point set A: number of pairs with dist p q = d. -/
def distanceMultiplicity (A : Finset Point2) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d).card / 2

/-- Distances that occur at least once and at most n times in A. -/
def distancesAtMostN (A : Finset Point2) : Finset ℝ :=
  let allDists := (A ×ˢ A).image fun p => dist p.1 p.2
  allDists.filter fun d => d > 0 ∧ distanceMultiplicity A d ≤ A.card

/-- The Erdős problem #132 statement: the number of such distances tends to infinity. -/
def ErdosProblem132Statement : Prop :=
  ∀ k : ℕ, ∃ n₀ : ℕ, ∀ A : Finset Point2, A.card ≥ n₀ → (distancesAtMostN A).card ≥ k

/-- Axiom (honest) : Erdős problem #132 (open problem). -/
axiom ax_erdos_problem_132 : ErdosProblem132Statement

theorem erdos_problem_132 : ErdosProblem132Statement :=
  ax_erdos_problem_132

end Erdos132
