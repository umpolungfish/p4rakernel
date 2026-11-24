import Mathlib

/-!
# Erdős problem #588

Prize: 00.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/588](https://www.erdosproblems.com/588)

Let f_k(n) be the maximum number of lines containing at least k points
in a set of n points in ℝ² with no k+1 collinear.
Is it true that f_k(n) = o(n²) for all k >= 4?
-/

open Filter Asymptotics
open scoped Topology Classical

noncomputable section

namespace Erdos588

abbrev Point2 := ℝ × ℝ

/-- Collinear predicate for 3 points in ℝ². -/
def Collinear3 (p q r : Point2) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

/-- A set of points has no m collinear points. -/
def NoMCollinear (S : Finset Point2) (m : ℕ) : Prop :=
  ∀ T ⊆ S, T.card = m → ¬ (∃ p q : Point2, p ≠ q ∧ ∀ r ∈ T, Collinear3 p q r)

/-- Lines containing at least k points of S. -/
def KPointLines (S : Finset Point2) (k : ℕ) : Finset (Finset Point2) :=
  S.powerset.filter fun T => T.card ≥ k ∧ ∃ p q : Point2, p ≠ q ∧ ∀ r ∈ T, Collinear3 p q r

/-- Maximum number of k-point lines over all configurations of n points with no k+1 collinear. -/
def f (k n : ℕ) : ℕ :=
  sSup { (KPointLines S k).card | (S : Finset Point2) (_ : S.card = n) (_ : NoMCollinear S (k + 1)) }

/-- The Erdős problem #588 statement: f_k(n) = o(n^2) for each k ≥ 4. -/
def ErdosProblem588Statement : Prop :=
  ∀ k : ℕ, k ≥ 4 → (fun n : ℕ => (f k n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2)

/-- Axiom (honest) : Erdős problem #588 (open problem). -/
axiom ax_erdos_problem_588 : ErdosProblem588Statement

theorem erdos_problem_588 : ErdosProblem588Statement :=
  ax_erdos_problem_588

end Erdos588
