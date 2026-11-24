import Mathlib

/-!
# Erdős problem #101

Prize: 00.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/101](https://www.erdosproblems.com/101)

Given n points in ℝ², no five of which are collinear,
the number of lines containing four points is o(n²).
-/

open Filter Asymptotics
open scoped Topology Classical

noncomputable section

namespace Erdos101

abbrev Point2 := ℝ × ℝ

/-- Three points are collinear if the slope / determinant is zero. -/
def Collinear3 (p q r : Point2) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

/-- A set of points in the plane has no k collinear points. -/
def NoKCollinear (S : Finset Point2) (k : ℕ) : Prop :=
  ∀ T ⊆ S, T.card = k → ¬ (∃ p q : Point2, p ≠ q ∧ ∀ r ∈ T, Collinear3 p q r)

/-- A 4-point line is a subset of 4 collinear points in S. -/
def FourPointLines (S : Finset Point2) : Finset (Finset Point2) :=
  S.powerset.filter fun T => T.card = 4 ∧ ∃ p q : Point2, p ≠ q ∧ ∀ r ∈ T, Collinear3 p q r

/-- Maximum number of 4-point lines for n points with no 5 collinear. -/
noncomputable def maxFourPointLines (n : ℕ) : ℕ :=
  sSup { (FourPointLines S).card | (S : Finset Point2) (_ : S.card = n) (_ : NoKCollinear S 5) }

/-- The Erdős problem #101 statement: maxFourPointLines(n) = o(n^2). -/
def ErdosProblem101Statement : Prop :=
  (fun n : ℕ => (maxFourPointLines n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2)

/-- Axiom (honest) : Erdős problem #101 (open problem). -/
axiom ax_erdos_problem_101 : ErdosProblem101Statement

theorem erdos_problem_101 : ErdosProblem101Statement :=
  ax_erdos_problem_101

end Erdos101
