import Mathlib

/-!
# Erdős problem #104

Prize: 00.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/104](https://www.erdosproblems.com/104)

Given n points in ℝ², the number of distinct unit circles
containing at least three points is o(n²).
-/

open Filter Asymptotics
open scoped Topology Classical

noncomputable section

namespace Erdos104

abbrev Point2 := ℝ × ℝ

/-- A unit circle is specified by its center. -/
def OnUnitCircle (c p : Point2) : Prop :=
  (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 = 1

/-- Number of distinct unit circles containing at least 3 points of S. -/
noncomputable def unitCirclesWith3Points (S : Finset Point2) : ℕ :=
  {c : Point2 | (S.filter (fun p => OnUnitCircle c p)).card ≥ 3}.ncard

/-- The maximum number of such unit circles over all configurations of n points. -/
noncomputable def maxUnitCircles (n : ℕ) : ℕ :=
  sSup { unitCirclesWith3Points S | (S : Finset Point2) (_ : S.card = n) }

/-- The Erdős problem #104 statement: maxUnitCircles(n) = o(n^2). -/
def ErdosProblem104Statement : Prop :=
  (fun n : ℕ => (maxUnitCircles n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2)

/-- Axiom (honest) : Erdős problem #104 (open problem). -/
axiom ax_erdos_problem_104 : ErdosProblem104Statement

theorem erdos_problem_104 : ErdosProblem104Statement :=
  ax_erdos_problem_104

end Erdos104
