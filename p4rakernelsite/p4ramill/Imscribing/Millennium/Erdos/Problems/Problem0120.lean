import Mathlib

/-!
# Erdős problem #120

Prize: 00.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/120](https://www.erdosproblems.com/120)

Erdős similarity problem:
Let A ⊆ ℝ be an infinite set. Must there be a set E ⊆ ℝ
of positive measure which does not contain any set of the shape a · A + b
for any a, b ∈ ℝ with a ≠ 0?
-/

open Set MeasureTheory

namespace Erdos120

/-- Property that E avoids all affine copies of A. -/
def AvoidsAffineCopies (A E : Set ℝ) : Prop :=
  ∀ a b : ℝ, a ≠ 0 → ¬ (image (fun x => a * x + b) A ⊆ E)

/-- The Erdős problem #120 statement. -/
def ErdosProblem120Statement : Prop :=
  ∀ A : Set ℝ, A.Infinite → ∃ E : Set ℝ, MeasurableSet E ∧ 0 < volume E ∧ AvoidsAffineCopies A E

/-- Axiom (honest) : Erdős problem #120 (open problem). -/
axiom ax_erdos_problem_120 : ErdosProblem120Statement

theorem erdos_problem_120 : ErdosProblem120Statement :=
  ax_erdos_problem_120

end Erdos120
