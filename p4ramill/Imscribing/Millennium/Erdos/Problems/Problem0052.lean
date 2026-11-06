import Mathlib

/-!
# Erdős problem #52

Prize: 50.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/52](https://www.erdosproblems.com/52)

Erdős–Szemerédi sum-product conjecture:
Let $ be a finite set of integers. Is it true that for every $\varepsilon > 0$,
$\max(|A+A|, |AA|) \gg_\varepsilon |A|^{2 - \varepsilon}0
-/

open scoped Pointwise

namespace Erdos52

/-- The Erdős problem #52 statement (Erdős–Szemerédi sum-product conjecture). -/
def ErdosProblem52Statement : Prop :=
  ∀ ε > (0 : ℝ), ε < 1 → ∃ C > (0 : ℝ), ∀ A : Finset ℤ,
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

/-- Axiom (honest) : Erdős problem #52 (open problem). -/
axiom ax_erdos_problem_52 : ErdosProblem52Statement

theorem erdos_problem_52 : ErdosProblem52Statement :=
  ax_erdos_problem_52

end Erdos52
