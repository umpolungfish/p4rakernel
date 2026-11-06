import Mathlib

/-!
# Erdős problem #30

Prize: 000.  Status as catalogued: **OPEN**.

*References:*
* [erdosproblems.com/30](https://www.erdosproblems.com/30)
* [ErTu41] Erdős, P. and Turán, P., *On a problem of Sidon in additive number theory, and on some related problems*.

Let (N)$ be the maximum size of a Sidon set in {1, ..., N}.
Is it true that for every ε > 0, (N) = \sqrt{N} + O_ε(N^ε)0
-/

open Filter
open scoped Asymptotics Pointwise Classical

namespace Erdos30

/-- A Sidon set is a set such that all pairwise sums of elements are distinct
apart from coincidences forced by commutativity. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The maximum size of a Sidon set in {1, ..., N}. -/
noncomputable def h (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun B => IsSidon B)).sup Finset.card

/-- The Erdős problem #30 statement: (N) = \sqrt{N} + O_ε(N^ε)$. -/
def ErdosProblem30Statement : Prop :=
  ∀ ε > (0 : ℝ), (fun N : ℕ => (h N : ℝ) - Real.sqrt (N : ℝ)) =O[atTop] (fun N : ℕ => (N : ℝ) ^ ε)

/-- Axiom (honest) : Erdős problem #30 (open problem). -/
axiom ax_erdos_problem_30 : ErdosProblem30Statement

theorem erdos_problem_30 : ErdosProblem30Statement :=
  ax_erdos_problem_30

end Erdos30
