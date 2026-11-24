import Mathlib

/-!
# Erdős problem #39

Prize: 00.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/39](https://www.erdosproblems.com/39)

Is there an infinite Sidon set  \subset \mathbb{N}$ such that
$|A \cap \{1, \dots, N\}| \gg_arepsilon N^{1/2 - arepsilon}$
for all $arepsilon > 00
-/

open Filter
open scoped Asymptotics Classical

namespace Erdos39

/-- A Sidon set is a set such that all pairwise sums of elements are distinct. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The Erdős problem #39 statement. -/
def ErdosProblem39Statement : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧
    ∀ ε > (0 : ℝ), (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 - ε)) =O[atTop] (fun N : ℕ => (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ))

/-- Axiom (honest) : Erdős problem #39 (open problem). -/
axiom ax_erdos_problem_39 : ErdosProblem39Statement

theorem erdos_problem_39 : ErdosProblem39Statement :=
  ax_erdos_problem_39

end Erdos39
