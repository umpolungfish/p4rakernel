import Mathlib

/-!
# Erdős problem #241

Prize: 00.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/241](https://www.erdosproblems.com/241)

Let f(N) be the maximum size of A ⊆ {1, ..., N} such that the 3-fold sums
a+b+c with a,b,c ∈ A are all distinct. Is it true that f(N) ~ N^{1/3}?
-/

open Filter Asymptotics
open scoped Topology Classical

noncomputable section

namespace Erdos241

/-- A set A has distinct 3-fold sums. -/
def DistinctThreeSums (A : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a₃ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A,
    a₁ ≤ a₂ ∧ a₂ ≤ a₃ → b₁ ≤ b₂ ∧ b₂ ≤ b₃ →
    a₁ + a₂ + a₃ = b₁ + b₂ + b₃ → a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃

/-- Maximum size of a subset of {1, ..., N} with distinct 3-fold sums. -/
def f (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter DistinctThreeSums).sup Finset.card

/-- The Erdős problem #241 statement: f(N) ~ N^(1/3). -/
def ErdosProblem241Statement : Prop :=
  (fun N : ℕ => (f N : ℝ)) ~[atTop] (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 3))

/-- Axiom (honest) : Erdős problem #241 (open problem). -/
axiom ax_erdos_problem_241 : ErdosProblem241Statement

theorem erdos_problem_241 : ErdosProblem241Statement :=
  ax_erdos_problem_241

end Erdos241
