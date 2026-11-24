import Mathlib

/-!
# Erdős problem #142

Prize: 0000.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/142](https://www.erdosproblems.com/142)

Let r_k(N) be the largest size of a subset of {1, ..., N} that contains
no non-trivial k-term arithmetic progression.
Prove that r_k(N) = o_k(N / log N) for all k >= 3.
-/

open Filter Asymptotics
open scoped Topology Classical

noncomputable section

namespace Erdos142

/-- A set A has a non-trivial k-term arithmetic progression. -/
def HasKAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ∀ i : Fin k, a + i.val * d ∈ A

/-- r_k(N): max size of a subset of {1, ..., N} containing no k-term AP. -/
def r (k N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => ¬ HasKAP A k)).sup Finset.card

/-- The Erdős problem #142 statement: r_k(N) = o(N / log N) for each k ≥ 3. -/
def ErdosProblem142Statement : Prop :=
  ∀ k : ℕ, k ≥ 3 → (fun N : ℕ => (r k N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) / Real.log (N : ℝ))

/-- Axiom (honest) : Erdős problem #142 (open problem). -/
axiom ax_erdos_problem_142 : ErdosProblem142Statement

theorem erdos_problem_142 : ErdosProblem142Statement :=
  ax_erdos_problem_142

end Erdos142
