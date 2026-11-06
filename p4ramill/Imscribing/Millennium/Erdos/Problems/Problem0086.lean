import Mathlib

/-!
# Erdős problem #86

Prize: 00.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/86](https://www.erdosproblems.com/86)

Let Q_n be the n-dimensional hypercube graph. Is it true that every subgraph of Q_n
with >= (1/2 + o(1)) n 2^{n-1} edges contains a 4-cycle C_4?
-/

open Filter
open scoped Topology Classical

namespace Erdos86

/-- The n-dimensional hypercube graph on Fin n → Bool. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel fun u v => ∃! i : Fin n, u i ≠ v i

/-- The Erdős problem #86 statement. -/
def ErdosProblem86Statement : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ᶠ n : ℕ in atTop, ∀ H : SimpleGraph (Fin n → Bool),
    H ≤ hypercube n →
      (1 / 2 + ε) * (n : ℝ) * (2 : ℝ) ^ (n - 1) ≤ (H.edgeSet.ncard : ℝ) →
        ∃ (u : Fin n → Bool) (c : SimpleGraph.Walk H u u), c.IsCycle ∧ c.length = 4

/-- Axiom (honest) : Erdős problem #86 (open problem). -/
axiom ax_erdos_problem_86 : ErdosProblem86Statement

theorem erdos_problem_86 : ErdosProblem86Statement :=
  ax_erdos_problem_86

end Erdos86
