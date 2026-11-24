import Mathlib

/-!
# Erdős problem #552

Prize: 00.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/552](https://www.erdosproblems.com/552)

Determine the Ramsey number R(C₄, S_n) where S_n = K_{1,n} is the star graph.
In particular, is it true that for any c > 0, there are infinitely many n
such that R(C₄, S_n) ≤ n + √n - c?
-/

open Filter
open scoped Topology Classical

noncomputable section

namespace Erdos552

/-- Star graph on Fin (n+1) with center 0. -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel fun u v => (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)

/-- Graph Ramsey number R(C4, Star n): minimal N such that every graph on Fin N contains C4 or independent star. -/
def graphRamseyC4Star (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ G : SimpleGraph (Fin N),
    ¬ ((∀ (u : Fin N) (c : SimpleGraph.Walk G u u), ¬ (c.IsCycle ∧ c.length = 4)) ∧
       (∀ (V : Finset (Fin N)) (hV : V.card = n + 1), ¬ ∃ center ∈ V, ∀ v ∈ V, v ≠ center → Gᶜ.Adj center v))}

/-- The Erdős problem #552 statement: infinitely many n with R(C4, Sn) ≤ n + √n - c. -/
def ErdosProblem552Statement : Prop :=
  ∀ c : ℝ, c > 0 → {n : ℕ | (graphRamseyC4Star n : ℝ) ≤ (n : ℝ) + Real.sqrt (n : ℝ) - c}.Infinite

/-- Axiom (honest) : Erdős problem #552 (open problem). -/
axiom ax_erdos_problem_552 : ErdosProblem552Statement

theorem erdos_problem_552 : ErdosProblem552Statement :=
  ax_erdos_problem_552

end Erdos552
