import Mathlib

/-!
# Erdős problem #113

Prize: $500.  Status as catalogued: **DISPROVED**.

Erdős conjectured that a bipartite graph G has Turán exponent 3/2 if and only if
every subgraph has minimum degree ≤ 2. This was disproved by showing counterexamples.
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section


/-- The statement was false: there are bipartite graphs with min degree ≤ 2 but Turán exponent ≠ 3/2. -/
theorem erdos_problem_113 :
    ¬ (∀ G : SimpleGraph ℕ, G.IsBipartite →
      ((∀ H : SimpleGraph ℕ, H ≤ G → ∃ v : ℕ, (H.neighborSet v).encard ≤ 2) ↔ (∀ n : ℕ, ∃ C > 0, C * (n : ℝ) ^ (3 / 2 : ℝ) ≤ (SimpleGraph.extremalNumber n G : ℝ)))) := by sorry

/-- Counterexample: the even cycle C_{2k} has min degree 2 but Turán exponent 1+1/k. -/
lemma erdos_problem_113_counterexample :
    ∃ (G : SimpleGraph ℕ), G.IsBipartite ∧
      (∀ H : SimpleGraph ℕ, H ≤ G → ∃ v : ℕ, (H.neighborSet v).encard ≤ 2) ∧
      ¬ (∀ n : ℕ, ∃ C > 0, C * (n : ℝ) ^ (3 / 2 : ℝ) ≤ (SimpleGraph.extremalNumber n G : ℝ)) := by sorry