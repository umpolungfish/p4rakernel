import Mathlib

/-!
# Erdős problem #113

Prize: $500.  Status as catalogued: **DISPROVED**.

Erdős conjectured that a bipartite graph G has Turán exponent 3/2 if and only if
every subgraph has minimum degree ≤ 2. This was disproved by showing counterexamples.
-/

open scoped BigOperators
open Finset

def ex (G : SimpleGraph ℕ) (n : ℕ) : ℕ :=
  sSup { m | ∃ H : Finset (Finset ℕ), H.card = m ∧ (∀ S ∈ H, S.card = 2) ∧ ∀ S ∈ H, S ⊆ (G.edgeFinset : Finset (ℕ × ℕ)) }

/-- The statement was false: there are bipartite graphs with min degree ≤ 2 but Turán exponent ≠ 3/2. -/
theorem erdos_problem_113 :
    ¬ (∀ G : SimpleGraph ℕ, G.Bipartite →
      ((∀ H : SimpleGraph ℕ, H ≤ G → ∃ v : ℕ, H.degree v ≤ 2) ↔ (∀ n, ∃ C > 0, C * n ^ (3 / 2 : ℝ) ≤ ex G n))) := by sorry

/-- Counterexample: the even cycle C_{2k} has min degree 2 but Turán exponent 1+1/k. -/
lemma erdos_problem_113_counterexample :
    ∃ (G : SimpleGraph ℕ), G.Bipartite ∧
      (∀ H : SimpleGraph ℕ, H ≤ G → ∃ v : ℕ, H.degree v ≤ 2) ∧
      ¬ (∀ n, ∃ C > 0, C * (n : ℝ) ^ (3 / 2 : ℝ) ≤ (ex G n : ℝ)) := by sorry