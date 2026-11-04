import Mathlib

/-!
# Erdős problem #147

Prize: $500.  Status as catalogued: **DISPROVED**.

Erdős conjectured that if H is a bipartite graph with minimum degree r, then
ex(H, n) ≥ C·n^{2-1/(r-1)+ε} for some ε > 0. This was disproved by showing
counterexamples where the exponent is smaller.
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section


/-- The conjecture was false: there are bipartite graphs with min degree r but ex(H, n) = O(n^{2-1/r}). -/
theorem erdos_problem_147 :
    ¬ (∀ r : ℕ, ∀ H : SimpleGraph ℕ, H.IsBipartite → (∀ v : ℕ, r ≤ (H.neighborSet v).encard) →
      ∃ ε > 0, ∀ n : ℕ, ∃ C > 0, C * (n : ℝ) ^ (2 - 1 / ((r - 1 : ℕ) : ℝ) + ε) ≤ (SimpleGraph.extremalNumber n H : ℝ)) := by sorry

/-- Counterexample: the complete bipartite graph K_{r,r} has min degree r but ex(K_{r,r}, n) = Θ(n^{2-1/r}). -/
lemma erdos_problem_147_counterexample :
    ∃ (r : ℕ) (H : SimpleGraph ℕ), H.IsBipartite ∧ (∀ v : ℕ, r ≤ (H.neighborSet v).encard) ∧
      ¬ (∃ ε > 0, ∀ n : ℕ, ∃ C > 0, C * (n : ℝ) ^ (2 - 1 / ((r - 1 : ℕ) : ℝ) + ε) ≤ (SimpleGraph.extremalNumber n H : ℝ)) := by sorry