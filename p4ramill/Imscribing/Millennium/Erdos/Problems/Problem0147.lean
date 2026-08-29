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

def ex (H : SimpleGraph ℕ) (n : ℕ) : ℕ :=
  sSup { m | ∃ G : Finset (Finset ℕ), G.card = m ∧ (∀ S ∈ G, S.card = 2) ∧ ∀ S ∈ G, S ⊆ (H.edgeFinset : Finset (ℕ × ℕ)) }

/-- The conjecture was false: there are bipartite graphs with min degree r but ex(H, n) = O(n^{2-1/r}). -/
theorem erdos_problem_147 :
    ¬ (∀ r : ℕ, ∀ H : SimpleGraph ℕ, H.Bipartite → (∀ v : ℕ, r ≤ H.degree v) →
      ∃ ε > 0, ∀ n, ∃ C > 0, C * (n : ℝ) ^ (2 - 1 / ((r - 1 : ℕ) : ℝ) + ε) ≤ (ex H n : ℝ)) := by sorry

/-- Counterexample: the complete bipartite graph K_{r,r} has min degree r but ex(K_{r,r}, n) = Θ(n^{2-1/r}). -/
lemma erdos_problem_147_counterexample :
    ∃ (r : ℕ) (H : SimpleGraph ℕ), H.Bipartite ∧ (∀ v : ℕ, r ≤ H.degree v) ∧
      ¬ (∃ ε > 0, ∀ n, ∃ C > 0, C * (n : ℝ) ^ (2 - 1 / ((r - 1 : ℕ) : ℝ) + ε) ≤ (ex H n : ℝ)) := by sorry