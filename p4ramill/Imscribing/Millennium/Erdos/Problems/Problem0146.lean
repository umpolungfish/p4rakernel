import Mathlib

/-!
# Erdős problem #146

Prize: $500.  Status as catalogued: **OPEN**.

Let H be a bipartite graph with maximum degree r. Erdős conjectured that the Turán
number ex(H, n) ≥ C·n^{2-1/r} for some C > 0. This is known for small r and for r=2
(even cycles), but open in general.
-/

open scoped BigOperators
open Finset

def ex (H : SimpleGraph ℕ) (n : ℕ) : ℕ :=
  sSup { m | ∃ G : Finset (Finset ℕ), G.card = m ∧ (∀ S ∈ G, S.card = 2) ∧ ∀ S ∈ G, S ⊆ (H.edgeFinset : Finset (ℕ × ℕ)) }

/-- The Erdős–Simonovits conjecture: ex(H, n) = Θ(n^{2-1/r}) for bipartite H with max degree r. -/
theorem erdos_problem_146
    (r : ℕ) (hr : 1 < r)
    (H : SimpleGraph ℕ)
    (h_bip : H.Bipartite)
    (h_degen : ∀ H' : SimpleGraph ℕ, H' ≤ H → ∃ v : ℕ, H'.degree v ≤ r) :
    ∀ n, ∃ C > 0, C * (n : ℝ) ^ (2 - 1 / (r : ℝ)) ≤ (ex H n : ℝ) := by sorry

/-- Known for r = 2 (even cycles): ex(C_{2k}, n) = Θ(n^{1+1/k}). -/
lemma erdos_problem_146_r2 :
    ∀ k : ℕ, 2 ≤ k →
    ∃ C > 0, ∀ᶠ n in Filter.atTop,
      C * (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (ex (SimpleGraph.cycle (2 * k)) n : ℝ) := by sorry

/-- The trivial upper bound: ex(H, n) ≤ C·n^2 for any graph H. -/
lemma trivial_upper_bound (H : SimpleGraph ℕ) (n : ℕ) :
    (ex H n : ℝ) ≤ (n : ℝ) ^ 2 := by sorry