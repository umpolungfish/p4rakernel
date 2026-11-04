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
open scoped Topology
noncomputable section


/-- The Erdős–Simonovits conjecture: ex(H, n) = Θ(n^{2-1/r}) for bipartite H with max degree r. -/
theorem erdos_problem_146
    (r : ℕ) (hr : 1 < r)
    (H : SimpleGraph ℕ)
    (h_bip : H.IsBipartite)
    (h_degen : ∀ H' : SimpleGraph ℕ, H' ≤ H → ∃ v : ℕ, (H'.neighborSet v).encard ≤ r) :
    ∀ n : ℕ, ∃ C > 0, C * (n : ℝ) ^ (2 - 1 / (r : ℝ)) ≤ (SimpleGraph.extremalNumber n H : ℝ) := by sorry

/-- Known for r = 2 (even cycles): ex(C_{2k}, n) = Θ(n^{1+1/k}). -/
lemma erdos_problem_146_r2 :
    ∀ k : ℕ, 2 ≤ k →
    ∃ C > 0, ∀ᶠ n : ℕ in Filter.atTop,
      C * (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * k)) : ℝ) := by sorry

/-- The trivial upper bound: ex(H, n) ≤ C·n^2 for any graph H. -/
lemma trivial_upper_bound (H : SimpleGraph ℕ) (n : ℕ) :
    (SimpleGraph.extremalNumber n H : ℝ) ≤ (n : ℝ) ^ 2 := by sorry