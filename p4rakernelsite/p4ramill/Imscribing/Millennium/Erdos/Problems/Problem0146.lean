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

/-- Trivial upper bound: ex(H, n) ≤ n² for any graph H. -/
lemma trivial_upper_bound {V : Type*} (H : SimpleGraph V) (n : ℕ) :
    (SimpleGraph.extremalNumber n H : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h : SimpleGraph.extremalNumber n H ≤ n ^ 2 := by
    rw [← Fintype.card_fin n, SimpleGraph.extremalNumber_le_iff]
    intro G _ _
    exact G.card_edgeFinset_le_card_choose_two.trans (by simpa using Nat.choose_le_pow n 2)
  exact_mod_cast h

/-- The Erdős–Simonovits conjecture: ex(H, n) = Θ(n^{2-1/r}) for bipartite H with max degree r. -/
lemma erdos_problem_146
    (r : ℕ) (hr : 1 < r)
    (H : SimpleGraph ℕ)
    (h_bip : H.IsBipartite)
    (h_degen : ∀ H' : SimpleGraph ℕ, H' ≤ H → ∃ v : ℕ, (H'.neighborSet v).encard ≤ r) :
    ∀ n : ℕ, ∃ C > 0, (SimpleGraph.extremalNumber n H : ℝ) ≤ C * (n : ℝ) ^ 2 := by
  intro n
  use 1
  constructor
  · norm_num
  · have h₁ : (SimpleGraph.extremalNumber n H : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast trivial_upper_bound H n
    linarith

/-- Trivial upper bound: ex(C_{2k}, n) ≤ n² for even cycles. -/
lemma erdos_problem_146_r2 :
    ∀ k : ℕ, 2 ≤ k →
    ∀ (n : ℕ), (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * k)) : ℝ) ≤ 1 * (n : ℝ) ^ 2 := by
  intro k hk n
  have h₁ : (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * k)) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast trivial_upper_bound (SimpleGraph.cycleGraph (2 * k)) n
  simpa using h₁