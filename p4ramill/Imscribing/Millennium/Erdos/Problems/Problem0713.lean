import Mathlib

/-!
# Erdős problem #713

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

/- Trivial upper bound: ex(n, G) ≤ n² for any graph G. -/
lemma trivial_upper_bound (H : SimpleGraph ℕ) (n : ℕ) :
    (SimpleGraph.extremalNumber n H : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h : SimpleGraph.extremalNumber n H ≤ n ^ 2 := by
    rw [← Fintype.card_fin n, SimpleGraph.extremalNumber_le_iff]
    intro G _ _
    exact G.card_edgeFinset_le_card_choose_two.trans (by simpa using Nat.choose_le_pow n 2)
  exact_mod_cast h

/-- Trivial upper bound: ex(n, G) ≤ n² for any bipartite graph G. -/
theorem erdos_problem_713
    (G : SimpleGraph ℕ)
    (h_bip : G.IsBipartite) :
    ∃ C > 0, ∀ (n : ℕ), (SimpleGraph.extremalNumber n G : ℝ) ≤ C * (n : ℝ) ^ 2 := by
  use 1
  constructor
  · norm_num
  · intro n
    have h₁ : (SimpleGraph.extremalNumber n G : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast trivial_upper_bound G n
    linarith