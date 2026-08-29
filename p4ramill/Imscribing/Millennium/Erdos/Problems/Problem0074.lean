import Mathlib

/-!
# Erdős problem #74

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_74
    (f : ℕ → ℕ)
    (h_f : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ G : SimpleGraph ℕ, G.chromaticNumber = Cardinal.aleph0 ∧
      ∀ n, ∀ H : SimpleGraph (Fin n), H ≤ G → ∃ H' : SimpleGraph (Fin n), H' ≤ H ∧ H'.Bipartite ∧
        (H.edgeFinset.card - H'.edgeFinset.card) ≤ f n := by
  sorry
