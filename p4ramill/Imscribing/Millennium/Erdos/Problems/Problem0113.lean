import Mathlib

/-!
# Erdős problem #113

Prize: $500.  Status as catalogued: **DISPROVED**.

The statement below is a FORMALISATION ATTEMPT, not a proof and not a settled
reading of the problem. It carries `sorry`, which is the claim itself: what is
asserted here is that this sentence is the problem, and nothing more. A `sorry`
that elaborates is a typed claim on the ledger; a file that does not elaborate
is not yet a claim at all, and the two are graded separately.

"DISPROVED" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_113 :
    ¬ (∀ G : SimpleGraph ℕ, G.Bipartite →
      ((∀ H : SimpleGraph ℕ, H ≤ G → ∃ v : ℕ, H.degree v ≤ 2) ↔ (∀ n, ∃ C > 0, C * n^(3/2) ≤ ex G n))) := by
  sorry
