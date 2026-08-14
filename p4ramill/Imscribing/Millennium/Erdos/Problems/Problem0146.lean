import Mathlib

/-!
# Erdős problem #146

Prize: $500.  Status as catalogued: **OPEN**.

The statement below is a FORMALISATION ATTEMPT, not a proof and not a settled
reading of the problem. It carries `sorry`, which is the claim itself: what is
asserted here is that this sentence is the problem, and nothing more. A `sorry`
that elaborates is a typed claim on the ledger; a file that does not elaborate
is not yet a claim at all, and the two are graded separately.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_146
    (r : ℕ)
    (H : SimpleGraph ℕ)
    (h_bip : H.Bipartite)
    (h_degen : ∀ H' : SimpleGraph ℕ, H' ≤ H → ∃ v : ℕ, H'.degree v ≤ r) :
    ∀ n, ∃ C > 0, C * n^(2 - 1/r) ≤ ex H n := by
  sorry
