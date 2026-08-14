import Mathlib

/-!
# Erdős problem #604

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

theorem erdos_problem_604
    (A : Finset (ℝ × ℝ))
    (h_distinct : A.card = A.ncard) :
    ∃ x ∈ A, ∃ C > 0, C * (A.card / Real.sqrt (Real.log A.card)) ≤ (distancesFrom x A).card := by
  sorry
