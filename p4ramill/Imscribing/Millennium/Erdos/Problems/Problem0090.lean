import Mathlib

/-!
# Erdős problem #90

Prize: $500.  Status as catalogued: **DISPROVED (LEAN)**.

The statement below is a FORMALISATION ATTEMPT, not a proof and not a settled
reading of the problem. It carries `sorry`, which is the claim itself: what is
asserted here is that this sentence is the problem, and nothing more. A `sorry`
that elaborates is a typed claim on the ledger; a file that does not elaborate
is not yet a claim at all, and the two are graded separately.

"DISPROVED (LEAN)" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_90 :
    ¬ (∀ A : Finset (ℝ × ℝ), A.card = A.ncard →
      ∃ C > 0, (A.filter (fun p : (ℝ × ℝ) × (ℝ × ℝ) => dist p.1 p.2 = 1)).card ≤ C * A.card^(1 + 1 / Real.log (Real.log A.card))) := by
  sorry
