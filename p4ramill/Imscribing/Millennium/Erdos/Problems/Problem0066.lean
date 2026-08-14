import Mathlib

/-!
# Erdős problem #66

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

theorem erdos_problem_66 :
    ∃ A : Set ℕ, ∃ l : ℝ, l ≠ 0 ∧
      Filter.Tendsto (fun n => ((A ×ˢ A).filter (fun p => p.1 + p.2 = n)).ncard / Real.log n) Filter.atTop (𝓝 l) := by
  sorry
