import Mathlib

/-!
# Erdős problem #95

Prize: $500.  Status as catalogued: **PROVED**.

The statement below is a FORMALISATION ATTEMPT, not a proof and not a settled
reading of the problem. It carries `sorry`, which is the claim itself: what is
asserted here is that this sentence is the problem, and nothing more. A `sorry`
that elaborates is a typed claim on the ledger; a file that does not elaborate
is not yet a claim at all, and the two are graded separately.

"PROVED" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_95 :
    ∀ ε > 0, ∃ C > 0, ∀ A : Finset (ℝ × ℝ),
      let dists := A.product A |>.filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)
      let f := fun u => (A.product A |>.filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = u)).card
      (∑ u in dists, (f u)^2) ≤ C * A.card^(3 + ε) := by
  sorry
