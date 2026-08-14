import Mathlib

/-!
# Erdős problem #92

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

theorem erdos_problem_92
    (f : ℕ → ℕ)
    (h_f : ∀ n, ∀ A : Finset (ℝ × ℝ), A.card = n → ∃ x ∈ A, f n ≤ (A.filter (fun y => dist x y = dist x (x + (1, 0)))).card) :
    ¬ (∀ᶠ n in Filter.atTop, f n ≤ n^(1 / Real.log (Real.log n))) := by
  sorry
