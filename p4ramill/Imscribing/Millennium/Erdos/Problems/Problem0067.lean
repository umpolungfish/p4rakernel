import Mathlib

/-!
# Erdős problem #67

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

theorem erdos_problem_67
    (f : ℕ → {x : ℝ // x = 1 ∨ x = -1}) :
    ∀ C > 0, ∃ d m : ℕ, m ≥ 1 ∧ C < |∑ k in Finset.Icc 1 m, (f (k * d) : ℝ)| := by
  sorry
