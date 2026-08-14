import Mathlib

/-!
# Erdős problem #107

Prize: $500.  Status as catalogued: **FALSIFIABLE**.

The statement below is a FORMALISATION ATTEMPT, not a proof and not a settled
reading of the problem. It carries `sorry`, which is the claim itself: what is
asserted here is that this sentence is the problem, and nothing more. A `sorry`
that elaborates is a typed claim on the ledger; a file that does not elaborate
is not yet a claim at all, and the two are graded separately.

"FALSIFIABLE" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_107
    (f : ℕ → ℕ)
    (h_f : ∀ n, f n = sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x y z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬Collinear x y z) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent B }) :
    f n = 2^(n - 2) + 1 := by
  sorry
