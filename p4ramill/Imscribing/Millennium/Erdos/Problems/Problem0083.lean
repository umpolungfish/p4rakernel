import Mathlib

/-!
# Erdős problem #83

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

theorem erdos_problem_83
    (n : ℕ)
    (F : Finset (Finset (Fin (4 * n))))
    (h_size : ∀ A ∈ F, A.card = 2 * n)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    F.card ≤ (1/2 : ℝ) * (Nat.choose (4 * n) (2 * n) - (Nat.choose (2 * n) n)^2) := by
  sorry
