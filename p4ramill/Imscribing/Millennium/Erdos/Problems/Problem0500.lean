import Mathlib

/-!
# Erdős problem #500

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

theorem erdos_problem_500
    (n : ℕ)
    (H : Finset (Finset (Fin n)))
    (h_H : ∀ S ∈ H, S.card = 3)
    (h_no_K4 : ¬ ∃ X : Finset (Fin n), X.card = 4 ∧ ∀ S : Finset (Fin n), S ⊆ X → S.card = 3 → S ∈ H) :
    ∃ C > 0, H.card ≤ C * n^3 := by
  sorry
