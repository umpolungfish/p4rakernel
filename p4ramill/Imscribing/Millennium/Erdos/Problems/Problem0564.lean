import Mathlib

/-!
# Erdős problem #564

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

theorem erdos_problem_564
    (R3 : ℕ → ℕ)
    (h_R3 : ∀ n, R3 n = sInf { m | ∃ c : Fin (m.choose 3) → Fin 2, ∀ H : Finset (Fin m), H.card = n → ∃ i, c i = c (H.toFinset.image (fun h => h.1)) }) :
    ∃ c > 0, ∀ᶠ n in Filter.atTop, 2^(2^(c * n)) ≤ R3 n := by
  sorry
