import Mathlib

/-!
# Erdős problem #140

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

theorem erdos_problem_140
    (r3 : ℕ → ℕ)
    (h_r3 : ∀ N, r3 N = sSup { n | ∃ A : Finset ℕ, A.card = n ∧ A ⊆ Finset.Icc 1 N ∧ ∀ a b c ∈ A, a + b = 2 * c → a = b }) :
    ∀ C > 0, ∀ᶠ N in Filter.atTop, r3 N ≤ C * N / (Real.log N)^C := by
  sorry
