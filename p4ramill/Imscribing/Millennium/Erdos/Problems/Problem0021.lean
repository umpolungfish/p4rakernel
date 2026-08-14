import Mathlib

/-!
# Erdős problem #21

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

theorem erdos_problem_21
    (f : ℕ → ℕ)
    (h_min : ∀ n, f n = sInf { m | ∃ (F : Finset (Finset ℕ)),
      (∀ A ∈ F, A.card = n) ∧
      (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
      F.card = m ∧
      (∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A) }) :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, f n ≤ C * n := by
  sorry
