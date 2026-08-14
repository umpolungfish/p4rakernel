import Mathlib

/-!
# Erdős problem #19

Prize: $500.  Status as catalogued: **DECIDABLE**.

The statement below is a FORMALISATION ATTEMPT, not a proof and not a settled
reading of the problem. It carries `sorry`, which is the claim itself: what is
asserted here is that this sentence is the problem, and nothing more. A `sorry`
that elaborates is a typed claim on the ledger; a file that does not elaborate
is not yet a claim at all, and the two are graded separately.

"DECIDABLE" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_19
    (n : ℕ)
    (G : SimpleGraph (Fin n))
    (h_union : ∃ (f : Fin n → SimpleGraph (Fin n)), (∀ i, (f i).IsClique) ∧
      (∀ i, (f i).edgeFinset.card = n) ∧
      (∀ e, G.edgeFinset.mem e ↔ ∃ i, (f i).edgeFinset.mem e) ∧
      (∀ i j, i ≠ j → Disjoint (f i).edgeFinset (f j).edgeFinset)) :
    G.chromaticNumber = n := by
  sorry
