import Mathlib

/-!
# Erdős problem #712

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

theorem erdos_problem_712
    (k r : ℕ)
    (h_conds : 2 < r ∧ r < k)
    (ex_r : ℕ → ℕ)
    (h_ex : ∀ n, ex_r n = sSup { m | ∃ H : Finset (Finset (Fin n)), H.card = m ∧ (∀ S ∈ H, S.card = r) ∧
      ¬ ∃ X : Finset (Fin n), X.card = k ∧ ∀ S : Finset (Fin n), S ⊆ X → S.card = r → S ∈ H }) :
    ∃ L : ℝ, Filter.Tendsto (fun n => (ex_r n / Nat.choose n r : ℝ)) Filter.atTop (𝓝 L) := by
  sorry
