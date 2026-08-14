import Mathlib

/-!
# Erdős problem #713

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

theorem erdos_problem_713
    (G : SimpleGraph ℕ)
    (h_bip : G.Bipartite) :
    ∃ α : ℝ, 1 ≤ α ∧ α < 2 ∧ ∃ c > 0, Filter.Tendsto (fun n => (ex G n / (c * n^α) : ℝ)) Filter.atTop (𝓝 1) := by
  sorry
