import Mathlib

/-!
# Erdős problem #713

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

theorem erdos_problem_713
    (G : SimpleGraph ℕ)
    (h_bip : G.IsBipartite) :
    ∃ α : ℝ, 1 ≤ α ∧ α < 2 ∧ ∃ c > 0, Filter.Tendsto (fun n => (SimpleGraph.extremalNumber n G / (c * n^α) : ℝ)) Filter.atTop (𝓝 1) := by
  sorry
