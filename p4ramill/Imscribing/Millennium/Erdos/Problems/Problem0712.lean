import Imscribing.Millennium.Erdos.UniformHypergraphDensity

/-!
# Erdős problem #712

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

theorem erdos_problem_712
    (k r : ℕ)
    (h_conds : 2 < r ∧ r < k)
    (ex_r : ℕ → ℕ)
    (h_ex : ∀ n, ex_r n = sSup { m | ∃ H : Finset (Finset (Fin n)), H.card = m ∧ (∀ S ∈ H, S.card = r) ∧
      ¬ ∃ X : Finset (Fin n), X.card = k ∧ ∀ S : Finset (Fin n), S ⊆ X → S.card = r → S ∈ H }) :
    ∃ L : ℝ, Filter.Tendsto (fun n => (ex_r n / Nat.choose n r : ℝ)) Filter.atTop (𝓝 L) := by
  have heq : ex_r = Erdos712.extremal k r := by
    funext n
    exact h_ex n
  subst ex_r
  simpa only [Erdos712.density] using Erdos712.density_limit k r (by omega)
