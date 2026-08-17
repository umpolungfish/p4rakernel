import Mathlib

open scoped BigOperators
open Finset

theorem erdos_problem_564
    (R3 : ℕ → ℕ)
    (h_R3 : ∀ n, R3 n = sInf { m | ∃ c : Fin (m.choose 3) → Fin 2, ∀ H : Finset (Fin m), H.card = n → ∃ i, c i = c (H.toFinset.image (fun h => h.1)) }) :
    ∃ c > 0, ∀ᶠ n in Filter.atTop, 2^(2^(c * n)) ≤ R3 n := by
  sorry
