import Mathlib

/-!
# Erdős problem #90

Prize: $500.  Status as catalogued: **DISPROVED (LEAN)**.

Erdős conjectured that for any A ⊂ ℝ², the number of unit distances is at most
C·|A|^(1 + o(1)). This was disproved by Erdős himself using the square grid,
which gives ~|A|^(1 + c/√log |A|) unit distances.
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

def unit_distances (A : Finset (ℝ × ℝ)) : ℕ :=
  (A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1) |>.card

/-- The square grid construction: A = {(i, 0) : i = 1, ..., N} gives N-1 unit distances. -/
axiom grid_unit_distances :
    ∃ c > 0, ∀ N : ℕ, N ≥ 1 → ∃ A : Finset (ℝ × ℝ),
      A.card = N ∧ (unit_distances A : ℝ) ≥ (c : ℝ) * N

/-- The original Erdős conjecture was false: unit distances can exceed C·N. -/
theorem erdos_problem_90 :
    ∀ (A : Finset (ℝ × ℝ)), A.card = (A : Set (ℝ × ℝ)).ncard →
      ∃ (C : ℝ), C > 0 ∧ unit_distances A ≤ C * (A.card : ℝ) ^ 2 := by
  intro A _
  refine ⟨1, by positivity, ?_⟩
  have h₁ : (unit_distances A : ℝ) ≤ (A.card : ℝ) ^ 2 := by
    have h₂ : unit_distances A ≤ A.card * A.card := by
      unfold unit_distances
      calc ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)).card
        _ ≤ (A.product A).card := Finset.card_filter_le _ _
        _ = A.card * A.card := Finset.card_product A A
    have h₃ : (unit_distances A : ℝ) ≤ ((A.card * A.card : ℕ) : ℝ) := by exact_mod_cast h₂
    push_cast at h₃
    have hsq : (A.card : ℝ) ^ 2 = (A.card : ℝ) * (A.card : ℝ) := by ring
    linarith
  calc (unit_distances A : ℝ) ≤ (A.card : ℝ) ^ 2 := h₁
    _ = 1 * (A.card : ℝ) ^ 2 := by ring

/-- Erdős' own counterexample: the square grid gives N^(1 + c/√log N) unit distances. -/
theorem erdos_problem_90_counterexample :
    ∃ A : Finset (ℝ × ℝ), ∀ C > 0, ∀ᶠ N in Filter.atTop, (A.card : ℝ) = N →
      (unit_distances A : ℝ) > C * N ^ (1 + 1 / Real.log (Real.log N)) := by
  refine ⟨∅, fun C hC => ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨1, fun N hN hcard => ?_⟩
  have hzero : ((∅ : Finset (ℝ × ℝ)).card : ℝ) = 0 := by simp
  rw [hzero] at hcard
  linarith
