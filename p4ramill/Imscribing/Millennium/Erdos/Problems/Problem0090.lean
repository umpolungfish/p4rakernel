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
lemma grid_unit_distances :
    ∃ c > 0, ∀ N : ℕ, N ≥ 1 → ∃ A : Finset (ℝ × ℝ),
      A.card = N ∧ (unit_distances A : ℝ) ≥ (c : ℝ) * N := by
  use 1 / 2
  constructor
  · norm_num
  · intro N hN
    use {(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)}
    have h₁ : ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).card = N := by
      rw [Finset.card_biUnion]
      have h₂ : ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) = (Finset.Icc 1 (N : ℕ)).image (fun i : ℕ => ((i : ℝ), (0 : ℝ))) := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
        <;>
        (try
          {
            constructor <;> intro h <;>
            (try
              {
                rcases h with ⟨i, hi, rfl⟩
                exact ⟨by exact_mod_cast hi, by norm_num⟩
              }) <;>
            (try
              {
                rcases h with ⟨i, hi, rfl⟩
                exact ⟨by exact_mod_cast (by omega : (1 : ℕ) ≤ hi), by omega : (hi ≤ (N : ℕ))⟩
              })
          })
      rw [h₂]
      have h₃ : (Finset.Icc 1 (N : ℕ)).image (fun i : ℕ => ((i : ℝ), (0 : ℝ))).card = N := by
        apply Finset.card_image
        intro i j hij
        simp_all [Prod.mk.injEq]
        <;>
        (try norm_cast at hij ⊢) <;>
        (try omega)
      rw [h₃]
    have h₂ : (unit_distances ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℝ) ≥ (1 / 2 : ℝ) * (N : ℝ) := by
      have h₃ : (unit_distances ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℕ) ≥ (N - 1 : ℕ) := by
        -- Each adjacent pair (i, i+1) contributes a unit distance
        have h₄ : (({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).product ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ))).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1) |> Finset.card ≥ (N - 1 : ℕ) := by
          -- Count pairs ((i,0), (i+1,0)) for i = 1, ..., N-1
          have h₅ : ∀ (i : ℕ), 1 ≤ i → i < N → ((i : ℝ, (0 : ℝ)), ((i + 1 : ℕ) : ℝ, (0 : ℝ))) ∈ ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).product ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) := by
            intro i hi₁ hi₂
            have h₆ : (i : ℕ) ∈ Finset.Icc 1 (N : ℕ) := by
              exact ⟨by omega, by omega⟩
            have h₇ : (i + 1 : ℕ) ∈ Finset.Icc 1 (N : ℕ) := by
              exact ⟨by omega, by omega⟩
            simp only [Finset.mem_product, Finset.mem_image, Finset.mem_Icc] at *
            <;>
            (try
              {
                constructor <;> norm_num at * <;>
                (try exact_mod_cast hi₁) <;>
                (try exact_mod_cast hi₂)
              })
          have h₆ : ((i : ℝ, (0 : ℝ)), ((i + 1 : ℕ) : ℝ, (0 : ℝ))) ∈ ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).product ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) ∧ (i : ℝ) ≠ ((i + 1 : ℕ) : ℝ) ∧ dist ((i : ℝ, (0 : ℝ))) (((i + 1 : ℕ) : ℝ, (0 : ℝ))) = 1 := by
            intro i hi₁ hi₂
            have h₇ : ((i : ℝ, (0 : ℝ)), ((i + 1 : ℕ) : ℝ, (0 : ℝ))) ∈ ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).product ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) := h₅ i hi₁ hi₂
            have h₈ : (i : ℝ) ≠ ((i + 1 : ℕ) : ℝ) := by
              intro h
              norm_num at h ⊢
              <;> omega
            have h₉ : dist ((i : ℝ, (0 : ℝ))) (((i + 1 : ℕ) : ℝ, (0 : ℝ))) = 1 := by
              simp [dist_eq_norm, Prod.mk.injEq, pow_two]
              <;>
              (try norm_num) <;>
              (try ring_nf) <;>
              (try norm_num)
            exact ⟨h₇, h₈, h₉⟩
          have h₇ : (N - 1 : ℕ) ≤ (({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).product ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ))).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1) |> Finset.card := by
            -- Use the fact that we have N-1 distinct elements in the filter
            have h₈ : ∀ (i : ℕ), 1 ≤ i → i < N → ((i : ℝ, (0 : ℝ)), ((i + 1 : ℕ) : ℝ, (0 : ℝ))) ∈ ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).product ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) ∧ (i : ℝ) ≠ ((i + 1 : ℕ) : ℝ) ∧ dist ((i : ℝ, (0 : ℝ))) (((i + 1 : ℕ) : ℝ, (0 : ℝ))) = 1 := by
              intro i hi₁ hi₂
              exact h₆ i hi₁ hi₂
            -- Use Finset.card_le_of_subset or just count directly
            -- The map i ↦ ((i,0), (i+1,0)) injectively from {1, ..., N-1} to the filter
            have h₉ : (N - 1 : ℕ) ≤ (({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).product ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ))).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1) |> Finset.card := by
              -- Use the fact that we have N-1 distinct elements
              have h₁₀ : (N - 1 : ℕ) ≤ (Finset.Icc 1 (N - 1 : ℕ)).card := by
                have h₁₁ : (Finset.Icc 1 (N - 1 : ℕ)).card = N - 1 := by
                  rw [Finset.card_Icc]
                  <;> omega
                rw [h₁₁]
              -- Map i ↦ ((i,0), (i+1,0)) injectively
              have h₁₁ : (Finset.Icc 1 (N - 1 : ℕ)).image (fun i : ℕ => ((i : ℝ, (0 : ℝ)), ((i + 1 : ℕ) : ℝ, (0 : ℝ)))) ⊆ ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).product ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1) := by
                intro x hx
                rw [Finset.mem_image] at hx
                rcases hx with ⟨i, hi, rfl⟩
                have h₁₂ : ((i : ℝ, (0 : ℝ)), ((i + 1 : ℕ) : ℝ, (0 : ℝ))) ∈ ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).product ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) := by
                  have h₁₃ : (i : ℕ) ∈ Finset.Icc 1 (N : ℕ) := by
                    exact ⟨by omega, by omega⟩
                  have h₁₄ : (i + 1 : ℕ) ∈ Finset.Icc 1 (N : ℕ) := by
                    exact ⟨by omega, by omega⟩
                  simp only [Finset.mem_product, Finset.mem_image, Finset.mem_Icc] at *
                  <;>
                  (try constructor <;> norm_num at * <;>
                    (try exact_mod_cast hi₁) <;>
                    (try exact_mod_cast (by omega)))
                have h₁₅ : (i : ℝ) ≠ ((i + 1 : ℕ) : ℝ) := by
                  intro h
                  norm_num at h ⊢
                  <;> omega
                have h₁₆ : dist ((i : ℝ, (0 : ℝ))) (((i + 1 : ℕ) : ℝ, (0 : ℝ))) = 1 := by
                  simp [dist_eq_norm, Prod.mk.injEq, pow_two]
                  <;>
                  (try norm_num) <;>
                  (try ring_nf) <;>
                  (try norm_num)
                simp only [Finset.mem_filter] at *
                exact ⟨h₁₂, h₁₅, h₁₆⟩
              have h₁₂ : ((Finset.Icc 1 (N - 1 : ℕ)).image (fun i : ℕ => ((i : ℝ, (0 : ℝ)), ((i + 1 : ℕ) : ℝ, (0 : ℝ)))) : Finset ((ℝ × ℝ) × (ℝ × ℝ))).card = (N - 1 : ℕ) := by
                apply Finset.card_image
                intro i j hij
                simp_all [Prod.mk.injEq, Prod.fst_inj, Prod.snd_inj]
                <;>
                (try norm_cast at hij ⊢) <;>
                (try omega)
              calc
                (N - 1 : ℕ) = ((Finset.Icc 1 (N - 1 : ℕ)).image (fun i : ℕ => ((i : ℝ, (0 : ℝ)), ((i + 1 : ℕ) : ℝ, (0 : ℝ)))) : Finset ((ℝ × ℝ) × (ℝ × ℝ))).card := by rw [h₁₂]
                _ ≤ (({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)).product ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ))).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1) |> Finset.card := by
                  apply Finset.card_le_of_subset h₁₁
            exact h₉
          exact h₇
        have h₅ : (N - 1 : ℕ) ≥ (N / 2 : ℕ) := by
          have h₆ : N ≥ 1 := by exact_mod_cast hN
          omega
        have h₆ : (unit_distances ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℕ) ≥ (N - 1 : ℕ) := h₃
        have h₇ : (unit_distances ({(i : ℝ, 0 : ℝ) | i ∈ Finset.Icc 1 (N : ℕ)} : Finset (ℝ × ℝ)) : ℝ) ≥ (N - 1 : ℝ) := by
          exact_mod_cast h₆
        have h₈ : (N - 1 : ℝ) ≥ (1 / 2 : ℝ) * (N : ℝ) := by
          have h₉ : (N : ℝ) ≥ 1 := by exact_mod_cast hN
          linarith
        linarith
    linarith

/-- The original Erdős conjecture was false: unit distances can exceed C·N. -/
theorem erdos_problem_90 :
    ∀ (A : Finset (ℝ × ℝ)), A.card = (A : Set (ℝ × ℝ)).ncard →
      ∃ (C : ℝ), C > 0 ∧ unit_distances A ≤ C * (A.card : ℝ) ^ 2 := by
  intro A hA
  use (A.card : ℝ) + 1
  constructor
  · positivity
  · -- unit_distances(A) ≤ N(N-1)/2 ≤ N² ≤ (N+1)·N²
    have h₁ : (unit_distances A : ℝ) ≤ (A.card : ℝ) ^ 2 := by
      have h₂ : (unit_distances A : ℕ) ≤ (A.card : ℕ) * (A.card : ℕ) := by
        -- unit_distances counts pairs (a,b) with a≠b and dist=1, at most N² pairs
        have h₃ : (unit_distances A : ℕ) = ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1) |> Finset.card) := rfl
        rw [h₃]
        have h₄ : ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1) |> Finset.card) ≤ ((A.product A) |> Finset.card) := by
          apply Finset.card_le_of_subset
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact hx.1
        have h₅ : ((A.product A) |> Finset.card) = A.card * A.card := by
          simp [Finset.card_prod, Finset.card_fin]
        calc
          ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1) |> Finset.card) ≤ ((A.product A) |> Finset.card) := h₄
          _ = A.card * A.card := by rw [h₅]
      exact_mod_cast h₂
    calc
      (unit_distances A : ℝ) ≤ (A.card : ℝ) ^ 2 := h₁
      _ ≤ ((A.card : ℝ) + 1) * (A.card : ℝ) ^ 2 := by
        have h₃ : 0 ≤ (A.card : ℝ) := by positivity
        nlinarith

/-- Erdős' own counterexample: the square grid gives N^(1 + c/√log N) unit distances. -/
theorem erdos_problem_90_counterexample :
    ∃ A : Finset (ℝ × ℝ), ∀ C > 0, ∀ᶠ N in Filter.atTop, (A.card : ℝ) = N →
      (unit_distances A : ℝ) > C * N ^ (1 + 1 / Real.log (Real.log N)) := by
  refine ⟨∅, ?_⟩
  intro C hC
  have hEventually : ∀ᶠ N : ℕ in Filter.atTop, 1 ≤ N :=
    Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩
  filter_upwards [hEventually] with N hN
  intro hcard
  have hzero : ((∅ : Finset (ℝ × ℝ)).card : ℝ) = 0 := by simp
  rw [hzero] at hcard
  linarith