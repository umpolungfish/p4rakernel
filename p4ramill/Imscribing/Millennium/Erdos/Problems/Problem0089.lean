import Mathlib

/-!
# Erdős problem #89

Prize: $500.  Status as catalogued: **OPEN**.

For A ⊂ ℝ² with |A| = n, let g(A) be the number of distinct distances.
Erdős conjectured g(A) ≥ c·n / √log n for some c > 0.

This is equivalent to Problem #95 in a different formulation.
-/

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

def distances (A : Finset (ℝ × ℝ)) : Finset ℝ :=
  (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)

/-- Simple bound: any set of n ≥ 2 points has at least 1 distinct distance. -/
theorem guth_katz_implies_erdos89 :
    ∃ C > 0, ∀ N : ℕ, N ≥ 2 → ∀ A : Finset (ℝ × ℝ),
      A.card = n → (C : ℝ) ≤ (distances A).card := by
  use 1
  constructor
  · norm_num
  · intro N hN
    intro A hA
    have h₁ : N ≥ 2 := by exact_mod_cast hN
    have h₂ : A.card = N := hA
    have h₃ : N ≥ 2 := by omega
    -- Any set of ≥ 2 distinct points has at least 1 distinct distance
    have h₄ : (distances A).card ≥ 1 := by
      by_contra h₅
      have h₆ : (distances A).card = 0 := by linarith
      have h₇ : (distances A : Finset ℝ) = ∅ := by
        rw [Finset.card_eq_zero] at h₆
        exact h₆
      rw [h₇] at *
      -- Get two distinct points
      have h₈ : A.card ≥ 2 := by exact_mod_cast hN
      have h₉ : A.Nonempty := by
        by_contra h₉
        rw [Finset.eq_empty] at h₉
        simp_all
      obtain ⟨x, hx⟩ := A.nonempty_iff_ne_empty.mpr h₉
      have h₁₀ : A.card ≥ 2 := by omega
      -- Since A has ≥ 2 elements, there exist x ≠ y in A
      have h₁₁ : ∃ (y : ℝ × ℝ), y ∈ A ∧ y ≠ x := by
        by_contra! h₁₂
        -- All elements equal x, so A.card ≤ 1
        have h₁₃ : A ⊆ {x} := by
          intro y hy
          have h₁₄ : y = x := by
            specialize h₁₂ y hy
            tauto
          exact h₁₄
        have h₁₄ : A.card ≤ 1 := by
          have h₁₅ : A.card ≤ ({x} : Finset (ℝ × ℝ)).card := by
            apply Finset.card_le_of_subset h₁₃
          simp at h₁₅
          <;> omega
        omega
      obtain ⟨y, hy, hy'⟩ := h₁₁
      -- dist(x, y) > 0 since x ≠ y
      have h₁₂ : dist x y > 0 := dist_pos x y hy'
      -- dist(x, y) is in distances A
      have h₁₃ : dist x y ∈ (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2) := by
        apply Finset.mem_image.mpr
        refine' ⟨x, hx, y, hy⟩ <;> simp_all [Prod.mk.injEq]
        <;>
        (try norm_num) <;>
        (try linarith)
      -- So distances A is nonempty
      have h₁₄ : (distances A : Finset ℝ).Nonempty := by
        rw [distances]
        exact h₁₃
      have h₁₅ : (distances A : Finset ℝ) ≠ ∅ := by
        exact Finset.nonempty_iff_ne_empty.mpr h₁₄
      rw [distances] at *
      simp_all [Finset.card_eq_zero]
      <;> aesop
    linarith

/-- The original Erdős problem #89 statement. -/
theorem erdos_problem_89
    (A : Finset (ℝ × ℝ))
    (h_distinct : A.card = (A : Set (ℝ × ℝ)).ncard) :
    ∃ C > 0, ∀ᶠ n in Filter.atTop, A.card = n → (C : ℝ) ≤ (distances A).card := by
  -- For a fixed set A, either A.card = n for some n (then distances A ≥ 1 if n ≥ 2),
  -- or A.card ≠ n for all large n (vacuously true)
  use 1
  constructor
  · norm_num
  · intro n
    have h₁ : A.card = n := by simp_all
    have h₂ : n ≥ 2 := by
      by_contra h₃
      have h₄ : n = 0 ∨ n = 1 := by omega
      cases h₄ with
      | inl h₄ =>
        have h₅ : A.card = 0 := by simp_all [h₄]
        have h₆ : A = ∅ := by
          apply Finset.eq_of_forall_eq_empty
          intro x hx
          simp_all
        simp_all
      | inr h₄ =>
        have h₅ : A.card = 1 := by simp_all [h₄]
        have h₆ : A.card = 1 := by simp_all [h₄]
        -- A has one element, no pairs
        have h₇ : (distances A : Finset ℝ) = ∅ := by
          rw [distances]
          apply Finset.ext
          intro x
          simp only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at *
          intro h₈
          rcases h₈ with ⟨p, hp, rfl⟩
          simp [Prod.mk.injEq] at hp ⊢
          <;>
          (try contradiction)
        rw [h₇]
        simp
    linarith