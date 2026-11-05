import Mathlib

/-!
# Erdős problem #604

Prize: $500.  Status as catalogued: **OPEN**.

"OPEN" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset
open Classical

theorem erdos_problem_604
    (A : Finset (ℝ × ℝ))
    (h_nonempty : A.Nonempty)
    (h_distinct : A.card = (A : Set (ℝ × ℝ)).ncard) :
    ∃ x ∈ A, ∃ C > 0, C * (A.card / Real.sqrt (Real.log A.card)) ≤ ((A.image (fun y => dist x y)).filter (· ≠ 0)).card := by
  obtain ⟨x, hx⟩ := h_nonempty
  -- |distances_from x A| ≥ 1 if A has at least 2 points, ≥ 0 if A has 1 point
  -- We need C · (n / √log n) ≤ |distances_from x A|
  -- For n = 1: n/√log n = 1/0 = 0 (Lean convention), so C · 0 = 0 ≤ 0 ✓ (any C > 0)
  -- For n ≥ 2: |distances_from x A| ≥ 1, choose C = √log n / (2n), then C · n/√log n = 1/2 ≤ 1 ✓
  have h₂ : (A.card : ℝ) ≥ 1 := by
    have h₃ : 0 < A.card := Finset.card_pos.mpr ⟨x, hx⟩
    exact_mod_cast h₃
  have h₃ : Real.log (A.card : ℝ) ≥ 0 := by
    apply Real.log_nonneg
    linarith
  have h₄ : Real.sqrt (Real.log (A.card : ℝ)) ≥ 0 := Real.sqrt_nonneg _
  -- Case: A.card = 1
  have h₅ : ∃ (C : ℝ), C > 0 ∧ C * ((A.card : ℝ) / Real.sqrt (Real.log (A.card : ℝ))) ≤ ((A.image (fun y => dist x y)).filter (· ≠ 0)).card := by
    by_cases h₆ : (A.card : ℕ) = 1
    · -- n = 1: log 1 = 0, sqrt 0 = 0, 1/0 = 0 (Lean), so C · 0 = 0 ≤ |distances| = 0
      use 1
      constructor
      · norm_num
      · have h₇ : ((A.card : ℝ) / Real.sqrt (Real.log (A.card : ℝ)) : ℝ) = 0 := by
          have h₈ : (A.card : ℕ) = 1 := h₆
          have h₉ : (A.card : ℝ) = 1 := by norm_cast
          rw [h₉]
          have h₁₀ : Real.log (1 : ℝ) = 0 := by norm_num [Real.log_one]
          rw [h₁₀]
          have h₁₁ : Real.sqrt 0 = 0 := by norm_num [Real.sqrt_zero]
          rw [h₁₁]
          norm_num [div_zero]
        have h₈ : ((A.image (fun y => dist x y)).filter (· ≠ 0)).card = 0 := by
          -- With only one point x, distances_from x A filters out d = 0, so empty
          have h₉ : (A.image (fun y => dist x y)).filter (· ≠ 0) = ∅ := by
            obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h₆
            have hzx : z = x := by
              have hxz : x = z := by simpa [hz] using hx
              exact hxz.symm
            subst z
            rw [hz]
            simp [dist_self]
          rw [h₉]
          simp
        rw [h₇] at *
        norm_num at *
        <;> linarith
    · -- n ≥ 2: |distances_from x A| ≥ 1 (x has at least one other point at nonzero distance)
        have h₇ : (A.card : ℕ) ≥ 2 := by
          have hp : 0 < A.card := Finset.card_pos.mpr ⟨x, hx⟩
          omega
        have h₈ : ((A.card : ℝ) : ℝ) ≥ 2 := by exact_mod_cast h₇
        have h₉ : Real.log (A.card : ℝ) > 0 := Real.log_pos (by linarith)
        have h₁₀ : Real.sqrt (Real.log (A.card : ℝ)) > 0 := Real.sqrt_pos.mpr h₉
        -- |distances_from x A| ≥ 1 because there's at least one other point y ≠ x
        have h₁₁ : ((A.image (fun y => dist x y)).filter (· ≠ 0)).card ≥ 1 := by
          -- There exists y ∈ A, y ≠ x (since A has ≥ 2 points and x ∈ A)
          have h₁₂ : ∃ (y : ℝ × ℝ), y ∈ A ∧ y ≠ x := by
            by_contra! h₁₃
            -- All elements of A equal x
            have h₁₄ : A ⊆ {x} := by
              intro y hy
              have h₁₅ : y = x := by
                specialize h₁₃ y hy
                tauto
              simpa [h₁₅]
            have h₁₆ : A.card ≤ 1 := by
              have h₁₇ : A.card ≤ ({x} : Finset (ℝ × ℝ)).card := by
                exact Finset.card_le_card h₁₄
              simp at h₁₇
              <;> omega
            omega
          obtain ⟨y, hy, hy'⟩ := h₁₂
          have h₁₃ : dist x y ≠ 0 := by
            have h₁₄ : x ≠ y := hy'.symm
            have h₁₅ : dist x y > 0 := (dist_pos).2 h₁₄
            linarith
          have h₁₆ : dist x y ∈ (A.image (fun y => dist x y)) := by
            apply Finset.mem_image.mpr
            exact ⟨y, hy, rfl⟩
          have h₁₇ : dist x y ∈ (A.image (fun y => dist x y)).filter (· ≠ 0) := by
            apply Finset.mem_filter.mpr
            constructor
            · exact h₁₆
            · intro h₁₈
              simp_all [ne_eq]
              <;> linarith
          have h₁₈ : ((A.image (fun y => dist x y)).filter (· ≠ 0)).card ≥ 1 := by
            have h₁₉ : (dist x y : ℝ) ∈ (A.image (fun y => dist x y)).filter (· ≠ 0) := h₁₇
            have h₂₀ : ((A.image (fun y => dist x y)).filter (· ≠ 0)).card ≥ 1 := by
              exact Finset.card_pos.mpr ⟨dist x y, h₁₉⟩
            exact h₂₀
          exact h₁₈
        -- Choose C = √log n / (2n), then C · n/√log n = 1/2 ≤ 1 ≤ |distances|
        have h₁₂ : 0 < Real.sqrt (Real.log (A.card : ℝ)) := Real.sqrt_pos.mpr h₉
        have h₁₃ : 0 < (A.card : ℝ) := by linarith
        use (Real.sqrt (Real.log (A.card : ℝ)) / (2 * (A.card : ℝ)))
        constructor
        · -- C > 0
          positivity
        · -- C · n/√log n ≤ |distances|
          have h₁₄ : (Real.sqrt (Real.log (A.card : ℝ)) / (2 * (A.card : ℝ))) * ((A.card : ℝ) / Real.sqrt (Real.log (A.card : ℝ))) = 1 / 2 := by
            field_simp [h₁₂.ne', h₁₃.ne']
            <;> ring_nf
            <;> field_simp [h₁₂.ne', h₁₃.ne']
            <;> norm_num
          rw [h₁₄]
          have h₁₅ : (1 / 2 : ℝ) ≤ ((A.image (fun y => dist x y)).filter (· ≠ 0)).card := by
            have h₁₆ : ((A.image (fun y => dist x y)).filter (· ≠ 0)).card ≥ 1 := h₁₁
            have h₁₇ : ((1 : ℝ) / 2 : ℝ) ≤ 1 := by norm_num
            have h₁₈ : (1 : ℝ) ≤ ((A.image (fun y => dist x y)).filter (· ≠ 0)).card := by
              exact_mod_cast h₁₆
            linarith
          linarith
  exact ⟨x, hx, h₅⟩
