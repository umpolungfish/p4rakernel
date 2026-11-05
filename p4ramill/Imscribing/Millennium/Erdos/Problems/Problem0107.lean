import Mathlib

/-!
# Erdős problem #107

Prize: $500.  Status as catalogued: **FALSIFIABLE**.

"FALSIFIABLE" is the status of the MATHEMATICS in the literature, not of this file.
-/

open scoped BigOperators
open Finset

theorem erdos_problem_107
    (n : ℕ)
    (f : ℕ → ℕ)
    (h_f : ∀ n, f n = sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) }) :
    (f n : ℕ) ≥ n := by
  -- f(n) ≥ n because you need at least n points to select n convex independent points.
  -- If f(n) < n, then sInf < n, meaning there's some m < n in the set.
  -- But no set of m < n points can contain n convex independent points, contradiction.
  have h₁ : (f n : ℕ) ≥ n := by
    by_contra h
    have h₂ : (f n : ℕ) < n := by linarith
    have h₃ : f n = sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } := h_f n
    rw [h₃] at h₂
    -- sInf < n means there exists m < n in the set (sInf of a set of ℕ is its minimum)
    have h₄ : ∃ (m : ℕ), m ∈ { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } ∧ m < n := by
      -- sInf(S) < n means not all elements are ≥ n
      have h₅ : ¬ (∀ (m : ℕ), m ∈ { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } → m ≥ n) := by
        intro h₅
        have h₆ : (n : ℕ) ≤ (sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } : ℕ) := by
          -- n is a lower bound of the set
          have h₇ : ∀ (m : ℕ), m ∈ { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } → m ≥ n := by
            intro m hm
            exact h₅ m hm
          -- n is a lower bound, so sInf ≥ n
          have h₈ : (n : ℕ) ≤ (sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } : ℕ) := by
            -- Use the fact that every element of the set is ≥ n
            -- So n is a lower bound, hence sInf ≥ n
            have h₉ : ∀ (m : ℕ), m ∈ { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } → m ≥ n := h₇
            -- Show n ≤ sInf(S) by showing n is a lower bound
            -- sInf(S) is the greatest lower bound, so any lower bound ≤ sInf(S)
            -- But we need n ≤ sInf(S), which follows from n being a lower bound
            have h₁₀ : (n : ℕ) ≤ (sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } : ℕ) := by
              -- Use csSup_le on the negated set, or just use the fact that sInf ≥ n when n is a lower bound
              -- Actually, we can use the property: if x ≤ s for all s ∈ S, then x ≤ sInf(S)
              -- This is le_csInf
              have h₁₁ : ∀ (m : ℕ), m ∈ { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } → (n : ℕ) ≤ m := by
                intro m hm
                exact h₇ m hm
              -- Now use le_csInf: n ≤ sInf(S) if n ≤ s for all s ∈ S and S is bounded below
              have h₁₂ : BddBelow ({m : ℕ | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ))} : Set ℕ) := by
                refine' ⟨0, _⟩
                intro m hm
                have h₁₃ : m ∈ { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } := hm
                have h₁₄ : m ≥ n := h₁₁ m hm
                linarith
              -- Now apply le_csInf
              have h₁₃ : (n : ℕ) ≤ sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } := by
                apply le_csInf
                · -- S is bounded below (by 0)
                  exact h₁₂
                · -- n ≤ s for all s ∈ S
                  intro m hm
                  exact h₁₁ m hm
              exact h₁₃
            exact h₁₁
          exact_mod_cast h₉
        linarith
      -- sInf < n means there's some m < n in the set
      have h₅ : ∃ (m : ℕ), m ∈ { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } ∧ m < n := by
        by_contra h₆
        have h₇ : ∀ (m : ℕ), m ∈ { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } → m ≥ n := by
          intro m hm
          exact h₆ m hm
        have h₈ : (sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } : ℕ) ≥ n := by
          have h₉ : (n : ℕ) ≤ (sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } : ℕ) := by
            have h₁₀ : ∀ (m : ℕ), m ∈ { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } → m ≥ n := by
              intro m hm
              exact h₇ m hm
            have h₁₁ : (n : ℕ) ≤ (sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } : ℕ) := by
              have h₁₂ : BddBelow ({m : ℕ | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ))} : Set ℕ) := by
                refine' ⟨0, _⟩
                intro m hm
                have h₁₃ : m ∈ { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } := hm
                have h₁₄ : m ≥ n := h₁₀ m hm
                linarith
              have h₁₃ : (n : ℕ) ≤ sInf { m | ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) } := by
                apply le_csInf
                · exact h₁₂
                · intro m hm
                  exact h₁₀ m hm
              exact h₁₃
          exact_mod_cast h₉
        linarith
      obtain ⟨m, hm, h₈⟩ := h₅
      have h₉ : m < n := h₈
      -- But m < n, so take A with exactly m points in general position
      -- A cannot contain n convex independent points
      have h₁₀ : ∃ (A : Finset (ℝ × ℝ)), A.card = m ∧ (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) := by
        use {(i : ℝ, (i : ℝ) ^ 2) | i ∈ Finset.Icc 0 (m - 1 : ℕ)}
        constructor
        · -- Cardinality = m
          have h₁₁ : ({(i : ℝ, (i : ℝ) ^ 2) | i ∈ Finset.Icc 0 (m - 1 : ℕ)} : Finset (ℝ × ℝ)).card = m := by
            have h₁₂ : ({(i : ℝ, (i : ℝ) ^ 2) | i ∈ Finset.Icc 0 (m - 1 : ℕ)} : Finset (ℝ × ℝ)) = (Finset.Icc 0 (m - 1 : ℕ)).image (fun i : ℕ => ((i : ℝ), (i : ℝ) ^ 2)) := by
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
                      exact ⟨by exact_mod_cast i, by linarith⟩
                    }) <;>
                  (try
                    {
                      rcases h with ⟨i, hi, rfl⟩
                      exact ⟨by exact_mod_cast i, by linarith⟩
                    })
                })
            rw [h₁₂]
            have h₁₃ : (Finset.Icc 0 (m - 1 : ℕ)).image (fun i : ℕ => ((i : ℝ), (i : ℝ) ^ 2)).card = m := by
              apply Finset.card_image
              intro i j hij
              simp_all [Prod.mk.injEq]
              <;>
              (try norm_cast at hij ⊢) <;>
              (try omega)
            rw [h₁₃]
        · -- No 3 collinear: points on parabola y = x²
          intro x y z hx hy hz h₁₁ h₁₂ h₁₃
          intro h₁₄
          simp_all [Collinear, Set.mem_insert, Set.mem_singleton_iff, Prod.mk.injEq, Real.sqrt_eq_iff_sq_eq]
          <;>
          (try
            {
              rcases h₁₄ with ⟨h₁₅, h₁₆, h₁₇⟩
              norm_num [Prod.mk.injEq] at h₁₅ h₁₆ h₁₇ ⊢
              <;>
              (try contradiction)
            })
          <;>
          (try
            {
              intro h₁₈
              simp_all [Collinear, Set.mem_insert, Set.mem_singleton_iff, Prod.mk.injEq, Real.sqrt_eq_iff_sq_eq]
              <;>
              (try
                {
                  rcases h₁₈ with ⟨h₁₉, h₂₀, h₂₁⟩
                  norm_num [Prod.mk.injEq] at h₁₉ h₂₀ h₂₁ ⊢
                  <;>
                  (try contradiction)
                })
              })
          <;>
          (try
            {
              intro h₁₈
              simp_all [Collinear, Set.mem_insert, Set.mem_singleton_iff, Prod.mk.injEq, Real.sqrt_eq_iff_sq_eq]
              <;>
              (try
                {
                  rcases h₁₈ with ⟨h₁₉, h₂₀, h₂₁⟩
                  norm_num [Prod.mk.injEq] at h₁₉ h₂₀ h₂₁ ⊢
                  <;>
                  (try contradiction)
                })
              })
      -- A satisfies the property (m is in the set), so A contains n convex independent points
      -- But A has m < n points, contradiction
      have h₁₁ : ∀ A : Finset (ℝ × ℝ), A.card ≥ m → (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (ℝ × ℝ))) → ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) := hm
      have h₁₂ : ∃ B ⊆ A, B.card = n ∧ ConvexIndependent ℝ (fun b : B => (b : ℝ × ℝ)) := by
        have h₁₃ : A.card ≥ m := by
          have h₁₄ : A.card = m := by
            -- A = {(i : ℝ, (i : ℝ) ^ 2) | i ∈ Finset.Icc 0 (m - 1 : ℕ)}
            -- has cardinality m because the map i ↦ (i, i²) is injective on [0, m-1]
            have h₁₅ : ({(i : ℝ, (i : ℝ) ^ 2) | i ∈ Finset.Icc 0 (m - 1 : ℕ)} : Finset (ℝ × ℝ)).card = m := by
              have h₁₆ : ({(i : ℝ, (i : ℝ) ^ 2) | i ∈ Finset.Icc 0 (m - 1 : ℕ)} : Finset (ℝ × ℝ)) = (Finset.Icc 0 (m - 1 : ℕ)).image (fun i : ℕ => ((i : ℝ), (i : ℝ) ^ 2)) := by
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
                        exact ⟨by exact_mod_cast i, by linarith⟩
                      }) <;>
                    (try
                      {
                        rcases h with ⟨i, hi, rfl⟩
                        exact ⟨by exact_mod_cast i, by linarith⟩
                      })
                    })
                rw [h₁₆]
                have h₁₇ : (Finset.Icc 0 (m - 1 : ℕ)).image (fun i : ℕ => ((i : ℝ), (i : ℝ) ^ 2)).card = m := by
                  apply Finset.card_image
                  intro i j hij
                  simp_all [Prod.mk.injEq]
                  <;>
                  (try norm_cast at hij ⊢) <;>
                  (try omega)
                rw [h₁₇]
              rw [h₁₅]
            exact h₁₄
        exact h₁₁ A h₁₂ h₁₃
      exfalso
      exact h₉ h₁₀
    exact h₁
  exact h₁