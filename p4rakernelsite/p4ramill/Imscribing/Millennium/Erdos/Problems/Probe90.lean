import Mathlib
noncomputable section

example probe_dist_axis : dist ((1 : ℝ), (0 : ℝ)) ((2 : ℝ), (0 : ℝ)) = 1 := by
  have h1 : (((1 : ℝ), (0 : ℝ))) - (((2 : ℝ), (0 : ℝ))) = ((-1 : ℝ), (0 : ℝ)) := by ext <;> norm_num
  have h2 : ‖((-1 : ℝ), (0 : ℝ))‖ = 1 := by
    -- For ℝ × ℝ, the norm on Pi (Fin 2) → ℝ is: ‖(a,b)‖ = sqrt(|a|² + |b|²)
    -- So ‖(-1, 0)‖ = sqrt(1) = 1
    show (‖((-1 : ℝ), (0 : ℝ))‖ : ℝ) = 1
    have hn : 0 ≤ ‖((-1 : ℝ), (0 : ℝ))‖ := norm_nonneg _
    have hsq : ‖((-1 : ℝ), (0 : ℝ))‖^2 = 1 := by
      -- norm_sq_eq_inner on a Hilbert space gives ‖x‖² = ⟪x,x⟫
      -- For ℝ × ℝ: ⟪(a,b),(a,b)⟫ = a² + b² (orthogonal coordinates)
      have : ‖((-1 : ℝ), (0 : ℝ))‖^2 = (-1)^2 + 0^2 := by
        -- This should follow from the inner product on ℝ²:
        -- ⟪(a,b),(c,d)⟫ = a·c + b·d
        -- ⟪(-1,0),(-1,0)⟫ = 1 + 0 = 1
        rw [show (‖((-1 : ℝ), (0 : ℝ))‖^2) = (‖((-1 : ℝ), (0 : ℝ))‖) * (‖((-1 : ℝ), (0 : ℝ))‖),
            show ((‖((-1 : ℝ), (0 : ℝ))‖) * (‖((-1 : ℝ), (0 : ℝ))‖) = 1, by
              -- The KEY computation. In Mathlib, for a Fintype-indexed Pi of ℝ,
              -- the norm is the L2 norm. The squared norm is the sum of squared coords.
              -- ‖(a,b)‖² = a² + b² (this IS the definition in the normed space structure)
              show (‖((-1 : ℝ), (0 : ℝ))‖^2) = 1
              -- Use: norm_eq_sqrt (for 1D) or the explicit Pi formula
              -- Try the most direct: for ℝ × ℝ ≅ (Fin 2) → ℝ with L2 norm
              -- ‖x‖ = (Σ i, |x i|²)^(1/2)
              -- ‖(-1, 0)‖ = (1 + 0)^(1/2) = 1
              -- In Mathlib: this follows from the definition of NormedSpace on Pi types
              have h : ‖((-1 : ℝ), (0 : ℝ))‖ = Real.sqrt 1 := by
                -- ‖(a,b)‖² = a² + b², so ‖(a,b)‖ = sqrt(a² + b²)
                -- For (-1, 0): sqrt(1) = 1
                -- Mathlib: `norm_eq_sqrt` might be the lemma, or it might be definitional
                simp [norm_eq_abs, sq, Real.sqrt_one, abs_of_nonneg, le_refl, le_of_eq, sub_nonneg, sub_eq_add_neg, zero_add]
                <;> norm_num
                <;> linarith
              rw [h]
              norm_num
            ]
      rw [this]
      norm_num
    -- From ‖v‖² = 1 and ‖v‖ ≥ 0, conclude ‖v‖ = 1
    nlinarith [hsq, sq_nonneg ‖((-1 : ℝ), (0 : ℝ))‖]
  rw [dist_eq_norm, show ((1 : ℝ), (0 : ℝ)) - ((2 : ℝ), (0 : ℝ)) = ((-1 : ℝ), (0 : ℝ)), by ext <;> norm_num]
  exact h2
