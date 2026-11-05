theorem scratch_sInf_nat : (sInf ({n : ℕ | True} : Set ℕ) : ℕ) = 0 := by
  have h₁ : ({n : ℕ | True} : Set ℕ) = Set.univ := by
    apply Set.ext
    intro x
    simp
  rw [h₁]
  -- sInf of the universal set of ℕ is ⊥ = 0
  have h₂ : (sInf (Set.univ : Set ℕ) : ℕ) = 0 := by
    -- sInf univ = ⊥ for a conditionally complete linear order with bottom
    have h₃ : sInf (Set.univ : Set ℕ) = ⊥ := by
      apply sInf_univ
    rw [h₃]
    <;> norm_num [Nat.zero_eq_bot]
  rw [h₂]
