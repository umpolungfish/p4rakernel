import Mathlib

lemma memo_2ce9858e960a066f : ∀ (n : ℕ), Continuous (λ x : ℝ => ∑ k in Finset.Icc 1 n, (1 / (k : ℝ)) * Real.sin (2 * Real.pi * k * x)) := by
  intro n
  apply continuous_finset_sum
  intro k _
  apply Continuous.mul
  · exact continuous_const
  · apply Real.continuous_sin.comp
    apply Continuous.mul
    · apply Continuous.mul
      · apply Continuous.mul
        · exact continuous_const
        · exact continuous_const
      · exact continuous_const
    · exact continuous_id