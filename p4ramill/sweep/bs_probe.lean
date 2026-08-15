import Mathlib
#check @sq_sum_le_card_mul_sum_sq
#check @Finset.inner_mul_le_norm_mul_norm
#check @Finset.sum_div_pow_mul_fract_le
example (s : Finset ℕ) (f : ℕ → ℝ) : (∑ i ∈ s, f i)^2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  exact?
