import Mathlib
noncomputable section

example : dist ((1 : ℝ), (0 : ℝ)) ((2 : ℝ), (0 : ℝ)) = 1 := by
  rw [dist_eq_norm]
  norm_num
