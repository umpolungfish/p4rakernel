import Mathlib

open Complex Real

example : ((2 : ℂ)).re = 2 := by simp
example : ((2 : ℂ)).im = 0 := by simp
example (t : ℝ) : ((t : ℂ) - 2 * I).re = t := by simp
example (t : ℝ) : ((t : ℂ) - 2 * I).im = -2 := by simp
example (n : ℕ) : ((n : ℕ) : ℂ).re = (n : ℝ) := by simp
example (n : ℕ) : ((n : ℕ) : ℂ).im = 0 := by simp
example (n : ℤ) : ((n : ℤ) : ℂ).re = (n : ℝ) := by simp
example (n : ℤ) : ((n : ℤ) : ℂ).im = 0 := by simp
example (x : ℝ) : ‖cexp ((x : ℂ))‖ = rexp x := by rw [Complex.norm_exp, Complex.ofReal_re]
example (n : ℕ) : ((2 * n : ℕ) : ℤ) = 2 * ((n : ℕ) : ℤ) := by push_cast; rfl
example (n : ℕ) : ((2 * n + 1 : ℕ) : ℤ) = 2 * ((n : ℕ) : ℤ) + 1 := by push_cast; rfl

#check @Summable.tsum_le_tsum
#check @Summable.tsum_mul_left
#check @Summable.tsum_add
#check @Summable.tsum_eq_zero_add
#check @tsum_congr
#check @squeeze_zero
#check @tendsto_zero_iff_norm_tendsto_zero
#check @mul_le_mul_of_nonneg_left
#check @Real.sqrt_nonneg
#check @norm_mul_le
#check @exp_le_exp
#check @Complex.exp_add
#check @Real.cos_two_mul'
#check @Real.sin_two_mul
#check @Real.abs_sin_le_abs
#check @Complex.ofReal_pow
#check @Complex.ofRealCLM.map_tsum

theorem probe_ofReal_intCast (n : ℤ) : ((n : ℤ) : ℂ) = Complex.ofReal ((n : ℤ) : ℝ) := by
  refine Complex.ext ?_ ?_ <;> simp [Complex.intCast_re, Complex.intCast_im]

example (t : ℝ) (n : ℤ) (A B : ℝ) :
    (Complex.ofReal (-(π : ℝ)) * (Complex.ofReal A + Complex.ofReal B * I)
        * ((n : ℤ) : ℂ) ^ 2).re
      = -(π : ℝ) * A * ((n : ℤ) : ℝ) ^ 2 := by
  have hq2 : ((n : ℤ) : ℂ) ^ 2 = Complex.ofReal (((n : ℤ) : ℝ) ^ 2) := by
    rw [probe_ofReal_intCast, ← Complex.ofReal_pow]
  simp only [hq2, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

example (t : ℝ) (n : ℤ) (A B : ℝ) :
    (Complex.ofReal (-(π : ℝ)) * (Complex.ofReal A + Complex.ofReal B * I)
        * ((n : ℤ) : ℂ) ^ 2).im
      = -(π : ℝ) * B * ((n : ℤ) : ℝ) ^ 2 := by
  have hq2 : ((n : ℤ) : ℂ) ^ 2 = Complex.ofReal (((n : ℤ) : ℝ) ^ 2) := by
    rw [probe_ofReal_intCast, ← Complex.ofReal_pow]
  simp only [hq2, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  ring

example (t : ℝ) (c : ℝ) : (Complex.ofReal c / ((t : ℂ) - 2 * I) : ℂ).im = c * 2 / (t ^ 2 + 4) := by
  simp only [Complex.div_im, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring
