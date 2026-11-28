import Mathlib
import Imscribing.Millennium.ClinkStarkBridge
import Imscribing.Millennium.SIC_D2048_StarkTheorem

/-!
# SIC_D2048_StarkAbelianity — the abelianity clause K(√ε)/ℚ at d = 2048

ε = ε_{2048} = (2047 + √4190205)/2 with ε̄ = (2047 − √4190205)/2 = 1/ε.
√ε is a root of the biquadratic f = X⁴ − 2047X² + 1 = (X² − ε)(X² − ε̄),
and since ε̄ = 1/ε the other square root √ε̄ = 1/√ε lies in ℚ(√ε).

This module certifies the root structure completely: every root of f over
ℝ and over ℂ is one of ±√ε, ±√ε̄ (§2, §3); the minimal polynomial of √ε
over ℚ divides f, hence has degree ≤ 4 (§4). Normality of ℚ⟮√ε⟯/ℚ — the
abelianity clause — then reduces to the splitting of f inside ℚ⟮√ε⟯, the
next rung.
-/

noncomputable section

namespace Imscribing.Millennium.StarkAbelianityD2048

open Imscribing.Millennium.ClinkStarkBridge
open Imscribing.Millennium.StarkTheoremD2048

open scoped Real
open scoped Polynomial

/-- The dominant embedding ε = (2047 + √4190205)/2. -/
abbrev alpha : ℝ := epsilonReal 2048

/-- The contracting embedding ε̄ = (2047 − √4190205)/2. -/
abbrev beta : ℝ := epsilonConjReal 2048

/-- The two real square roots: √ε and √ε̄. -/
abbrev s : ℝ := Real.sqrt alpha
abbrev t : ℝ := Real.sqrt beta

/-- The biquadratic annihilator of √ε over ℚ. -/
def quarticQ : ℚ[X] :=
  Polynomial.X ^ 4 - Polynomial.C (2047 : ℚ) * Polynomial.X ^ 2 + Polynomial.C (1 : ℚ)

/-! ## §1 The adjunction identities -/

theorem alpha_beta_sum : alpha + beta = (2048 : ℝ) - 1 := epsilonReal_add_conj 2048

theorem alpha_beta_sum' : alpha + beta = (2047 : ℝ) := by
  rw [alpha_beta_sum]
  norm_num

theorem alpha_beta_mul : alpha * beta = 1 := epsilonReal_mul_conj 2048 (by norm_num)

theorem alpha_pos : 0 < alpha := by
  have := epsilonReal_2048_bounds.1
  linarith

theorem beta_pos : 0 < beta := by
  have := epsilonConjReal_2048_bounds.1
  linarith

theorem s_pos : 0 < s := Real.sqrt_pos.mpr alpha_pos

theorem t_pos : 0 < t := Real.sqrt_pos.mpr beta_pos

theorem s_ne_zero : s ≠ 0 := ne_of_gt s_pos

theorem t_ne_zero : t ≠ 0 := ne_of_gt t_pos

/-- The contraction: √ε · √ε̄ = 1. -/
theorem s_mul_t : s * t = 1 := by
  rw [← Real.sqrt_mul (le_of_lt alpha_pos) beta, alpha_beta_mul, Real.sqrt_one]

/-- So √ε̄ = 1/√ε. -/
theorem t_eq_inv_s : s⁻¹ = t := inv_eq_of_mul_eq_one_right s_mul_t

/-- ε satisfies the quadratic x² − 2047x + 1 = 0. -/
theorem alpha_quadratic : alpha ^ 2 - 2047 * alpha + 1 = 0 := by
  have h1 := alpha_beta_sum'
  have h2 := alpha_beta_mul
  have hkey : alpha * (2047 - alpha) = 1 := by
    rw [← h2, ← h1]
    ring
  have hexp : alpha * (2047 - alpha) = 2047 * alpha - alpha ^ 2 := by ring
  linarith

/-- ε̄ satisfies the same quadratic x² − 2047x + 1 = 0. -/
theorem beta_quadratic : beta ^ 2 - 2047 * beta + 1 = 0 := by
  have hbeta : beta = 2047 - alpha := by
    have := alpha_beta_sum'
    linarith
  have hexp : (2047 - alpha) * (2047 - alpha) - 2047 * (2047 - alpha) + 1
      = alpha ^ 2 - 2047 * alpha + 1 := by ring
  rw [hbeta, pow_two, hexp]
  exact alpha_quadratic

theorem s_sq : s ^ 2 = alpha := Real.sq_sqrt alpha_pos.le

theorem t_sq : t ^ 2 = beta := Real.sq_sqrt beta_pos.le

/-! ## §2 The biquadratic and its real roots -/

/-- f(√ε) = 0: the quartic X⁴ − 2047X² + 1 vanishes at the dominant root. -/
theorem s_quartic : s ^ 4 - 2047 * s ^ 2 + 1 = 0 := by
  show s ^ (2 * 2) - 2047 * s ^ 2 + 1 = 0
  rw [pow_mul, s_sq]
  exact alpha_quadratic

/-- f(√ε̄) = 0: the quartic vanishes at the contracting root. -/
theorem t_quartic : t ^ 4 - 2047 * t ^ 2 + 1 = 0 := by
  show t ^ (2 * 2) - 2047 * t ^ 2 + 1 = 0
  rw [pow_mul, t_sq]
  exact beta_quadratic

/-- Every real root of X⁴ − 2047X² + 1 is one of ±√ε, ±√ε̄. -/
theorem real_root_structure (x : ℝ) (hx : x ^ 4 - 2047 * x ^ 2 + 1 = 0) :
    x = s ∨ x = -s ∨ x = t ∨ x = -t := by
  have hexpand : (x ^ 2 - alpha) * (x ^ 2 - beta)
      = x ^ 4 - (alpha + beta) * x ^ 2 + alpha * beta := by ring
  have hprod : (x ^ 2 - alpha) * (x ^ 2 - beta) = 0 := by
    rw [hexpand, alpha_beta_sum', alpha_beta_mul]
    exact hx
  rcases mul_eq_zero.mp hprod with h | h
  · have habs : |x| = s := by
      show |x| = Real.sqrt alpha
      have h1 : Real.sqrt (x ^ 2) = |x| := Real.sqrt_sq_eq_abs x
      have h2 : x ^ 2 = alpha := by linarith
      rw [← h1, h2]
    rcases (abs_eq s_pos.le).mp habs with hxs | hxs
    · exact Or.inl hxs
    · exact Or.inr (Or.inl hxs)
  · have habs : |x| = t := by
      show |x| = Real.sqrt beta
      have h1 : Real.sqrt (x ^ 2) = |x| := Real.sqrt_sq_eq_abs x
      have h2 : x ^ 2 = beta := by linarith
      rw [← h1, h2]
    rcases (abs_eq t_pos.le).mp habs with hxs | hxs
    · exact Or.inr (Or.inr (Or.inl hxs))
    · exact Or.inr (Or.inr (Or.inr hxs))

/-! ## §3 The complex roots -/

/-- A complex number whose square is a positive real is one of the two real
    square roots of that real. -/
theorem complex_sq_real (z : ℂ) (a : ℝ) (ha : 0 < a) (hz : z ^ 2 = (a : ℂ)) :
    z = ((Real.sqrt a : ℝ) : ℂ) ∨ z = -((Real.sqrt a : ℝ) : ℂ) := by
  have hzz : z * z = (a : ℂ) := by rw [← pow_two]; exact hz
  have him : z.re * z.im = 0 := by
    have hi : z.re * z.im + z.im * z.re = 0 := by
      have h2 := congrArg Complex.im hzz
      rwa [Complex.mul_im] at h2
    have hcomm : z.im * z.re = z.re * z.im := mul_comm _ _
    rw [hcomm] at hi
    linarith
  rcases mul_eq_zero.mp him with hre0 | him0
  · exfalso
    have hre : z.re * z.re - z.im * z.im = a := by
      have h2 := congrArg Complex.re hzz
      rwa [Complex.mul_re] at h2
    rw [hre0] at hre
    have hnn := mul_self_nonneg (z.im)
    linarith
  · have hzreal : z = Complex.ofReal z.re := by
      apply Complex.ext
      · rfl
      · rw [him0]; simp
    have hzzc : Complex.ofReal (z.re ^ 2) = Complex.ofReal a := by
      rw [pow_two, Complex.ofReal_mul, ← hzreal]
      exact hzz
    have hsq2 : z.re ^ 2 = a := by
      have hparts := congrArg Complex.re hzzc
      rwa [Complex.ofReal_re, Complex.ofReal_re] at hparts
    have habs : |z.re| = Real.sqrt a := by
      have h1 : Real.sqrt (z.re ^ 2) = |z.re| := Real.sqrt_sq_eq_abs z.re
      rw [← h1, hsq2]
    rcases (abs_eq (Real.sqrt_nonneg a)).mp habs with h1 | h1
    · exact Or.inl (by rw [hzreal, h1])
    · exact Or.inr (by rw [hzreal, h1, Complex.ofReal_neg])

/-- Every complex root of X⁴ − 2047X² + 1 is one of ±√ε, ±√ε̄ — all four
    of them real. -/
theorem complex_root_structure (z : ℂ)
    (hz : z ^ 4 - ((2047 : ℝ) : ℂ) * z ^ 2 + ((1 : ℝ) : ℂ) = 0) :
    z = ((s : ℝ) : ℂ) ∨ z = -((s : ℝ) : ℂ) ∨ z = ((t : ℝ) : ℂ) ∨ z = -((t : ℝ) : ℂ) := by
  have hexpand : (z ^ 2 - ((alpha : ℝ) : ℂ)) * (z ^ 2 - ((beta : ℝ) : ℂ))
      = z ^ 4 - (((alpha : ℝ) : ℂ) + ((beta : ℝ) : ℂ)) * z ^ 2
        + ((alpha : ℝ) : ℂ) * ((beta : ℝ) : ℂ) := by ring
  have hprod : (z ^ 2 - ((alpha : ℝ) : ℂ)) * (z ^ 2 - ((beta : ℝ) : ℂ)) = 0 := by
    rw [hexpand, ← Complex.ofReal_add, alpha_beta_sum', ← Complex.ofReal_mul,
      alpha_beta_mul]
    exact hz
  rcases mul_eq_zero.mp hprod with h | h
  · rcases complex_sq_real z alpha alpha_pos (by linear_combination h) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases complex_sq_real z beta beta_pos (by linear_combination h) with h1 | h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))

/-! ## §4 The minimal polynomial of √ε -/

/-- Evaluating the quartic at 2 gives −8171, so it is not the zero polynomial. -/
theorem quartic_ne_zero : quarticQ ≠ 0 := by
  have hev : Polynomial.eval (2 : ℚ) quarticQ = -8171 := by norm_num [quarticQ]
  intro h
  rw [h, Polynomial.eval_zero] at hev
  norm_num at hev

/-- The X⁴-coefficient of the quartic is 1. -/
theorem quartic_coeff_four : quarticQ.coeff 4 = 1 := by
  simp only [quarticQ, Polynomial.coeff_sub, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow]
  norm_num

/-- The quartic's degree is below five: every coefficient past X⁴ vanishes. -/
theorem quartic_natDegree_le : quarticQ.natDegree ≤ 4 := by
  have h1 : quarticQ.degree < ((5 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero quarticQ 5]
    intro m hm
    simp only [quarticQ, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    split_ifs with hc1 hc2 hc3 <;> simp_all
  have h2 : quarticQ.natDegree < 5 :=
    Polynomial.natDegree_lt_iff_degree_lt quartic_ne_zero |>.mpr h1
  omega

/-- The minimal polynomial of √ε vanishes on the quartic's point. -/
theorem aeval_sqrt_quartic : (Polynomial.aeval s) quarticQ = 0 := by
  rw [quarticQ]
  simp only [map_sub, map_add, Polynomial.aeval_C, Polynomial.aeval_X, map_pow,
    map_mul, map_one]
  rw [show s ^ 4 = alpha ^ 2 from by show s ^ (2 * 2) = alpha ^ 2; rw [pow_mul, s_sq]]
  rw [s_sq]
  norm_num
  exact alpha_quadratic

/-- The minimal polynomial of √ε over ℚ divides X⁴ − 2047X² + 1. -/
theorem minpoly_sqrt_dvd : minpoly ℚ s ∣ quarticQ :=
  minpoly.dvd ℚ s aeval_sqrt_quartic

/-- [ℚ(√ε) : ℚ] ≤ 4: the minimal polynomial of √ε has degree at most four. -/
theorem natDegree_minpoly_sqrt_le :
    (minpoly ℚ s).natDegree ≤ 4 := by
  have h1 : (minpoly ℚ s).natDegree ≤ quarticQ.natDegree :=
    Polynomial.natDegree_le_of_dvd minpoly_sqrt_dvd quartic_ne_zero
  exact le_trans h1 quartic_natDegree_le

end Imscribing.Millennium.StarkAbelianityD2048

end
