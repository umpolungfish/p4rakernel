import Imscribing.Millennium.StarkRungFiveDual
import Imscribing.Millennium.SIC_D2048_StarkTheorem
import Imscribing.Millennium.StarkRungFiveTheta

/-!
# StarkRungFiveDualLimit — the dual theta `t → 0⁺` limits

We are given, for `0 < t`:
- `chirp_theta t` `= ∑' n : ℤ, cexp (-((t - 2*I) / con) * n²)` (Mathlib lemma
  `Complex.tsum_exp_neg_mul_int_sq` at `a = (t - 2*i)/con`).
- The dual series `∑' n : ℤ, cexp (-(π : ℂ) * (con / (t - 2*i)) * n²)`, split
  into even and odd parts:
  `dualEven t = 2·∑' m:ℕ, dualTerm t (2m) - 1`,
  `dualOdd  t = 2·∑' m:ℕ, dualTerm t (2m+1)`.

Since `t / (t - 2*i) = i/2 + t²/(2(t²+4)) + i·t/(t²+4)`, the exponent rewrites as
`-(π·con)·t/(t-2i)·n² = u(n) + v(n)·i` with the real parts
`u(n) = -π·(con·t/(t²+4))·n²` (Gaussian) and the imaginary parts
`v(n) = -π·(2·con/(t²+4))·n²` (phase).

For `n = 2m`: `v(2m) = -2π·con·m² + δ(m)` with `-2π·con·m²` an integer multiple
of `2πi` (killed, `con ≡ 1 (mod 4)`) and `δ(m) = 2π·con·m²·t²/(t²+4) → 0`.
So the even part tends to `gaussSumInt(4·con·t/(t²+4))` and `√(t·con)·that → 1`
(the quadratic limit); the deviation is squeezed via `sqMoment_le`.

For `n = 2m+1`: `v(2m+1) = -2π·con·m(m+1) - π·con/2 + φ(m)`; the integer phase
dies, `e^{-iπ·con/2} = -i` (`con ≡ 1 (mod 4)`), `φ(m) → 0`:
the odd part tends to `-i·2·gaussSumHalf(4·con·t/(t²+4))` and `√(t·con)·that → -i`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

open Complex Real Filter Topology
open scoped Complex Real Topology
open Imscribing.Millennium.StarkCharacterD2048
open Imscribing.Millennium.StarkAsympt
open Imscribing.Millennium.StarkDual
open Imscribing.Millennium.StarkTheta

noncomputable section

namespace Imscribing.Millennium.StarkDualLimit

/-! ## Phase and norm utilities -/

/-- The modulus of `e^{iθ} - 1` is controlled by `|θ|`. -/
theorem norm_exp_I_sub_one (θ : ℝ) : ‖cexp (I * (θ : ℂ)) - 1‖ ≤ |θ| := by
  have hθ2 : θ = 2 * (θ / 2) := by ring
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have hc2 : Real.cos (2 * (θ / 2)) = 2 * Real.cos (θ / 2) ^ 2 - 1 := Real.cos_two_mul _
    conv_lhs => rw [hθ2]
    rw [hc2]
    have h := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  have hsq : ‖cexp (I * (θ : ℂ)) - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    have h1 : ‖cexp (I * (θ : ℂ)) - 1‖ ^ 2 = Complex.normSq (cexp (I * (θ : ℂ)) - 1) :=
      (Complex.normSq_eq_norm_sq _).symm
    have hre : (cexp (I * (θ : ℂ))).re = Real.cos θ := by
      simp [Complex.exp_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    have him : (cexp (I * (θ : ℂ))).im = Real.sin θ := by
      simp [Complex.exp_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    have hsq1 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      have h := Real.sin_sq_add_cos_sq θ
      linarith
    rw [h1, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hre, him,
      Complex.one_re, Complex.one_im, sub_zero]
    have hp : Real.sin θ * Real.sin θ = Real.sin θ ^ 2 := by ring
    rw [hp, hsq1, hcos]
    ring
  have hsq2 : ‖cexp (I * (θ : ℂ)) - 1‖ ^ 2 ≤ θ ^ 2 := by
    have hθ4 : θ ^ 2 = 4 * (θ / 2) ^ 2 := by rw [hθ2]; ring
    rw [hsq, hθ4]
    exact mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq) (by norm_num)
  calc ‖cexp (I * (θ : ℂ)) - 1‖ = Real.sqrt (‖cexp (I * (θ : ℂ)) - 1‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (θ ^ 2) := Real.sqrt_le_sqrt hsq2
    _ = |θ| := Real.sqrt_sq_eq_abs θ

/-- Norm of a nonnegative real scalar times a complex number. -/
theorem norm_real_scale (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    ‖Complex.ofReal c * z‖ = c * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

theorem ofReal_intCast (n : ℤ) : ((n : ℤ) : ℂ) = Complex.ofReal ((n : ℤ) : ℝ) := by
  refine Complex.ext ?_ ?_ <;> simp [Complex.intCast_re, Complex.intCast_im]

theorem cexp_ofReal (x : ℝ) : cexp ((x : ℂ)) = Complex.ofReal (rexp x) :=
  (Complex.ofReal_exp x).symm

theorem rexp_norm_ofReal (x : ℝ) : ‖cexp ((x : ℂ))‖ = rexp x := by
  rw [Complex.norm_exp, Complex.ofReal_re]

/-- An integer multiple of `2πi` in the exponent kills the exponential. -/
theorem exp_I_two_pi (k : ℤ) :
    cexp (I * Complex.ofReal (((k : ℤ) : ℝ) * 2 * π)) = 1 := by
  have h : I * Complex.ofReal (((k : ℤ) : ℝ) * 2 * π) = ((k : ℤ) : ℂ) * ((2 : ℂ) * π * I) := by
    push_cast
    ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem exp_I_two_pi_natneg (m : ℕ) :
    cexp (I * Complex.ofReal (((-((m : ℕ) : ℤ)) : ℝ) * 2 * π)) = 1 := by
  convert exp_I_two_pi (-(m : ℤ)) using 1 <;> push_cast <;> ring

theorem exp_I_neg_half : cexp (I * (Complex.ofReal (-(π / 2 : ℝ)))) = -(I : ℂ) := by
  have h : I * (Complex.ofReal (-(π / 2 : ℝ))) = -↑π / 2 * I := by
    push_cast
    ring
  rw [h]
  exact Complex.exp_neg_pi_div_two_mul_I

/-! ## The dual parameter -/

/-- The dual parameter `con / (t - 2i)` in real-imaginary form. -/
theorem dualParam_eq (t : ℝ) :
    Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)
      = Complex.ofReal ((con : ℝ) * t / (t ^ 2 + 4))
        + Complex.ofReal ((con : ℝ) * 2 / (t ^ 2 + 4)) * I := by
  apply Complex.ext
  · rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.normSq_apply, Complex.add_re, Complex.sub_im]
    norm_num
    ring
  · rw [Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.normSq_apply, Complex.add_im, Complex.sub_re]
    norm_num
    ring

/-- The real part of `con / (t - 2i)`. -/
theorem re_dualParam (t : ℝ) : (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)).re
    = (con : ℝ) * t / (t ^ 2 + 4) := by
  rw [dualParam_eq t]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

/-- The imaginary part of `con / (t - 2i)`. -/
theorem im_dualParam (t : ℝ) : (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)).im
    = (con : ℝ) * 2 / (t ^ 2 + 4) := by
  rw [dualParam_eq t]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add, add_zero]

/-- The exponent of the dual series, rewritten into Gaussian + phase parts. -/
theorem dualExponent_eq (t : ℝ) (ht : 0 < t) (n : ℤ) :
    ((-(↑π) * (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)) * ((n : ℂ) ^ 2)) : ℂ)
      = Complex.ofReal (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2)
        + Complex.ofReal (-π * ((con : ℝ) * 2 / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2) * I := by
  have hq2 : ((n : ℤ) : ℂ) ^ 2 = Complex.ofReal (((n : ℤ) : ℝ) ^ 2) := by
    rw [ofReal_intCast, ← Complex.ofReal_pow]
  have hsplit : ((-(↑π) * (Complex.ofReal ((con : ℝ) * t / (t ^ 2 + 4))
        + Complex.ofReal ((con : ℝ) * 2 / (t ^ 2 + 4)) * I)
      * Complex.ofReal (((n : ℤ) : ℝ) ^ 2) : ℂ))
      = Complex.ofReal (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2)
        + Complex.ofReal (-π * ((con : ℝ) * 2 / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2) * I := by
    refine Complex.ext ?_ ?_
    · simp only [mul_add, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    · simp only [mul_add, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  rw [hq2, dualParam_eq t, hsplit]

/-! ## The dual series and its even/odd split -/

/-- The `n`-th term of the dual theta series. -/
noncomputable def dualTerm (t : ℝ) (n : ℤ) : ℂ :=
  cexp (-(↑π) * (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)) * ((n : ℂ) ^ 2))

/-- The full dual theta series. -/
noncomputable def dualTheta (t : ℝ) : ℂ := ∑' n : ℤ, dualTerm t n

/-- Twice the even part (`n = 2m`, `m ≥ 0`), minus the `m = 0` term. -/
noncomputable def dualEven (t : ℝ) : ℂ :=
  2 * (∑' n : ℕ, dualTerm t ((2 * n : ℕ) : ℤ)) - 1

/-- Twice the odd part (`n = 2m+1`, `m ≥ 0`). -/
noncomputable def dualOdd (t : ℝ) : ℂ :=
  2 * (∑' n : ℕ, dualTerm t ((2 * n + 1 : ℕ) : ℤ))

/-- Norm of a dual-series term. -/
theorem dualTerm_norm (t : ℝ) (ht : 0 < t) (n : ℤ) :
    ‖dualTerm t n‖ = rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2) := by
  have harg := dualExponent_eq t ht n
  have h2 : ‖cexp (Complex.ofReal (-π * ((con : ℝ) * 2 / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2) * I)‖
      = 1 := by
    have hre2 : (Complex.ofReal (-π * ((con : ℝ) * 2 / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2) * I).re
        = 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_self]
    rw [Complex.norm_exp, hre2, Real.exp_zero]
  simp only [dualTerm]
  rw [harg, Complex.exp_add, norm_mul, rexp_norm_ofReal, h2] <;> simp

theorem summable_dualTerm (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℤ => dualTerm t n) := by
  refine Summable.of_norm ?_
  have ha : 0 < (con : ℝ) * t / (t ^ 2 + 4) := by
    exact div_pos (mul_pos (Nat.cast_pos.mpr con_pos) ht) (by positivity)
  exact (summable_gaussReal _ ha).congr (fun n => by rw [dualTerm_norm t ht n])

/-- Evenness of the dual terms. -/
theorem dualTerm_even (t : ℝ) : ∀ k : ℤ, dualTerm t (-k) = dualTerm t k := by
  intro k
  have h1 : ((-k : ℤ) : ℂ) ^ 2 = ((k : ℤ) : ℂ) ^ 2 := by push_cast; ring
  simp only [dualTerm, h1]

/-- The full dual theta series splits into even and odd parts. -/
theorem dualTheta_split (t : ℝ) (ht : 0 < t) : dualTheta t = dualEven t + dualOdd t := by
  have hg := summable_dualTerm t ht
  have h0 : dualTerm t 0 = 1 := by simp [dualTerm]
  have h := tsum_int_even_odd (fun n : ℤ => dualTerm t n) hg (dualTerm_even t)
  simp only [dualTheta, dualEven, dualOdd]
  rw [h]
  simp only [h0]
  ring

/-! ## Summability of the Gaussian moment series -/

theorem summable_sqMoment (a : ℝ) (ha : 0 < a) :
    Summable (fun k : ℕ => ((k : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * ((k : ℕ) : ℝ) ^ 2)) := by
  have hc : 0 < π * a := mul_pos Real.pi_pos ha
  have hgsum : Summable (fun k : ℕ => rexp (-(π * a / 2) * ((k : ℕ) : ℝ) ^ 2)) :=
    (summable_gaussNat (a / 2) (by positivity)).congr fun k => by congr 1; ring
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (exp_nonneg _))
    (fun k => sqMoment_pointwise hc ((k : ℕ) : ℝ)) (summable_const_mul hgsum (4 / (π * a)))

/-- Unconditional version of `sqMoment_le` (for `a > 1` dominated by `a = 1`). -/
theorem sqMoment_le' (a : ℝ) (ha : 0 < a) :
    ∑' k : ℕ, ((k : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * ((k : ℕ) : ℝ) ^ 2)
      ≤ 2 / (a * Real.sqrt a) + 2 := by
  by_cases hle : a ≤ 1
  · have := sqMoment_le a ha hle
    linarith
  · have h1 : (1 : ℝ) ≤ a := le_of_lt (lt_of_not_ge hle)
    have hpt : ∀ k : ℕ, ((k : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * ((k : ℕ) : ℝ) ^ 2)
        ≤ ((k : ℕ) : ℝ) ^ 2 * rexp (-(π * 1) * ((k : ℕ) : ℝ) ^ 2) := by
      intro k
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine exp_le_exp.mpr ?_
      have hle2 : π * 1 ≤ π * a := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
      have hneg : -(π * a) * ((k : ℕ) : ℝ) ^ 2 ≤ -(π * 1) * ((k : ℕ) : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      exact hneg
    have hd : Summable (fun k : ℕ => ((k : ℕ) : ℝ) ^ 2 * rexp (-(π * 1) * ((k : ℕ) : ℝ) ^ 2)) :=
      summable_sqMoment 1 (by norm_num)
    have hs := Summable.tsum_le_tsum hpt (summable_sqMoment a ha) hd
    have h2 := sqMoment_le 1 (by norm_num) (by norm_num)
    rw [show ((1 : ℝ) * Real.sqrt 1) = 1 from by norm_num] at h2
    have hpos2 : (0 : ℝ) ≤ 2 / (a * Real.sqrt a) :=
      div_nonneg (by norm_num) (mul_nonneg ha.le (Real.sqrt_nonneg a))
    linarith

theorem summable_gaussHalf (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => rexp (-π * a * (((n : ℕ) : ℝ) + 1 / 2) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => exp_nonneg _) (fun n => ?_) (summable_gaussNat a ha)
  refine exp_le_exp.mpr ?_
  have hsq : ((n : ℕ) : ℝ) ^ 2 ≤ (((n : ℕ) : ℝ) + 1 / 2) ^ 2 := by
    have hexp : (((n : ℕ) : ℝ) + 1 / 2) ^ 2
        = ((n : ℕ) : ℝ) ^ 2 + ((n : ℕ) : ℝ) + 1 / 4 := by ring
    rw [hexp]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hneg : -π * a ≤ 0 := by linarith [mul_pos Real.pi_pos ha]
  exact mul_le_mul_of_nonpos_left hsq hneg

theorem summable_oddSq (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ) ^ 2)
      * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := by
  have hterm : ∀ n : ℕ, (((2 * n + 1 : ℕ) : ℝ) ^ 2)
      * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
      ≤ 4 * (((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2) * rexp (-(π * a) * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2))) := by
    intro n
    have h1 : (((2 * n + 1 : ℕ) : ℝ) ^ 2) ≤ 4 * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2) := by
      have hq : (((2 * n + 1 : ℕ) : ℝ)) = 2 * ((n : ℕ) : ℝ) + 1 := by push_cast; ring
      have hr : ((((n : ℕ) + 1 : ℕ) : ℝ)) = ((n : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hq, hr]
      have hx : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h2 : rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
        ≤ rexp (-(π * a) * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)) := by
      refine exp_le_exp.mpr ?_
      have hge : ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2) ≤ (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
        have hq : (((2 * n + 1 : ℕ) : ℝ)) = 2 * ((n : ℕ) : ℝ) + 1 := by push_cast; ring
        have hr : ((((n : ℕ) + 1 : ℕ) : ℝ)) = ((n : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [hq, hr]
        nlinarith [sq_nonneg ((n : ℕ) : ℝ)]
      have hneg : -(π * a) ≤ 0 := by linarith [mul_pos Real.pi_pos ha]
      exact mul_le_mul_of_nonpos_left hge hneg
    calc ((2 * n + 1 : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
        ≤ (4:ℝ) * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 (exp_nonneg _)
      _ = 4 * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := by
          ring
      _ ≤ 4 * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)) :=
          (by refine mul_le_mul_of_nonneg_left ?_ (by norm_num); exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
  have hsucc : Summable (fun n : ℕ => ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2
      * rexp (-(π * a) * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2))) :=
    (summable_sqMoment a ha).comp_injective Nat.succ_injective
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sq_nonneg _) (exp_nonneg _)) hterm (summable_const_mul hsucc 4)

theorem oddSqMoment_le (a : ℝ) (ha : 0 < a) (hle : a ≤ 1) :
    ∑' n : ℕ, (((2 * n + 1 : ℕ) : ℝ) ^ 2)
      * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
      ≤ 8 / (a * Real.sqrt a) := by
  have hmain := sqMoment_le a ha hle
  have hterm : ∀ n : ℕ, (((2 * n + 1 : ℕ) : ℝ) ^ 2)
      * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
      ≤ 4 * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)) := by
    intro n
    have h1 : (((2 * n + 1 : ℕ) : ℝ) ^ 2) ≤ 4 * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2) := by
      have hq : (((2 * n + 1 : ℕ) : ℝ)) = 2 * ((n : ℕ) : ℝ) + 1 := by push_cast; ring
      have hr : ((((n : ℕ) + 1 : ℕ) : ℝ)) = ((n : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hq, hr]
      have hx : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h2 : rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
        ≤ rexp (-(π * a) * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)) := by
      refine exp_le_exp.mpr ?_
      have hge : ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2) ≤ (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
        have hq : (((2 * n + 1 : ℕ) : ℝ)) = 2 * ((n : ℕ) : ℝ) + 1 := by push_cast; ring
        have hr : ((((n : ℕ) + 1 : ℕ) : ℝ)) = ((n : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [hq, hr]
        nlinarith [sq_nonneg ((n : ℕ) : ℝ)]
      have hneg : -(π * a) ≤ 0 := by linarith [mul_pos Real.pi_pos ha]
      exact mul_le_mul_of_nonpos_left hge hneg
    calc ((2 * n + 1 : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
        ≤ (4:ℝ) * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 (exp_nonneg _)
      _ = 4 * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := by
          ring
      _ ≤ 4 * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)) :=
          (by refine mul_le_mul_of_nonneg_left ?_ (by norm_num); exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
  have hsucc : Summable (fun n : ℕ => ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2
      * rexp (-(π * a) * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2))) :=
    (summable_sqMoment a ha).comp_injective Nat.succ_injective
  have h4s : Summable (fun n : ℕ => (4 : ℝ) * ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2
      * rexp (-(π * a) * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2))) := summable_const_mul hsucc 4
  have hle2 := Summable.tsum_le_tsum hterm (summable_oddSq a ha) h4s
  have htail := (summable_sqMoment a ha).tsum_eq_zero_add
  have h0 : ((0 : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * ((0 : ℕ) : ℝ) ^ 2) = 0 := by simp
  rw [h0, zero_add] at htail
  rw [Summable.tsum_mul_left (4 : ℝ) hsucc] at hle2
  rw [← htail] at hle2
  have hpos : 0 ≤ 4 * (∑' k : ℕ, ((k : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * ((k : ℕ) : ℝ) ^ 2)) := by
    positivity
  calc ∑' n : ℕ, (((2 * n + 1 : ℕ) : ℝ) ^ 2)
        * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
      ≤ 4 * (∑' k : ℕ, ((k : ℕ) : ℝ) ^ 2 * rexp (-(π * a) * ((k : ℕ) : ℝ) ^ 2)) := hle2
    _ ≤ 4 * (2 / (a * Real.sqrt a)) :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 8 / (a * Real.sqrt a) := by ring

/-- Unconditional version of `oddSqMoment_le`. -/
theorem oddSqMoment_le' (a : ℝ) (ha : 0 < a) :
    ∑' n : ℕ, (((2 * n + 1 : ℕ) : ℝ) ^ 2)
      * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
      ≤ 8 / (a * Real.sqrt a) + 8 := by
  by_cases hle : a ≤ 1
  · have := oddSqMoment_le a ha hle
    linarith
  · have h1 : (1 : ℝ) ≤ a := le_of_lt (lt_of_not_ge hle)
    have hpt : ∀ n : ℕ, (((2 * n + 1 : ℕ) : ℝ) ^ 2)
        * rexp (-(π * a) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
        ≤ (((2 * n + 1 : ℕ) : ℝ) ^ 2) * rexp (-(π * 1) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) := by
      intro n
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine exp_le_exp.mpr ?_
      have hle2 : π * 1 ≤ π * a := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have hd : Summable (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ) ^ 2)
        * rexp (-(π * 1) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := summable_oddSq 1 (by norm_num)
    have hs := Summable.tsum_le_tsum hpt (summable_oddSq a ha) hd
    have h2 := oddSqMoment_le 1 (by norm_num) (by norm_num)
    rw [show ((1 : ℝ) * Real.sqrt 1) = 1 from by norm_num] at h2
    have hpos2 : (0 : ℝ) ≤ 8 / (a * Real.sqrt a) :=
      div_nonneg (by norm_num) (mul_nonneg ha.le (Real.sqrt_nonneg a))
    linarith

/-! ## The main terms match the Gaussian bricks -/

/-- The even main half-line series is the complexification of `gaussSumNat`. -/
theorem evenMain_eq (a : ℝ) (ha : 0 < a) :
    (∑' n : ℕ, cexp ((-π * a * ((n : ℕ) : ℝ) ^ 2) : ℂ))
      = ((gaussSumNat a : ℝ) : ℂ) := by
  have hconv : (∑' n : ℕ, cexp ((-π * a * ((n : ℕ) : ℝ) ^ 2) : ℂ))
      = ∑' n : ℕ, (Complex.ofReal (rexp (-π * a * ((n : ℕ) : ℝ) ^ 2)) : ℂ) := by
    refine tsum_congr (fun n => ?_)
    have hx : ((-π * a * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)
        = -↑π * ↑a * ↑((n : ℕ) : ℝ) ^ 2 := by push_cast; ring
    rw [← hx]
    exact cexp_ofReal _
  rw [hconv]
  simpa [gaussSumNat] using
    (Complex.ofRealCLM.map_tsum (summable_gaussNat a ha)).symm

/-- The odd main half-line series is the complexification of `gaussSumHalf`. -/
theorem oddMain_eq (a : ℝ) (ha : 0 < a) :
    (∑' n : ℕ, cexp ((-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ))
      = ((gaussSumHalf (4 * a) : ℝ) : ℂ) := by
  have hconv : (∑' n : ℕ, cexp ((-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ))
      = ∑' n : ℕ, (Complex.ofReal (rexp (-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) : ℂ) := by
    refine tsum_congr (fun n => ?_)
    have hx : ((-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2) : ℝ) : ℂ)
        = -↑π * ↑a * ↑(((2 * n + 1 : ℕ) : ℝ)) ^ 2 := by push_cast; ring
    rw [← hx]
    exact cexp_ofReal _
  have hsum : Summable (fun n : ℕ =>
      rexp (-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun n => exp_nonneg _) (fun n => ?_)
      (summable_gaussNat a ha)
    refine exp_le_exp.mpr ?_
    have h1 : ((n : ℕ) : ℝ) ^ 2 ≤ (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
      have h2 : (((2 * n + 1 : ℕ) : ℝ)) = 2 * ((n : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [h2]; nlinarith [sq_nonneg ((n : ℕ) : ℝ)]
    have hneg : -π * a ≤ 0 := by linarith [mul_pos Real.pi_pos ha]
    exact mul_le_mul_of_nonpos_left h1 hneg
  rw [hconv]
  have ht : (∑' n : ℕ, (Complex.ofReal (rexp (-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) : ℂ))
      = Complex.ofReal (∑' n : ℕ, rexp (-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) :=
    (Complex.ofRealCLM.map_tsum hsum).symm
  rw [ht]
  rw [tsum_congr (fun n : ℕ => (by congr 1; push_cast; ring :
    rexp (-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
      = rexp (-π * (4 * a) * (((n : ℕ) : ℝ) + 1 / 2) ^ 2)))]
  rfl

/-- The even `n = 2m` term: Gaussian times a unit phase. -/
theorem dualEven_term (t : ℝ) (ht : 0 < t) (n : ℕ) :
    dualTerm t ((2 * n : ℕ) : ℤ)
      = cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
        * cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) := by
  have h := dualExponent_eq t ht ((2 * n : ℕ) : ℤ)
  have hcast : (((2 * n : ℕ) : ℤ) : ℝ) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at h
  simp only [dualTerm]
  rw [h, Complex.exp_add, mul_comm (Complex.ofReal _) I]
  have hvs : Complex.ofReal (-π * ((con : ℝ) * 2 / (t ^ 2 + 4)) * (((2 * n : ℕ) : ℝ) ^ 2))
      = Complex.ofReal (((-((con * (n * n) : ℕ) : ℤ)) : ℝ) * 2 * π)
        + Complex.ofReal (2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) := by
    rw [← Complex.ofReal_add]
    congr 1
    push_cast
    field_simp
    ring_nf
  rw [hvs, mul_add, Complex.exp_add]
  rw [exp_I_two_pi_natneg (con * (n * n)), one_mul]
  rw [mul_comm]
  rw [show (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n : ℕ) : ℝ) ^ 2))
      = -π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2 from by push_cast; ring_nf]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
/-- The odd `n = 2m+1` term: Gaussian times `-i` up to a decaying phase. -/
theorem dualOdd_term (t : ℝ) (ht : 0 < t) (n : ℕ) :
    dualTerm t ((2 * n + 1 : ℕ) : ℤ)
      = -(I : ℂ) * cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ))
        * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ) := by
  have h := dualExponent_eq t ht ((2 * n + 1 : ℕ) : ℤ)
  have hcast : (((2 * n + 1 : ℕ) : ℤ) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at h
  simp only [dualTerm]
  rw [h, Complex.exp_add, mul_comm (Complex.ofReal _) I]
  have hvs : Complex.ofReal (-π * ((con : ℝ) * 2 / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
      = Complex.ofReal (((-((con * (n * (n + 1)) : ℕ) : ℤ)) : ℝ) * 2 * π)
        + Complex.ofReal (-(π * (con : ℝ) / 2))
        + Complex.ofReal (π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) := by
    rw [← Complex.ofReal_add, ← Complex.ofReal_add]
    congr 1
    push_cast
    field_simp
    ring_nf
  rw [hvs, mul_add, mul_add, Complex.exp_add, Complex.exp_add]
  rw [exp_I_two_pi_natneg (con * (n * (n + 1))), one_mul]
  have h5 := Nat.div_add_mod con 4
  rw [con_mod_four] at h5
  have h6 : con / 4 = (con - 1) / 4 := by omega
  have hint2 : cexp (I * (Complex.ofReal (-(π * (con : ℝ) / 2)))) = -(I : ℂ) := by
    have hsplit : (-(π * (con : ℝ) / 2) : ℝ)
        = (((-(((con - 1) / 4 : ℕ) : ℤ)) : ℝ) * 2 * π) + (-(π / 2 : ℝ)) := by
      have hq : (con : ℝ) = 4 * (((con - 1) / 4 : ℕ) : ℝ) + 1 := by
        norm_num [con]
      rw [hq]
      field_simp
      ring
    rw [hsplit, Complex.ofReal_add, mul_add, Complex.exp_add,
      exp_I_two_pi_natneg ((con - 1) / 4), one_mul, exp_I_neg_half]
  rw [hint2]
  ring_nf
  push_cast
  ring_nf

/-! ## Deviation terms and their bounds -/

/-- Per-term bound for the even deviation series. -/
theorem dualEven_dev_term (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ‖cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
        * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)‖
      ≤ (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (((n : ℕ) : ℝ) ^ 2
          * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)) := by
  calc ‖cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
          * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)‖
      ≤ ‖cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)‖
          * ‖cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1‖ :=
        norm_mul_le _ _
    _ = rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)
          * ‖cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1‖ := by
        congr 1
        convert rexp_norm_ofReal (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) using 1 <;> push_cast <;> ring
    _ ≤ rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)
          * (2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) := by
        have hθ : 0 ≤ 2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4) := by positivity
        refine mul_le_mul_of_nonneg_left ?_ (exp_nonneg _)
        have hh := norm_exp_I_sub_one (2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4))
        rw [abs_of_nonneg hθ] at hh
        convert hh using 1 <;> push_cast <;> ring
    _ = (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (((n : ℕ) : ℝ) ^ 2
          * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)) := by ring

theorem dualEven_dev_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
        * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)) := by
  have ha0 : 0 < 4 * (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht) (by positivity)
  have hdom : Summable (fun n : ℕ => (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (((n : ℕ) : ℝ) ^ 2
      * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2))) :=
    by convert summable_const_mul (summable_sqMoment (4 * (con : ℝ) * t / (t ^ 2 + 4)) ha0)
        (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) using 1 <;> ext n <;> ring
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (dualEven_dev_term t ht) hdom)

theorem dualEven_dev_bound (t : ℝ) (ht : 0 < t) :
    (∑' n : ℕ, ‖cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
        * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)‖)
      ≤ (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))
        * (2 / ((4 * (con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
          + 2) := by
  have ha0 : 0 < 4 * (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht) (by positivity)
  have hdom : Summable (fun n : ℕ => (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (((n : ℕ) : ℝ) ^ 2
      * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2))) :=
    by convert summable_const_mul (summable_sqMoment (4 * (con : ℝ) * t / (t ^ 2 + 4)) ha0)
        (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) using 1 <;> ext n <;> ring
  have hnorms : Summable (fun n : ℕ =>
      ‖cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
        * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (dualEven_dev_term t ht) hdom
  have hsq := sqMoment_le' (4 * (con : ℝ) * t / (t ^ 2 + 4)) ha0
  have hsucc : Summable (fun n : ℕ => ((n : ℕ) : ℝ) ^ 2
      * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)) := by
    convert summable_sqMoment (4 * (con : ℝ) * t / (t ^ 2 + 4)) ha0 using 1 <;> ext n <;> ring_nf
  calc (∑' n : ℕ, ‖cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
          * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)‖)
      ≤ ∑' n : ℕ, (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (((n : ℕ) : ℝ) ^ 2
          * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)) :=
        Summable.tsum_le_tsum (dualEven_dev_term t ht) hnorms hdom
    _ = (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (∑' n : ℕ, ((n : ℕ) : ℝ) ^ 2
          * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)) :=
        (by
          rw [← Summable.tsum_mul_left (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) hsucc])
    _ ≤ (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))
          * (2 / ((4 * (con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
            + 2) := mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hsq) (by positivity)

theorem summable_oddGauss (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => rexp (-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := by
  refine Summable.of_nonneg_of_le (fun n => exp_nonneg _) (fun n => ?_) (summable_gaussNat a ha)
  refine exp_le_exp.mpr ?_
  have h1 : ((n : ℕ) : ℝ) ^ 2 ≤ (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
    have h2 : (((2 * n + 1 : ℕ) : ℝ)) = 2 * ((n : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h2]; nlinarith [sq_nonneg ((n : ℕ) : ℝ)]
  have hneg : -π * a ≤ 0 := by linarith [mul_pos Real.pi_pos ha]
  exact mul_le_mul_of_nonpos_left h1 hneg

/-- Per-term bound for the odd deviation series. -/
theorem dualOdd_dev_term (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ‖(I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))‖
      ≤ (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4))) * ((((2 * n + 1 : ℕ) : ℝ) ^ 2)
          * rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := by
  have hphi : 0 ≤ π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2 / (2 * (t ^ 2 + 4)) := by
    positivity
  calc ‖(I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
          * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))‖
      ≤ ‖cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)‖
          * ‖1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ))‖ := by
        simp [norm_mul, Complex.norm_I]
    _ = rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
          * ‖1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ))‖ := by
        congr 1
        convert rexp_norm_ofReal (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) using 1 <;> push_cast <;> ring
    _ ≤ rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
          * (π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2 / (2 * (t ^ 2 + 4))) := by
        refine mul_le_mul_of_nonneg_left ?_ (exp_nonneg _)
        rw [norm_sub_rev]
        have hθ : 0 ≤ π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2 / (2 * (t ^ 2 + 4)) := by positivity
        have hh := norm_exp_I_sub_one (π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2 / (2 * (t ^ 2 + 4)))
        rw [abs_of_nonneg hθ] at hh
        convert hh using 1 <;> push_cast <;> ring
    _ = (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4))) * ((((2 * n + 1 : ℕ) : ℝ) ^ 2)
          * rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := by ring

theorem dualOdd_dev_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))) := by
  have ha0 : 0 < (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (Nat.cast_pos.mpr con_pos) ht) (by positivity)
  have hdom : Summable (fun n : ℕ => (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
      * ((((2 * n + 1 : ℕ) : ℝ) ^ 2)
        * rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)))) :=
    by convert summable_const_mul (summable_oddSq ((con : ℝ) * t / (t ^ 2 + 4)) ha0)
        (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4))) using 1 <;> ext n <;> ring
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (dualOdd_dev_term t ht) hdom)

theorem dualOdd_dev_bound (t : ℝ) (ht : 0 < t) :
    (∑' n : ℕ, ‖(I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))‖)
      ≤ (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
        * (8 / (((con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt ((con : ℝ) * t / (t ^ 2 + 4))) + 8) := by
  have ha0 : 0 < (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (Nat.cast_pos.mpr con_pos) ht) (by positivity)
  have hdom : Summable (fun n : ℕ => (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
      * ((((2 * n + 1 : ℕ) : ℝ) ^ 2)
        * rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)))) :=
    by convert summable_const_mul (summable_oddSq ((con : ℝ) * t / (t ^ 2 + 4)) ha0)
        (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4))) using 1 <;> ext n <;> ring
  have hnorms : Summable (fun n : ℕ =>
      ‖(I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (dualOdd_dev_term t ht) hdom
  have hsq := oddSqMoment_le' ((con : ℝ) * t / (t ^ 2 + 4)) ha0
  have hsucc : Summable (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ) ^ 2)
      * rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := by
    convert summable_oddSq ((con : ℝ) * t / (t ^ 2 + 4)) ha0 using 1 <;> ext n <;> ring_nf
  calc (∑' n : ℕ, ‖(I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))‖)
      ≤ ∑' n : ℕ, (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4))) * ((((2 * n + 1 : ℕ) : ℝ) ^ 2)
          * rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) :=
        Summable.tsum_le_tsum (dualOdd_dev_term t ht) hnorms hdom
    _ = (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4))) * (∑' n : ℕ, (((2 * n + 1 : ℕ) : ℝ) ^ 2)
          * rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) :=
        (by
          rw [← Summable.tsum_mul_left (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4))) hsucc])
    _ ≤ (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
          * (8 / (((con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt ((con : ℝ) * t / (t ^ 2 + 4)))
            + 8) := mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hsq) (by positivity)

/-! ## The even/odd rearrangements -/

theorem dualEven_eq (t : ℝ) (ht : 0 < t) :
    dualEven t
      = ((gaussSumInt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)
        + 2 * (∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1)) := by
  have ha0 : 0 < 4 * (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht) (by positivity)
  have hsu : Summable (fun n : ℕ =>
      cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)) := by
    refine Summable.of_norm ?_
    exact (summable_gaussNat (4 * (con : ℝ) * t / (t ^ 2 + 4)) ha0).congr
      (fun n => by
        convert (rexp_norm_ofReal (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)).symm using 1 <;> push_cast <;> ring)
  have hsd := dualEven_dev_summable t ht
  have hsplit : (∑' n : ℕ, dualTerm t ((2 * n : ℕ) : ℤ))
      = (∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ))
        + (∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1)) := by
    rw [← Summable.tsum_add hsu hsd]
    exact tsum_congr (fun n => by rw [dualEven_term t ht n]; ring)
  have hGint : ((gaussSumInt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)
      = 2 * ((gaussSumNat (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ) - 1 := by
    have h := gaussSumInt_eq (4 * (con : ℝ) * t / (t ^ 2 + 4)) ha0
    rw [h]
    push_cast
    ring
  have hE : (∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ))
      = ((gaussSumNat (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ) := by
    convert evenMain_eq (4 * (con : ℝ) * t / (t ^ 2 + 4)) ha0 using 1 <;> push_cast <;> ring
  calc dualEven t
      = 2 * (∑' n : ℕ, dualTerm t ((2 * n : ℕ) : ℤ)) - 1 := rfl
    _ = 2 * ((∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ))
          + (∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1))) - 1 := by rw [hsplit]
    _ = ((gaussSumInt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)
          + 2 * (∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1)) := by
        rw [hE, hGint]
        ring

theorem dualOdd_eq (t : ℝ) (ht : 0 < t) :
    dualOdd t
      = -(I : ℂ) * ((2 * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)
        + 2 * (∑' n : ℕ, (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
              * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ)))) := by
  have ha0 : 0 < (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (Nat.cast_pos.mpr con_pos) ht) (by positivity)
  have hsu : Summable (fun n : ℕ =>
      cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)) := by
    refine Summable.of_norm ?_
    exact (summable_oddGauss ((con : ℝ) * t / (t ^ 2 + 4)) ha0).congr
      (fun n => by
        convert (rexp_norm_ofReal (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))).symm using 1 <;> push_cast <;> ring)
  have hsd := dualOdd_dev_summable t ht
  have hsuI : Summable (fun n : ℕ => (-(I : ℂ)) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
      * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)) := Summable.mul_left (-(I : ℂ)) hsu
  have hsplit : (∑' n : ℕ, dualTerm t ((2 * n + 1 : ℕ) : ℤ))
      = (-(I : ℂ)) * (∑' n : ℕ, cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ))
        + (∑' n : ℕ, (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
              * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ)))) := by
    rw [← Summable.tsum_mul_left (-(I : ℂ)) hsu]
    rw [← Summable.tsum_add hsuI hsd]
    exact tsum_congr (fun n => by rw [dualOdd_term t ht n]; ring_nf)
  have hodd : ((2 * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)
      = 2 * (∑' n : ℕ, cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)) := by
    have hO : (∑' n : ℕ, cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
          * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ))
        = ((gaussSumHalf (4 * ((con : ℝ) * t / (t ^ 2 + 4))) : ℝ) : ℂ) := by
      convert oddMain_eq ((con : ℝ) * t / (t ^ 2 + 4)) ha0 using 1 <;> push_cast <;> ring
    rw [hO]
    push_cast
    congr 2
    ring
  calc dualOdd t
      = 2 * (∑' n : ℕ, dualTerm t ((2 * n + 1 : ℕ) : ℤ)) := rfl
    _ = 2 * ((-(I : ℂ)) * (∑' n : ℕ, cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
              * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ))
          + (∑' n : ℕ, (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
              * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ))))) := by rw [hsplit]
    _ = -(I : ℂ) * ((2 * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)
          + 2 * (∑' n : ℕ, (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
              * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ)))) := by
        rw [mul_add]
        rw [show 2 * ((-(I : ℂ)) * (∑' n : ℕ, cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
              * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ))
            ) = (-(I : ℂ)) * (2 * (∑' n : ℕ, cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
              * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ))) by ring]
        rw [← hodd]

/-! ## Tendsto machinery -/

/-- `√(t·con) · K·(π·con·t²/(t²+4)) → 0` — the slack term. -/
theorem extra_tendsto (K : ℝ) :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t)
        * (K * ((π : ℝ) * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => Real.sqrt ((con : ℝ) * t)) 0 :=
      Real.continuous_sqrt.continuousAt.comp (by fun_prop)
    exact Tendsto.mono_left (by simpa using hc.tendsto) nhdsWithin_le_nhds
  have h2 : Tendsto (fun t : ℝ => K * ((π : ℝ) * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => K * ((π : ℝ) * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))) 0 := by
      refine ContinuousAt.mul continuousAt_const ?_
      refine ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by norm_num)
    exact Tendsto.mono_left (by simpa using hc.tendsto) nhdsWithin_le_nhds
  simpa using h1.mul h2

/-- `√(t·con)/√(4·con·t/(t²+4)) → 1`. -/
theorem sqrtRatio_tendsto :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t)
      / Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4))) (𝓝[>] 0) (𝓝 1) := by
  have hcongr : (fun t : ℝ => Real.sqrt ((con : ℝ) * t)
        / Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun t : ℝ => Real.sqrt ((t ^ 2 + 4) / 4)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have htne : (t : ℝ) ≠ 0 := ne_of_gt ht.1
    have h1 : Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4))
        = Real.sqrt (4 * (con : ℝ) * t) / Real.sqrt (t ^ 2 + 4) :=
      Real.sqrt_div (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (Nat.cast_nonneg _)) (le_of_lt ht.1)) (t ^ 2 + 4)
    have hD : Real.sqrt ((con : ℝ) * t) / (Real.sqrt (4 * (con : ℝ) * t)
          / Real.sqrt (t ^ 2 + 4)) = Real.sqrt ((t ^ 2 + 4) / 4) := by
      have hposct : 0 < (con : ℝ) * t := mul_pos (Nat.cast_pos.mpr con_pos) ht.1
      have hs4 : Real.sqrt (4 * (con : ℝ) * t) = 2 * Real.sqrt ((con : ℝ) * t) := by
        rw [show 4 * (con : ℝ) * t = (4 : ℝ) * ((con : ℝ) * t) by ring,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      rw [hs4, Real.sqrt_div (by positivity : 0 ≤ t ^ 2 + 4) 4]
      field_simp [Real.sqrt_ne_zero'.2 hposct]
      ring
    rw [h1, hD]
  refine Tendsto.congr' hcongr.symm ?_
  have hcv : ContinuousAt (fun t : ℝ => Real.sqrt ((t ^ 2 + 4) / 4)) 0 := by
    refine Real.continuous_sqrt.continuousAt.comp ?_
    exact ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by norm_num)
  have hval : (Real.sqrt ((0 ^ 2 + 4) / 4) : ℝ) = 1 := by norm_num
  have hT := hcv.tendsto
  rw [hval] at hT
  exact Tendsto.mono_left hT nhdsWithin_le_nhds

/-- `c₀·t/(t²+4) → 0⁺` along `t → 0⁺`. -/
theorem tendsto_a1 {c₀ : ℝ} (hc₀ : 0 < c₀) :
    Tendsto (fun t : ℝ => c₀ * t / (t ^ 2 + 4)) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hc : ContinuousAt (fun t : ℝ => c₀ * t / (t ^ 2 + 4)) 0 := by
      refine ContinuousAt.div₀ (by fun_prop) (by fun_prop) (by norm_num)
    exact Tendsto.mono_left (by simpa using hc.tendsto) nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact Set.mem_Ioi.mpr (div_pos (mul_pos hc₀ ht.1) (by positivity))

/-- **Brick R1b, scaled.** `√(t·con)·gaussSumHalf(4·con·t/(t²+4)) → 1/2`. -/
theorem sq_mul_gaussHalf_tendsto :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t)
      * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4))) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hc₀ : 0 < 4 * (con : ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)
  have hcongr : (fun t : ℝ => Real.sqrt ((con : ℝ) * t)
        * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (Real.sqrt ((con : ℝ) * t) / Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
        * (Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4))
          * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)))) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hpos : 0 < 4 * (con : ℝ) * t / (t ^ 2 + 4) :=
      div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht.1) (by positivity)
    rw [← mul_assoc, div_mul_cancel₀ _ (Real.sqrt_ne_zero'.2 hpos)]
  refine Tendsto.congr' hcongr.symm ?_
  have h1 : Tendsto (fun t : ℝ => Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4))
      * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4))) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have hA := gaussSumHalf_asympt.comp (tendsto_a1 hc₀)
    convert hA using 1 <;> ext t <;> simp [Real.sqrt_eq_rpow]
  simpa using sqrtRatio_tendsto.mul h1

/-- **Brick R1b, doubled and scaled.** `√(t·con)·2·gaussSumHalf(4·con·t/(t²+4)) → 1`. -/
theorem gaussSumHalf2_scaled :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t)
      * (2 * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)))) (𝓝[>] 0) (𝓝 1) := by
  have hcongr : (fun t : ℝ => Real.sqrt ((con : ℝ) * t)
        * (2 * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4))))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => 2 * (Real.sqrt ((con : ℝ) * t)
        * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)))) := by
    filter_upwards with t
    ring
  refine Tendsto.congr' hcongr.symm ?_
  simpa using (sq_mul_gaussHalf_tendsto).const_mul 2

/-- **Brick R0, scaled.** `√(t·con)·gaussSumInt(4·con·t/(t²+4)) → 1`. -/
theorem gaussSumInt_scaled :
    Tendsto (fun t : ℝ => ((Real.sqrt ((con : ℝ) * t) : ℂ)
      * ((gaussSumInt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 1) := by
  have hc₀ : 0 < 4 * (con : ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)
  have hcongr : (fun t : ℝ => ((Real.sqrt ((con : ℝ) * t) : ℂ)
        * ((gaussSumInt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ((Real.sqrt ((con : ℝ) * t) / Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)
        * ((Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4))
          * gaussSumInt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hpos : 0 < 4 * (con : ℝ) * t / (t ^ 2 + 4) :=
      div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht.1) (by positivity)
    push_cast
    have hsne : Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)) ≠ 0 := Real.sqrt_ne_zero'.2 hpos
    have hsne' : ((Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsne
    have harg3 : 0 < 4190205 * (t * 4) / (t ^ 2 + 4) := by
      apply div_pos
      · nlinarith [ht.1]
      · positivity
    have hsne3 : (↑√(4190205 * (t * 4) / (t ^ 2 + 4)) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.2 harg3)
    have hsne4 : (↑√(4190205 * t * (4 / (t ^ 2 + 4))) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.2 (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4190205) ht.1)
        (mul_pos (by norm_num : (0 : ℝ) < 4) (inv_pos.mpr (by positivity)))))
    field_simp [hsne, hsne', hsne3, hsne4]
    have hsneX : (↑√(4190205 * t * 4 / (t ^ 2 + 4)) : ℂ) ≠ 0 := by
      have hnum : 0 < 4190205 * t * 4 := by nlinarith [ht.1]
      have hden : 0 < t ^ 2 + 4 := by positivity
      exact_mod_cast (Real.sqrt_ne_zero'.2 (div_pos hnum hden))
    exact (mul_div_cancel_right₀ _ hsneX).symm
  refine Tendsto.congr' hcongr.symm ?_
  have h1 : Tendsto (fun t : ℝ => ((Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4))
        * gaussSumInt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    have hcomp := thetaAsympt_full.comp (tendsto_a1 hc₀)
    have hcast := (Complex.ofRealCLM).continuous.continuousAt.tendsto.comp hcomp
    have hA := (Complex.ofRealCLM).continuous.continuousAt.tendsto.comp
      (thetaAsympt_full.comp (tendsto_a1 hc₀))
    convert hA using 1 <;> ext t <;> simp [Real.sqrt_eq_rpow, gaussSumInt] <;> push_cast <;> ring_nf
  have h2 : Tendsto (fun t : ℝ => ((Real.sqrt ((con : ℝ) * t)
      / Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    have hcast := (Complex.ofRealCLM).continuous.continuousAt.tendsto.comp sqrtRatio_tendsto
    convert hcast using 1 <;> ext t <;> simp [Function.comp_def] <;> push_cast <;> ring
  simpa using h2.mul h1

/-- **The scaled deviation brick.** `√(t·con)·κ·(π·con·t²/(t²+4))·2/(a·√a) → 0`
with `a = c₀·t/(t²+4)` — the whole point is the `t^{1/2}` decay of
`δ·S₂(a)·√(t·con)` in disguise. -/
theorem devScale_tendsto {κ c₀ : ℝ} (hc₀ : 0 < c₀) :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t)
      * ((κ * ((π : ℝ) * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)))
        * (2 / ((c₀ * t / (t ^ 2 + 4)) * Real.sqrt (c₀ * t / (t ^ 2 + 4))))))
      (𝓝[>] 0) (𝓝 0) := by
  have hcongr : (fun t : ℝ => Real.sqrt ((con : ℝ) * t)
        * ((κ * ((π : ℝ) * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)))
          * (2 / ((c₀ * t / (t ^ 2 + 4)) * Real.sqrt (c₀ * t / (t ^ 2 + 4))))))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (2 * κ * π * (con : ℝ) * Real.sqrt ((con : ℝ) / c₀) / c₀)
        * (t * Real.sqrt (t ^ 2 + 4))) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hc0 : c₀ ≠ 0 := ne_of_gt hc₀
    have htne : (t : ℝ) ≠ 0 := ne_of_gt ht.1
    have hT4 : (t ^ 2 + 4) ≠ 0 := ne_of_gt (by positivity)
    have hpt : 0 < c₀ * t := mul_pos hc₀ ht.1
    have hsqne : Real.sqrt (c₀ * t) ≠ 0 := Real.sqrt_ne_zero'.2 hpt
    have h1 : Real.sqrt (c₀ * t / (t ^ 2 + 4)) = Real.sqrt (c₀ * t) / Real.sqrt (t ^ 2 + 4) :=
      Real.sqrt_div (mul_nonneg (le_of_lt hc₀) (le_of_lt ht.1)) (t ^ 2 + 4)
    have h2 : Real.sqrt ((con : ℝ) * t) / Real.sqrt (c₀ * t) = Real.sqrt ((con : ℝ) / c₀) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _) t,
          Real.sqrt_mul (le_of_lt hc₀) t,
          Real.sqrt_div (Nat.cast_nonneg _) c₀]
      field_simp [Real.sqrt_ne_zero'.2 ht.1, Real.sqrt_ne_zero'.2 (Nat.cast_pos.mpr con_pos),
        Real.sqrt_ne_zero'.2 hc₀]
    have h4 : (2 : ℝ) / ((c₀ * t / (t ^ 2 + 4)) * Real.sqrt (c₀ * t / (t ^ 2 + 4)))
        = 2 * ((t ^ 2 + 4) * Real.sqrt (t ^ 2 + 4)) / (c₀ * t * Real.sqrt (c₀ * t)) := by
      rw [h1, div_mul_div_comm, div_eq_mul_inv, inv_div]
      ring_nf
    rw [h4]
    have hkey : Real.sqrt ((con : ℝ) * t)
          * ((κ * ((π : ℝ) * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)))
            * (2 * ((t ^ 2 + 4) * Real.sqrt (t ^ 2 + 4)) / (c₀ * t * Real.sqrt (c₀ * t))))
        = (2 * κ * π * (con : ℝ) * t / c₀)
          * (Real.sqrt ((con : ℝ) * t) / Real.sqrt (c₀ * t) * Real.sqrt (t ^ 2 + 4)) := by
      first
        | (field_simp; ring)
        | field_simp
    rw [hkey, h2]
    ring
  refine Tendsto.congr' hcongr.symm ?_
  have hc : ContinuousAt (fun t : ℝ => (t : ℝ) * Real.sqrt (t ^ 2 + 4)) 0 := by
    refine ContinuousAt.mul (by fun_prop) ?_
    exact Real.continuous_sqrt.continuousAt.comp (by fun_prop)
  have h1 : Tendsto (fun t : ℝ => (t : ℝ) * Real.sqrt (t ^ 2 + 4)) (𝓝[>] 0) (𝓝 0) := by
    exact Tendsto.mono_left (by simpa using hc.tendsto) nhdsWithin_le_nhds
  simpa using h1.const_mul _

/-! ## Squeeze helper -/

/-- If `0 ≤ f ≤ g` eventually along `𝓝[>] 0` and `g → 0`, then `f → 0`. -/
theorem nonneg_le_tendsto_zero {f g : ℝ → ℝ}
    (hnn : ∀ t : ℝ, 0 ≤ f t) (hfg : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ g t)
    (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0)) : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact squeeze_zero' (Filter.Eventually.of_forall hnn) hfg hg

/-! ## Scaled deviation limits -/

/-- The norm bound for the scaled even deviation. -/
theorem dualEven_norm_dev (t : ℝ) (ht : 0 < t) :
    ‖(((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ) * (2 * (∑' n : ℕ,
        cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
          * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
            - 1))))‖
      ≤ Real.sqrt ((con : ℝ) * t) * (2 * ((2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))
        * (2 / ((4 * (con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
          + 2))) := by
  have hpos : 0 < 4 * (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht) (by positivity)
  have hsqnn : ‖((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ)‖
      = Real.sqrt ((con : ℝ) * t) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_mul, hsqnn]
  have hS : Summable (fun n : ℕ =>
      cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
        * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
          - 1)) := dualEven_dev_summable t ht
  calc Real.sqrt ((con : ℝ) * t) * ‖(2 * (∑' n : ℕ,
          cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1)))‖
      ≤ Real.sqrt ((con : ℝ) * t) * (2 * ‖(∑' n : ℕ,
          cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1))‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        have h2n : ‖((2 : ℂ))‖ = 2 := by norm_num
        rw [norm_mul, h2n]
    _ ≤ Real.sqrt ((con : ℝ) * t) * (2 * ∑' n : ℕ, ‖(
          cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1))‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hS.norm) (by norm_num)
    _ ≤ Real.sqrt ((con : ℝ) * t) * (2 * ((2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))
          * (2 / ((4 * (con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
            + 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left (dualEven_dev_bound t ht) (by norm_num)

/-- The scaled even deviation tends to `0`. -/
theorem dualEven_dev_limit :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t) * (2 * (∑' n : ℕ,
        cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
          * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
            - 1)))) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine nonneg_le_tendsto_zero (f := fun t => ‖(((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ)
      * (2 * (∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
          * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
            - 1))))‖)
    (g := fun t => Real.sqrt ((con : ℝ) * t) * (2 * ((2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))
      * (2 / ((4 * (con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
        + 2)))) ?_ ?_ ?_
  · intro t; exact norm_nonneg _
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact dualEven_norm_dev t ht.1
  · have hA := devScale_tendsto (c₀ := 4 * (con : ℝ)) (κ := 4)
        (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos))
    have hB := extra_tendsto 8
    convert hA.add hB using 1 <;> ext t <;> ring

/-- The norm bound for the scaled odd deviation. -/
theorem dualOdd_norm_dev (t : ℝ) (ht : 0 < t) :
    ‖(((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ) * (2 * (∑' n : ℕ,
        (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
          * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ))))))‖
      ≤ Real.sqrt ((con : ℝ) * t) * (2 * ((π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
        * (8 / (((con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt ((con : ℝ) * t / (t ^ 2 + 4)))
          + 8))) := by
  have hpos : 0 < (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (Nat.cast_pos.mpr con_pos) ht) (by positivity)
  have hsqnn : ‖((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ)‖
      = Real.sqrt ((con : ℝ) * t) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_mul, hsqnn]
  have hS : Summable (fun n : ℕ =>
      (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
          / (2 * (t ^ 2 + 4))) : ℂ)))) := dualOdd_dev_summable t ht
  calc Real.sqrt ((con : ℝ) * t) * ‖(2 * (∑' n : ℕ,
          (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ)))))‖
      ≤ Real.sqrt ((con : ℝ) * t) * (2 * ‖(∑' n : ℕ,
          (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ))))‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        have h2n : ‖((2 : ℂ))‖ = 2 := by norm_num
        rw [norm_mul, h2n]
    _ ≤ Real.sqrt ((con : ℝ) * t) * (2 * ∑' n : ℕ, ‖(
          (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ))))‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hS.norm) (by norm_num)
    _ ≤ Real.sqrt ((con : ℝ) * t) * (2 * ((π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
          * (8 / (((con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt ((con : ℝ) * t / (t ^ 2 + 4)))
            + 8))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left (dualOdd_dev_bound t ht) (by norm_num)

/-- The scaled odd deviation tends to `0`. -/
theorem dualOdd_dev_limit :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t) * (2 * (∑' n : ℕ,
        (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
          * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))))) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine nonneg_le_tendsto_zero (f := fun t => ‖(((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ)
      * (2 * (∑' n : ℕ, (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
          * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
          / (2 * (t ^ 2 + 4))) : ℂ))))))‖
    ) (g := fun t => Real.sqrt ((con : ℝ) * t) * (2 * ((π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
      * (8 / (((con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt ((con : ℝ) * t / (t ^ 2 + 4))) + 8))))
    ?_ ?_ ?_
  · intro t; exact norm_nonneg _
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact dualOdd_norm_dev t ht.1
  · have hA := devScale_tendsto (c₀ := (con : ℝ)) (κ := 4) (Nat.cast_pos.mpr con_pos)
    have hB := extra_tendsto 8
    convert hA.add hB using 1
    ext t
    by_cases ht0 : t = 0
    · subst t
      norm_num
    · have h1 : (t ^ 2 + 4) ≠ 0 := by positivity
      have h2 : (8 + t ^ 2 * 2) ≠ 0 := by positivity
      field_simp [h1, h2, ht0]
      ring
    simp

/-! ## The three dual limits -/

/-- **The even dual limit.** `√(t·con)·dualEven(t) → 1` as `t → 0⁺`. -/
theorem dualEven_limit :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t) * (dualEven t)) (𝓝[>] 0) (𝓝 1) := by
  have hcongr : (fun t : ℝ => Real.sqrt ((con : ℝ) * t) * (dualEven t))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ((Real.sqrt ((con : ℝ) * t) : ℂ)
          * ((gaussSumInt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ))
        + Real.sqrt ((con : ℝ) * t) * (2 * (∑' n : ℕ,
          cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1)))) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [dualEven_eq t ht.1, mul_add]
  refine Tendsto.congr' hcongr.symm ?_
  simpa using (gaussSumInt_scaled).add dualEven_dev_limit

/-- **The odd dual limit.** `√(t·con)·dualOdd(t) → −i` as `t → 0⁺`. -/
theorem dualOdd_limit :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t) * (dualOdd t)) (𝓝[>] 0)
      (𝓝 (-(I : ℂ))) := by
  have hcongr : (fun t : ℝ => Real.sqrt ((con : ℝ) * t) * (dualOdd t))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (-(I : ℂ) * ((Real.sqrt ((con : ℝ) * t) : ℂ)
          * ((2 * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)))
        + Real.sqrt ((con : ℝ) * t) * (2 * (∑' n : ℕ,
          (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ)))))) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [dualOdd_eq t ht.1, mul_add]
    ring
  refine Tendsto.congr' hcongr.symm ?_
  have hcast : Tendsto (fun t : ℝ => ((Real.sqrt ((con : ℝ) * t) : ℂ)
      * ((2 * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 1) := by
    convert (Complex.ofRealCLM).continuous.continuousAt.tendsto.comp gaussSumHalf2_scaled using 1 <;> ext t <;> simp [Function.comp_def] <;> push_cast <;> ring_nf
  have h1 : Tendsto (fun t : ℝ => (-(I : ℂ) * ((Real.sqrt ((con : ℝ) * t) : ℂ)
      * ((2 * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)))) (𝓝[>] 0)
      (𝓝 (-(I : ℂ))) := by
    simpa using hcast.const_mul (-(I : ℂ))
  simpa using h1.add dualOdd_dev_limit

/-- **The full dual theta limit.** `√(t·con)·dualTheta(t) → 1 − i` as `t → 0⁺`. -/
theorem dualTheta_limit :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t) * (dualTheta t)) (𝓝[>] 0)
      (𝓝 (1 - (I : ℂ))) := by
  have hcongr : (fun t : ℝ => Real.sqrt ((con : ℝ) * t) * (dualTheta t))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => Real.sqrt ((con : ℝ) * t) * (dualEven t)
        + Real.sqrt ((con : ℝ) * t) * (dualOdd t)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [dualTheta_split t ht.1, mul_add]
  refine Tendsto.congr' hcongr.symm ?_
  simpa using (dualEven_limit).add (dualOdd_limit)

/-! ## K3b: from the dual theta limit to the Gauss-sum sign

The powerset re-entry is the identity here: just as bind unions `{f(x) | x ∈ K}`,
the theta-grouping below re-indexes one resident ℤ-word by its residue frame and
reassembles the boundary marks; no independent producers are created.
-/

lemma sqrt_neg_two_I_div_con : ((-2 * I) / (con : ℂ)) ^ ((1 : ℂ) / 2) = (1 - I) / (Real.sqrt (con : ℝ) : ℂ) := by
  rw [show ((1:ℂ)/2) = (2:ℂ)⁻¹ by norm_num]
  change Complex.sqrt ((-2 * I) / (con : ℂ)) = (1 - I) / (Real.sqrt (con : ℝ) : ℂ)
  rw [Complex.sqrt_eq_real_add_ite]
  have hnorm : ‖((-2 * I) / (con : ℂ))‖ = 2 / (con : ℝ) := by
    rw [norm_div, norm_mul]
    norm_num [Complex.normSq, Complex.norm_real]
  have hre : ((-2 * I) / (con : ℂ)).re = 0 := by simp
  have him : ((-2 * I) / (con : ℂ)).im = -2 / (con : ℝ) := by simp
  rw [hnorm, hre, him]
  have hneg : ¬ (0 : ℝ) ≤ -2 / (con : ℝ) := by norm_num [con]
  rw [if_neg hneg]
  rw [show (2 / (con : ℝ) + 0) / 2 = 1 / (con : ℝ) by ring]
  rw [show (2 / (con : ℝ) - 0) / 2 = 1 / (con : ℝ) by ring]
  rw [show Real.sqrt (1 / (con : ℝ)) = (Real.sqrt (con : ℝ))⁻¹ by rw [one_div, Real.sqrt_inv]]
  rw [div_eq_mul_inv, Complex.ofReal_inv]
  ring

theorem inv_cpow_tendsto :
    Tendsto (fun t : ℝ => 1 / ((((t : ℂ) - 2 * I) / (con : ℂ)) ^ ((1 : ℂ) / 2)))
    (𝓝[>] 0) (𝓝 ((Real.sqrt (con : ℝ) : ℂ) * (1 + I) / 2)) := by
  have hofreal : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun t : ℝ => ((t : ℂ) - 2 * I) / (con : ℂ)) (𝓝[>] 0)
      (𝓝 ((-2 * I) / (con : ℂ))) := by
    simpa using (hofreal.sub_const (2 * I)).div_const (con : ℂ)
  have hslit : ((-2 * I) / (con : ℂ)) ∈ slitPlane := by
    rw [slitPlane]
    right
    simp [con]
  have hcpow : Tendsto (fun t : ℝ => (((t : ℂ) - 2 * I) / (con : ℂ)) ^ ((1 : ℂ) / 2))
      (𝓝[>] 0) (𝓝 (((-2 * I) / (con : ℂ)) ^ ((1 : ℂ) / 2))) :=
    hz.cpow tendsto_const_nhds hslit
  rw [sqrt_neg_two_I_div_con] at hcpow
  have hne : (1 - I : ℂ) ≠ 0 := by norm_num [Complex.ext_iff]
  have hsne : (Real.sqrt (con : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : Real.sqrt (con : ℝ) ≠ 0)
  have hinv := hcpow.inv₀ (div_ne_zero hne hsne)
  have hcalc : ((1 - I) / (Real.sqrt (con : ℝ) : ℂ))⁻¹ = (Real.sqrt (con : ℝ) : ℂ) * (1 + I) / 2 := by
    rw [inv_div]
    field_simp [hsne]
    ring_nf
    rw [show I ^ 2 = (-1 : ℂ) by norm_num [pow_two, Complex.I_mul_I]]
    ring
  rw [hcalc] at hinv
  simpa [one_div] using hinv

lemma sqrt_t_div_sqrt_t_mul_con (t : ℝ) (ht : 0 < t) :
    Real.sqrt t / Real.sqrt ((con : ℝ) * t) = 1 / Real.sqrt (con : ℝ) := by
  rw [show (con : ℝ) * t = t * (con : ℝ) by ring]
  rw [Real.sqrt_mul (le_of_lt ht) (con : ℝ)]
  field_simp [Real.sqrt_ne_zero'.2 ht, Real.sqrt_ne_zero'.2 (by exact_mod_cast con_pos : (0:ℝ) < con)]

theorem sqrt_t_chirp_theta_tendsto_one :
    Tendsto (fun t : ℝ => Real.sqrt t *
      (1 / ((((t : ℂ) - 2 * I) / (con : ℂ)) ^ ((1 : ℂ) / 2))) * (dualTheta t))
    (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ => 1 / ((((t : ℂ) - 2 * I) / (con : ℂ)) ^ ((1 : ℂ) / 2)))
      (𝓝[>] 0) (𝓝 ((Real.sqrt (con : ℝ) : ℂ) * (1 + I) / 2)) := by
    -- reuse previous proof
    have hofreal : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hz : Tendsto (fun t : ℝ => ((t : ℂ) - 2 * I) / (con : ℂ)) (𝓝[>] 0)
        (𝓝 ((-2 * I) / (con : ℂ))) := by
      simpa using (hofreal.sub_const (2 * I)).div_const (con : ℂ)
    have hslit : ((-2 * I) / (con : ℂ)) ∈ slitPlane := by
      rw [slitPlane]; right; simp [con]
    have hcpow : Tendsto (fun t : ℝ => (((t : ℂ) - 2 * I) / (con : ℂ)) ^ ((1 : ℂ) / 2))
        (𝓝[>] 0) (𝓝 (((-2 * I) / (con : ℂ)) ^ ((1 : ℂ) / 2))) :=
      hz.cpow tendsto_const_nhds hslit
    rw [sqrt_neg_two_I_div_con] at hcpow
    have hne : (1 - I : ℂ) ≠ 0 := by norm_num [Complex.ext_iff]
    have hsne : (Real.sqrt (con : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : Real.sqrt (con : ℝ) ≠ 0)
    have hinv := hcpow.inv₀ (div_ne_zero hne hsne)
    have hcalc : ((1 - I) / (Real.sqrt (con : ℝ) : ℂ))⁻¹ = (Real.sqrt (con : ℝ) : ℂ) * (1 + I) / 2 := by
      rw [inv_div]
      field_simp [hsne]
      ring_nf
      rw [show I ^ 2 = (-1 : ℂ) by norm_num [pow_two, Complex.I_mul_I]]
      ring
    rw [hcalc] at hinv
    simpa [one_div] using hinv
  have h2 : Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t) * (dualTheta t)) (𝓝[>] 0)
      (𝓝 (1 - I)) := dualTheta_limit
  have hprod := h1.mul h2
  -- hprod limit: √con(1+I)/2 * (1-I) = 1
  have hlimval : ((Real.sqrt (con : ℝ) : ℂ) * (1 + I) / 2) * (1 - I) = (Real.sqrt (con : ℝ) : ℂ) := by
    have hsne : (Real.sqrt (con : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : Real.sqrt (con : ℝ) ≠ 0)
    field_simp [hsne]
    ring_nf
    rw [show I ^ 2 = (-1 : ℂ) by norm_num [pow_two, Complex.I_mul_I]]
    ring
  rw [hlimval] at hprod
  -- congr: √t*(1/z)*dualTheta = (1/√con) * ((1/z)* (√con_t*dualTheta))
  have hconst := hprod.const_mul ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ)
  have hcanc : ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) * (Real.sqrt (con : ℝ) : ℂ) = 1 := by
    norm_cast
    exact one_div_mul_cancel (by positivity)
  rw [hcanc] at hconst
  refine Tendsto.congr' ?_ hconst
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  have hs : Real.sqrt t / Real.sqrt ((con : ℝ) * t) = 1 / Real.sqrt (con : ℝ) :=
    sqrt_t_div_sqrt_t_mul_con t ht.1
  push_cast
  have hre : Real.sqrt t = (Real.sqrt t / Real.sqrt ((con : ℝ) * t)) * Real.sqrt ((con : ℝ) * t) := by
    have hsne : Real.sqrt ((con : ℝ) * t) ≠ 0 := Real.sqrt_ne_zero'.2 (mul_pos (by exact_mod_cast con_pos : (0:ℝ) < con) ht.1)
    field_simp [hsne]
  have hreC : (Real.sqrt t : ℂ) = ((Real.sqrt t / Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ) * (Real.sqrt ((con : ℝ) * t) : ℂ) := by
    exact_mod_cast hre
  rw [hreC]
  have hsC2 : ((Real.sqrt t / Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ) = ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) := by
    rw [hs]
  rw [hsC2]
  have hinvC : ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) = 1 / (Real.sqrt (con : ℝ) : ℂ) := by
    rw [one_div, Complex.ofReal_inv, one_div]
  rw [hinvC]
  ring

/-! ### K3b theta-grouping machinery ### -/

lemma T_r_tendsto (r : ℕ) :
    Tendsto (fun t : ℝ => ∑' m : ℤ,
        cexp (-π / (t * (con : ℝ)) * ((m : ℝ) ^ 2)) *
          cexp (2 * π * I * ((r : ℝ) / (con : ℝ)) * (m : ℝ)))
      (𝓝[>] 0) (𝓝 1) := by
  let f : ℝ → ℤ → ℂ := fun t m =>
    (rexp (-π / (t * (con : ℝ)) * ((m : ℝ) ^ 2)) : ℂ) *
      cexp (2 * π * I * ((r : ℝ) / (con : ℝ)) * (m : ℝ))
  let g : ℤ → ℂ := fun m => if m = 0 then 1 else 0
  let bound : ℤ → ℝ := fun m => rexp (-π * (1 / (con : ℝ)) * ((m : ℝ) ^ 2))
  have hsum : Summable bound := by
    dsimp [bound]
    exact summable_gaussReal (1 / (con : ℝ)) (by positivity)
  have hterm : ∀ m : ℤ, Tendsto (f · m) (𝓝[>] 0) (𝓝 (g m)) := by
    intro m
    by_cases hm : m = 0
    · subst m
      simp [f, g]
    · simp only [g, hm, if_false]
      have hm2 : (0 : ℝ) < ((m : ℝ) ^ 2) := by
        have hne : (m : ℝ) ≠ 0 := by exact_mod_cast hm
        exact sq_pos_of_ne_zero hne
      have hc : (0 : ℝ) < π * ((m : ℝ) ^ 2) / (con : ℝ) := by positivity
      have htop : Tendsto (fun t : ℝ => (π * ((m : ℝ) ^ 2) / (con : ℝ)) * t⁻¹)
          (𝓝[>] 0) atTop := Tendsto.const_mul_atTop hc tendsto_inv_nhdsGT_zero
      have hexp : Tendsto (fun t : ℝ => rexp (-((π * ((m : ℝ) ^ 2) / (con : ℝ)) * t⁻¹)))
          (𝓝[>] 0) (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
      have hfeq : (fun t : ℝ => -π / (t * (con : ℝ)) * ((m : ℝ) ^ 2))
          = (fun t : ℝ => -((π * ((m : ℝ) ^ 2) / (con : ℝ)) * t⁻¹)) := by
        funext t
        field_simp
      have hreal : Tendsto (fun t : ℝ => rexp (-π / (t * (con : ℝ)) * ((m : ℝ) ^ 2)))
          (𝓝[>] 0) (𝓝 0) := by
        convert hexp using 1
        funext t
        congr 1
        exact congrFun hfeq t
      have hcast : Tendsto (fun t : ℝ => (rexp (-π / (t * (con : ℝ)) * ((m : ℝ) ^ 2)) : ℂ))
          (𝓝[>] 0) (𝓝 (0 : ℂ)) := Complex.continuous_ofReal.tendsto 0 |>.comp hreal
      simpa [f] using hcast.mul_const (cexp (2 * π * I * ((r : ℝ) / (con : ℝ)) * (m : ℝ)))
  have hbound_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ m : ℤ, ‖f t m‖ ≤ bound m := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    intro m
    dsimp [f, bound]
    rw [norm_mul]
    conv_lhs =>
      rhs
      rw [Complex.norm_exp]
      norm_num [Complex.mul_re, Complex.div_re, Complex.normSq_apply]
    rw [mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hle : -π / (t * (con : ℝ)) * ((m : ℝ) ^ 2) ≤ -π * (1 / (con : ℝ)) * ((m : ℝ) ^ 2) := by
      have hinv : (1 : ℝ) ≤ t⁻¹ := by
        have hmul := mul_le_mul_of_nonneg_right ht.2.le (inv_nonneg.mpr ht.1.le)
        simpa [mul_inv_cancel₀ (ne_of_gt ht.1)] using hmul
      have hform : -π / (t * (con : ℝ)) * ((m : ℝ) ^ 2) = -(π * ((m : ℝ) ^ 2) / (con : ℝ)) * t⁻¹ := by field_simp
      have hform2 : -π * (1 / (con : ℝ)) * ((m : ℝ) ^ 2) = -(π * ((m : ℝ) ^ 2) / (con : ℝ)) := by field_simp
      rw [hform, hform2]
      have hnon : 0 ≤ π * ((m : ℝ) ^ 2) / (con : ℝ) := by positivity
      nlinarith
    exact Real.exp_le_exp.mpr hle
  have htsum := tendsto_tsum_of_dominated_convergence hsum hterm hbound_ev
  have hval : (∑' m : ℤ, g m) = 1 := by
    dsimp [g]
    rw [tsum_eq_single 0]
    · simp
    · intro b hb
      simp [hb]
  have htsum' : Tendsto (fun t : ℝ => ∑' m : ℤ, f t m) (𝓝[>] 0) (𝓝 1) := by simpa [hval] using htsum
  refine Tendsto.congr' ?_ htsum'
  filter_upwards with t
  apply tsum_congr
  intro m
  dsimp [f]
  apply congrArg (fun z : ℂ => z * cexp (2 * π * I * ((r : ℝ) / (con : ℝ)) * (m : ℝ)))
  apply Complex.ext <;>
    simp [Complex.exp_re, Complex.exp_im] <;>
    push_cast <;> ring

lemma shifted_gauss_poisson (r : ℕ) (t : ℝ) (ht : 0 < t) :
    (∑' q : ℤ, cexp (-π * (t * (con : ℝ) : ℂ) * ((q : ℂ) ^ 2)
        + 2 * π * (-(t * (r : ℝ)) : ℂ) * (q : ℂ)))
      = 1 / ((t * (con : ℝ) : ℂ) ^ ((1 : ℂ) / 2)) *
        (∑' n : ℤ, cexp (-π / (t * (con : ℝ) : ℂ) *
          (((n : ℂ) + I * (-(t * (r : ℝ)) : ℂ)) ^ 2))) := by
  have ha : 0 < ((t * (con : ℝ) : ℂ)).re := by simp [ht]
  exact Complex.tsum_exp_neg_quadratic ha (-(t * (r : ℝ)) : ℂ)

lemma rhs_sum_eq (r : ℕ) (t : ℝ) (ht : 0 < t) :
    (∑' n : ℤ, cexp (-π / (t * (con : ℝ) : ℂ) *
      (((n : ℂ) + I * (-(t * (r : ℝ)) : ℂ)) ^ 2)))
      = (cexp (π * (t : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (con : ℂ))) *
        (∑' n : ℤ, cexp (-π / (t * (con : ℝ) : ℂ) * ((n : ℂ) ^ 2)) *
          cexp (2 * π * I * ((r : ℝ) / (con : ℝ)) * (n : ℝ))) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have harg : -π / (t * (con : ℝ) : ℂ) * (((n : ℂ) + I * (-(t * (r : ℝ)) : ℂ)) ^ 2)
      = π * (t : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (con : ℂ)
        + (-π / (t * (con : ℝ) : ℂ) * ((n : ℂ) ^ 2)
          + 2 * π * I * ((r : ℝ) / (con : ℝ)) * (n : ℝ)) := by
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    field_simp [htne]
    ring_nf
    rw [show I ^ 2 = (-1 : ℂ) by norm_num [pow_two, Complex.I_mul_I]]
    norm_num
    ring_nf
  rw [harg, Complex.exp_add, Complex.exp_add]

lemma shifted_term_eq (r : ℕ) (t : ℝ) (ht : 0 < t) (q : ℤ) :
    cexp (-π * (t / (con : ℝ) : ℝ) * (((r : ℝ) + (q : ℝ) * (con : ℝ)) ^ 2) : ℂ)
      = cexp (-π * (t : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (con : ℂ)) *
        cexp (-π * (t * (con : ℝ) : ℂ) * ((q : ℂ) ^ 2)
          + 2 * π * (-(t * (r : ℝ)) : ℂ) * (q : ℂ)) := by
  have harg : (-π * (t / (con : ℝ)) * (((r : ℝ) + (q : ℝ) * (con : ℝ)) ^ 2) : ℂ)
      = (-(π * (t : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (con : ℂ)))
        + (-π * (t * (con : ℝ) : ℂ) * ((q : ℂ) ^ 2)
          + 2 * π * (-(t * (r : ℝ)) : ℂ) * (q : ℂ)) := by
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    have hcne : (con : ℂ) ≠ 0 := by norm_num [con]
    field_simp [htne, hcne]
    push_cast
    ring
  rw [Complex.ofReal_div, harg, Complex.exp_add]
  ring

lemma sqrt_t_shifted_gauss (r : ℕ) (t : ℝ) (ht : 0 < t) :
    Real.sqrt t * (∑' q : ℤ, cexp (-π * (t / (con : ℝ) : ℝ) * (((r : ℝ) + (q : ℝ) * (con : ℝ)) ^ 2)))
      = ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) *
        (∑' n : ℤ, cexp (-π / (t * (con : ℝ) : ℂ) * ((n : ℂ) ^ 2)) *
          cexp (2 * π * I * ((r : ℝ) / (con : ℝ)) * (n : ℝ))) := by
  rw [show (∑' q : ℤ, cexp (-π * (t / (con : ℝ) : ℝ) * (((r : ℝ) + (q : ℝ) * (con : ℝ)) ^ 2)))
      = cexp (-π * (t : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (con : ℂ)) *
        (∑' q : ℤ, cexp (-π * (t * (con : ℝ) : ℂ) * ((q : ℂ) ^ 2)
          + 2 * π * (-(t * (r : ℝ)) : ℂ) * (q : ℂ))) from by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro q
    exact shifted_term_eq r t ht q]
  rw [shifted_gauss_poisson r t ht]
  rw [rhs_sum_eq r t ht]
  let T : ℂ := ∑' n : ℤ, cexp (-π / (t * (con : ℝ) : ℂ) * ((n : ℂ) ^ 2)) *
          cexp (2 * π * I * ((r : ℝ) / (con : ℝ)) * (n : ℝ))
  let A : ℂ := -π * (t : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (con : ℂ)
  have hcoef : (Real.sqrt t : ℂ) * cexp A * (1 / ((t * (con : ℝ) : ℂ) ^ ((1 : ℂ) / 2))) * cexp (-A)
      = ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) := by
    rw [one_div]
    have hreorder : (Real.sqrt t : ℂ) * cexp A * (((t * (con : ℝ) : ℂ) ^ ((1 : ℂ) / 2))⁻¹) * cexp (-A)
        = (Real.sqrt t : ℂ) * ((cexp A * cexp (-A)) * (((t * (con : ℝ) : ℂ) ^ ((1 : ℂ) / 2))⁻¹)) := by ring
    rw [hreorder]
    rw [← Complex.exp_add]
    have hA : A + -A = 0 := by ring
    rw [hA, Complex.exp_zero]
    simp
    have hcpow : (((t : ℂ) * 4190205) ^ ((2 : ℂ)⁻¹)) = (Real.sqrt ((con : ℝ) * t) : ℂ) := by
      change Complex.sqrt (((t : ℂ) * 4190205)) = (Real.sqrt ((con : ℝ) * t) : ℂ)
      rw [show ((t : ℂ) * 4190205) = ((con : ℝ) * t : ℝ) by norm_num [con]; push_cast; ring]
      rw [Complex.sqrt_of_nonneg]
      · simp
      · exact_mod_cast (mul_nonneg (Nat.cast_nonneg _) (le_of_lt ht))
    rw [hcpow]
    have hratio := sqrt_t_div_sqrt_t_mul_con t ht
    have hratio' : Real.sqrt t * (Real.sqrt ((con : ℝ) * t))⁻¹ = (Real.sqrt (con : ℝ))⁻¹ := by
      rw [← div_eq_mul_inv, hratio, one_div]
    exact_mod_cast hratio'
  ring_nf
  have hce : cexp (↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (-1 / 4190205)) * ((((t : ℂ) * ((4190205 : ℝ) : ℂ)) ^ ((1 : ℂ) / 2))⁻¹) * cexp (↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (1 / 4190205)) = ((((t : ℂ) * ((4190205 : ℝ) : ℂ)) ^ ((1 : ℂ) / 2))⁻¹) := by
    rw [show cexp (↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (-1 / 4190205)) * ((((t : ℂ) * ((4190205 : ℝ) : ℂ)) ^ ((1 : ℂ) / 2))⁻¹) * cexp (↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (1 / 4190205))
      = (cexp (↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (-1 / 4190205)) * cexp (↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (1 / 4190205))) * ((((t : ℂ) * ((4190205 : ℝ) : ℂ)) ^ ((1 : ℂ) / 2))⁻¹) by ring]
    rw [← Complex.exp_add]
    have hz : ↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (-1 / 4190205) +
        ↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (1 / 4190205) = 0 := by ring
    rw [hz, Complex.exp_zero, one_mul]
  rw [show (Real.sqrt t : ℂ) * cexp (↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (-1 / 4190205)) * ((((t : ℂ) * ((4190205 : ℝ) : ℂ)) ^ ((1 : ℂ) / 2))⁻¹) * cexp (↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (1 / 4190205)) * (∑' (n : ℤ), cexp (-(↑π * ((t : ℂ)⁻¹) * (((4190205 : ℝ) : ℂ))⁻¹ * ((n : ℤ) : ℂ) ^ 2)) * cexp (↑π * ((r : ℝ) : ℂ) * (((4190205 : ℝ) : ℂ))⁻¹ * I * (((n : ℤ) : ℝ) : ℂ) * 2))
      = (cexp (↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (-1 / 4190205)) * ((((t : ℂ) * ((4190205 : ℝ) : ℂ)) ^ ((1 : ℂ) / 2))⁻¹) * cexp (↑π * (t : ℂ) * ((r : ℝ) : ℂ) ^ 2 * (1 / 4190205))) * ((Real.sqrt t : ℂ) * (∑' (n : ℤ), cexp (-(↑π * ((t : ℂ)⁻¹) * (((4190205 : ℝ) : ℂ))⁻¹ * ((n : ℤ) : ℂ) ^ 2)) * cexp (↑π * ((r : ℝ) : ℂ) * (((4190205 : ℝ) : ℂ))⁻¹ * I * (((n : ℤ) : ℝ) : ℂ) * 2))) by ring]
  rw [hce]
  have hcpow : ((t : ℂ) * ((4190205 : ℝ) : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt ((con : ℝ) * t) : ℂ) := by
    rw [show ((1:ℂ)/2) = (2:ℂ)⁻¹ by norm_num]
    change Complex.sqrt ((t : ℂ) * ((4190205 : ℝ) : ℂ)) = (Real.sqrt ((con : ℝ) * t) : ℂ)
    rw [show (t : ℂ) * ((4190205 : ℝ) : ℂ) = ((con : ℝ) * t : ℝ) by norm_num [con]; push_cast; ring]
    rw [Complex.sqrt_of_nonneg]
    · simp
    · exact_mod_cast (mul_nonneg (Nat.cast_nonneg _) (le_of_lt ht))
  rw [hcpow]
  have hratio := sqrt_t_div_sqrt_t_mul_con t ht
  have hratio' : (Real.sqrt t : ℂ) * ((Real.sqrt ((con : ℝ) * t) : ℂ)⁻¹) = ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv]
    exact_mod_cast (by
      rw [← div_eq_mul_inv]
      exact hratio)
  rw [show (Real.sqrt ((con : ℝ) * t) : ℂ)⁻¹ * ((Real.sqrt t : ℂ) *
        (∑' (n : ℤ), cexp (-(↑π * ((t : ℂ)⁻¹) * (((4190205 : ℝ) : ℂ))⁻¹ * (((n : ℤ) : ℂ) ^ 2))) * cexp (↑π * ((r : ℝ) : ℂ) * (((4190205 : ℝ) : ℂ))⁻¹ * I * (((n : ℤ) : ℝ) : ℂ) * 2)))
      = ((Real.sqrt t : ℂ) * (Real.sqrt ((con : ℝ) * t) : ℂ)⁻¹) *
        (∑' (n : ℤ), cexp (-(↑π * ((t : ℂ)⁻¹) * (((4190205 : ℝ) : ℂ))⁻¹ * (((n : ℤ) : ℂ) ^ 2))) * cexp (↑π * ((r : ℝ) : ℂ) * (((4190205 : ℝ) : ℂ))⁻¹ * I * (((n : ℤ) : ℝ) : ℂ) * 2)) by ring]
  rw [hratio']
  rw [show ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) = (Real.sqrt (con : ℝ) : ℂ)⁻¹ by
    rw [one_div, Complex.ofReal_inv]]
  rw [Complex.ofReal_inv]
  ring

open ZMod
open StarkLogRung
open Imscribing.Millennium.StarkGaussSign
open Imscribing.Millennium.StarkTheta
open Imscribing.Millennium.StarkRungOne
open Imscribing.Millennium.StarkRungFour
open Imscribing.Millennium.ClinkStarkBridge
open Imscribing.Millennium.StarkTheoremD2048

/-! ### K3b grouping ### -/

noncomputable def zmodQuotEquiv (N : ℕ) [NeZero N] : ℤ ≃ (ZMod N × ℤ) where
  toFun n := ((n : ZMod N), n / (N : ℤ))
  invFun p := (p.1.val : ℤ) + p.2 * (N : ℤ)
  left_inv n := by
    simp only
    rw [ZMod.val_intCast]
    have h := Int.emod_add_mul_ediv n (N : ℤ)
    linarith
  right_inv p := by
    rcases p with ⟨x, k⟩
    apply Prod.ext
    · simp
    · simp only
      rw [Int.add_ediv_of_dvd_right]
      · have hxlt : (x.val : ℤ) < (N : ℤ) := by exact_mod_cast x.val_lt
        have hxdiv : (x.val : ℤ) / (N : ℤ) = 0 :=
          Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) hxlt
        have hkdiv : (k * (N : ℤ)) / (N : ℤ) = k := by
          rw [mul_comm]
          exact Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne N))
        rw [hxdiv, hkdiv, zero_add]
      · exact dvd_mul_left _ _

noncomputable def chirpSum (t : ℝ) : ℂ :=
  ∑' n : ℤ, cexp (-(π : ℂ) * ((t / (con : ℝ) : ℝ) : ℂ) * ((n : ℂ) ^ 2)) *
    cexp (2 * (π : ℂ) * I * ((n : ℂ) ^ 2) / (con : ℂ))

lemma chirpSum_group (t : ℝ) (ht : 0 < t) :
    chirpSum t = ∑' x : ZMod con,
      (cexp (2 * π * I * ((x.val : ℝ) ^ 2) / (con : ℝ))) *
      (∑' k : ℤ, cexp (-π * (t / (con : ℝ) : ℝ) *
        (((x.val : ℝ) + (k : ℝ) * (con : ℝ)) ^ 2))) := by
  dsimp [chirpSum]
  rw [show (∑' n : ℤ, cexp (-(π : ℂ) * ((t / (4190205 : ℝ) : ℝ) : ℂ) * ((n : ℂ) ^ 2)) *
      cexp (2 * (π : ℂ) * I * ((n : ℂ) ^ 2) / (4190205 : ℂ)))
      = ∑' p : ZMod con × ℤ,
          cexp (-(π : ℂ) * ((t / (4190205 : ℝ) : ℝ) : ℂ) * (((p.1.val : ℤ) + p.2 * (con : ℤ) : ℤ) : ℂ) ^ 2) *
          cexp (2 * (π : ℂ) * I * ((((p.1.val : ℤ) + p.2 * (con : ℤ) : ℤ) : ℂ) ^ 2) / (4190205 : ℂ)) from by
    exact ((zmodQuotEquiv con).symm.tsum_eq (fun n : ℤ =>
      cexp (-(π : ℂ) * ((t / (4190205 : ℝ) : ℝ) : ℂ) * ((n : ℂ) ^ 2)) *
      cexp (2 * (π : ℂ) * I * ((n : ℂ) ^ 2) / (4190205 : ℂ)))).symm]
  have hf : Summable (fun n : ℤ =>
      cexp (-(π : ℂ) * ((t / (4190205 : ℝ) : ℝ) : ℂ) * ((n : ℂ) ^ 2)) *
      cexp (2 * (π : ℂ) * I * ((n : ℂ) ^ 2) / (4190205 : ℂ))) := by
    refine Summable.of_norm ?_
    have hg := summable_gaussReal (t / (con : ℝ)) (by positivity)
    refine hg.congr (fun n => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
    have hnre : (((n : ℤ) : ℂ) ^ 2).re = ((n : ℝ) ^ 2) := by
      norm_num [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hnim : (((n : ℤ) : ℂ) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hre1 : (-(π : ℂ) * ((t / (4190205 : ℝ) : ℝ) : ℂ) * ((n : ℂ) ^ 2)).re
        = -π * (t / (con : ℝ)) * ((n : ℝ) ^ 2) := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hnre, hnim]
    have hre2 : (2 * (π : ℂ) * I * ((n : ℂ) ^ 2) / (4190205 : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hnim]
    rw [hre1, hre2, Real.exp_zero, mul_one]
  have hfprod : Summable (fun p : ZMod con × ℤ =>
      cexp (-(π : ℂ) * ((t / (4190205 : ℝ) : ℝ) : ℂ) * ((((p.1.val : ℤ) + p.2 * (con : ℤ) : ℤ) : ℂ) ^ 2)) *
      cexp (2 * (π : ℂ) * I * ((((p.1.val : ℤ) + p.2 * (con : ℤ) : ℤ) : ℂ) ^ 2) / (4190205 : ℂ))) := by
    exact hf.comp_injective (zmodQuotEquiv con).symm.injective
  rw [hfprod.tsum_prod]
  apply tsum_congr
  intro x
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [Prod.fst, Prod.snd]
  have hphase : cexp (2 * (π : ℂ) * I * ((((x.val : ℤ) + k * (con : ℤ) : ℤ) : ℂ) ^ 2) / (con : ℂ))
      = cexp (2 * (π : ℂ) * I * ((x.val : ℂ) ^ 2) / (con : ℂ)) := by
    have hsq_int : ((x.val : ℤ) + k * (con : ℤ)) ^ 2
        = (x.val : ℤ) ^ 2 + (k * (2 * (x.val : ℤ) + k * (con : ℤ))) * (con : ℤ) := by ring
    have hcne : (con : ℂ) ≠ 0 := by norm_num [con]
    have harg : 2 * (π : ℂ) * I * ((((x.val : ℤ) + k * (con : ℤ) : ℤ) : ℂ) ^ 2) / (con : ℂ)
        = 2 * (π : ℂ) * I * ((x.val : ℂ) ^ 2) / (con : ℂ)
          + ((k * (2 * (x.val : ℤ) + k * (con : ℤ)) : ℤ) : ℂ) * (2 * (π : ℂ) * I) := by
      rw [show ((((x.val : ℤ) + k * (con : ℤ) : ℤ) : ℂ) ^ 2)
          = (((x.val : ℤ) + k * (con : ℤ)) ^ 2 : ℤ) by norm_num]
      rw [hsq_int]
      push_cast
      field_simp [hcne]
    rw [harg, Complex.exp_add]
    have hper : cexp (((k * (2 * (x.val : ℤ) + k * (con : ℤ)) : ℤ) : ℂ) * (2 * (π : ℂ) * I)) = 1 := by
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [hper, mul_one]
  rw [show (con : ℂ) = 4190205 by norm_num [con]] at hphase
  rw [hphase]
  have hgauss : cexp (-(π : ℂ) * ((t / (4190205 : ℝ) : ℝ) : ℂ) *
        ((((x.val : ℤ) + k * (con : ℤ) : ℤ) : ℂ) ^ 2))
      = cexp (-(π : ℂ) * ((t / (4190205 : ℝ) : ℝ) : ℂ) *
        (((x.val : ℂ) + (k : ℂ) * (4190205 : ℂ)) ^ 2)) := by
    congr 1
    push_cast
    norm_num [con]
  rw [hgauss]
  ring

lemma chirpSum_eq_chirp_lhs (t : ℝ) :
    chirpSum t = ∑' n : ℤ,
      cexp (-(π : ℂ) * (((t : ℂ) - 2 * I) / (con : ℂ)) * ((n : ℂ) ^ 2)) := by
  dsimp [chirpSum]
  apply tsum_congr
  intro n
  have hcne : (4190205 : ℂ) ≠ 0 := by norm_num
  have harg : -(π : ℂ) * (((t : ℂ) - 2 * I) / (4190205 : ℂ)) * ((n : ℂ) ^ 2)
      = -(π : ℂ) * ((t / (4190205 : ℝ) : ℝ) : ℂ) * ((n : ℂ) ^ 2)
        + 2 * (π : ℂ) * I * ((n : ℂ) ^ 2) / (4190205 : ℂ) := by
    field_simp [hcne]
    push_cast
    ring_nf
  rw [harg, Complex.exp_add]

lemma sqrt_t_chirpSum_tendsto_one :
    Tendsto (fun t : ℝ => Real.sqrt t * chirpSum t) (𝓝[>] 0) (𝓝 1) := by
  refine Tendsto.congr' ?_ sqrt_t_chirp_theta_tendsto_one
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  rw [chirpSum_eq_chirp_lhs t, chirp_theta t ht.1]
  have hsum : (∑' n : ℤ, cexp (-↑π / ((↑t - 2 * I) / ↑con) * ((n : ℂ) ^ 2))) = dualTheta t := by
    dsimp [dualTheta, dualTerm]
    apply tsum_congr
    intro n
    congr 1
    have hcne2 : (con : ℂ) ≠ 0 := by norm_num [con]
    have htne : (↑t - 2 * I : ℂ) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      norm_num [con] at him
    field_simp [hcne2, htne]
  rw [hsum]
  ring

lemma phase_eq_stdAddChar (x : ZMod con) :
    cexp (2 * (π : ℂ) * I * (((x.val ^ 2 : ℕ) : ℝ) : ℂ) / (con : ℂ))
      = stdAddChar (N := con) (x * x) := by
  have hsc : stdAddChar (N := con) (x * x) = rootExp (x * x).val con := by
    have hj : ((((x * x).val : ℤ) : ZMod con)) = x * x := by simp
    have h1 := stdAddChar_coe (N := con) ((x * x).val : ℤ)
    rw [hj] at h1
    rw [h1]
    unfold rootExp
    push_cast
    ring_nf
  rw [hsc]
  unfold rootExp
  rw [ZMod.val_mul]
  have hnat : x.val ^ 2 = x.val ^ 2 / con * con + x.val ^ 2 % con := by
    rw [mul_comm (x.val ^ 2 / con) con]
    exact (Nat.div_add_mod (x.val ^ 2) con).symm
  have hnatC : (((x.val ^ 2 : ℕ) : ℝ) : ℂ)
      = (((x.val ^ 2 / con : ℕ) : ℝ) : ℂ) * (con : ℂ)
        + (((x.val ^ 2 % con : ℕ) : ℝ) : ℂ) := by
    exact_mod_cast hnat
  have hcne : (con : ℂ) ≠ 0 := by norm_num [con]
  have harg : (2 * (π : ℂ) * I * (((x.val ^ 2 : ℕ) : ℝ) : ℂ) / (con : ℂ))
      = 2 * (π : ℂ) * I * (((x.val ^ 2 % con : ℕ) : ℝ) : ℂ) / (con : ℂ)
        + (((x.val ^ 2 / con : ℕ) : ℝ) : ℂ) * (2 * (π : ℂ) * I) := by
    rw [hnatC]
    field_simp [hcne]
    ring
  norm_num [pow_two] at harg ⊢
  rw [harg, Complex.exp_add]
  have hper : cexp (((x.val * x.val / con : ℕ) : ℂ) * (2 * (π : ℂ) * I)) = 1 := by
    simpa using (Complex.exp_int_mul_two_pi_mul_I ((x.val * x.val / con : ℕ) : ℤ))
  rw [hper, mul_one]
  congr 1
  ring

noncomputable def GShift (r : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℤ, cexp (-π * (t / (con : ℝ) : ℝ) * (((r : ℝ) + (k : ℝ) * (con : ℝ)) ^ 2))

lemma sqrt_t_shifted_gauss' (r : ℕ) (t : ℝ) (ht : 0 < t) :
    Real.sqrt t * GShift r t = ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) *
      (∑' n : ℤ, cexp (-π / (t * (con : ℝ) : ℂ) * ((n : ℂ) ^ 2)) *
        cexp (2 * π * I * ((r : ℝ) / (con : ℝ)) * (n : ℝ))) := by
  exact sqrt_t_shifted_gauss r t ht

lemma sum_phase_eq_tau :
    (∑' x : ZMod con, cexp (2 * (π : ℂ) * I * (((x.val ^ 2 : ℕ) : ℝ) : ℂ) / (con : ℂ)))
      = gaussSum qchar' stdAddChar := by
  rw [tsum_fintype]
  calc
    (∑ x : ZMod con, cexp (2 * (π : ℂ) * I * (((x.val ^ 2 : ℕ) : ℝ) : ℂ) / (con : ℂ)))
        = ∑ x : ZMod con, stdAddChar (N := con) (x * x) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact phase_eq_stdAddChar x
    _ = gaussSum qchar' stdAddChar := by rw [chirp_con]

lemma sqrt_t_chirpSum_tendsto_tau :
    Tendsto (fun t : ℝ => Real.sqrt t * chirpSum t) (𝓝[>] 0)
      (𝓝 (gaussSum qchar' stdAddChar * ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ))) := by
  have hS : ∀ x : ZMod con, Tendsto (fun t : ℝ => Real.sqrt t * GShift x.val t)
      (𝓝[>] 0) (𝓝 ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ)) := by
    intro x
    have hT : Tendsto (fun t : ℝ => ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) *
        (∑' m : ℤ, cexp (-↑π / (↑t * ↑↑con) * ↑m ^ 2) * cexp (2 * ↑π * I * (↑↑x.val / ↑↑con) * ↑m)))
        (𝓝[>] 0) (𝓝 ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ)) := by
      simpa using (T_r_tendsto x.val).const_mul ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ)
    refine Tendsto.congr' ?_ hT
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact (sqrt_t_shifted_gauss' x.val t ht.1).symm
  have hsumlim : Tendsto (fun t : ℝ => ∑' x : ZMod con,
        (cexp (2 * (π : ℂ) * I * (((x.val ^ 2 : ℕ) : ℝ) : ℂ) / (con : ℂ))) *
          (Real.sqrt t * GShift x.val t)) (𝓝[>] 0)
      (𝓝 (∑' x : ZMod con,
        (cexp (2 * (π : ℂ) * I * (((x.val ^ 2 : ℕ) : ℝ) : ℂ) / (con : ℂ))) *
          ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ))) := by
    simp only [tsum_fintype]
    exact tendsto_finset_sum Finset.univ (fun x hx => (hS x).const_mul _)
  have hlimval : (∑' x : ZMod con,
      (cexp (2 * (π : ℂ) * I * (((x.val ^ 2 : ℕ) : ℝ) : ℂ) / (con : ℂ))) *
        ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ))
      = gaussSum qchar' stdAddChar * ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) := by
    rw [tsum_mul_right, sum_phase_eq_tau]
  have hsumlim' : Tendsto (fun t : ℝ => ∑' x : ZMod con,
        (cexp (2 * (π : ℂ) * I * (((x.val ^ 2 : ℕ) : ℝ) : ℂ) / (con : ℂ))) *
          (Real.sqrt t * GShift x.val t)) (𝓝[>] 0)
      (𝓝 (gaussSum qchar' stdAddChar * ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ))) := by
    rw [hlimval] at hsumlim
    exact hsumlim
  refine Tendsto.congr' ?_ hsumlim'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  rw [chirpSum_group t ht.1]
  rw [show (∑' x : ZMod con,
        (cexp (2 * (π : ℂ) * I * (((x.val ^ 2 : ℕ) : ℝ) : ℂ) / (con : ℂ))) *
          (Real.sqrt t * GShift x.val t))
      = Real.sqrt t * (∑' x : ZMod con,
        (cexp (2 * (π : ℂ) * I * (((x.val ^ 2 : ℕ) : ℝ) : ℂ) / (con : ℂ))) *
          GShift x.val t) by
    rw [tsum_fintype, tsum_fintype, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring]
  congr 1
  apply tsum_congr
  intro x
  congr 2
  all_goals norm_num [pow_two]


/-- **K3b closed.** The quadratic Gauss sum is `+√con`, unconditionally. -/
theorem gaussSum_re_pos : 0 < (gaussSum qchar' stdAddChar : ℂ).re := by
  have h1 := sqrt_t_chirpSum_tendsto_one
  have h2 := sqrt_t_chirpSum_tendsto_tau
  have heq : (1 : ℂ) = gaussSum qchar' stdAddChar * ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) :=
    tendsto_nhds_unique h1 h2
  have hspos : (0 : ℝ) < Real.sqrt (con : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast con_pos)
  have hsne : (Real.sqrt (con : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hspos)
  have hmul : (1 : ℂ) * (Real.sqrt (con : ℝ) : ℂ)
      = (gaussSum qchar' stdAddChar * ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ)) *
        (Real.sqrt (con : ℝ) : ℂ) := by
    simpa using congrArg (fun z : ℂ => z * (Real.sqrt (con : ℝ) : ℂ)) heq
  rw [one_mul] at hmul
  have hcanc : ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) * (Real.sqrt (con : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    norm_num
  rw [show (gaussSum qchar' stdAddChar * ((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ)) *
        (Real.sqrt (con : ℝ) : ℂ)
      = gaussSum qchar' stdAddChar * (((1 / Real.sqrt (con : ℝ) : ℝ) : ℂ) *
        (Real.sqrt (con : ℝ) : ℂ)) by ring] at hmul
  rw [hcanc, mul_one] at hmul
  have hτ : gaussSum qchar' stdAddChar = (Real.sqrt (con : ℝ) : ℂ) := hmul.symm
  rw [hτ]
  exact hspos

theorem gaussSum_eq_sqrt_con_unconditional :
    gaussSum qchar' stdAddChar = ((Real.sqrt (con : ℝ) : ℝ) : ℂ) := by
  exact gaussSum_eq_sqrt_con gaussSum_re_pos


/-! ### Final rung: K4 / class-number relation ### -/

/-- K3b converts the analytic side to the Kronecker log-sum form. -/
theorem sqrt_con_mul_L_one_eq_neg_log_sum :
    ((Real.sqrt (con : ℝ) : ℝ) : ℂ) * ZMod.LFunction qchar 1
      = ((∑ j : ZMod con, qcharR j *
          -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (con : ℝ))))) : ℝ) := by
  have hre := re_tau_mul_L_one_eq_log_sum
  rw [gaussSum_eq_sqrt_con_unconditional] at hre
  change (((Real.sqrt (con : ℝ) : ℝ) : ℂ) * ZMod.LFunction qchar 1).re = _ at hre
  rw [show (((Real.sqrt (con : ℝ) : ℝ) : ℂ) * ZMod.LFunction qchar 1).re
      = (Real.sqrt (con : ℝ)) * (ZMod.LFunction qchar 1).re by simp [Complex.mul_re]] at hre
  have him : (ZMod.LFunction qchar 1).im = 0 := im_LFunction_one_eq_zero
  apply Complex.ext
  · -- real part
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hre
  · -- imaginary part
    simp [Complex.mul_im, Complex.ofReal_im, him]

/-- K4 has two equivalent statements: the complex class-number relation and the
    Kronecker log-sum relation. -/
theorem cnf_iff_kronecker :
    (((Real.sqrt (con : ℝ) : ℝ) : ℂ) * ZMod.LFunction qchar 1
        = (2 : ℂ) * ((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ)) ↔
    (∑ j : ZMod con, qcharR j *
        -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (con : ℝ)))))
      = 2 * (((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048)) := by
  rw [sqrt_con_mul_L_one_eq_neg_log_sum]
  let S : ℝ := ∑ j : ZMod con, qcharR j *
        -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (con : ℝ))))
  let T : ℝ := ((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048)
  change ((S : ℝ) : ℂ) = (2 : ℂ) * ((T : ℝ) : ℂ) ↔ S = 2 * T
  constructor
  · intro h
    simpa using congrArg Complex.re h
  · intro h
    have h' : ((S : ℝ) : ℂ) = ((2 * T : ℝ) : ℂ) := by exact_mod_cast h
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using h'

/-- The analytic Stark theorem at d = 2048: K3b is discharged; the single
    remaining named input is the Dirichlet class-number relation. -/
theorem analytic_stark_of_CNF
    (hCNF : ((Real.sqrt (con : ℝ) : ℝ) : ℂ) * ZMod.LFunction qchar 1
        = (2 : ℂ) * ((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ)) :
    deriv (ZMod.LFunction qchar) 0
      = ((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ) := by
  exact lprime_zero_eq_hLog_of_gaussSign_of_CNF
    gaussSum_eq_sqrt_con_unconditional hCNF



/-- CNF and the Stark L-side derivative identity are the same statement now
    that K3b is discharged. -/
theorem cnf_iff_stark_L_side :
    ((Real.sqrt (con : ℝ) : ℝ) : ℂ) * ZMod.LFunction qchar 1
        = (2 : ℂ) * ((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ) ↔
    deriv (ZMod.LFunction qchar) 0
      = ((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ) := by
  constructor
  · exact analytic_stark_of_CNF
  · intro hL
    have h1 := two_lprime_zero_eq_tau
    rw [gaussSum_eq_sqrt_con_unconditional] at h1
    rw [hL] at h1
    simpa only [mul_assoc] using h1.symm

/-- **The last rung.** With K3b discharged, the complete Stark Theorem at
    d = 2048 — algebraic unit data and the analytic derivative identity —
    follows from the single Dirichlet class-number relation. -/
theorem stark_ladder_closed
    (hCNF : ((Real.sqrt (con : ℝ) : ℝ) : ℂ) * ZMod.LFunction qchar 1
        = (2 : ℂ) * ((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ)) :
    (epsilonReal 2048 * epsilonConjReal 2048 = 1 ∧
    epsilonReal 2048 + epsilonConjReal 2048 = (2047 : ℝ) ∧
    (2046 : ℝ) < epsilonReal 2048 ∧ epsilonReal 2048 < (2047 : ℝ) ∧
    (1/2047 : ℝ) < epsilonConjReal 2048 ∧ epsilonConjReal 2048 < (1/2046 : ℝ) ∧
    epsilonReal 2048 ≠ 0 ∧ epsilonConjReal 2048 ≠ 0 ∧
    2 * Real.cosh (Real.log (epsilonReal 2048)) = (2047 : ℝ) ∧
    Real.log (epsilonReal 2048) + Real.log (epsilonConjReal 2048) = 0) ∧
    deriv (ZMod.LFunction qchar) 0
      = ((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ) := by
  exact ⟨stark_theorem_d2048, analytic_stark_of_CNF hCNF⟩

end Imscribing.Millennium.StarkDualLimit
