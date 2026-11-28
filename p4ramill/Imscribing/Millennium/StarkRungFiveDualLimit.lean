import Imscribing.Millennium.StarkRungFiveDual
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

set_option maxHeartbeats 1000000

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
  have hZ : ((t : ℂ) - 2 * I) ≠ 0 := by
    intro h
    have him : ((t : ℂ) - 2 * I).im = -2 := by
      simp [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im]
    rw [h] at him
    simp at him
  have hmul : ((t : ℂ) - 2 * I)
        * (Complex.ofReal ((con : ℝ) * t / (t ^ 2 + 4))
          + Complex.ofReal ((con : ℝ) * 2 / (t ^ 2 + 4)) * I)
      = Complex.ofReal (con : ℝ) := by
    refine Complex.ext ?_ ?_
    · simp only [mul_add, mul_sub, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      have hD : (0 : ℝ) < t ^ 2 + 4 := by positivity
      field_simp
      ring
    · simp only [mul_add, mul_sub, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      have hD : (0 : ℝ) < t ^ 2 + 4 := by positivity
      field_simp
      ring
  exact (eq_div_of_mul_eq hZ (by rw [mul_comm]; exact hmul)).symm

/-- The real part of `con / (t - 2i)`. -/
theorem re_dualParam (t : ℝ) : (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)).re
    = (con : ℝ) * t / (t ^ 2 + 4) := by
  rw [dualParam_eq t]
  simp

/-- The imaginary part of `con / (t - 2i)`. -/
theorem im_dualParam (t : ℝ) : (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)).im
    = (con : ℝ) * 2 / (t ^ 2 + 4) := by
  rw [dualParam_eq t]
  simp

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
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [Complex.norm_exp, hre2, Real.exp_zero]
  simp only [dualTerm]
  rw [harg, Complex.exp_add, norm_mul, rexp_norm_ofReal, h2, mul_one]

theorem summable_dualTerm (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℤ => dualTerm t n) := by
  refine Summable.of_norm ?_
  have ha : 0 < (con : ℝ) * t / (t ^ 2 + 4) := by
    exact div_pos (mul_pos (Nat.cast_pos.mpr con_pos) ht) (by positivity)
  exact (summable_gaussReal _ ha).congr (fun n => by rw [dualTerm_norm t ht n]; congr 1; ring)

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
          (by refine mul_le_mul_of_nonneg_left ?_ (by norm_num); exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
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
          (by refine mul_le_mul_of_nonneg_left ?_ (by norm_num); exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
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
theorem evenMain_eq (a : ℝ) :
    (∑' n : ℕ, cexp ((-π * a * ((n : ℕ) : ℝ) ^ 2) : ℂ))
      = ((gaussSumNat a : ℝ) : ℂ) := by
  have hconv : (∑' n : ℕ, cexp ((-π * a * ((n : ℕ) : ℝ) ^ 2) : ℂ))
      = ∑' n : ℕ, (Complex.ofReal (rexp (-π * a * ((n : ℕ) : ℝ) ^ 2)) : ℂ) :=
    tsum_congr (fun n => (Complex.ofReal_exp _).symm)
  rw [hconv, Complex.ofRealCLM.map_tsum (summable_gaussNat a (by positivity))]

/-- The odd main half-line series is the complexification of `gaussSumHalf`. -/
theorem oddMain_eq (a : ℝ) (ha : 0 < a) :
    (∑' n : ℕ, cexp ((-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ))
      = ((gaussSumHalf (4 * a) : ℝ) : ℂ) := by
  have hconv : (∑' n : ℕ, cexp ((-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ))
      = ∑' n : ℕ, (Complex.ofReal (rexp (-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) : ℂ) :=
    tsum_congr (fun n => (Complex.ofReal_exp _).symm)
  have hsum : Summable (fun n : ℕ =>
      rexp (-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun n => exp_nonneg _) (fun n => ?_)
      (summable_gaussNat a ha)
    refine exp_le_exp.mpr ?_
    have h1 : ((n : ℕ) : ℝ) ^ 2 ≤ (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
      have h2 : (((2 * n + 1 : ℕ) : ℝ)) = 2 * ((n : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [h2]; nlinarith [sq_nonneg ((n : ℕ) : ℝ)]
    have hneg : -π * a ≤ 0 := by linarith [mul_pos Real.pi_pos ha]
    exact mul_le_mul_of_nonpos_right h1 hneg
  rw [hconv, Complex.ofRealCLM.map_tsum hsum]
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
  have hcast : (((2 * n : ℕ) : ℤ) : ℝ) = ((2 * n : ℕ) : ℝ) := by push_cast
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
    ring
  rw [hvs, mul_add, Complex.exp_add]
  rw [exp_I_two_pi (-((con * (n * n) : ℕ) : ℤ)), one_mul]
  rw [mul_comm]
  rw [show (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n : ℕ) : ℝ) ^ 2))
      = -π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2 from by ring]
/-- The odd `n = 2m+1` term: Gaussian times `-i` up to a decaying phase. -/
theorem dualOdd_term (t : ℝ) (ht : 0 < t) (n : ℕ) :
    dualTerm t ((2 * n + 1 : ℕ) : ℤ)
      = -(I : ℂ) * cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ))
        * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ) := by
  have h := dualExponent_eq t ht ((2 * n + 1 : ℕ) : ℤ)
  have hcast : (((2 * n + 1 : ℕ) : ℤ) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) := by push_cast
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
    ring
  rw [hvs, mul_add, mul_add, Complex.exp_add, Complex.exp_add]
  rw [exp_I_two_pi (-((con * (n * (n + 1)) : ℕ) : ℤ)), one_mul]
  have h5 := Nat.div_add_mod con 4
  rw [con_mod_four] at h5
  have h6 : con / 4 = (con - 1) / 4 := by omega
  have hint2 : cexp (I * (Complex.ofReal (-(π * (con : ℝ) / 2)))) = -(I : ℂ) := by
    have hsplit : (-(π * (con : ℝ) / 2) : ℝ)
        = (((-(((con - 1) / 4 : ℕ) : ℤ)) : ℝ) * 2 * π) + (-(π / 2 : ℝ)) := by
      have hq : (con : ℝ) = 4 * (((con - 1) / 4 : ℕ) : ℝ) + 1 := by
        conv_lhs => rw [h5, h6]
        push_cast
      rw [hq]
      field_simp
      ring
    rw [hsplit, Complex.ofReal_add, mul_add, Complex.exp_add,
      exp_I_two_pi (-(((con - 1) / 4 : ℕ) : ℤ)), one_mul, exp_I_neg_half]
  rw [hint2]
  ring

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
        rw [rexp_norm_ofReal]
    _ ≤ rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)
          * (2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) :=
        mul_le_mul_of_nonneg_left (norm_exp_I_sub_one _) (exp_nonneg _)
    _ = (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (((n : ℕ) : ℝ) ^ 2
          * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)) := by ring

theorem dualEven_dev_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
        * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)) := by
  have ha0 : 0 < 4 * (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht) (by positivity)
  have hdom : Summable (fun n : ℕ => (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (((n : ℕ) : ℝ) ^ 2
      * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2))) :=
    summable_const_mul (summable_sqMoment _ ha0) _
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (dualEven_dev_term t ht) hdom

theorem dualEven_dev_bound (t : ℝ) (ht : 0 < t) :
    ‖∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
        * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)‖
      ≤ (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))
        * (2 / ((4 * (con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
          + 2) := by
  have ha0 : 0 < 4 * (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht) (by positivity)
  have hdom : Summable (fun n : ℕ => (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (((n : ℕ) : ℝ) ^ 2
      * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2))) :=
    summable_const_mul (summable_sqMoment _ ha0) _
  have hnorms : Summable (fun n : ℕ =>
      ‖cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
        * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (dualEven_dev_term t ht) hdom
  have hsq := sqMoment_le' (4 * (con : ℝ) * t / (t ^ 2 + 4)) ha0
  calc ‖∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
          * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)‖
      ≤ ∑' n : ℕ, ‖cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
          * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ)) - 1)‖ :=
        norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' n : ℕ, (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (((n : ℕ) : ℝ) ^ 2
          * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)) :=
        Summable.tsum_le_tsum (dualEven_dev_term t ht) hnorms hdom
    _ = (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)) * (∑' n : ℕ, ((n : ℕ) : ℝ) ^ 2
          * rexp (-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)) :=
        (Summable.tsum_mul_left _ hdom).symm
    _ ≤ (2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))
          * (2 / ((4 * (con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
            + 2) := mul_le_mul_of_nonneg_left hsq (by positivity)

theorem summable_oddGauss (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => rexp (-π * a * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) := by
  refine Summable.of_nonneg_of_le (fun n => exp_nonneg _) (fun n => ?_) (summable_gaussNat a ha)
  refine exp_le_exp.mpr ?_
  have h1 : ((n : ℕ) : ℝ) ^ 2 ≤ (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
    have h2 : (((2 * n + 1 : ℕ) : ℝ)) = 2 * ((n : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h2]; nlinarith [sq_nonneg ((n : ℕ) : ℝ)]
  have hneg : -π * a ≤ 0 := by linarith [mul_pos Real.pi_pos ha]
  exact mul_le_mul_of_nonpos_right h1 hneg

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
            / (2 * (t ^ 2 + 4))) : ℂ))‖ :=
        le_trans (norm_mul_le _ _)
          (mul_le_mul_of_nonneg_right (le_trans (norm_mul_le _ _)
            (mul_le_mul (by norm_num [Complex.norm_I]) (le_refl _) (by simp [Complex.norm_I])
              (norm_nonneg _))) (norm_nonneg _))
    _ = rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
          * ‖1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ))‖ := by
        rw [rexp_norm_ofReal]
    _ ≤ rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))
          * (π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2 / (2 * (t ^ 2 + 4))) := by
        refine mul_le_mul_of_nonneg_left ?_ (exp_nonneg _)
        rw [norm_sub_rev]
        exact norm_exp_I_sub_one _
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
    summable_const_mul (summable_oddSq _ ha0) _
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (dualOdd_dev_term t ht) hdom

theorem dualOdd_dev_bound (t : ℝ) (ht : 0 < t) :
    ‖∑' n : ℕ, (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))‖
      ≤ (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
        * (8 / (((con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt ((con : ℝ) * t / (t ^ 2 + 4))) + 8) := by
  have ha0 : 0 < (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (Nat.cast_pos.mpr con_pos) ht) (by positivity)
  have hdom : Summable (fun n : ℕ => (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
      * ((((2 * n + 1 : ℕ) : ℝ) ^ 2)
        * rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)))) :=
    summable_const_mul (summable_oddSq _ ha0) _
  have hnorms : Summable (fun n : ℕ =>
      ‖(I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (dualOdd_dev_term t ht) hdom
  have hsq := oddSqMoment_le' ((con : ℝ) * t / (t ^ 2 + 4)) ha0
  calc ‖∑' n : ℕ, (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))‖
      ≤ ∑' n : ℕ, ‖(I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
          * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ)))‖ := norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' n : ℕ, (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4))) * ((((2 * n + 1 : ℕ) : ℝ) ^ 2)
          * rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) :=
        Summable.tsum_le_tsum (dualOdd_dev_term t ht) hnorms hdom
    _ = (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4))) * (∑' n : ℕ, (((2 * n + 1 : ℕ) : ℝ) ^ 2)
          * rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2))) :=
        (Summable.tsum_mul_left _ hdom).symm
    _ ≤ (π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
          * (8 / (((con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt ((con : ℝ) * t / (t ^ 2 + 4)))
            + 8) := mul_le_mul_of_nonneg_left hsq (by positivity)

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
      (fun n => by rw [rexp_norm_ofReal])
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
        rw [evenMain_eq, hGint]
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
      (fun n => by rw [rexp_norm_ofReal])
  have hsd := dualOdd_dev_summable t ht
  have hsplit : (∑' n : ℕ, dualTerm t ((2 * n + 1 : ℕ) : ℤ))
      = (∑' n : ℕ, cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ))
        + (∑' n : ℕ, (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
              * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ)))) := by
    rw [← Summable.tsum_add hsu hsd]
    exact tsum_congr (fun n => by rw [dualOdd_term t ht n]; ring)
  have hodd : ((2 * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)
      = 2 * (∑' n : ℕ, cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
            * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)) := by
    rw [oddMain_eq]
  calc dualOdd t
      = 2 * (∑' n : ℕ, dualTerm t ((2 * n + 1 : ℕ) : ℤ)) := rfl
    _ = 2 * ((∑' n : ℕ, cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
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
        rw [hodd]
        ring

/-! ## Tendsto machinery -/

/-- `√(t·con) · K·(π·con·t²/(t²+4)) → 0` — the slack term. -/
theorem extra_tendsto (K : ℝ) :
    Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t)
        * (K * ((π : ℝ) * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.sqrt ((con : ℝ) * t)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => Real.sqrt ((con : ℝ) * t)) 0 :=
      Real.continuous_sqrt.continuousAt.comp (by fun_prop)
    exact Tendsto.mono_left nhdsWithin_le_nhds (by simpa using hc.tendsto)
  have h2 : Tendsto (fun t : ℝ => K * ((π : ℝ) * (con : ℝ) * t ^ 2 / (t ^ 2 + 4)))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => K * ((π : ℝ) * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))) 0 := by
      refine ContinuousAt.mul continuousAt_const ?_
      refine ContinuousAt.div₀ (by fun_prop) continuousAt_const (by norm_num)
      fun_prop
    exact Tendsto.mono_left nhdsWithin_le_nhds (by simpa using hc.tendsto)
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
      Real.sqrt_div (by positivity)
    have hD : Real.sqrt ((con : ℝ) * t) / (Real.sqrt (4 * (con : ℝ) * t)
          / Real.sqrt (t ^ 2 + 4)) = Real.sqrt ((t ^ 2 + 4) / 4) := by
      rw [div_eq_mul_inv, inv_div, mul_div_assoc',
        ← Real.sqrt_mul (by positivity : 0 ≤ (con : ℝ) * t),
        Real.sqrt_div (by positivity : 0 ≤ (con : ℝ) * t * (t ^ 2 + 4))]
      congr 1
      field_simp
    rw [h1, hD]
  refine Tendsto.congr' hcongr ?_
  have hcv : ContinuousAt (fun t : ℝ => Real.sqrt ((t ^ 2 + 4) / 4)) 0 := by
    refine Real.continuous_sqrt.continuousAt.comp ?_
    exact ContinuousAt.div₀ (by fun_prop) continuousAt_const (by norm_num)
  have hval : (Real.sqrt ((0 ^ 2 + 4) / 4) : ℝ) = 1 := by norm_num
  have hT := hcv.tendsto
  rw [hval] at hT
  exact Tendsto.mono_left nhdsWithin_le_nhds hT

/-- `c₀·t/(t²+4) → 0⁺` along `t → 0⁺`. -/
theorem tendsto_a1 {c₀ : ℝ} (hc₀ : 0 < c₀) :
    Tendsto (fun t : ℝ => c₀ * t / (t ^ 2 + 4)) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hc : ContinuousAt (fun t : ℝ => c₀ * t / (t ^ 2 + 4)) 0 := by
      refine ContinuousAt.div₀ (by fun_prop) continuousAt_const (by norm_num)
      fun_prop
    exact Tendsto.mono_left nhdsWithin_le_nhds (by simpa using hc.tendsto)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact mem_Ioi.mpr (div_pos (mul_pos hc₀ ht.1) (by positivity))

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
      div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht) (by positivity)
    rw [← mul_assoc, div_mul_cancel₀ _ (sqrt_ne_zero.mpr (ne_of_gt hpos))]
  refine Tendsto.congr' hcongr ?_
  have h1 : Tendsto (fun t : ℝ => Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4))
      * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4))) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    refine Tendsto.congr'
      (Filter.Eventually.of_forall (fun t => by rw [Real.sqrt_eq_rpow])) ?_
    exact gaussSumHalf_asympt.comp (tendsto_a1 hc₀)
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
  refine Tendsto.congr' hcongr ?_
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
      div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht) (by positivity)
    push_cast
    rw [← mul_assoc, div_mul_cancel₀ _ (sqrt_ne_zero.mpr (ne_of_gt hpos))]
  refine Tendsto.congr' hcongr ?_
  have h1 : Tendsto (fun t : ℝ => ((Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4))
        * gaussSumInt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    have hcomp := thetaAsympt_full.comp (tendsto_a1 hc₀)
    have hcast := (Complex.ofRealCLM).continuous.continuousAt.tendsto.comp hcomp
    refine Tendsto.congr'
      (Filter.Eventually.of_forall (fun t => by rw [Real.sqrt_eq_rpow])) ?_
    exact hcast
  have h2 : Tendsto (fun t : ℝ => ((Real.sqrt ((con : ℝ) * t)
      / Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    have hcast := (Complex.ofRealCLM).continuous.continuousAt.tendsto.comp sqrtRatio_tendsto
    simpa using hcast
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
    have hsqne : Real.sqrt (c₀ * t) ≠ 0 := sqrt_ne_zero.mpr (ne_of_gt hpt)
    have h1 : Real.sqrt (c₀ * t / (t ^ 2 + 4)) = Real.sqrt (c₀ * t) / Real.sqrt (t ^ 2 + 4) :=
      Real.sqrt_div (by positivity)
    have h2 : Real.sqrt ((con : ℝ) * t) / Real.sqrt (c₀ * t) = Real.sqrt ((con : ℝ) / c₀) := by
      rw [Real.sqrt_div (by positivity)]
      congr 1
      field_simp
    have h4 : (2 : ℝ) / ((c₀ * t / (t ^ 2 + 4)) * Real.sqrt (c₀ * t / (t ^ 2 + 4)))
        = 2 * ((t ^ 2 + 4) * Real.sqrt (t ^ 2 + 4)) / (c₀ * t * Real.sqrt (c₀ * t)) := by
      rw [h1, div_mul_div_comm, div_eq_mul_inv, inv_div]
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
  refine Tendsto.congr' hcongr ?_
  have hc : ContinuousAt (fun t : ℝ => (t : ℝ) * Real.sqrt (t ^ 2 + 4)) 0 := by
    refine ContinuousAt.mul (by fun_prop) ?_
    exact Real.continuous_sqrt.continuousAt.comp (by fun_prop)
  have h1 : Tendsto (fun t : ℝ => (t : ℝ) * Real.sqrt (t ^ 2 + 4)) (𝓝[>] 0) (𝓝 0) := by
    exact Tendsto.mono_left nhdsWithin_le_nhds (by simpa using hc.tendsto)
  simpa using h1.const_mul _

/-! ## Squeeze helper -/

/-- If `0 ≤ f ≤ g` eventually along `𝓝[>] 0` and `g → 0`, then `f → 0`. -/
theorem nonneg_le_tendsto_zero {f g : ℝ → ℝ}
    (hnn : ∀ t : ℝ, 0 ≤ f t) (hfg : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ g t)
    (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0)) : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hg' := Metric.tendsto_nhdsWithin_iff.mp hg ε hε
  filter_upwards [hfg, hg'] with t h1 h2
  rw [mem_ball, Real.dist_eq]
  simp only [sub_zero]
  have hgn : 0 ≤ g t := le_trans (hnn t) h1
  calc |f t| = f t := abs_of_nonneg (hnn t)
    _ ≤ g t := h1
    _ ≤ |g t| := le_abs_self _
    _ < ε := by simpa [Real.dist_eq, sub_zero] using h2.1

/-! ## Scaled deviation limits -/

/-- The norm bound for the scaled even deviation. -/
theorem dualEven_norm_dev (t : ℝ) (ht : 0 < t) :
    Complex.abs (((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ) * (2 * (∑' n : ℕ,
        cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
          * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
            - 1))))
      ≤ Real.sqrt ((con : ℝ) * t) * (2 * ((2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))
        * (2 / ((4 * (con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
          + 2))) := by
  have hpos : 0 < 4 * (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos)) ht) (by positivity)
  have hsqnn : Complex.abs ((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ)
      = Real.sqrt ((con : ℝ) * t) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_mul, hsqnn]
  have hS : Summable (fun n : ℕ =>
      cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
        * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
          - 1)) := dualEven_dev_summable t ht
  calc Real.sqrt ((con : ℝ) * t) * Complex.abs (2 * (∑' n : ℕ,
          cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1)))
      ≤ Real.sqrt ((con : ℝ) * t) * (2 * Complex.abs (∑' n : ℕ,
          cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        have h2n : Complex.abs ((2 : ℂ)) = 2 := by norm_num
        rw [norm_mul, h2n]
    _ ≤ Real.sqrt ((con : ℝ) * t) * (2 * ∑' n : ℕ, Complex.abs (
          cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
            * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
              - 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hS) (by norm_num)
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
  refine nonneg_le_tendsto_zero (f := fun t => Complex.abs (((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ)
      * (2 * (∑' n : ℕ, cexp ((-π * (4 * (con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) : ℂ)
          * (cexp (I * ((2 * π * (con : ℝ) * ((n : ℕ) : ℝ) ^ 2 * t ^ 2 / (t ^ 2 + 4)) : ℂ))
            - 1)))))
    (g := fun t => Real.sqrt ((con : ℝ) * t) * (2 * ((2 * π * (con : ℝ) * t ^ 2 / (t ^ 2 + 4))
      * (2 / ((4 * (con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt (4 * (con : ℝ) * t / (t ^ 2 + 4)))
        + 2)))) ?_ ?_ ?_
  · intro t; exact Real.zero_le _
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact dualEven_norm_dev t ht
  · refine Tendsto.congr' ?_ (Tendsto.add ?_ ?_)
    · filter_upwards with t; ring
    · exact devScale_tendsto (c₀ := 4 * (con : ℝ)) (κ := 4)
        (mul_pos (by norm_num) (Nat.cast_pos.mpr con_pos))
    · exact extra_tendsto 8

/-- The norm bound for the scaled odd deviation. -/
theorem dualOdd_norm_dev (t : ℝ) (ht : 0 < t) :
    Complex.abs (((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ) * (2 * (∑' n : ℕ,
        (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
          * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
            / (2 * (t ^ 2 + 4))) : ℂ))))))
      ≤ Real.sqrt ((con : ℝ) * t) * (2 * ((π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
        * (8 / (((con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt ((con : ℝ) * t / (t ^ 2 + 4)))
          + 8))) := by
  have hpos : 0 < (con : ℝ) * t / (t ^ 2 + 4) :=
    div_pos (mul_pos (Nat.cast_pos.mpr con_pos) ht) (by positivity)
  have hsqnn : Complex.abs ((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ)
      = Real.sqrt ((con : ℝ) * t) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_mul, hsqnn]
  have hS : Summable (fun n : ℕ =>
      (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
          / (2 * (t ^ 2 + 4))) : ℂ)))) := dualOdd_dev_summable t ht
  calc Real.sqrt ((con : ℝ) * t) * Complex.abs (2 * (∑' n : ℕ,
          (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ)))))
      ≤ Real.sqrt ((con : ℝ) * t) * (2 * Complex.abs (∑' n : ℕ,
          (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        have h2n : Complex.abs ((2 : ℂ)) = 2 := by norm_num
        rw [norm_mul, h2n]
    _ ≤ Real.sqrt ((con : ℝ) * t) * (2 * ∑' n : ℕ, Complex.abs (
          (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
            * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
              / (2 * (t ^ 2 + 4))) : ℂ))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hS) (by norm_num)
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
  refine nonneg_le_tendsto_zero (f := fun t => Complex.abs (((Real.sqrt ((con : ℝ) * t) : ℝ) : ℂ)
      * (2 * (∑' n : ℕ, (I : ℂ) * cexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))
          * (((2 * n + 1 : ℕ) : ℝ) ^ 2)) : ℂ)
        * (1 - cexp (I * ((π * (con : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) * t ^ 2
          / (2 * (t ^ 2 + 4))) : ℂ))))))
    (g := fun t => Real.sqrt ((con : ℝ) * t) * (2 * ((π * (con : ℝ) * t ^ 2 / (2 * (t ^ 2 + 4)))
      * (8 / (((con : ℝ) * t / (t ^ 2 + 4)) * Real.sqrt ((con : ℝ) * t / (t ^ 2 + 4))) + 8))))
    ?_ ?_ ?_
  · intro t; exact Real.zero_le _
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact dualOdd_norm_dev t ht
  · refine Tendsto.congr' ?_ (Tendsto.add ?_ ?_)
    · filter_upwards with t; ring
    · exact devScale_tendsto (c₀ := (con : ℝ)) (κ := 4) (Nat.cast_pos.mpr con_pos)
    · exact extra_tendsto 8

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
    rw [dualEven_eq t ht, mul_add]
  refine Tendsto.congr' hcongr ?_
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
    rw [dualOdd_eq t ht, mul_add]
    ring
  refine Tendsto.congr' hcongr ?_
  have hcast : Tendsto (fun t : ℝ => ((Real.sqrt ((con : ℝ) * t) : ℂ)
      * ((2 * gaussSumHalf (4 * (con : ℝ) * t / (t ^ 2 + 4)) : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 1) := by
    simpa using (Complex.ofRealCLM).continuous.continuousAt.tendsto.comp gaussSumHalf2_scaled
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
    rw [dualTheta_split t ht, mul_add]
  refine Tendsto.congr' hcongr ?_
  simpa using (dualEven_limit).add (dualOdd_limit)

end Imscribing.Millennium.StarkDualLimit
