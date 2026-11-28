import Imscribing.Millennium.StarkRungFour

/-!
# StarkRungFourContinued: the Kronecker class-number relation, piece by piece

The KNR `−∑_j χ(j)·log(2·sin(π·j/con)) = 2h·log ε` (h = 64, ε = epsilonReal 2048)
decomposes as follows, with the registered rung-1 identity
`two_lprime_zero_eq_tau` as the hinge:

* K1 (registered): `−∑χ log(2sin) = 2·Re L′(0,χ)` — so KNR ⟹ `Re L′(0,χ) = h·log ε`.
* K2 (this file): `Im τ(χ) = 0` — even-character pairing, elementary.
* K3a (this file): `τ(χ)^2 = con` — from registered `gaussSum_sq_conj` + K2.
* K3b (classical Gauss sign, open named input): `τ(χ) = +√con`.
* K4 (Dirichlet class number formula for ℚ(√4190205), open named input):
  `√con · L(1,χ) = 2h·log ε`.
* Reductions (this file): `Im L(1,χ) = 0` and `Im L′(0,χ) = 0`, hence
  K2 + KNR ⟹ the full ℂ-level Stark identification
  `L′(0,χ) = h·log ε`; and K3b + K4 ⟹ the same via rung 1 alone.
-/

open Complex Real Filter Finset Topology
open scoped ComplexConjugate
open ZMod
open Imscribing.Millennium.StarkCharacterD2048
open Imscribing.Millennium.StarkGaussSum
open Imscribing.Millennium.StarkRungOne
open Imscribing.Millennium.ClinkStarkBridge
open StarkLogRung

noncomputable section

namespace Imscribing.Millennium.StarkRungFour

/-! ## K2: the Gauss sum is real -/

/-- The standard additive character takes values on the unit circle:
`conj(ψ a) = (ψ a)⁻¹`. -/
private theorem stdAddChar_conj_self (a : ZMod con) :
    conj (stdAddChar (N := con) a) = (stdAddChar (N := con) a)⁻¹ := by
  rw [stdAddChar_eq_rootExp a]
  unfold rootExp
  have hcast : ∀ n : ℕ, conj ((n : ℂ)) = ((n : ℂ)) := Complex.conj_natCast
  have hconj : conj (2 * Real.pi * Complex.I * (((a.val : ℕ) : ℂ) / (con : ℂ)))
      = -(2 * Real.pi * Complex.I * (((a.val : ℕ) : ℂ) / (con : ℂ))) := by
    have h2 : conj (2 : ℂ) = 2 := Complex.conj_ofNat 2
    have hpi : conj ((Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) := Complex.conj_ofReal _
    have hI : conj Complex.I = -Complex.I := Complex.conj_I
    rw [div_eq_mul_inv, map_mul, map_mul, map_mul, map_mul, Complex.conj_inv,
      h2, hpi, hI, hcast, hcast]
    ring
  rw [← Complex.exp_conj, hconj, Complex.exp_neg]

/-- **K2.** The Gauss sum of the Stark character is real: the evenness
`χ(−a) = χ(a)` pairs each term with the conjugate of its additive-character
value. -/
theorem gaussSum_im_zero : (gaussSum qchar' stdAddChar).im = 0 := by
  have h1 : gaussSum qchar' stdAddChar
      = ∑ a : ZMod con, qchar' a * stdAddChar (N := con) (-a) := by
    rw [gaussSum, ← Fintype.sum_equiv (Equiv.neg (ZMod con))
      (fun a : ZMod con => qchar' (-a) * stdAddChar (N := con) (-a))
      (fun a : ZMod con => qchar' a * stdAddChar (N := con) a)
      (fun a => rfl)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [qchar_apply, qchar_apply, qchar_even a]
  have hterm : ∀ a : ZMod con,
      (qchar' a * (stdAddChar (N := con) a + stdAddChar (N := con) (-a))).im = 0 := by
    intro a
    rcases qchar'_isQuadratic a with hc | hc | hc
    · rw [hc]; simp
    · rw [hc, one_mul,
        show (stdAddChar (N := con) a + stdAddChar (N := con) (-a)).im = 0 from by
          rw [AddChar.map_neg_eq_inv, ← stdAddChar_conj_self, Complex.add_im,
            Complex.conj_im]
          ring]
    · rw [hc, neg_one_mul, Complex.neg_im, Complex.add_im, AddChar.map_neg_eq_inv,
        ← stdAddChar_conj_self, Complex.conj_im]
      ring
  have h2 : (2:ℂ) * gaussSum qchar' stdAddChar
      = ∑ a : ZMod con,
          qchar' a * (stdAddChar (N := con) a + stdAddChar (N := con) (-a)) := by
    calc (2:ℂ) * gaussSum qchar' stdAddChar
        = gaussSum qchar' stdAddChar
            + ∑ a : ZMod con, qchar' a * stdAddChar (N := con) (-a) := by
          rw [h1]; ring
      _ = ∑ a : ZMod con, qchar' a * stdAddChar (N := con) a
            + ∑ a : ZMod con, qchar' a * stdAddChar (N := con) (-a) := by
          rw [gaussSum]
      _ = ∑ a : ZMod con,
            qchar' a * (stdAddChar (N := con) a + stdAddChar (N := con) (-a)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun a _ => by ring
  have him2 : ((2:ℂ) * gaussSum qchar' stdAddChar).im = 0 := by
    rw [h2, Complex.im_sum]
    exact Finset.sum_eq_zero fun a _ => hterm a
  have hsplit : ((2:ℂ) * gaussSum qchar' stdAddChar).im
      = (2:ℝ) * (gaussSum qchar' stdAddChar).im := by
    rw [Complex.mul_im]
    norm_num
  rw [hsplit] at him2
  linarith

/-- **K2, real form.** The Gauss sum equals its own conjugate. -/
theorem conj_gaussSum_self :
    conj (gaussSum qchar' stdAddChar) = gaussSum qchar' stdAddChar := by
  refine Complex.ext ?_ ?_
  · exact Complex.conj_re _
  · rw [Complex.conj_im, gaussSum_im_zero, neg_zero]

/-! ## K3a: the square of the Gauss sum is the conductor -/

/-- **K3a.** The square of the Gauss sum is the conductor: `τ(χ)² = 4190205`
(from the registered `gaussSum_sq_conj` and K2). -/
theorem gaussSum_sq : gaussSum qchar' stdAddChar ^ 2 = (con : ℂ) := by
  have h1 := gaussSum_sq_conj
  rw [conj_gaussSum_self] at h1
  rw [pow_two]
  exact h1

/-- **K3, sign-isolated.** The Gauss sum is `±√4190205`; only the sign remains
(the classical quadratic Gauss-sum evaluation for the fundamental discriminant
4190205 ≡ 1 mod 4). -/
theorem gaussSum_eq_sqrt_or_neg :
    gaussSum qchar' stdAddChar = ((Real.sqrt (con : ℝ) : ℝ) : ℂ)
    ∨ gaussSum qchar' stdAddChar = -((Real.sqrt (con : ℝ) : ℝ) : ℂ) := by
  have hτself : gaussSum qchar' stdAddChar
      = (((gaussSum qchar' stdAddChar : ℂ).re : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · rw [Complex.ofReal_re]
    · rw [gaussSum_im_zero, Complex.ofReal_im]
  have hsq : gaussSum qchar' stdAddChar ^ 2 = ((Real.sqrt (con : ℝ) : ℝ) : ℂ) ^ 2 := by
    rw [gaussSum_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (by exact_mod_cast (le_of_lt con_pos)), Complex.ofReal_natCast]
  have hτre2 : (gaussSum qchar' stdAddChar : ℂ).re ^ 2 = Real.sqrt (con : ℝ) ^ 2 := by
    have h1 := congrArg Complex.re hsq
    rw [pow_two, pow_two, Complex.mul_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, gaussSum_im_zero] at h1
    simp only [mul_zero, sub_zero] at h1
    rw [pow_two, pow_two]
    exact h1
  have hpos : 0 ≤ Real.sqrt (con : ℝ) := Real.sqrt_nonneg _
  have habseq : |(gaussSum qchar' stdAddChar : ℂ).re| = Real.sqrt (con : ℝ) := by
    have h1 := (sq_eq_sq_iff_abs_eq_abs (gaussSum qchar' stdAddChar : ℂ).re
      (Real.sqrt (con : ℝ))).mp hτre2
    rwa [abs_of_nonneg hpos] at h1
  rw [hτself]
  rcases (abs_eq hpos).mp habseq with h | h
  · left
    rw [h]
  · right
    rw [h, Complex.ofReal_neg]

/-! ## Imaginary parts of the L-side -/

/-- The partial sums of the Stark L-series at `s = 1` are real (each summand is
a real character value divided by a positive real). -/
private theorem upartial_im_zero (K : ℕ) : (LValOne.Upartial qchar 1 K).im = 0 := by
  have hterm : ∀ n ∈ Finset.range K,
      ((LValOne.dcoef 1 n : ℝ) • LValOne.zseq qchar n).im = 0 := by
    intro n _
    have hz : LValOne.zseq qchar n = qchar ((n + 1 : ℕ) : ZMod con) := by
      show qchar ((n : ZMod con) + 1) = _
      rw [Nat.cast_add, Nat.cast_one]
    rw [hz, ← coe_qcharR, Complex.real_smul, Complex.mul_im]
    simp
  rw [LValOne.Upartial, Complex.im_sum]
  exact Finset.sum_eq_zero hterm

/-- `Im L(1,χ) = 0`: the L-value is the limit of the real partial sums, and ℝ
is closed in ℂ. -/
theorem im_LFunction_one_eq_zero : (ZMod.LFunction qchar 1).im = 0 := by
  have hUP : Tendsto (LValOne.Upartial qchar 1) atTop
      (𝓝 (ZMod.LFunction qchar 1)) := by
    have h := LValOne.Slim_spec qchar sum_qchar_eq_zero 1 le_rfl
    rwa [← LValOne.lFunction_one_eq qchar sum_qchar_eq_zero] at h
  have h1 : Tendsto (fun K : ℕ => (LValOne.Upartial qchar 1 K).im) atTop
      (𝓝 ((ZMod.LFunction qchar 1).im)) := by
    have h := (continuous_im.tendsto (ZMod.LFunction qchar 1)).comp hUP
    exact h
  have h2 : Tendsto (fun K : ℕ => (LValOne.Upartial qchar 1 K).im) atTop
      (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr'
      (Filter.Eventually.of_forall fun K => (upartial_im_zero K).symm)
  exact tendsto_nhds_unique h1 h2

/-- With K2, the imaginary part of `τ(χ)·L(1,χ)` vanishes: the Gauss sum is
real and `Im L(1,χ) = 0`. -/
theorem im_tau_mul_L_one_eq_zero :
    (gaussSum qchar' stdAddChar * ZMod.LFunction qchar 1).im = 0 := by
  rw [Complex.mul_im, gaussSum_im_zero, im_LFunction_one_eq_zero]
  norm_num

/-- **K2 on the L-side.** `Im L′(0,χ) = 0`: by rung 1, `2·L′(0,χ) = τ(χ)·L(1,χ)`,
whose imaginary part vanishes. -/
theorem im_lprime_zero_eq_zero : (deriv (ZMod.LFunction qchar) 0).im = 0 := by
  have h := congrArg Complex.im two_lprime_zero_eq_tau
  rw [im_tau_mul_L_one_eq_zero, Complex.mul_im] at h
  norm_num at h
  linarith

/-! ## The KNR reductions -/

/-- **Reduction, K2 route.** Given the Kronecker class-number relation
(hypothesis `hKNR`), rung 1 + K2 yield the full ℂ-level Stark identification
`L′(0,χ) = h·log ε` — no real-part bookkeeping left. -/
theorem lprime_zero_eq_hLog_of_hKNR
    (hKNR : ∑ j : ZMod con, qcharR j
        * -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (con : ℝ))))
      = 2 * ((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048)) :
    deriv (ZMod.LFunction qchar) 0
      = (((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ)) := by
  have hre := re_lprime_zero_eq_hRegulator hKNR
  have him := im_lprime_zero_eq_zero
  refine Complex.ext ?_ ?_
  · have hr : Complex.reCLM (deriv (ZMod.LFunction qchar) 0)
        = (deriv (ZMod.LFunction qchar) 0).re := rfl
    rwa [hr] at hre
  · rw [him, Complex.ofReal_im]

/-- **Reduction, K3+K4 route.** Given the classical Gauss sign `τ(χ) = +√con`
(K3b) and the Dirichlet class number formula for `ℚ(√4190205)` in the form
`√con·L(1,χ) = 2h·log ε` (K4, hypothesis `hCNF`), rung 1 alone yields the full
ℂ-level Stark identification `L′(0,χ) = h·log ε`. -/
theorem lprime_zero_eq_hLog_of_gaussSign_of_CNF
    (hsign : gaussSum qchar' stdAddChar = ((Real.sqrt (con : ℝ) : ℝ) : ℂ))
    (hCNF : ((Real.sqrt (con : ℝ) : ℝ) : ℂ) * ZMod.LFunction qchar 1
      = (2:ℂ) * ((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ)) :
    deriv (ZMod.LFunction qchar) 0
      = (((((hField : ℕ) : ℝ) * Real.log (epsilonReal 2048) : ℝ) : ℂ)) := by
  have h1 := two_lprime_zero_eq_tau
  rw [hsign, hCNF] at h1
  have h2 : (2:ℂ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ h2 h1

end Imscribing.Millennium.StarkRungFour

end
