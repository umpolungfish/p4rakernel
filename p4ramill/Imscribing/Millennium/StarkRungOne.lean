import Mathlib
import Imscribing.Millennium.LValOne
import Imscribing.Millennium.StarkGaussSum
import Imscribing.Millennium.SIC_D2048_StarkCharacter
import Imscribing.Millennium.LFuncDerivZero
import Imscribing.Millennium.StarkCharFilter

/-!
# StarkRungOne: rung-1 specialization to the Stark character

Specializing the rung-1 core (`LFuncDerivZero.lfunction_deriv_zero_eq`) to the
Stark quadratic character `χ` of conductor 4190205:

* `qchar'_inv_self`: `χ⁻¹ = χ` (public re-proof; values `0, 1, −1`).
* `LFunction_const_mul`: constants pull out of the congruence L-function.
* `dft_qchar`: `𝓕 χ = τ(χ) · χ` (Fourier reindex + self-inverse + evenness).

Main results:
* `two_lprime_zero_eq_tau`: **2 · L′(0, χ) = τ(χ) · L(1, χ)**.
* `re_tau_mul_L_one_eq_log_sum`: **Re(τ(χ) · L(1, χ)) = −∑_j χ(j)·log(2·sin(π·j/con))**.
-/

open Complex Real Filter Finset Topology
open ZMod HurwitzZeta
open scoped LSeries
open Imscribing.Millennium.StarkCharacterD2048
open Imscribing.Millennium.StarkGaussSum
open StarkCharFilter StarkLogRung

noncomputable section

namespace Imscribing.Millennium.StarkRungOne

/-- The Stark character is self-inverse (public version of the folded
`StarkGaussSum` helper): values `0, 1, −1` are all fixed by inversion. -/
theorem qchar'_inv_self (x : ZMod con) : MulChar.inv qchar' x = qchar' x := by
  have h : MulChar.inv qchar' x = (qchar' x)⁻¹ := MulChar.inv_apply_eq_inv' qchar' x
  rw [h]
  rcases qchar'_isQuadratic x with h' | h' | h'
  · rw [h']; norm_num
  · rw [h', inv_one]
  · rw [h']; norm_num

/-- Linearity: constants pull out of the congruence L-function (immediate from
its Hurwitz-zeta finite-sum definition). -/
theorem LFunction_const_mul {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (c : ℂ) (s : ℂ) :
    ZMod.LFunction (fun j => c * Φ j) s = c * ZMod.LFunction Φ s := by
  have hterm : ∀ j : ZMod N, c * Φ j * hurwitzZeta (toAddCircle j) s
      = c * (Φ j * hurwitzZeta (toAddCircle j) s) := fun j => by ring
  have hsum : ∑ j : ZMod N, c * Φ j * hurwitzZeta (toAddCircle j) s
      = c * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s := by
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j, ← Finset.mul_sum]
  simp only [LFunction]
  rw [hsum]
  ring

/-- The Fourier transform of the Stark character is the Gauss sum times the
character itself: `𝓕 χ k = τ(χ) · χ k`. -/
theorem dft_qchar (k : ZMod con) :
    ZMod.dft qchar k = gaussSum qchar' stdAddChar * qchar k := by
  rw [qchar_fourierReindex k, qchar'_inv_self, qchar_apply, qchar_even k, mul_comm]

/-- **Rung 1, Stark specialization.** `2 · L′(0, χ) = τ(χ) · L(1, χ)` for the
Stark quadratic character of conductor 4190205. -/
theorem two_lprime_zero_eq_tau :
    2 * deriv (ZMod.LFunction qchar) 0
      = gaussSum qchar' stdAddChar * ZMod.LFunction qchar 1 := by
  have hcore := LFuncDerivZero.lfunction_deriv_zero_eq qchar_even qchar_zero
    sum_qchar_eq_zero
  rw [hcore]
  have hdft : ZMod.dft qchar = fun k => gaussSum qchar' stdAddChar * qchar k :=
    funext dft_qchar
  rw [hdft, LFunction_const_mul]

/-! ## The real-part match -/

/-- The Stark character as a real-valued function (the input shape of the
character filter). -/
def qcharR (j : ZMod con) : ℝ := ((jacobiSym (j.val : ℤ) con : ℤ) : ℝ)

/-- The `ℂ`-valued and `ℝ`-valued forms of the Stark character agree after
coercion. -/
theorem coe_qcharR (j : ZMod con) : ((qcharR j : ℝ) : ℂ) = qchar j := by
  simp only [qcharR, qchar, Complex.ofReal_intCast]

theorem qcharR_zero : qcharR 0 = 0 := by
  simp only [qcharR, ZMod.val_zero]
  push_cast
  exact_mod_cast jacobiSym.zero_left con_one_lt

/-- Per-term bridge: the filtered summand in `Upartial` form is the divided
twisted term. -/
theorem tau_term (n : ℕ) :
    gaussSum qchar' stdAddChar * ((LValOne.dcoef 1 n : ℝ) • LValOne.zseq qchar n)
      = gaussSum qchar' stdAddChar
          * (qchar ((n + 1 : ℕ) : ZMod con) / (n + 1 : ℂ)) := by
  have hz : LValOne.zseq qchar n = qchar ((n + 1 : ℕ) : ZMod con) := by
    show qchar ((n : ZMod con) + 1) = _
    rw [Nat.cast_add, Nat.cast_one]
  have hdc : LValOne.dcoef 1 n = 1 / ((n : ℝ) + 1) := by
    show ((n : ℝ) + 1) ^ (-(1 : ℝ)) = 1 / ((n : ℝ) + 1)
    rw [Real.rpow_neg_one, inv_eq_one_div]
  have hcoe : (((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) = ((n + 1 : ℕ) : ℂ)⁻¹ := by
    rw [← inv_eq_one_div, Complex.ofReal_inv,
      ← Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one]
  have hsm : (LValOne.dcoef 1 n : ℝ) • LValOne.zseq qchar n
      = qchar ((n + 1 : ℕ) : ZMod con) / (n + 1 : ℂ) := by
    rw [hz, Complex.real_smul, hdc, hcoe, div_eq_inv_mul, Nat.cast_add, Nat.cast_one]
  rw [hsm]

/-- The twisted sum at level `m + 1` is the Gauss sum times the character. -/
theorem twisted_qcharR (m : ℕ) :
    ∑ j : ZMod con, ((qcharR j : ℝ) : ℂ) * (rootExp j.val con) ^ (m + 1)
      = gaussSum qchar' stdAddChar * qchar ((m + 1 : ℕ) : ZMod con) := by
  have hstep : ∀ j : ZMod con,
      stdAddChar (N := con) (-(j * (-((m + 1 : ℕ) : ZMod con)))) • qchar j
        = ((qcharR j : ℝ) : ℂ) * (rootExp j.val con) ^ (m + 1) := by
    intro j
    rw [mul_neg, neg_neg, smul_eq_mul,
      show (j * ((m + 1 : ℕ) : ZMod con) : ZMod con) = (m + 1 : ℕ) • j from by
        rw [nsmul_eq_mul, mul_comm],
      AddChar.map_nsmul_eq_pow, stdAddChar_eq_rootExp, coe_qcharR, mul_comm]
  calc ∑ j : ZMod con, ((qcharR j : ℝ) : ℂ) * (rootExp j.val con) ^ (m + 1)
      = ∑ j : ZMod con,
          stdAddChar (N := con) (-(j * (-((m + 1 : ℕ) : ZMod con)))) • qchar j :=
        Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => (hstep j).symm
    _ = ZMod.dft qchar (-((m + 1 : ℕ) : ZMod con)) := (ZMod.dft_apply qchar _).symm
    _ = gaussSum qchar' stdAddChar * qchar (-((m + 1 : ℕ) : ZMod con)) := dft_qchar _
    _ = gaussSum qchar' stdAddChar * qchar ((m + 1 : ℕ) : ZMod con) := by
        rw [qchar_even ((m + 1 : ℕ) : ZMod con)]

/-- **Rung 1, real-part match.** The real part of `τ(χ) · L(1, χ)` is exactly
the Stark-log summand series `−∑_j χ(j)·log(2·sin(π·j/con))`. -/
theorem re_tau_mul_L_one_eq_log_sum :
    reCLM (gaussSum qchar' stdAddChar * ZMod.LFunction qchar 1)
      = ∑ j : ZMod con, qcharR j
          * -(Real.log (2 * Real.sin (Real.pi * (j.val : ℝ) / (con : ℝ)))) := by
  have hUP : Tendsto (LValOne.Upartial qchar 1) atTop
      (𝓝 (ZMod.LFunction qchar 1)) := by
    have h := LValOne.Slim_spec qchar sum_qchar_eq_zero 1 le_rfl
    rwa [← LValOne.lFunction_one_eq qchar sum_qchar_eq_zero] at h
  have hmul : Continuous fun x : ℂ => gaussSum qchar' stdAddChar * x :=
    continuous_const.mul continuous_id
  have hre : ContinuousAt (fun x : ℂ => reCLM (gaussSum qchar' stdAddChar * x))
      (ZMod.LFunction qchar 1) := (reCLM.continuous.comp hmul).continuousAt
  have hlim : Tendsto (fun K : ℕ => reCLM (gaussSum qchar' stdAddChar
      * LValOne.Upartial qchar 1 K))
      atTop (𝓝 (reCLM (gaussSum qchar' stdAddChar * ZMod.LFunction qchar 1))) :=
    hre.tendsto.comp hUP
  have hev : (fun K : ℕ => reCLM (gaussSum qchar' stdAddChar
        * LValOne.Upartial qchar 1 K))
      =ᶠ[atTop] (fun K : ℕ => reCLM (∑ j ∈ Finset.univ, ((qcharR j : ℝ) : ℂ) *
        (∑ n ∈ Finset.range K, (rootExp j.val con) ^ (n + 1) / (n + 1 : ℂ)))) := by
    refine Filter.Eventually.of_forall fun K => ?_
    dsimp only
    rw [twistedSumForm qcharR K]
    have hnum : ∀ n ∈ Finset.range K,
        (∑ j ∈ Finset.univ, ((qcharR j : ℝ) : ℂ) * (rootExp j.val con) ^ (n + 1))
          / (n + 1 : ℂ)
        = gaussSum qchar' stdAddChar
            * (qchar ((n + 1 : ℕ) : ZMod con) / (n + 1 : ℂ)) := by
      intro n _
      rw [twisted_qcharR n, ← mul_div_assoc']
    have hrev : ∑ n ∈ Finset.range K, gaussSum qchar' stdAddChar
          * (qchar ((n + 1 : ℕ) : ZMod con) / (n + 1 : ℂ))
        = gaussSum qchar' stdAddChar
            * ∑ n ∈ Finset.range K, (LValOne.dcoef 1 n : ℝ) • LValOne.zseq qchar n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n (_ : n ∈ Finset.range K) => (tau_term n).symm
    rw [Finset.sum_congr rfl hnum, hrev]
    rfl
  have hgoal : Tendsto (fun K : ℕ => reCLM (∑ j ∈ Finset.univ, ((qcharR j : ℝ) : ℂ) *
      (∑ n ∈ Finset.range K, (rootExp j.val con) ^ (n + 1) / (n + 1 : ℂ))))
      atTop (𝓝 (reCLM (gaussSum qchar' stdAddChar * ZMod.LFunction qchar 1))) :=
    hlim.congr' hev
  exact tendsto_nhds_unique hgoal (charFilterRealLimit con_pos qcharR qcharR_zero)

end Imscribing.Millennium.StarkRungOne

end
