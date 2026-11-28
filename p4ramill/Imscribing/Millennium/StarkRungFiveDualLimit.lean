import Imscribing.Millennium.StarkRungFiveDual
import Imscribing.Millennium.StarkRungFiveTheta

set_option maxHeartbeats 1000000

open Complex Real Filter Topology
open scoped Complex Real Topology
open Imscribing.Millennium.StarkCharacterD2048
open Imscribing.Millennium.StarkAsympt
open Imscribing.Millennium.StarkDual
open Imscribing.Millennium.StarkTheta

noncomputable section

namespace Imscribing.Millennium.StarkDualLimit

theorem norm_exp_I_sub_one (θ : ℝ) : ‖cexp (I * (θ : ℂ)) - 1‖ ≤ |θ| := by
  have h₁ : ‖cexp (I * (θ : ℂ)) - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    calc
      ‖cexp (I * (θ : ℂ)) - 1‖ ^ 2 = Complex.normSq (cexp (I * (θ : ℂ)) - 1) := by rw [Complex.normSq_eq_norm_sq]
      _ = (cexp (I * (θ : ℂ)) - 1).re ^ 2 + (cexp (I * (θ : ℂ)) - 1).im ^ 2 := by
        simp [Complex.normSq, Complex.ext_iff, Complex.add_re, Complex.add_im]
        <;> ring_nf
      _ = (Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2 := by
        have h₂ : (cexp (I * (θ : ℂ))).re = Real.cos θ := by simp [Complex.exp_re, Complex.mul_re, Complex.I_re, Complex.I_im]
        have h₃ : (cexp (I * (θ : ℂ))).im = Real.sin θ := by simp [Complex.exp_im, Complex.mul_re, Complex.I_re, Complex.I_im]
        simp [Complex.sub_re, Complex.sub_im, h₂, h₃]
        <;> ring_nf
      _ = Real.cos θ ^ 2 - 2 * Real.cos θ + 1 + Real.sin θ ^ 2 := by ring_nf
      _ = 1 - 2 * Real.cos θ + 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
      _ = 2 - 2 * Real.cos θ := by ring_nf
      _ = 4 * Real.sin (θ / 2) ^ 2 := by
        have h₄ : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
          nlinarith [Real.cos_two_mul (θ / 2), Real.sin_sq_add_cos_sq (θ / 2)]
        rw [h₄]
        ring_nf
        <;> nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have h₂ : ‖cexp (I * (θ : ℂ)) - 1‖ ^ 2 ≤ θ ^ 2 := by
    have h₃ : ‖cexp (I * (θ : ℂ)) - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := h₁
    rw [h₃]
    have h₄ : Real.sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := by
      have h₅ : |Real.sin (θ / 2)| ≤ |θ / 2| := abs_sin_le _ _
      calc
        Real.sin (θ / 2) ^ 2 = |Real.sin (θ / 2)| ^ 2 := by rw [sq_abs]
        _ ≤ |θ / 2| ^ 2 := by gcongr
        _ = (θ / 2) ^ 2 := by simp [abs_mul_abs_self]
    nlinarith
  have h₃ : ‖cexp (I * (θ : ℂ)) - 1‖ ≤ |θ| := by
    have h₄ : ‖cexp (I * (θ : ℂ)) - 1‖ ≥ 0 := by positivity
    have h₅ : ‖cexp (I * (θ : ℂ)) - 1‖ ^ 2 ≤ θ ^ 2 := h₂
    have h₆ : |θ| ≥ 0 := abs_nonneg θ
    nlinarith [sq_nonneg (‖cexp (I * (θ : ℂ)) - 1‖ - |θ|)]
  exact h₃

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

theorem re_dualParam (t : ℝ) : (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)).re
    = (con : ℝ) * t / (t ^ 2 + 4) := by
  rw [dualParam_eq t]
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  <;> norm_num

theorem im_dualParam (t : ℝ) : (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)).im
    = (con : ℝ) * 2 / (t ^ 2 + 4) := by
  rw [dualParam_eq t]
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add, add_zero]
  <;> norm_num

noncomputable def dualTerm (t : ℝ) (n : ℤ) : ℂ :=
  cexp (-(↑π) * (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)) * ((n : ℂ) ^ 2))

noncomputable def dualTheta (t : ℝ) : ℂ := ∑' n : ℤ, dualTerm t n

noncomputable def dualEven (t : ℝ) : ℂ :=
  2 * (∑' n : ℕ, dualTerm t ((2 * n : ℕ) : ℤ)) - 1

noncomputable def dualOdd (t : ℝ) : ℂ :=
  2 * (∑' n : ℕ, dualTerm t ((2 * n + 1 : ℕ) : ℤ))

theorem dualTerm_norm (t : ℝ) (ht : 0 < t) (n : ℤ) :
    ‖dualTerm t n‖ = rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2) := by
  have h₁ : dualTerm t n = cexp (-(↑π) * (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)) * ((n : ℂ) ^ 2)) := rfl
  rw [h₁]
  have h₂ : ((n : ℤ) : ℂ) ^ 2 = Complex.ofReal (((n : ℤ) : ℝ) ^ 2) := by
    rw [ofReal_intCast, ← Complex.ofReal_pow]
  rw [h₂]
  have h₃ : ‖cexp (-(↑π) * (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)) * Complex.ofReal (((n : ℤ) : ℝ) ^ 2))‖ =
      rexp (-(↑π) * (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)) * Complex.ofReal (((n : ℤ) : ℝ) ^ 2)).re := by
    rw [Complex.norm_exp]
    <;> simp [Complex.exp_re]
    <;> ring_nf
    <;> field_simp [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    <;> ring_nf
  rw [h₃]
  have h₄ : (-(↑π) * (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)) * Complex.ofReal (((n : ℤ) : ℝ) ^ 2)).re =
      -π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2 := by
    have h₅ : (((t : ℂ) - 2 * I) : ℂ) ≠ 0 := by
      intro h
      simp [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at h
      norm_num at h ⊢
      <;>
      (try
        {
          cases' le_or_gt 0 t with h₆ h₆ <;> simp_all [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
          <;> field_simp [h₆] at h ⊢ <;> norm_num at h ⊢ <;> linarith
        })
    have h₆ : (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)) = (con : ℂ) / ((t : ℂ) - 2 * I) := by
      simp [Complex.ofReal_eq_coe]
      <;> ring_nf
    rw [h₆]
    have h₇ : (-↑π * ((con : ℂ) / ((t : ℂ) - 2 * I)) * Complex.ofReal (((n : ℤ) : ℝ) ^ 2)).re =
        -π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2 := by
      calc
        (-↑π * ((con : ℂ) / ((t : ℂ) - 2 * I)) * Complex.ofReal (((n : ℤ) : ℝ) ^ 2)).re
          = (-↑π : ℝ) * (((con : ℂ) / ((t : ℂ) - 2 * I)) * Complex.ofReal (((n : ℤ) : ℝ) ^ 2)).re := by
            simp [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_re]
            <;> ring_nf
            <;> norm_cast
          _ = (-↑π : ℝ) * (((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2) := by
            have h₈ : (((con : ℂ) / ((t : ℂ) - 2 * I)) * Complex.ofReal (((n : ℤ) : ℝ) ^ 2)).re =
                ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2 := by
              have h₉ : re_dualParam t := by rw [dualParam_eq t]; simp
              have h₁₀ : im_dualParam t := by rw [dualParam_eq t]; simp
              simp [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
                Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h₉ h₁₀ ⊢
              <;>
              (try
                {
                  field_simp [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
                  <;> ring_nf
                  <;> norm_num
                })
              <;>
              (try
                {
                  norm_num [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
                })
              <;>
              (try
                {
                  linarith
                })
            rw [h₈]
            ring_nf
            <;> norm_cast
          _ = -π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2 := by ring_nf
    rw [h₇]
    <;> ring_nf
  rw [h₄]
  <;> norm_num [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  <;> linarith [Real.sqrt_nonneg 0, Real.sq_nonneg (con : ℝ)]

theorem summable_dualTerm (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℤ => dualTerm t n) := by
  refine Summable.of_norm ?_
  have h₁ : ∀ n : ℤ, ‖dualTerm t n‖ = rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2) := by
    intro n
    exact dualTerm_norm t ht n
  have h₂ : Summable (fun n : ℤ => rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℤ) : ℝ) ^ 2)) := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · have h₃ : Summable (fun n : ℕ => rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)) := by
        have h₄ : 0 < (con : ℝ) * t / (t ^ 2 + 4) := by
          exact div_pos (Nat.cast_pos.mpr con_pos) (by positivity)
        have h₅ : Summable (fun n : ℕ => rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ))) := by
          have h₆ : ∀ n : ℕ, rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ)) = (rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4))) : ℝ) ^ n := by
            intro n
            calc
              rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ)) = rexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))) * n) := by
                ring_nf
                <;> norm_cast
                <;> simp [nsmul_eq_mul]
                <;> ring_nf
              _ = (rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4))) : ℝ) ^ n := by
                rw [show (-π * ((con : ℝ) * t / (t ^ 2 + 4)) : ℝ) * n = (-π * ((con : ℝ) * t / (t ^ 2 + 4))) * n := rfl]
                <;> simp [Real.exp_rpow]
                <;> ring_nf
          rw [h₆]
          have h₇ : (rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4))) : ℝ) < 1 := by
            have h₈ : -π * ((con : ℝ) * t / (t ^ 2 + 4)) < 0 := by neg_pos
            have h₉ : rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4))) < 1 := by
              rw [Real.exp_lt_one (by neg_pos)]
            exact h₉
          exact Summable.geometric h₇
        have h₆ : ∀ n : ℕ, rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) ≤ rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ)) := by
          intro n
          have h₇ : 0 ≤ (n : ℝ) := by positivity
          have h₈ : (n : ℝ) ^ 2 ≥ (n : ℝ) := by
            cases n with
            | zero => norm_num
            | succ n =>
              cases n with
              | zero => norm_num
              | succ n =>
                simp [Nat.succ_eq_add_one, pow_two, mul_add, add_mul, mul_one, mul_comm, mul_left_comm, mul_assoc]
                <;> nlinarith [sq_nonneg (n : ℝ)]
          have h₉ : -π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2 ≤ -π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) := by
            have h₁₀ : 0 < π * ((con : ℝ) * t / (t ^ 2 + 4)) := by positivity
            have h₁₁ : 0 ≤ (n : ℝ) ^ 2 - (n : ℝ) := by nlinarith
            nlinarith
          have h₁₀ : rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2) ≤ rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ)) := by
            apply Real.exp_le_exp.2
            linarith
          exact h₁₀
        have h₇ : Summable (fun n : ℕ => rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n : ℕ) : ℝ) ^ 2)) := by
          refine Summable.of_le_of_summlable (fun n _ => by rfl) h₅
          intro n _
          exact h₆ n
        exact h₇
      exact h₃
    · have h₃ : Summable (fun n : ℕ => rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((-(n + 1 : ℕ) : ℤ) : ℝ) ^ 2))) := by
        have h₄ : (fun n : ℕ => rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * (((-(n + 1 : ℕ) : ℤ) : ℝ) ^ 2))) =
            (fun n : ℕ => rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
          funext n
          norm_cast
          <;>
          (try
            {
              cases n with
              | zero => norm_num
              | succ n =>
                simp [Nat.succ_eq_add_one, pow_two, mul_add, add_mul, mul_one, mul_comm, mul_left_comm, mul_assoc]
                <;> ring_nf
                <;> norm_cast
                <;> simp [Int.cast_sub, Int.cast_add, Int.cast_one, Int.cast_zero]
                <;> ring_nf
                <;> norm_num
            })
        rw [h₄]
        have h₅ : 0 < (con : ℝ) * t / (t ^ 2 + 4) := by
          exact div_pos (Nat.cast_pos.mpr con_pos) (by positivity)
        have h₆ : ∀ n : ℕ, rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ) ^ 2) ≤ rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ)) := by
          intro n
          have h₇ : 0 ≤ (n + 1 : ℝ) := by positivity
          have h₈ : (n + 1 : ℝ) ^ 2 ≥ (n + 1 : ℝ) := by
            nlinarith [sq_nonneg ((n + 1 : ℝ) - 1)]
          have h₉ : -π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ -π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ) := by
            have h₁₀ : 0 < π * ((con : ℝ) * t / (t ^ 2 + 4)) := by positivity
            have h₁₁ : 0 ≤ (n + 1 : ℝ) ^ 2 - (n + 1 : ℝ) := by nlinarith
            nlinarith
          have h₁₀ : rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ) ^ 2) ≤ rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ)) := by
            apply Real.exp_le_exp.2
            linarith
          exact h₁₀
        have h₇ : Summable (fun n : ℕ => rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ))) := by
          have h₈ : ∀ n : ℕ, rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ)) = (rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4))) : ℝ) ^ (n + 1) := by
            intro n
            calc
              rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ)) = rexp ((-π * ((con : ℝ) * t / (t ^ 2 + 4))) * (n + 1)) := by
                ring_nf
                <;> norm_cast
                <;> simp [nsmul_eq_mul]
                <;> ring_nf
              _ = (rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4))) : ℝ) ^ (n + 1) := by
                rw [show (-π * ((con : ℝ) * t / (t ^ 2 + 4)) : ℝ) * (n + 1) = (-π * ((con : ℝ) * t / (t ^ 2 + 4))) * (n + 1) := rfl]
                <;> simp [Real.exp_rpow]
                <;> ring_nf
          rw [h₈]
          have h₉ : (rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4))) : ℝ) < 1 := by
            have h₁₀ : -π * ((con : ℝ) * t / (t ^ 2 + 4)) < 0 := by neg_pos
            have h₁₁ : rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4))) < 1 := by
              rw [Real.exp_lt_one (by neg_pos)]
            exact h₁₁
          exact Summable.geometric h₉
        have h₈ : Summable (fun n : ℕ => rexp (-π * ((con : ℝ) * t / (t ^ 2 + 4)) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
          refine Summable.of_le_of_summlable (fun n _ => by rfl) h₇
          intro n _
          exact h₆ n
        exact h₈
      exact h₃
  exact h₂

theorem dualTerm_even (t : ℝ) : ∀ k : ℤ, dualTerm t (-k) = dualTerm t k := by
  intro k
  have h₁ : dualTerm t (-k) = cexp (-(↑π) * (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)) * (((-k : ℤ) : ℂ) ^ 2)) := rfl
  have h₂ : dualTerm t k = cexp (-(↑π) * (Complex.ofReal (con : ℝ) / ((t : ℂ) - 2 * I)) * (((k : ℤ) : ℂ) ^ 2)) := rfl
  rw [h₁, h₂]
  have h₃ : (((-k : ℤ) : ℂ) ^ 2 : ℂ) = (((k : ℤ) : ℂ) ^ 2 : ℂ) := by
    norm_cast
    <;>
    (try
      {
        simp [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        <;> ring_nf
        <;> norm_num
      })
  rw [h₃]
  <;>
  (try
    {
      simp [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      <;> ring_nf
      <;> norm_num
    })

theorem dualTheta_split (t : ℝ) (ht : 0 < t) : dualTheta t = dualEven t + dualOdd t := by
  have hg := summable_dualTerm t ht
  have h0 : dualTerm t 0 = 1 := by simp [dualTerm]
  have h := tsum_int_even_odd (fun n : ℤ => dualTerm t n) hg (dualTerm_even t)
  simp only [dualTheta, dualEven, dualOdd]
  rw [h]
  simp only [h0]
  ring

end Imscribing.Millennium.StarkDualLimit
