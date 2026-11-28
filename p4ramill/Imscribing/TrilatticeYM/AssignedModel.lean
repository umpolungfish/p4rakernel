import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Imscribing.TrilatticeYM


noncomputable def d4Scalar : ℝ := 2
noncomputable def d4Traceless : ℝ := 27 / 26

noncomputable def assignedLambda0 : ℝ := (1 / 1024 : ℝ) * d4Scalar ^ 2
noncomputable def assignedLambda1 : ℝ := (1 / 1024 : ℝ) * d4Traceless ^ 2
noncomputable def assignedRatio : ℝ := 729 / 2704

theorem assigned_eigenvalues_exact :
    assignedLambda0 = 1 / 256 ∧
    assignedLambda1 = 729 / 692224 ∧
    assignedLambda1 / assignedLambda0 = assignedRatio ∧
    assignedRatio = (27 / 52 : ℝ) ^ 2 := by
  unfold assignedLambda0 assignedLambda1 assignedRatio d4Scalar d4Traceless
  norm_num

theorem assigned_gap_pos {ℓ_star : ℝ} (hℓ : 0 < ℓ_star) :
    0 < (2 * Real.log (52 / 27)) / ℓ_star ∧
    Real.exp (-((2 * Real.log (52 / 27)) / ℓ_star) * ℓ_star) = assignedRatio := by
  have hlog : 0 < Real.log (52 / 27) := Real.log_pos (by norm_num)
  refine ⟨by positivity, ?_⟩
  have hℓ0 : ℓ_star ≠ 0 := ne_of_gt hℓ
  have heq : -((2 * Real.log (52 / 27)) / ℓ_star) * ℓ_star = -(2 * Real.log (52 / 27)) := by
    field_simp [hℓ0]
  rw [heq, Real.exp_neg, show (2 * Real.log (52 / 27)) = Real.log ((52 / 27 : ℝ) ^ 2) by
    rw [Real.log_pow]; norm_num]
  rw [Real.exp_log (by norm_num)]
  unfold assignedRatio
  norm_num

noncomputable def phiTransverse : ℝ := Real.arccos (Real.sqrt (5 / 14))

theorem sin_phiTransverse : Real.sin phiTransverse = 3 / Real.sqrt 14 := by
  unfold phiTransverse
  rw [Real.sin_arccos, Real.sq_sqrt (by norm_num)]
  have h1 : (1 - 5 / 14 : ℝ) = 9 / 14 := by norm_num
  rw [h1, Real.sqrt_div (by norm_num), show Real.sqrt 9 = 3 by norm_num]

theorem cos_phiTransverse : Real.cos phiTransverse = Real.sqrt (5 / 14) := by
  unfold phiTransverse
  exact Real.cos_arccos (by linarith [Real.sqrt_nonneg (5 / 14)])
    (by rw [Real.sqrt_le_one]; norm_num)

noncomputable def tMult (d : ℕ) : ℝ :=
  Real.sin ((d : ℝ) * phiTransverse) / ((d : ℝ) * Real.sin phiTransverse)

theorem tMult_one : tMult 1 = 1 := by
  unfold tMult
  have hsin : Real.sin phiTransverse ≠ 0 := by rw [sin_phiTransverse]; positivity
  simp [hsin]

theorem tMult_two_abs : |tMult 2| = Real.sqrt (5 / 14) := by
  unfold tMult
  have hsin : Real.sin phiTransverse ≠ 0 := by rw [sin_phiTransverse]; positivity
  have h2 : Real.sin ((2 : ℝ) * phiTransverse) =
      2 * Real.sin phiTransverse * Real.cos phiTransverse := Real.sin_two_mul phiTransverse
  rw [Nat.cast_ofNat, h2]
  have hdiv : 2 * Real.sin phiTransverse * Real.cos phiTransverse /
      (2 * Real.sin phiTransverse) = Real.cos phiTransverse := by
    field_simp [hsin]
  rw [hdiv, cos_phiTransverse, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem tMult_all_spin_bound (d : ℕ) (hd : 2 ≤ d) :
    |tMult d| ≤ Real.sqrt (5 / 14) := by
  rcases eq_or_lt_of_le hd with rfl | hge3
  · exact le_of_eq tMult_two_abs
  · have hd3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hge3
    have hsin : Real.sin phiTransverse = 3 / Real.sqrt 14 := sin_phiTransverse
    have hdenom_pos : 0 < (d : ℝ) * Real.sin phiTransverse := by rw [hsin]; positivity
    have h1 : |tMult d| ≤ 1 / ((d : ℝ) * Real.sin phiTransverse) := by
      unfold tMult
      rw [abs_div, abs_of_pos hdenom_pos]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (le_of_lt hdenom_pos)
    have h2 : 1 / ((d : ℝ) * Real.sin phiTransverse) ≤ Real.sqrt 14 / 9 := by
      rw [hsin]
      have hge9 : 9 / Real.sqrt 14 ≤ (d : ℝ) * (3 / Real.sqrt 14) := by
        have hpos : 0 ≤ 3 / Real.sqrt 14 := by positivity
        calc 9 / Real.sqrt 14 = 3 * (3 / Real.sqrt 14) := by ring
          _ ≤ (d : ℝ) * (3 / Real.sqrt 14) := mul_le_mul_of_nonneg_right hd3 hpos
      have hle := one_div_le_one_div_of_le (by positivity) hge9
      calc 1 / ((d : ℝ) * (3 / Real.sqrt 14))
          ≤ 1 / (9 / Real.sqrt 14) := hle
        _ = Real.sqrt 14 / 9 := by rw [one_div_div]
    have h3 : Real.sqrt 14 / 9 ≤ Real.sqrt (5 / 14) := by
      have hsq : (Real.sqrt 14 / 9) ^ 2 ≤ (Real.sqrt (5 / 14)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
        norm_num
      nlinarith [Real.sqrt_nonneg 14, Real.sqrt_nonneg (5 / 14)]
    exact le_trans h1 (le_trans h2 h3)

theorem girth4_flux_bound (d₁ d₂ d₃ d₄ : ℕ)
    (h1 : 2 ≤ d₁) (h2 : 2 ≤ d₂) (h3 : 2 ≤ d₃) (h4 : 2 ≤ d₄) :
    (tMult d₁) ^ 2 * (tMult d₂) ^ 2 * (tMult d₃) ^ 2 * (tMult d₄) ^ 2 ≤ 625 / 38416 ∧
    (625 / 38416 : ℝ) < assignedRatio := by
  have hb : ∀ d, 2 ≤ d → (tMult d) ^ 2 ≤ 5 / 14 := by
    intro d hd
    have ha := tMult_all_spin_bound d hd
    have hsq : |tMult d| ^ 2 ≤ (Real.sqrt (5 / 14)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) ha 2
    rw [sq_abs, Real.sq_sqrt (by norm_num)] at hsq
    exact hsq
  have h1' := hb d₁ h1
  have h2' := hb d₂ h2
  have h3' := hb d₃ h3
  have h4' := hb d₄ h4
  have hp2 : 0 ≤ (tMult d₂) ^ 2 := sq_nonneg _
  have hp3 : 0 ≤ (tMult d₃) ^ 2 := sq_nonneg _
  have hp4 : 0 ≤ (tMult d₄) ^ 2 := sq_nonneg _
  have hmul : (tMult d₁) ^ 2 * (tMult d₂) ^ 2 * (tMult d₃) ^ 2 * (tMult d₄) ^ 2 ≤
      (5 / 14 : ℝ) * (5 / 14) * (5 / 14) * (5 / 14) := by
    have h12 : (tMult d₁) ^ 2 * (tMult d₂) ^ 2 ≤ (5 / 14 : ℝ) * (5 / 14) :=
      mul_le_mul h1' h2' hp2 (by norm_num)
    have h123 : (tMult d₁) ^ 2 * (tMult d₂) ^ 2 * (tMult d₃) ^ 2 ≤
        (5 / 14 : ℝ) * (5 / 14) * (5 / 14) :=
      mul_le_mul h12 h3' hp3 (by norm_num)
    exact mul_le_mul h123 h4' hp4 (by norm_num)
  refine ⟨le_trans hmul (by norm_num), ?_⟩
  unfold assignedRatio; norm_num

noncomputable def bessel1Term (n k : ℕ) : ℝ :=
  ((1 / 2 : ℝ) ^ (2 * k + n)) / ((Nat.factorial k : ℝ) * (Nat.factorial (k + n) : ℝ))

theorem bessel1Term_nonneg (n k : ℕ) : 0 ≤ bessel1Term n k := by
  unfold bessel1Term; positivity

theorem bessel_face_termwise_lt_assigned (k : ℕ) :
    bessel1Term 2 k ≤ (1 / 4 : ℝ) * bessel1Term 1 k ∧
    (1 / 4 : ℝ) < assignedRatio := by
  constructor
  · unfold bessel1Term
    have hk2 : Nat.factorial (k + 2) = (k + 2) * Nat.factorial (k + 1) :=
      Nat.factorial_succ (k + 1)
    have hpow : (1 / 2 : ℝ) ^ (2 * k + 2) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (2 * k + 1) := by
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, pow_succ']
    rw [hk2, hpow]
    push_cast
    have hdiv :
        ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (2 * k + 1)) /
          ((Nat.factorial k : ℝ) * (((k : ℝ) + 2) * (Nat.factorial (k + 1) : ℝ))) =
        (1 / (2 * ((k : ℝ) + 2))) * ((1 / 2 : ℝ) ^ (2 * k + 1) /
          ((Nat.factorial k : ℝ) * (Nat.factorial (k + 1) : ℝ))) := by
      have hk0 : (Nat.factorial k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have hk1 : (Nat.factorial (k + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))
      have hk2ne : (k : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hk0, hk1, hk2ne]
    rw [hdiv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [one_div_le (by positivity) (by norm_num)]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  · unfold assignedRatio; norm_num

theorem assigned_sector_dominance (b_F b_L : ℝ)
    (hbF : b_F ≤ 1 / 4) (hbL : b_L ≤ 625 / 38416) :
    max assignedRatio (max b_F b_L) = assignedRatio := by
  have h1 : b_F ≤ assignedRatio := le_trans hbF (by unfold assignedRatio; norm_num)
  have h2 : b_L ≤ assignedRatio := le_trans hbL (by unfold assignedRatio; norm_num)
  simp [max_eq_left, h1, h2]

end Imscribing.TrilatticeYM
