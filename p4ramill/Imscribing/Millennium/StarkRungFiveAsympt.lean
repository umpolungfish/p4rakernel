import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Imscribing.Millennium.StarkRungFiveTheta

/-!
# StarkRungFiveAsympt — real theta asymptotics bricks

The real-analysis bricks of the Landsberg–Schaar sign mechanism for the
quadratic Gauss sum of `con = 4190205`:

* `summable_gaussReal` : the discrete Gaussian `exp(-π·a·n²)` is summable
  over `ℤ` for `a > 0`;
* `thetaReal_poisson` : `s^(1/2) · ∑' exp(-π·s·n²) = ∑' exp(-π/s·n²)` (Poisson);
* `thetaAsympt_full` : `β^(1/2) · ∑'_n exp(-π·β·n²) → 1` as `β → 0⁺`.

These feed the dual-side limits (even/odd parts of the transformed chirp)
and the L-side Abel limit that fix the sign `τ = +√con`.
-/

open Real Filter
open scoped Real Topology

noncomputable section

namespace Imscribing.Millennium.StarkAsympt

/-! ## Gaussian series summability -/

/-- The discrete Gaussian over `ℕ` is summable: `exp(-π·a·n²) ≤ exp(-π·a)^n`
and the latter is geometric. -/
theorem summable_gaussNat (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => exp (-π * a * ((n : ℕ) : ℝ) ^ 2)) := by
  have hgeo : Summable (fun n : ℕ => exp (-π * a) ^ (n : ℕ)) := by
    refine summable_geometric_of_lt_one (by positivity) ?_
    simpa using exp_lt_exp.mpr (show -π * a < 0 by nlinarith [Real.pi_pos])
  refine Summable.of_nonneg_of_le (fun n => exp_nonneg _) (fun n => ?_) hgeo
  have hsq : ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) ≥ ((n : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact_mod_cast Nat.le_mul_of_pos_right n h
  have hmono : -π * a * ((n : ℕ) : ℝ) ^ 2 ≤ -π * a * ((n : ℕ) : ℝ) := by
    have hneg : -π * a ≤ 0 := by nlinarith [Real.pi_pos, ha]
    have hflip := mul_le_mul_of_nonpos_right hsq hneg
    nlinarith [Real.pi_pos, ha, hflip]
  calc exp (-π * a * ((n : ℕ) : ℝ) ^ 2)
      ≤ exp (-π * a * ((n : ℕ) : ℝ)) := exp_le_exp.mpr hmono
    _ = exp (-π * a) ^ (n : ℕ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- The discrete Gaussian `exp(-π·a·n²)` is summable over `ℤ` for `a > 0`. -/
theorem summable_gaussReal (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℤ => exp (-π * a * ((n : ℤ) : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine Summable.congr (summable_gaussNat a ha) (fun n => ?_)
    push_cast
    ring
  · refine Summable.congr (summable_gaussNat a ha) (fun n => ?_)
    push_cast
    ring_nf

/-! ## The real theta function -/

/-- Poisson at the real parameter: `s^(1/2) · ∑' exp(-π·s·n²) = ∑' exp(-π/s·n²)`. -/
theorem thetaReal_poisson (s : ℝ) (hs : 0 < s) :
    (s ^ ((1:ℝ)/2)) * ∑' n : ℤ, exp (-π * s * ((n : ℤ) : ℝ) ^ 2)
      = ∑' n : ℤ, exp (-π / s * ((n : ℝ) ^ 2)) := by
  have h := Real.tsum_exp_neg_mul_int_sq hs
  have hne : s ^ ((1:ℝ)/2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hs _)
  have h4 : s ^ ((1:ℝ)/2) * (1 / s ^ ((1:ℝ)/2)) = 1 := by
    field_simp
  rw [h, ← mul_assoc, h4, one_mul]

/-! ## Brick R1a: the full-line theta asymptotics -/

/-- **Brick R1a.** `β^(1/2) · ∑'_n exp(-π·β·n²) → 1` as `β → 0⁺`. -/
theorem thetaAsympt_full :
    Tendsto (fun β : ℝ => (β ^ ((1:ℝ)/2)) * ∑' n : ℤ, exp (-π * β * ((n : ℤ) : ℝ) ^ 2))
      (𝓝[>] 0) (𝓝 1) := by
  have hpois : ∀ β : ℝ, 0 < β →
      (β ^ ((1:ℝ)/2)) * ∑' n : ℤ, exp (-π * β * ((n : ℤ) : ℝ) ^ 2)
        = ∑' n : ℤ, exp (-π / β * ((n : ℝ) ^ 2)) :=
    fun β hβ => thetaReal_poisson β hβ
  have hDCT : Tendsto (fun β : ℝ => ∑' n : ℤ, exp (-π / β * ((n : ℝ) ^ 2)))
      (𝓝[>] 0) (𝓝 (∑' n : ℤ, (if n = 0 then (1 : ℝ) else 0))) := by
    refine tendsto_tsum_of_dominated_convergence
      (summable_gaussReal 1 (by norm_num)) (fun k => ?_) ?_
    · by_cases hk : k = 0
      · rw [hk]
        simp
      · simp only [hk, if_neg hk]
        have hk2 : (0:ℝ) < (k:ℝ) ^ 2 := by
          have hne : (k:ℝ) ≠ 0 := by exact_mod_cast hk
          exact sq_pos_iff.mpr hne
        have hpc : (0:ℝ) < π * ((k:ℝ) ^ 2) := by nlinarith [Real.pi_pos, hk2]
        have htop : Tendsto (fun β : ℝ => (π * ((k:ℝ) ^ 2)) * β⁻¹) (𝓝[>] 0) atTop :=
          Tendsto.const_mul_atTop hpc tendsto_inv_nhdsGT_zero
        have hcomp : Tendsto (fun β : ℝ => exp (-((π * ((k:ℝ) ^ 2)) * β⁻¹)))
            (𝓝[>] 0) (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
        have hfeq : (fun β : ℝ => exp (-π / β * ((k:ℝ) ^ 2)))
            = (fun β : ℝ => exp (-((π * ((k:ℝ) ^ 2)) * β⁻¹))) := by
          funext β
          congr 1
          ring
        rw [hfeq]
        exact hcomp
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with β hβ
      obtain ⟨hβ0, hβlt⟩ := hβ
      intro k
      rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
      have hβ1 : 1 ≤ 1 / β := by
        rw [le_div_iff₀ hβ0]
        linarith
      have hkey : π * ((k : ℝ) ^ 2) * 1 ≤ π * ((k : ℝ) ^ 2) * (1 / β) :=
        mul_le_mul_of_nonneg_left hβ1 (mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg _))
      have hmono : -π / β * ((k : ℝ) ^ 2) ≤ -π * 1 * ((k : ℤ) : ℝ) ^ 2 := by
        have e1 : -π / β * ((k : ℝ) ^ 2) = -(π * ((k : ℝ) ^ 2) * (1 / β)) := by ring
        have e2 : -π * 1 * ((k : ℤ) : ℝ) ^ 2 = -(π * ((k : ℝ) ^ 2) * 1) := by ring
        rw [e1, e2]
        exact neg_le_neg hkey
      exact exp_le_exp.mpr hmono
  have hsum : ∑' n : ℤ, (if n = 0 then (1 : ℝ) else 0) = 1 := by simp
  rw [hsum] at hDCT
  refine Tendsto.congr' ?_ hDCT
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with β hβ
  exact (hpois β hβ.1).symm

/-! ## ℕ-indexed Gaussian sums and the half-shift asymptotics -/

/-- Full-line Gaussian sum over `ℕ`. -/
def gaussSumNat (a : ℝ) : ℝ := ∑' n : ℕ, exp (-π * a * ((n : ℕ) : ℝ) ^ 2)

/-- Half-shift Gaussian sum over `ℕ`. -/
def gaussSumHalf (a : ℝ) : ℝ := ∑' n : ℕ, exp (-π * a * (((n : ℕ) : ℝ) + 1 / 2) ^ 2)

/-- Full-line Gaussian sum over `ℤ`. -/
def gaussSumInt (a : ℝ) : ℝ := ∑' n : ℤ, exp (-π * a * ((n : ℤ) : ℝ) ^ 2)

/-- The ℤ-line Gaussian sum is `1 + 2·(A(a) − 1)` where `A` is the ℕ-sum
(paired by `k ↔ -k`). -/
theorem gaussSumInt_eq (a : ℝ) (ha : 0 < a) :
    gaussSumInt a = 1 + 2 * (gaussSumNat a - 1) := by
  have heven : Function.Even (fun n : ℤ => exp (-π * a * ((n : ℤ) : ℝ) ^ 2)) := by
    intro n
    show exp (-π * a * ((-n : ℤ) : ℝ) ^ 2) = exp (-π * a * ((n : ℤ) : ℝ) ^ 2)
    have hsq : ((-n : ℤ) : ℝ) ^ 2 = ((n : ℤ) : ℝ) ^ 2 := by
      push_cast
      ring
    rw [hsq]
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat heven (summable_gaussReal a ha)
  simp only [] at h
  have h0 : exp (-π * a * ((0:ℤ) : ℝ) ^ 2) = 1 := by simp
  rw [h0] at h
  simp only [nsmul_eq_mul] at h
  have hp : ∑' n : ℕ+, (fun m : ℤ => exp (-π * a * ((m : ℤ) : ℝ) ^ 2)) ↑↑n
      = gaussSumNat a - 1 := by
    have hnat : ∑' n : ℕ+, (fun m : ℤ => exp (-π * a * ((m : ℤ) : ℝ) ^ 2)) ↑↑n
        = ∑' n : ℕ+, (fun k : ℕ => exp (-π * a * ((k : ℕ) : ℝ) ^ 2)) ↑n := by
      refine tsum_congr (fun n => ?_)
      push_cast
      ring
    rw [hnat, tsum_pnat_eq_tsum_succ (f := fun k : ℕ => exp (-π * a * ((k : ℕ) : ℝ) ^ 2))]
    have hz' : gaussSumNat a
        = 1 + ∑' n : ℕ, exp (-π * a * (((n + 1 : ℕ) : ℕ) : ℝ) ^ 2) := by
      have hz := (summable_gaussNat a ha).tsum_eq_zero_add
      have hzero : exp (-π * a * ((0:ℕ) : ℝ) ^ 2) = 1 := by simp
      rw [hzero] at hz
      exact hz
    linarith
  rw [hp] at h
  exact h

/-- **Brick R1a (ℕ version).** `a^(1/2) · ∑'_n e^{-π·a·n²} → 1/2` as `a → 0⁺`. -/
theorem gaussSumNat_asympt :
    Tendsto (fun a : ℝ => (a ^ ((1:ℝ)/2)) * gaussSumNat a) (𝓝[>] 0) (𝓝 (1/2)) := by
  have hsqrt0 : Tendsto (fun a : ℝ => (a ^ ((1:ℝ)/2))) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun a : ℝ => √a) (0:ℝ) := Real.continuous_sqrt.continuousAt
    have h1 : Tendsto (fun a : ℝ => √a) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa using hc.tendsto
    have h : Tendsto (fun a : ℝ => √a) (𝓝[>] 0) (𝓝 (0:ℝ)) :=
      h1.mono_left nhdsWithin_le_nhds
    refine Tendsto.congr' ?_ h
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with a _
    exact Real.sqrt_eq_rpow a
  have hmain : Tendsto
      (fun a : ℝ => (a ^ ((1:ℝ)/2)) * gaussSumInt a + (a ^ ((1:ℝ)/2))) (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun a : ℝ => (a ^ ((1:ℝ)/2)) * gaussSumInt a) (𝓝[>] 0) (𝓝 1) :=
      thetaAsympt_full
    simpa using h1.add hsqrt0
  have hcongr : ∀ᶠ a in 𝓝[>] (0:ℝ),
      ((a ^ ((1:ℝ)/2)) * gaussSumInt a + (a ^ ((1:ℝ)/2))) / 2
        = (a ^ ((1:ℝ)/2)) * gaussSumNat a := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with a ha
    have h := gaussSumInt_eq a ha.1
    rw [h]
    ring
  exact Tendsto.congr' hcongr (hmain.div_const 2)


set_option maxHeartbeats 800000 in
/-- The half-shift ℕ-sum is the difference of full-line ℕ-sums:
`H(b) = A(b/4) − A(b)` (even/odd split of the `b/4`-Gaussian). -/
theorem gaussSumHalf_eq (b : ℝ) (hb : 0 < b) :
    gaussSumHalf b = gaussSumNat (b/4) - gaussSumNat b := by
  have hkey : ∀ k : ℕ, ((k:ℕ):ℝ) ^ 2 / 4 ≤ (((k:ℕ):ℝ) + 1/2) ^ 2 := by
    intro k
    have hexp : (((k:ℕ):ℝ) + 1/2) ^ 2 = ((k:ℕ):ℝ) ^ 2 + ((k:ℕ):ℝ) + 1/4 := by ring
    rw [hexp]
    linarith [sq_nonneg ((k:ℕ):ℝ), Nat.cast_nonneg (α := ℝ) k]
  have hpa : (0:ℝ) < π * b := mul_pos Real.pi_pos hb
  have hOsumm : Summable (fun k : ℕ => exp (-π * b * (((k:ℕ):ℝ) + 1/2) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun k => exp_nonneg _) (fun k => ?_)
      (summable_gaussNat (b/4) (by linarith))
    refine exp_le_exp.mpr ?_
    have h2 : π * (b / 4) * ((k:ℕ):ℝ) ^ 2 = π * b * (((k:ℕ):ℝ) ^ 2 / 4) := by ring
    have h1 : π * b * (((k:ℕ):ℝ) ^ 2 / 4) ≤ π * b * (((k:ℕ):ℝ) + 1/2) ^ 2 :=
      mul_le_mul_of_nonneg_left (hkey k) hpa.le
    rw [← h2] at h1
    have e2 : -π * b * (((k:ℕ):ℝ) + 1/2) ^ 2 = -(π * b * (((k:ℕ):ℝ) + 1/2) ^ 2) := by ring
    have e3 : -π * (b / 4) * ((k:ℕ):ℝ) ^ 2 = -(π * (b / 4) * ((k:ℕ):ℝ) ^ 2) := by ring
    rw [e2, e3]
    exact neg_le_neg h1
  have fE : Summable (fun k : ℕ => exp (-π * (b/4) * ((2*k : ℕ) : ℝ) ^ 2)) := by
    refine Summable.congr (summable_gaussNat b hb) (fun k => ?_)
    have hc : ((2*k : ℕ) : ℝ) = ((k:ℕ):ℝ) * 2 := by push_cast; ring
    rw [hc]
    ring_nf
  have fO : Summable (fun k : ℕ => exp (-π * (b/4) * ((2*k+1 : ℕ) : ℝ) ^ 2)) := by
    refine Summable.congr hOsumm (fun k => ?_)
    have hc : ((2*k+1 : ℕ) : ℝ) = ((k:ℕ):ℝ) * 2 + 1 := by push_cast; ring
    rw [hc]
    ring_nf
  calc gaussSumHalf b = ∑' k : ℕ, exp (-π * b * (((k:ℕ):ℝ) + 1/2) ^ 2) := rfl
    _ = ∑' k : ℕ, exp (-π * (b/4) * ((2*k+1 : ℕ) : ℝ) ^ 2) := by
        refine tsum_congr (fun k => ?_)
        have hc : ((2*k+1 : ℕ) : ℝ) = ((k:ℕ):ℝ) * 2 + 1 := by push_cast; ring
        rw [hc]
        ring_nf
    _ = ∑' k : ℕ, exp (-π * (b/4) * ((k:ℕ):ℝ) ^ 2)
          - ∑' k : ℕ, exp (-π * (b/4) * ((2*k : ℕ) : ℝ) ^ 2) :=
        eq_sub_of_add_eq' (tsum_even_add_odd
          (f := fun n : ℕ => exp (-π * (b/4) * ((n:ℕ):ℝ) ^ 2)) fE fO)
    _ = gaussSumNat (b/4) - gaussSumNat b := by
        have h1 : ∑' k : ℕ, exp (-π * (b/4) * ((k:ℕ):ℝ) ^ 2) = gaussSumNat (b/4) := rfl
        have h2 : ∑' k : ℕ, exp (-π * (b/4) * ((2*k : ℕ) : ℝ) ^ 2) = gaussSumNat b := by
          refine tsum_congr (fun k => ?_)
          have hc : ((2*k : ℕ) : ℝ) = ((k:ℕ):ℝ) * 2 := by push_cast; ring
          rw [hc]
          ring_nf
        rw [← h1, ← h2]

set_option maxHeartbeats 800000 in
/-- **Brick R1b.** `β^(1/2) · ∑'_n e^{-π·β·(n+1/2)²} → 1/2` as `β → 0⁺`. -/
theorem gaussSumHalf_asympt :
    Tendsto (fun b : ℝ => (b ^ ((1:ℝ)/2)) * gaussSumHalf b) (𝓝[>] 0) (𝓝 (1/2)) := by
  have hscale : ∀ b : ℝ, 0 < b → (b ^ ((1:ℝ)/2)) * gaussSumHalf b
      = (b ^ ((1:ℝ)/2)) * gaussSumNat (b/4) - (b ^ ((1:ℝ)/2)) * gaussSumNat b := by
    intro b hb
    rw [gaussSumHalf_eq b hb]
    ring
  have hsqrt4 : ∀ b : ℝ, 0 < b → (b ^ ((1:ℝ)/2)) = 2 * ((b/4) ^ ((1:ℝ)/2)) := by
    intro b hb
    have h1 : b = 4 * (b/4) := by field_simp
    have h4 : (4:ℝ) ^ ((1:ℝ)/2) = 2 := by norm_num
    calc b ^ ((1:ℝ)/2) = (4 * (b/4)) ^ ((1:ℝ)/2) := congrArg (fun x => x ^ ((1:ℝ)/2)) h1
      _ = (4:ℝ) ^ ((1:ℝ)/2) * ((b/4) ^ ((1:ℝ)/2)) :=
          Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : (0:ℝ) ≤ b/4)
      _ = 2 * ((b/4) ^ ((1:ℝ)/2)) := by rw [h4]
  have hdiv4 : Tendsto (fun b : ℝ => b / 4) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun b : ℝ => b / 4) (0:ℝ) := by fun_prop
      have h1 : Tendsto (fun b : ℝ => b / 4) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
        simpa using hc.tendsto
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with b hb
      simpa using hb.1
  have hA : Tendsto (fun b : ℝ => (b ^ ((1:ℝ)/2)) * gaussSumNat b) (𝓝[>] 0) (𝓝 (1/2)) :=
    gaussSumNat_asympt
  have hfirst : Tendsto (fun b : ℝ => (b ^ ((1:ℝ)/2)) * gaussSumNat (b/4))
      (𝓝[>] 0) (𝓝 1) := by
    have hcomp : Tendsto (fun b : ℝ => ((b/4) ^ ((1:ℝ)/2)) * gaussSumNat (b/4))
        (𝓝[>] 0) (𝓝 (1/2)) := gaussSumNat_asympt.comp hdiv4
    have h2 : Tendsto (fun b : ℝ => 2 * (((b/4) ^ ((1:ℝ)/2)) * gaussSumNat (b/4)))
        (𝓝[>] 0) (𝓝 (2 * (1/2))) := hcomp.const_mul 2
    have h1' : Tendsto (fun b : ℝ => 2 * (((b/4) ^ ((1:ℝ)/2)) * gaussSumNat (b/4)))
        (𝓝[>] 0) (𝓝 1) := by simpa using h2
    refine Tendsto.congr' ?_ h1'
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with b hb
    rw [hsqrt4 b hb.1]
    ring
  have hcongr : ∀ᶠ b in 𝓝[>] (0:ℝ),
      (b ^ ((1:ℝ)/2)) * gaussSumNat (b/4) - (b ^ ((1:ℝ)/2)) * gaussSumNat b
        = (b ^ ((1:ℝ)/2)) * gaussSumHalf b := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with b hb
    exact (hscale b hb.1).symm
  have hsub : Tendsto (fun b : ℝ =>
      (b ^ ((1:ℝ)/2)) * gaussSumNat (b/4) - (b ^ ((1:ℝ)/2)) * gaussSumNat b)
      (𝓝[>] 0) (𝓝 (1/2)) := by
    have hs := hfirst.sub hA
    have heq : ((1:ℝ) - 1/2) = 1/2 := by norm_num
    rw [heq] at hs
    exact hs
  exact Tendsto.congr' hcongr hsub

end Imscribing.Millennium.StarkAsympt
