/-
  Imscribing/YangMills/RademacherL1.lean

  Rademacher functions and their L1 annihilation: for q in L1([0,1]^r),
  the integral of q times a nonempty product of high-frequency Rademacher
  functions tends to 0.  Built from first principles (standard axioms only).
-/
import Mathlib
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Pi

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped BigOperators Topology ENNReal
open Complex Real Filter MeasureTheory Set

namespace YangMills

/-- The K-th Rademacher function on [0,1]: (-1)^{floor(2^K u)}. -/
noncomputable def rademacher (K : ℕ) (u : ℝ) : ℝ :=
  if Even (Int.floor ((2 : ℝ) ^ K * u)) then 1 else -1

lemma rademacher_abs (K : ℕ) (u : ℝ) : |rademacher K u| = 1 := by
  unfold rademacher
  split <;> norm_num

lemma rademacher_const_on_cell (K : ℕ) (n : ℤ)
    (u : ℝ) (hu : u ∈ Set.Ico ((n : ℝ) / (2 : ℝ)^K) (((n + 1 : ℤ) : ℝ) / (2 : ℝ)^K)) :
    rademacher K u = (if Even n then 1 else -1) := by
  unfold rademacher
  have hpow : 0 < (2 : ℝ) ^ K := by positivity
  have hmul : (n : ℝ) ≤ (2 : ℝ) ^ K * u := by
    have := hu.1
    field_simp [hpow.ne'] at this ⊢
    nlinarith
  have hmul' : (2 : ℝ) ^ K * u < (n : ℝ) + 1 := by
    have htmp : u < ((n + 1 : ℤ) : ℝ) / (2 : ℝ) ^ K := hu.2
    have htmp2 : u * (2 : ℝ) ^ K < ((n + 1 : ℤ) : ℝ) := by
      rwa [lt_div_iff₀ hpow] at htmp
    simpa [mul_comm] using htmp2
  have hfloor : Int.floor ((2 : ℝ) ^ K * u) = n := by
    exact Int.floor_eq_iff.mpr ⟨hmul, hmul'⟩
  rw [hfloor]

end YangMills

namespace YangMills

/-- The K-th dyadic interval [n/2^K, (n+1)/2^K) as a measurable set. -/
noncomputable def dyadicCell (K : ℕ) (n : ℤ) : Set ℝ :=
  Set.Ico ((n : ℝ) / (2 : ℝ)^K) (((n + 1 : ℤ) : ℝ) / (2 : ℝ)^K)

/-- r_K is measurable. -/
lemma rademacher_measurable (K : ℕ) : Measurable (rademacher K) := by
  unfold rademacher
  have hfloor : Measurable (fun u : ℝ => Int.floor ((2 : ℝ)^K * u)) := by fun_prop
  have hsetZ : MeasurableSet {z : ℤ | Even z} := (Set.to_countable _).measurableSet
  exact Measurable.ite (hfloor hsetZ) measurable_const measurable_const

private lemma rbound (K : ℕ) : ∀ x : ℝ, ‖rademacher K x‖ ≤ (1:ℝ) := by
  intro x; unfold rademacher; split <;> norm_num

/-- r_K is integrable on any interval. -/
private lemma rademacher_intervalIntegrable (K : ℕ) (a b : ℝ) :
    IntervalIntegrable (rademacher K) volume a b := by
  rw [intervalIntegrable_iff]
  constructor
  · exact (rademacher_measurable K).aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · have hfin : volume (uIoc a b) < ⊤ := by rw [Real.volume_uIoc]; finiteness
    exact (IntegrableOn.of_bound hfin
      ((rademacher_measurable K).aestronglyMeasurable.mono_measure Measure.restrict_le_self) 1
      (Filter.Eventually.of_forall (rbound K))).2

/-- Integral of r_K over one level-K cell Ioc(m/2^K,(m+1)/2^K). -/
private lemma integral_rademacher_cell (K : ℕ) (m : ℕ) :
    ∫ u in Set.Ico ((m : ℝ) / (2 : ℝ)^K) (((m+1 : ℕ) : ℝ) / (2 : ℝ)^K), rademacher K u =
      ((if Even m then (1 : ℝ) else -1) / (2 : ℝ)^K) := by
  have hle : ((m : ℝ) / (2 : ℝ)^K) ≤ (((m+1 : ℕ) : ℝ) / (2 : ℝ)^K) := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^K) (by positivity : (0:ℝ) < (2:ℝ)^K)]
    norm_num
  have hconst : (fun u => rademacher K u) =ᵐ[volume.restrict (Set.Ico ((m : ℝ) / (2 : ℝ)^K) (((m+1 : ℕ) : ℝ) / (2 : ℝ)^K))]
      (fun _ => (if Even m then (1 : ℝ) else -1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    have hc := rademacher_const_on_cell K (m : ℤ) u hu
    simpa using hc
  rw [integral_congr_ae hconst]
  rw [MeasureTheory.integral_const]
  simp only [Measure.restrict_apply_univ, measureReal_def]
  rw [Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hle)]
  by_cases he : Even m <;> simp [he] <;> ring

end YangMills

namespace YangMills

/-- Integral of r_K over a level-K0 parent cell is zero when K > K0.
Uses interval-integral telescoping over the 2^(K-K0) level-K sub-cells; the
Rademacher signs alternate, and there are an even number of them. -/
private lemma integral_rademacher_parent_zero (K K0 : ℕ) (hK : K0 < K) (n : ℕ) :
    ∫ u in Set.Ico ((n : ℝ) / (2 : ℝ)^K0) (((n+1 : ℕ) : ℝ) / (2 : ℝ)^K0), rademacher K u = 0 := by
  let d := 2 ^ (K - K0)
  have hd_even : Even d := Nat.even_pow.mpr ⟨by norm_num, by omega⟩
  have hd_pos : 0 < d := by unfold d; positivity
  let a : ℕ → ℝ := fun j => ((n*d + j : ℕ) : ℝ) / (2 : ℝ)^K
  have ha0 : a 0 = (n : ℝ) / (2 : ℝ)^K0 := by
    unfold a d
    simp only [Nat.mul_zero, Nat.add_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, Nat.cast_pow]
    rw [show (2:ℝ)^K = (2:ℝ)^(K-K0) * (2:ℝ)^K0 by
      rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hK)]]
    norm_num
    field_simp
  have had : a d = ((n+1 : ℕ) : ℝ) / (2 : ℝ)^K0 := by
    unfold a d
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    rw [show (2:ℝ)^K = (2:ℝ)^(K-K0) * (2:ℝ)^K0 by
      rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hK)]]
    push_cast
    field_simp
  -- telescoping: sum of interval integrals over sub-cells = integral over parent
  have htel := intervalIntegral.sum_integral_adjacent_intervals_Ico (f := rademacher K) (μ := volume)
    (a := a) (m := 0) (n := d) (by omega)
    (by intro j hj; exact rademacher_intervalIntegrable K (a j) (a (j+1)))
  -- each sub-integral (interval = Ioc set integral) equals the Ico cell formula
  have hcell : ∀ j ∈ Finset.Ico 0 d,
      ∫ u in a j..a (j+1), rademacher K u =
        (if Even (n*d + j) then (1:ℝ) else -1) / (2:ℝ)^K := by
    intro j hj
    rw [intervalIntegral.integral_of_le (by
      unfold a
      rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (2:ℝ)^K)]
      norm_num)]
    rw [← restrict_Ico_eq_restrict_Ioc]
    unfold a
    convert integral_rademacher_cell K (n*d+j) using 1 <;> norm_num
  rw [← ha0, ← had]
  rw [restrict_Ico_eq_restrict_Ioc]
  have hle_parent : a 0 ≤ a d := by
    rw [ha0, had]
    rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<(2:ℝ)^K0)]
    norm_num
  rw [← intervalIntegral.integral_of_le hle_parent]
  rw [← htel]
  rw [Finset.sum_congr rfl hcell]
  -- sum of alternating signs over even d is zero
  have hnd_even : Even (n*d) := by exact hd_even.mul_left n
  have hpar : ∀ j, (if Even (n*d + j) then (1:ℝ) else -1) = (if Even j then (1:ℝ) else -1) := by
    intro j
    by_cases hj : Even j
    · have : Even (n*d + j) := hnd_even.add hj
      simp [hj, this]
    · have hjodd : Odd j := by simpa using hj
      have : Odd (n*d + j) := hnd_even.add_odd hjodd
      have hne : ¬ Even (n*d + j) := by simpa using this
      simp [hj, hne]
  simp_rw [hpar]
  rw [← Finset.sum_div]
  have halt_range : ∀ k : ℕ, ∑ j ∈ Finset.range (2*k), (if Even j then (1:ℝ) else -1) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      simp [ih]
  have halt : ∑ j ∈ Finset.Ico 0 d, (if Even j then (1:ℝ) else -1) = 0 := by
    rw [Finset.sum_Ico_eq_sub (fun j => (if Even j then (1:ℝ) else -1)) (by omega : 0 ≤ d)]
    obtain ⟨k, hk⟩ := hd_even
    rw [hk]
    have htwo : k + k = 2 * k := by ring
    rw [htwo]
    simpa using halt_range k
  rw [halt, zero_div]

/-- Every positive-frequency Rademacher function has mean zero on `[0,1)`. -/
theorem rademacher_integral_Ico_zero (K : ℕ) (hK : 0 < K) :
    ∫ u in Set.Ico (0 : ℝ) 1, rademacher K u = 0 := by
  simpa using integral_rademacher_parent_zero K 0 hK 0


end YangMills

namespace YangMills

/-- r_{K0} is constant with value (if Even j then 1 else -1) on level-K0 cell j. -/
private lemma rademacher_const_parent (K0 : ℕ) (j : ℕ)
    (u : ℝ) (hu : u ∈ Set.Ico ((j:ℝ)/(2:ℝ)^K0) (((j+1:ℕ):ℝ)/(2:ℝ)^K0)) :
    rademacher K0 u = (if Even j then (1:ℝ) else -1) := by
  have h := rademacher_const_on_cell K0 (j : ℤ) u hu
  by_cases hj : Even j
  · have hjz : Even (j : ℤ) := by exact_mod_cast hj
    simp [hj, hjz] at h ⊢
    exact h
  · have hjz : ¬ Even (j : ℤ) := by exact_mod_cast hj
    simp [hj, hjz] at h ⊢
    exact h

/-- Orthogonality: for K0 < K, ∫ r_{K0} * r_K over [0,1] = 0. -/
private lemma rademacher_orthogonal (K0 K : ℕ) (hK : K0 < K) :
    ∫ u in Set.Ico 0 1, rademacher K0 u * rademacher K u = 0 := by
  let d := 2^K0
  let a : ℕ → ℝ := fun j => (j : ℝ) / (2 : ℝ)^K0
  have ha0 : a 0 = 0 := by simp [a]
  have had : a d = 1 := by
    unfold a d
    norm_num
  -- telescoping over level-K0 cells
  have hmn : 0 ≤ d := by unfold d; norm_num
  have hmeas_prod : AEStronglyMeasurable (fun u => rademacher K0 u * rademacher K u) volume :=
    ((rademacher_measurable K0).mul (rademacher_measurable K)).aestronglyMeasurable
  have hbound_prod : ∀ x : ℝ, ‖rademacher K0 x * rademacher K x‖ ≤ (1:ℝ) := by
    intro x
    simp [norm_mul, rademacher_abs]
  have hint : ∀ k ∈ Set.Ico 0 d, IntervalIntegrable (fun u => rademacher K0 u * rademacher K u) volume (a k) (a (k+1)) := by
    intro j hj
    rw [intervalIntegrable_iff]
    constructor
    · exact hmeas_prod.mono_measure Measure.restrict_le_self
    · have hfin : volume (uIoc (a j) (a (j+1))) < ⊤ := by rw [Real.volume_uIoc]; finiteness
      exact (IntegrableOn.of_bound hfin (hmeas_prod.mono_measure Measure.restrict_le_self) 1
        (Filter.Eventually.of_forall hbound_prod)).2
  have htel := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := fun u => rademacher K0 u * rademacher K u) (μ := volume)
    (a := a) (m := 0) (n := d) hmn hint
  rw [show (∫ u in Set.Ico 0 1, rademacher K0 u * rademacher K u) =
      ∫ u in a 0..a d, rademacher K0 u * rademacher K u by
    rw [ha0, had]
    rw [restrict_Ico_eq_restrict_Ioc]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]]
  rw [← htel]
  have hcell : ∀ j ∈ Finset.Ico 0 d,
      ∫ u in a j..a (j+1), rademacher K0 u * rademacher K u = 0 := by
    intro j hj
    have hjlt : j < d := Finset.mem_Ico.mp hj |>.2
    rw [intervalIntegral.integral_of_le (by
      unfold a
      rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (2:ℝ)^K0)]
      norm_num)]
    rw [← restrict_Ico_eq_restrict_Ioc]
    -- on Ico(a j)(a(j+1)), r_{K0} = ±1
    have hconst : ∀ u ∈ Set.Ico (a j) (a (j+1)),
        rademacher K0 u = (if Even j then (1:ℝ) else -1) := by
      intro u hu
      unfold a at hu
      exact rademacher_const_parent K0 j u hu
    have hconst_prod : ∀ u ∈ Set.Ico (a j) (a (j+1)),
        rademacher K0 u * rademacher K u = (if Even j then (1:ℝ) else -1) * rademacher K u := by
      intro u hu
      rw [hconst u hu]
    rw [setIntegral_congr_fun measurableSet_Ico hconst_prod]
    rw [MeasureTheory.integral_const_mul]
    exact mul_eq_zero_of_right _ (integral_rademacher_parent_zero K K0 hK j)
  rw [Finset.sum_eq_zero hcell]

/-- A dyadic step function at level K0: value g j on cell j. -/
noncomputable def dyadicStep (K0 : ℕ) (g : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (2^K0), g j * (Set.Ico ((j:ℝ)/(2:ℝ)^K0) (((j+1:ℕ):ℝ)/(2:ℝ)^K0)).indicator (fun _ => (1:ℝ)) u

/-- Level-K0 dyadic cells with distinct indices are disjoint. -/
private lemma dyadic_cell_disjoint (K0 : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Set.Ico ((i:ℝ)/(2:ℝ)^K0) (((i+1:ℕ):ℝ)/(2:ℝ)^K0))
             (Set.Ico ((j:ℝ)/(2:ℝ)^K0) (((j+1:ℕ):ℝ)/(2:ℝ)^K0)) := by
  by_cases hlt : i < j
  · apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hle : ((j:ℝ)/(2:ℝ)^K0) < ((i+1:ℕ):ℝ)/(2:ℝ)^K0 := lt_of_le_of_lt hxj.1 hxi.2
    have hpow : (0:ℝ) < (2:ℝ)^K0 := by positivity
    have hnat : j < i + 1 := by
      have h' : (j:ℝ) < ((i+1:ℕ):ℝ) := (div_lt_div_iff_of_pos_right hpow).mp hle
      exact_mod_cast h'
    omega
  · have hji : j < i := by omega
    rw [disjoint_comm]
    apply Set.disjoint_left.mpr
    intro x hxj hxi
    have hle : ((i:ℝ)/(2:ℝ)^K0) < ((j+1:ℕ):ℝ)/(2:ℝ)^K0 := lt_of_le_of_lt hxi.1 hxj.2
    have hpow : (0:ℝ) < (2:ℝ)^K0 := by positivity
    have hnat : i < j + 1 := by
      have h' : (i:ℝ) < ((j+1:ℕ):ℝ) := (div_lt_div_iff_of_pos_right hpow).mp hle
      exact_mod_cast h'
    omega

/-- On cell j, dyadicStep equals g j. -/
private lemma dyadicStep_on_cell (K0 : ℕ) (g : ℕ → ℝ) (j : ℕ) (hj : j < 2^K0)
    (u : ℝ) (hu : u ∈ Set.Ico ((j:ℝ)/(2:ℝ)^K0) (((j+1:ℕ):ℝ)/(2:ℝ)^K0)) :
    dyadicStep K0 g u = g j := by
  unfold dyadicStep
  rw [Finset.sum_eq_single j]
  · have hu' : u ∈ Set.Ico ((j:ℝ)/(2:ℝ)^K0) ((((j:ℝ)+1))/(2:ℝ)^K0) := by
      simpa [Nat.cast_add, Nat.cast_one] using hu
    simp [hu']
  · intro i hi hij
    have hnot : u ∉ Set.Ico ((i:ℝ)/(2:ℝ)^K0) (((i+1:ℕ):ℝ)/(2:ℝ)^K0) := by
      intro hui
      have hdisj := dyadic_cell_disjoint K0 hij
      exact Set.disjoint_left.mp hdisj hui hu
    rw [Set.indicator_of_notMem hnot]
    ring
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hj)).elim

/-- Integral of r_K against the dyadic step function vanishes for K > K0.
Uses interval-integral telescoping; on each level-K0 cell, dyadicStep is
constant g j and r_K integrates to zero there. -/
private lemma integral_dyadicStep_rademacher_zero (K K0 : ℕ) (hK : K0 < K) (g : ℕ → ℝ) :
    ∫ u in Set.Ico 0 1, dyadicStep K0 g u * rademacher K u = 0 := by
  let d := 2^K0
  let a : ℕ → ℝ := fun j => (j : ℝ) / (2 : ℝ)^K0
  have ha0 : a 0 = 0 := by simp [a]
  have had : a d = 1 := by unfold a d; norm_num
  have hmn : 0 ≤ d := by unfold d; norm_num
  -- integrability of the product on each subinterval
  have hstep_on : ∀ j < d, ∀ u ∈ Set.Ico (a j) (a (j+1)), dyadicStep K0 g u = g j := by
    intro j hj u hu
    unfold a at hu
    exact dyadicStep_on_cell K0 g j (by simpa [d] using hj) u hu
  have hmeas_step : AEStronglyMeasurable (dyadicStep K0 g) volume := by
    unfold dyadicStep
    exact (Finset.measurable_sum (Finset.range (2^K0)) (by
      intro j hj
      exact measurable_const.mul (measurable_const.indicator measurableSet_Ico))).aestronglyMeasurable
  have hbound_step : ∀ u, ‖dyadicStep K0 g u‖ ≤ ∑ j ∈ Finset.range d, ‖g j‖ := by
    intro u
    unfold dyadicStep d
    exact (norm_sum_le _ _).trans (by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      by_cases hu : u ∈ Set.Ico ((j:ℝ)/(2:ℝ)^K0) (((j+1:ℕ):ℝ)/(2:ℝ)^K0)
      · rw [Set.indicator_of_mem hu]
        simp
      · rw [Set.indicator_of_notMem hu]
        simp)
  have hmeas_prod : AEStronglyMeasurable (fun u => dyadicStep K0 g u * rademacher K u) volume :=
    hmeas_step.mul (rademacher_measurable K).aestronglyMeasurable
  have hbound_prod : ∀ u, ‖dyadicStep K0 g u * rademacher K u‖ ≤ ∑ j ∈ Finset.range d, ‖g j‖ := by
    intro u
    rw [norm_mul]
    have hr : ‖rademacher K u‖ = (1:ℝ) := by
      rw [Real.norm_eq_abs, rademacher_abs]
    rw [hr, mul_one]
    exact hbound_step u
  have hint : ∀ k ∈ Set.Ico 0 d, IntervalIntegrable (fun u => dyadicStep K0 g u * rademacher K u) volume (a k) (a (k+1)) := by
    intro j hj
    rw [intervalIntegrable_iff]
    constructor
    · exact hmeas_prod.mono_measure Measure.restrict_le_self
    · have hfin : volume (uIoc (a j) (a (j+1))) < ⊤ := by rw [Real.volume_uIoc]; finiteness
      exact (IntegrableOn.of_bound hfin (hmeas_prod.mono_measure Measure.restrict_le_self)
        (∑ j ∈ Finset.range d, ‖g j‖) (Filter.Eventually.of_forall hbound_prod)).2
  have htel := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := fun u => dyadicStep K0 g u * rademacher K u) (μ := volume)
    (a := a) (m := 0) (n := d) hmn hint
  rw [show (∫ u in Set.Ico 0 1, dyadicStep K0 g u * rademacher K u) =
      ∫ u in a 0..a d, dyadicStep K0 g u * rademacher K u by
    rw [ha0, had]
    rw [restrict_Ico_eq_restrict_Ioc]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]]
  rw [← htel]
  apply Finset.sum_eq_zero
  intro j hj
  have hjlt : j < d := Finset.mem_Ico.mp hj |>.2
  rw [intervalIntegral.integral_of_le (by
    unfold a
    rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (2:ℝ)^K0)]
    norm_num)]
  rw [← restrict_Ico_eq_restrict_Ioc]
  have hconst : ∀ u ∈ Set.Ico (a j) (a (j+1)),
      dyadicStep K0 g u * rademacher K u = g j * rademacher K u := by
    intro u hu
    rw [hstep_on j hjlt u hu]
  rw [setIntegral_congr_fun measurableSet_Ico hconst]
  rw [MeasureTheory.integral_const_mul]
  exact mul_eq_zero_of_right _ (integral_rademacher_parent_zero K K0 hK j)

end YangMills

namespace YangMills

/-- Every u in [0,1) lies in a level-K0 dyadic cell. -/
private lemma point_in_cell (K0 : ℕ) (u : ℝ) (hu : u ∈ Set.Ico 0 1) :
    ∃ (j : ℕ), j < 2^K0 ∧ u ∈ Set.Ico ((j:ℝ)/((2:ℝ)^K0)) (((j:ℝ)+1)/((2:ℝ)^K0)) := by
  let j := Nat.floor ((2:ℝ)^K0 * u)
  have hmul_nonneg : 0 ≤ (2:ℝ)^K0 * u := mul_nonneg (by positivity) hu.1
  have hcast : ((2^K0 : ℕ) : ℝ) = (2:ℝ)^K0 := by norm_num
  have hjlt : j < 2^K0 := by
    dsimp [j]
    rw [Nat.floor_lt hmul_nonneg]
    have hmul_lt := mul_lt_mul_of_pos_left hu.2 (by positivity : (0:ℝ) < (2:ℝ)^K0)
    nlinarith [hmul_lt, hcast]
  refine ⟨j, hjlt, ?_⟩
  constructor
  · dsimp [j]
    have hf := Nat.floor_le hmul_nonneg
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^K0)]
    simpa [mul_comm] using hf
  · dsimp [j]
    have hf := Nat.lt_floor_add_one ((2:ℝ)^K0 * u)
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^K0)]
    simpa [mul_comm] using hf

/-- If f is bounded and measurable on [0,1], then f * r_K is integrable there. -/
private lemma integrable_mul_rademacher (f : ℝ → ℝ) (C : ℝ)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ico 0 1)))
    (hbound : ∀ u ∈ Set.Ico 0 1, ‖f u‖ ≤ C) (K : ℕ) :
    Integrable (fun u => f u * rademacher K u) (volume.restrict (Set.Ico 0 1)) := by
  have hmeas' : AEStronglyMeasurable (fun u => f u * rademacher K u) (volume.restrict (Set.Ico 0 1)) :=
    hmeas.mul (rademacher_measurable K).aestronglyMeasurable
  have hfin : (volume : Measure ℝ) (Set.Ico 0 1) < ⊤ := by rw [Real.volume_Ico]; finiteness
  exact IntegrableOn.of_bound hfin hmeas' C (by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    rw [norm_mul]
    have hr : ‖rademacher K u‖ = (1:ℝ) := by rw [Real.norm_eq_abs, rademacher_abs]
    rw [hr, mul_one]
    exact hbound u hu)

/-- L1 annihilation for continuous functions on [0,1]. -/
lemma rademacher_annihilate_continuous (q : ℝ → ℝ) (hq : Continuous q) :
    Tendsto (fun K : ℕ => ∫ u in Set.Ico 0 1, q u * rademacher K u) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  let eps' := eps / 2
  have heps' : eps' > 0 := by dsimp [eps']; linarith
  have huc : UniformContinuousOn q (Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hq.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc eps' heps'
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℕ, (1 : ℝ) / (2 : ℝ)^K0 < δ := by
    have htend : Tendsto (fun K : ℕ => (1 : ℝ) / (2 : ℝ)^K) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨K0, hK0⟩ := htend δ hδpos
    refine ⟨K0, ?_⟩
    have hk := hK0 K0 (le_refl K0)
    rw [Real.dist_eq] at hk
    simpa [abs_of_nonneg (by positivity : (0:ℝ) ≤ (1:ℝ)/(2:ℝ)^K0)] using hk
  refine ⟨K0 + 1, ?_⟩
  intro K hK
  have hKgt : K0 < K := by omega
  let g : ℕ → ℝ := fun j => q ((j : ℝ) / (2 : ℝ)^K0)
  have hstep_zero := integral_dyadicStep_rademacher_zero K K0 hKgt g
  have hdiff : ∀ u ∈ Set.Ico 0 1, |q u - dyadicStep K0 g u| ≤ eps' := by
    intro u hu
    obtain ⟨j, hjlt, huj⟩ := point_in_cell K0 u hu
    have hstep_val : dyadicStep K0 g u = g j := by
      have huj' : u ∈ Set.Ico ((j:ℝ)/(2:ℝ)^K0) (((j+1:ℕ):ℝ)/(2:ℝ)^K0) := by
        simpa [Nat.cast_add, Nat.cast_one] using huj
      exact dyadicStep_on_cell K0 g j hjlt u huj'
    rw [hstep_val]
    dsimp [g]
    have hdist : dist u ((j : ℝ) / (2:ℝ)^K0) < δ := by
      rw [Real.dist_eq]
      have hju1 : (j:ℝ)/(2:ℝ)^K0 ≤ u := huj.1
      have hju2 : u < ((j:ℝ)+1)/(2:ℝ)^K0 := huj.2
      rw [abs_of_nonneg (sub_nonneg.mpr hju1)]
      have hcell_len : ((j:ℝ)+1)/(2:ℝ)^K0 - (j:ℝ)/(2:ℝ)^K0 = 1/(2:ℝ)^K0 := by field_simp; ring
      have : u - (j:ℝ)/(2:ℝ)^K0 < 1/(2:ℝ)^K0 := by nlinarith
      exact lt_trans this hK0
    have hjmem : ((j:ℝ)/(2:ℝ)^K0) ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · positivity
      · have hjle : (j:ℝ) ≤ (2:ℝ)^K0 := by exact_mod_cast (Nat.le_of_lt hjlt)
        rw [div_le_one (by positivity : (0:ℝ) < (2:ℝ)^K0)]
        exact hjle
    have huIcc : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.1, le_of_lt hu.2⟩
    have hdq := hδ u huIcc ((j:ℝ)/(2:ℝ)^K0) hjmem hdist
    simpa [Real.dist_eq] using (le_of_lt hdq)
  rw [Real.dist_eq, sub_zero]
  -- bounds
  obtain ⟨Cq, hCq⟩ : ∃ C : ℝ, ∀ u ∈ Set.Ico 0 1, ‖q u‖ ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq.continuousOn
    exact ⟨C, fun u hu => hC u ⟨hu.1, le_of_lt hu.2⟩⟩
  let Cs : ℝ := ∑ j ∈ Finset.range (2^K0), ‖g j‖
  have hstep_bound : ∀ u ∈ Set.Ico 0 1, ‖dyadicStep K0 g u‖ ≤ Cs := by
    intro u hu_unused
    unfold dyadicStep Cs
    exact (norm_sum_le _ _).trans (by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      by_cases huj : u ∈ Set.Ico ((j:ℝ)/(2:ℝ)^K0) (((j+1:ℕ):ℝ)/(2:ℝ)^K0)
      · rw [Set.indicator_of_mem huj]; simp
      · rw [Set.indicator_of_notMem huj]; simp)
  have hq_meas : AEStronglyMeasurable q (volume.restrict (Set.Ico 0 1)) := hq.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hstep_meas : AEStronglyMeasurable (dyadicStep K0 g) (volume.restrict (Set.Ico 0 1)) := by
    unfold dyadicStep
    exact (Finset.measurable_sum (Finset.range (2^K0)) (by
      intro j hj
      exact measurable_const.mul (measurable_const.indicator measurableSet_Ico))).aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hq_mul_int := integrable_mul_rademacher q Cq hq_meas hCq K
  have hstep_mul_int := integrable_mul_rademacher (dyadicStep K0 g) Cs hstep_meas hstep_bound K
  have hdiff_mul_int := integrable_mul_rademacher (fun u => q u - dyadicStep K0 g u) (Cq + Cs)
    (hq_meas.sub hstep_meas) (by
      intro u hu
      exact (norm_sub_le (q u) (dyadicStep K0 g u)).trans (add_le_add (hCq u hu) (hstep_bound u hu))) K
  have hint_eq : (∫ u in Set.Ico 0 1, q u * rademacher K u) =
      ∫ u in Set.Ico 0 1, (q u - dyadicStep K0 g u) * rademacher K u := by
    have hmul : (fun u => (q u - dyadicStep K0 g u) * rademacher K u) =
        fun u => q u * rademacher K u - dyadicStep K0 g u * rademacher K u := by
      funext u; ring
    rw [hmul, integral_sub hq_mul_int hstep_mul_int]
    rw [hstep_zero, sub_zero]
  rw [hint_eq]
  have hnorm : ‖∫ u in Set.Ico 0 1, (q u - dyadicStep K0 g u) * rademacher K u‖
      ≤ eps' * (volume : Measure ℝ).real (Set.Ico 0 1) := by
    apply norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Set.Ico (0:ℝ) 1)
      (by rw [Real.volume_Ico]; finiteness)
    intro u hu
    rw [norm_mul]
    have hr : ‖rademacher K u‖ = (1:ℝ) := by rw [Real.norm_eq_abs, rademacher_abs]
    rw [hr, mul_one]
    simpa [Real.norm_eq_abs] using hdiff u hu
  rw [measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (by norm_num)] at hnorm
  norm_num at hnorm
  dsimp [eps'] at hnorm
  linarith

end YangMills


