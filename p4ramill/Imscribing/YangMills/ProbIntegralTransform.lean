/-
  Imscribing/YangMills/ProbIntegralTransform.lean

  The probability integral transform: an atomless probability measure on R is
  pushed forward by its cdf to Lebesgue measure on [0,1).  Built from Mathlib's
  Stieltjes/CDF machinery.  Standard axioms only.
-/
import Mathlib
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace YangMills

/-- Right-continuity plus no-atoms implies continuity of the cdf. -/
theorem continuous_cdf_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hright : ContinuousWithinAt (cdf μ) (Ici x) x := (cdf μ).right_continuous x
  have hleft : ContinuousWithinAt (cdf μ) (Iic x) x := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    -- nested intervals Ioc (x - 1/(n+1)) x decrease to {x}
    have hIoc_inter : (⋂ n : ℕ, Ioc (x - 1 / (n + 1 : ℝ)) x) = {x} := by
      ext y
      simp only [mem_iInter, mem_Ioc, mem_singleton_iff]
      constructor
      · intro hy
        refine le_antisymm (hy 0).2 ?_
        by_contra hlt
        push_neg at hlt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        have h1 := (hy n).1
        linarith
      · rintro rfl n
        refine ⟨?_, le_rfl⟩
        linarith [show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity]
    have hanti : Antitone (fun n : ℕ => Ioc (x - 1 / (n + 1 : ℝ)) x) := by
      intro m n hmn
      apply Ioc_subset_Ioc_left
      gcongr
    have htend : Tendsto (fun n : ℕ => μ (Ioc (x - 1 / (n + 1 : ℝ)) x)) atTop (𝓝 (μ {x})) := by
      rw [← hIoc_inter]
      exact tendsto_measure_iInter_atTop (fun _ => measurableSet_Ioc.nullMeasurableSet)
        hanti ⟨0, measure_ne_top μ _⟩
    rw [measure_singleton] at htend
    have htend_real : Tendsto (fun n : ℕ => μ.real (Ioc (x - 1 / (n + 1 : ℝ)) x)) atTop (𝓝 0) := by
      simpa [Measure.real, ENNReal.toReal_zero] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htend_real) ε hε
    refine ⟨1 / (N + 1 : ℝ), by positivity, ?_⟩
    intro y hy hdist
    rcases eq_or_lt_of_le (mem_Iic.mp hy) with rfl | hyx
    · simpa using hε
    · have hy_mem : x - 1 / (N + 1 : ℝ) < y := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hyx)] at hdist
        linarith
      have hsub : Ioc y x ⊆ Ioc (x - 1 / (N + 1 : ℝ)) x := Ioc_subset_Ioc_left hy_mem.le
      have hdiff : cdf μ x - cdf μ y = μ.real (Ioc y x) := by
        rw [cdf_eq_real, cdf_eq_real]
        rw [show μ.real (Iic x) - μ.real (Iic y) = μ.real (Ioc y x) by
          simp only [Measure.real]
          rw [← ENNReal.toReal_sub_of_le (measure_mono (Iic_subset_Iic.mpr hyx.le)) (measure_ne_top μ (Iic x))]
          congr 1
          rw [← measure_diff (Iic_subset_Iic.mpr hyx.le) measurableSet_Iic.nullMeasurableSet (measure_ne_top μ (Iic y))]
          congr 1
          ext z; simp only [mem_Iic, mem_diff, mem_Ioc, not_le]; tauto]
      have hle : μ.real (Ioc y x) ≤ μ.real (Ioc (x - 1 / (N + 1 : ℝ)) x) :=
        measureReal_mono hsub
      have hN' : μ.real (Ioc (x - 1 / (N + 1 : ℝ)) x) < ε := by
        have := hN N le_rfl
        rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at this
        exact this
      rw [Real.dist_eq]
      have hyx_cdf : cdf μ y ≤ cdf μ x := (cdf μ).mono hyx.le
      rw [abs_of_nonpos (sub_nonpos.mpr hyx_cdf)]
      have heq : cdf μ y - cdf μ x = -(μ.real (Ioc y x)) := by linarith [hdiff]
      rw [heq, neg_neg]
      exact hle.trans_lt hN'
  -- combine left and right continuity
  exact (continuousAt_iff_continuous_left_right).2 ⟨hleft, hright⟩

end YangMills

namespace YangMills

/-- Preimage of Iic u under cdf has measure ofReal u, for 0 ≤ u < 1. -/
theorem measure_preimage_cdf_Iic
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    μ ((cdf μ) ⁻¹' Iic u) = ENNReal.ofReal u := by
  let S : Set ℝ := (cdf μ) ⁻¹' Iic u
  by_cases hS : S.Nonempty
  · have hbdd : BddAbove S := by
      have ht := tendsto_cdf_atTop μ
      rw [Metric.tendsto_atTop] at ht
      obtain ⟨M, hM⟩ := ht (1 - u) (by linarith)
      refine ⟨M, fun x hx => ?_⟩
      by_contra hMx
      push_neg at hMx
      have hxmem := hM x hMx.le
      rw [Real.dist_eq] at hxmem
      rw [abs_of_nonpos (by linarith [cdf_le_one μ x] : cdf μ x - 1 ≤ 0)] at hxmem
      have hxcdf : cdf μ x ≤ u := hx
      linarith
    let x₀ := sSup S
    have hcont : Continuous (cdf μ) := continuous_cdf_of_noAtoms μ
    have hclosed : IsClosed S := isClosed_Iic.preimage hcont
    have hx₀_mem : x₀ ∈ S := hclosed.csSup_mem hS hbdd
    have hS_eq : S = Iic x₀ := by
      ext x
      refine ⟨fun hx => le_csSup hbdd hx, fun hx => ?_⟩
      exact ((cdf μ).mono hx).trans hx₀_mem
    have hval : cdf μ x₀ = u := by
      refine le_antisymm hx₀_mem ?_
      have hgt : ∀ᶠ y in 𝓝[>] x₀, u ≤ cdf μ y := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        by_contra hnot
        push_neg at hnot
        exact absurd (le_csSup hbdd (le_of_lt hnot)) (not_le.mpr hy)
      have htend : Tendsto (cdf μ) (𝓝[>] x₀) (𝓝 (cdf μ x₀)) :=
        (hcont.continuousAt.tendsto).mono_left inf_le_left
      exact ge_of_tendsto htend hgt
    change μ S = ENNReal.ofReal u
    rw [hS_eq, ← ofReal_cdf μ x₀, hval]
  · rw [not_nonempty_iff_eq_empty] at hS
    have hu_eq : u = 0 := by
      refine le_antisymm ?_ hu0
      by_contra hpos
      push_neg at hpos
      have h : ∀ᶠ x in atBot, cdf μ x < u := (tendsto_order.1 (tendsto_cdf_atBot μ)).2 u hpos
      rw [eventually_atBot] at h
      obtain ⟨M, hM⟩ := h
      have hMem : M ∈ S := by
        change cdf μ M ≤ u
        exact le_of_lt (hM M le_rfl)
      exact (Set.eq_empty_iff_forall_notMem.mp hS M) hMem
    subst u
    change μ S = ENNReal.ofReal 0
    rw [hS]
    simp

end YangMills

namespace YangMills

/-- Probability Integral Transform: cdf pushes an atomless probability measure
forward to Lebesgue measure on Ioc 0 1. -/
theorem map_cdf_eq_uniform_Ioc
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    μ.map (cdf μ) = volume.restrict (Ioc 0 1) := by
  have hcont : Continuous (cdf μ) := continuous_cdf_of_noAtoms μ
  haveI : IsProbabilityMeasure (μ.map (cdf μ)) :=
    Measure.isProbabilityMeasure_map hcont.measurable.aemeasurable
  haveI : IsProbabilityMeasure (volume.restrict (Ioc (0:ℝ) 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    norm_num
  apply MeasureTheory.Measure.eq_of_cdf (μ.map (cdf μ)) (volume.restrict (Ioc (0:ℝ) 1))
  ext u
  rw [cdf_eq_real, cdf_eq_real, Measure.real, Measure.real,
      Measure.map_apply hcont.measurable measurableSet_Iic,
      Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge u 0 with hu_neg | hu_nonneg
  · have h1 : (cdf μ) ⁻¹' Iic u = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_lt_of_le hu_neg (cdf_nonneg μ x))
    have h2 : Iic u ∩ Ioc (0:ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
      intro hxu hx0
      linarith
    rw [h1, h2]
    simp
  · rcases lt_or_ge u 1 with hu_lt1 | hu_ge1
    · rw [measure_preimage_cdf_Iic μ hu_nonneg hu_lt1]
      have hI : Iic u ∩ Ioc (0:ℝ) 1 = Ioc 0 u := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
        · intro h; exact ⟨by linarith [h.2], ⟨by linarith [h.1], by linarith [h.2]⟩⟩
      rw [hI, Real.volume_Ioc, sub_zero]
    · have h1 : (cdf μ) ⁻¹' Iic u = univ := by
        ext x
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (cdf_le_one μ x).trans hu_ge1
      have h2 : Iic u ∩ Ioc (0:ℝ) 1 = Ioc 0 1 := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        exact ⟨fun h => h.2, fun h => ⟨h.2.trans hu_ge1, h⟩⟩
      rw [h1, h2]
      simp

theorem map_cdf_eq_uniform_Ico
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    μ.map (cdf μ) = volume.restrict (Ico 0 1) := by
  rw [map_cdf_eq_uniform_Ioc μ]
  exact Measure.restrict_congr_set (Ico_ae_eq_Ioc (μ := volume) (a := (0:ℝ)) (b := 1)).symm

#print axioms YangMills.map_cdf_eq_uniform_Ico

end YangMills
