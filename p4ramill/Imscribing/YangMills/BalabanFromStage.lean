/-
BalabanFromStage.lean

Constructs a concrete `BalabanRGContinuumHypothesis` instance from the
stage limit `stageObservableSchwinger_tendsto_iid` (`0 sorry`, standard axioms only).
-/

import Imscribing.YangMills.SchwingerConv
import Imscribing.YangMills.ContinuumClosure
import Imscribing.YangMills.IIDOS
import Imscribing.YangMills.IIDPoincareContinuation

open MeasureTheory Filter Set
open scoped ENNReal

namespace YangMills

/-- The 1D submersion pushforward theorem:
    If `g : ℝ → ℝ` is `C¹` on an open set `U` with `deriv g x ≠ 0` for all `x ∈ U`,
    then `g` pushes forward Lebesgue measure on `U` to `volume.withDensity ρ`. -/
lemma submersion_1d_absolutely_continuous
    {U : Set ℝ} {g : ℝ → ℝ} (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hderiv : ∀ x ∈ U, deriv g x ≠ 0) :
    ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ := by
  classical
  let P : ℚ × ℚ → Prop := fun q =>
    (q.1 : ℝ) < (q.2 : ℝ) ∧ Set.Ioo (q.1 : ℝ) (q.2 : ℝ) ⊆ U
  let A : ℕ → Set ℝ := fun n =>
    match Encodable.decode (α := ℚ × ℚ) n with
    | some q => if P q then Set.Ioo (q.1 : ℝ) (q.2 : ℝ) else ∅
    | none => ∅
  have hA_sub : ∀ n : ℕ, A n ⊆ U := by
    intro n
    dsimp [A]
    cases hdec : Encodable.decode (α := ℚ × ℚ) n with
    | none => exact Set.empty_subset _
    | some q =>
      dsimp only
      split_ifs with hq
      · exact hq.2
      · exact Set.empty_subset _
  have hA_meas : ∀ n : ℕ, MeasurableSet (A n) := by
    intro n
    dsimp [A]
    cases hdec : Encodable.decode (α := ℚ × ℚ) n with
    | none => exact MeasurableSet.empty
    | some q =>
      dsimp only
      split_ifs
      · exact measurableSet_Ioo
      · exact MeasurableSet.empty
  let E : ℕ → Set ℝ := disjointed A
  have hE_meas : ∀ n, MeasurableSet (E n) := MeasurableSet.disjointed hA_meas
  have hE_disj : Pairwise (Function.onFun Disjoint E) := disjoint_disjointed A
  have hE_sub_A : ∀ n, E n ⊆ A n := fun n => disjointed_le A n
  have hU_union : U = ⋃ n : ℕ, E n := by
    change U = ⋃ n : ℕ, disjointed A n
    rw [iUnion_disjointed]
    ext x
    constructor
    · intro hx
      obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hU x hx
      obtain ⟨q₁, hq₁_lo, hq₁_hi⟩ := exists_rat_btwn (by linarith : x - r < x)
      obtain ⟨q₂, hq₂_lo, hq₂_hi⟩ := exists_rat_btwn (by linarith : x < x + r)
      have h_sub_U : Set.Ioo (q₁ : ℝ) (q₂ : ℝ) ⊆ U := fun y hy =>
        hr_ball (Metric.mem_ball.mpr (by
          rw [Real.dist_eq, abs_lt]
          exact ⟨by linarith [hy.1], by linarith [hy.2]⟩))
      have hPq : P (q₁, q₂) := ⟨by linarith, h_sub_U⟩
      refine Set.mem_iUnion.mpr ⟨Encodable.encode (q₁, q₂), ?_⟩
      have hdec : Encodable.decode (α := ℚ × ℚ) (Encodable.encode (q₁, q₂)) = some (q₁, q₂) :=
        Encodable.encodek (q₁, q₂)
      change x ∈ match Encodable.decode (α := ℚ × ℚ) (Encodable.encode (q₁, q₂)) with
        | some q => if P q then Set.Ioo (q.1 : ℝ) (q.2 : ℝ) else ∅
        | none => ∅
      rw [hdec]
      dsimp only
      rw [if_pos hPq]
      exact ⟨hq₁_hi, hq₂_lo⟩
    · intro hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact hA_sub n hn
  have h_deriv_cont : ContinuousOn (deriv g) U :=
    hg.continuousOn_deriv_of_isOpen hU (le_refl 1)
  have h_piece : ∀ n : ℕ, ∃ ρn : ℝ → ℝ≥0∞,
      Measurable ρn ∧ (volume.restrict (E n)).map g = volume.withDensity ρn := by
    intro n
    by_cases hne : (E n).Nonempty
    · have hAn_ne : (A n).Nonempty := hne.mono (hE_sub_A n)
      cases hdec : Encodable.decode (α := ℚ × ℚ) n with
      | none =>
        exfalso
        have h_emp : A n = ∅ := by dsimp [A]; rw [hdec]
        rw [h_emp] at hAn_ne
        exact (Set.not_nonempty_empty) hAn_ne
      | some q =>
        have hPq : P q := by
          by_contra hnot
          have h_emp : A n = ∅ := by dsimp [A]; rw [hdec]; dsimp only; rw [if_neg hnot]
          rw [h_emp] at hAn_ne
          exact (Set.not_nonempty_empty) hAn_ne
        let I : Set ℝ := Set.Ioo (q.1 : ℝ) (q.2 : ℝ)
        have hEI : E n ⊆ I := by
          have hAI : A n = I := by dsimp [A, I]; rw [hdec]; dsimp only; rw [if_pos hPq]
          rw [← hAI]
          exact hE_sub_A n
        have hIU : I ⊆ U := hPq.2
        have h_sign : (∀ x ∈ I, 0 < deriv g x) ∨ (∀ x ∈ I, deriv g x < 0) := by
          by_contra h_both
          rw [not_or] at h_both
          rcases h_both with ⟨h_not_pos, h_not_neg⟩
          push_neg at h_not_pos h_not_neg
          obtain ⟨x, hxI, hx_le⟩ := h_not_pos
          obtain ⟨y, hyI, hy_ge⟩ := h_not_neg
          have hx_lt : deriv g x < 0 := lt_of_le_of_ne hx_le (hderiv x (hIU hxI))
          have hy_gt : 0 < deriv g y := lt_of_le_of_ne hy_ge (hderiv y (hIU hyI)).symm
          have hc : ∃ c ∈ I, deriv g c = 0 := by
            rcases le_total x y with hxy | hyx
            · have hcc_sub : Set.Icc x y ⊆ I :=
                fun z hz => ⟨lt_of_lt_of_le hxI.1 hz.1, lt_of_le_of_lt hz.2 hyI.2⟩
              have hcont_cc : ContinuousOn (deriv g) (Set.Icc x y) :=
                h_deriv_cont.mono (hcc_sub.trans hIU)
              obtain ⟨c, hc_mem, hc0⟩ :=
                intermediate_value_Icc hxy hcont_cc ⟨hx_lt.le, hy_gt.le⟩
              exact ⟨c, hcc_sub hc_mem, hc0⟩
            · have hcc_sub : Set.Icc y x ⊆ I :=
                fun z hz => ⟨lt_of_lt_of_le hyI.1 hz.1, lt_of_le_of_lt hz.2 hxI.2⟩
              have hcont_cc : ContinuousOn (deriv g) (Set.Icc y x) :=
                h_deriv_cont.mono (hcc_sub.trans hIU)
              obtain ⟨c, hc_mem, hc0⟩ :=
                intermediate_value_Icc' hyx hcont_cc ⟨hx_lt.le, hy_gt.le⟩
              exact ⟨c, hcc_sub hc_mem, hc0⟩
          rcases hc with ⟨c, hcI, hc0⟩
          exact hderiv c (hIU hcI) hc0
        have hg_inj_I : InjOn g I := by
          rcases h_sign with h_pos | h_neg
          · exact (strictMonoOn_of_deriv_pos (convex_Ioo _ _) (hg.continuousOn.mono hIU)
              (fun x hx => h_pos x (interior_subset hx))).injOn
          · exact (strictAntiOn_of_deriv_neg (convex_Ioo _ _) (hg.continuousOn.mono hIU)
              (fun x hx => h_neg x (interior_subset hx))).injOn
        have hg_inj : InjOn g (E n) := hg_inj_I.mono hEI
        let g' : ℝ → (ℝ →L[ℝ] ℝ) := fun x => (deriv g x) • ContinuousLinearMap.id ℝ ℝ
        have hg'_det : ∀ x ∈ E n, (g' x).det ≠ 0 := by
          intro x hx
          have hdet : (g' x).det = deriv g x := by
            change LinearMap.det ((deriv g x) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) = deriv g x
            rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]
          rw [hdet]
          exact hderiv x (hIU (hEI hx))
        have hg'_deriv : ∀ x ∈ E n, HasFDerivWithinAt g (g' x) (E n) x := by
          intro x hx
          have hxU : x ∈ U := hIU (hEI hx)
          have hdiff : DifferentiableAt ℝ g x :=
            (hg.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hxU)
          have hfd : HasFDerivAt g (g' x) x := by
            convert hdiff.hasDerivAt.hasFDerivAt using 1
            ext
            simp [g']
          exact hfd.hasFDerivWithinAt
        let μ : Measure ℝ := volume.restrict (E n)
        let w : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal |(g' x).det|
        have hw_ae : AEMeasurable w μ :=
          aemeasurable_ofReal_abs_det_fderivWithin (μ := volume) (hE_meas n) hg'_deriv
        have hac_mu : μ ≪ μ.withDensity w := by
          apply withDensity_absolutelyContinuous' hw_ae
          filter_upwards [ae_restrict_mem (hE_meas n)] with x hx hzero
          exact (not_le.mpr (abs_pos.mpr (hg'_det x hx))) (ENNReal.ofReal_eq_zero.mp hzero)
        have hg_ae_mu : AEMeasurable g μ :=
          ContinuousOn.aemeasurable₀
            (fun x hx => (hg'_deriv x hx).differentiableWithinAt.continuousWithinAt)
            (hE_meas n).nullMeasurableSet
        have hg_ae_w : AEMeasurable g (μ.withDensity w) :=
          hg_ae_mu.mono_ac (withDensity_absolutelyContinuous μ w)
        have hmap : Measure.map g (μ.withDensity w) = volume.restrict (g '' E n) :=
          map_withDensity_abs_det_fderiv_eq_addHaar (μ := volume)
            (hE_meas n).nullMeasurableSet hg'_deriv hg_inj
        have h_ac : Measure.map g μ ≪ volume := by
          intro N hNvol
          let N' : Set ℝ := toMeasurable volume N
          have hN'm : MeasurableSet N' := measurableSet_toMeasurable volume N
          have hN'vol : volume N' = 0 := by rw [measure_toMeasurable]; exact hNvol
          have hNrestrict : (volume.restrict (g '' E n)) N' = 0 := by
            rw [Measure.restrict_apply hN'm]
            exact measure_mono_null (fun _ hy => hy.1) hN'vol
          have hwd : (μ.withDensity w) (g ⁻¹' N') = 0 := by
            rw [← Measure.map_apply_of_aemeasurable hg_ae_w hN'm, hmap]
            exact hNrestrict
          have hmu : μ (g ⁻¹' N') = 0 := hac_mu hwd
          have hmapN' : (Measure.map g μ) N' = μ (g ⁻¹' N') :=
            Measure.map_apply_of_aemeasurable hg_ae_mu hN'm
          exact measure_mono_null (subset_toMeasurable volume N) (by rw [hmapN', hmu])
        refine ⟨(Measure.map g μ).rnDeriv volume, Measure.measurable_rnDeriv _ _, ?_⟩
        exact (Measure.withDensity_rnDeriv_eq (Measure.map g μ) volume h_ac).symm
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      refine ⟨0, measurable_const, ?_⟩
      simp [hne]
  choose ρ_seq hρ_meas hρ_eq using h_piece
  have hg_aemeas : AEMeasurable g (volume.restrict U) :=
    hg.continuousOn.aemeasurable hU.measurableSet
  refine ⟨∑' n : ℕ, ρ_seq n, ?_⟩
  have hg_aemeas_sum : AEMeasurable g (Measure.sum fun n : ℕ => volume.restrict (E n)) := by
    rwa [← Measure.restrict_iUnion hE_disj hE_meas, ← hU_union]
  rw [hU_union, Measure.restrict_iUnion hE_disj hE_meas, Measure.map_sum hg_aemeas_sum]
  simp_rw [hρ_eq]
  exact (MeasureTheory.withDensity_tsum hρ_meas).symm

private lemma stageSpacing_pos' (m : ℕ) : 0 < stageSpacing m := by
  dsimp [stageSpacing, stageLinearSize]
  positivity

private lemma stagePeriodicSide_ge_two (m : ℕ) : 2 ≤ stagePeriodicSide m := by
  change 2 ≤ (m + 2) ^ 2
  have h2 : 2 ≤ m + 2 := by omega
  have h4 : 2 ^ 2 ≤ (m + 2) ^ 2 := Nat.pow_le_pow_left h2 2
  omega

private lemma stagePeriodicSide_tendsto_atTop :
    Filter.Tendsto stagePeriodicSide Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun m hm => ?_⟩
  change b ≤ (m + 2) ^ 2
  nlinarith

private lemma stageFrequency_succ_pos (N : ℕ) (hN : 2 ≤ N)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (m : ℕ) :
    0 < stageFrequency N hN submersion_1d (m + 1) := by
  classical
  by_contra h_not_pos
  have hK0 : stageFrequency N hN submersion_1d (m + 1) = 0 := Nat.eq_zero_of_not_pos h_not_pos
  let L := stagePeriodicSide (m + 1)
  let a := stageSpacing (m + 1)
  have ha : 0 < a := stageSpacing_pos' (m + 1)
  let v0 : (cubicTorus4 L L).Site := stageSiteMap L L a ha (0 : Space4)
  let t : stageMomentIndex (m + 1) :=
    ⟨⟨1, by omega⟩, (⟨fun _ => v0, fun i j _ => Subsingleton.elim i j⟩, fun _ => ⟨1, by omega⟩)⟩
  have hspec := stageFrequency_spec N hN submersion_1d (m + 1) t
  rw [hK0] at hspec
  have hAC := wilson_plaquette_absolutelyContinuous L L N ((m + 1 : ℕ) : ℝ)
    (Nat.cast_nonneg _) hN (stagePeriodicSide_ge_two (m + 1)) submersion_1d
    (stageSiteMap L L a ha (stageSitePoint L L a v0))
  have hpush := stageObservable_pushforward_eq_uniform_orientation L L N ((m + 1 : ℕ) : ℝ)
    (Nat.cast_nonneg _) a ha (stageSitePoint L L a v0) 0 hAC
  have h_val_one :
      ∫ U, stageObservable L L N ((m + 1 : ℕ) : ℝ) (Nat.cast_nonneg _) a ha
          (stageSitePoint L L a v0) 0 U ∂(wilsonMeasure L L N ((m + 1 : ℕ) : ℝ)) = 1 := by
    calc
      ∫ U, stageObservable L L N ((m + 1 : ℕ) : ℝ) (Nat.cast_nonneg _) a ha
            (stageSitePoint L L a v0) 0 U ∂(wilsonMeasure L L N ((m + 1 : ℕ) : ℝ))
          = ∫ y : ℝ, y ∂((wilsonMeasure L L N ((m + 1 : ℕ) : ℝ)).map
              (fun U => stageObservable L L N ((m + 1 : ℕ) : ℝ) (Nat.cast_nonneg _) a ha
                (stageSitePoint L L a v0) 0 U)) := by
              symm
              exact MeasureTheory.integral_map
                (measurable_stageObservable L L N ((m + 1 : ℕ) : ℝ) (Nat.cast_nonneg _) a ha
                  (stageSitePoint L L a v0) 0).aemeasurable
                continuous_id.measurable.aestronglyMeasurable
      _ = ∫ y : ℝ, y ∂((volume.restrict (Set.Ico (0 : ℝ) 1)).map (fourierOrientation 0)) := by
            rw [hpush]
      _ = ∫ u in Set.Ico (0 : ℝ) 1, fourierOrientation 0 u := by
            exact MeasureTheory.integral_map
              (measurable_fourierOrientation 0).aemeasurable
              continuous_id.measurable.aestronglyMeasurable
      _ = ∫ _u in Set.Ico (0 : ℝ) 1, (1 : ℝ) := by
            refine setIntegral_congr_fun measurableSet_Ico fun u hu => ?_
            have hfl : Int.floor u = 0 :=
              Int.floor_eq_iff.mpr ⟨by simpa using hu.1, by simpa using hu.2⟩
            simp [fourierOrientation, rademacher, hfl]
            norm_num
      _ = 1 := by simp
  have h_val_eq :
      (∫ U, ∏ i : Fin 1,
        (stageObservable L L N ((m + 1 : ℕ) : ℝ) (Nat.cast_nonneg _) a ha
          (stageSitePoint L L a v0) 0 U) ^ 1
        ∂(wilsonMeasure L L N ((m + 1 : ℕ) : ℝ))) = 1 := by
    simpa only [Fin.prod_univ_one, pow_one] using h_val_one
  have h_lim_eq : (∏ _i : Fin 1, ((1 : ℝ) ^ 1 + (2 : ℝ) ^ 1) / 2) = (3 / 2 : ℝ) := by
    simp; norm_num
  change dist
      (∫ U, ∏ i : Fin 1,
        (stageObservable L L N ((m + 1 : ℕ) : ℝ) (Nat.cast_nonneg _) a ha
          (stageSitePoint L L a v0) 0 U) ^ 1
        ∂(wilsonMeasure L L N ((m + 1 : ℕ) : ℝ)))
      (∏ _i : Fin 1, ((1 : ℝ) ^ 1 + (2 : ℝ) ^ 1) / 2) < 1 / ((m + 1 : ℕ) + 1 : ℝ) at hspec
  rw [h_val_eq, h_lim_eq, Real.dist_eq] at hspec
  have h_half : (1 / 2 : ℝ) ≤ |1 - (3 / 2 : ℝ)| := by norm_num
  have h_rhs : (1 / ((m + 1 : ℕ) + 1 : ℝ)) ≤ 1 / 2 := by
    have hm2 : (2 : ℝ) ≤ ((m + 1 : ℕ) + 1 : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ (m + 1) + 1)
    exact one_div_le_one_div_of_le (by norm_num) hm2
  linarith

/-- Concrete Balaban RG continuum hypothesis from the stage limit. -/
noncomputable def iidBalabanHypothesis (N : ℕ) (hN : 2 ≤ N) :
    BalabanRGContinuumHypothesis N hN :=
  let Ls_seq : ℕ → ℕ := fun m => stagePeriodicSide (m + 1)
  let β_seq : ℕ → ℝ := fun m => ((m + 1 : ℕ) : ℝ)
  let a_seq : ℕ → ℝ := fun m => stageSpacing (m + 1)
  let K_seq : ℕ → ℕ := fun m => stageFrequency N hN submersion_1d_absolutely_continuous (m + 1)
  let obs := stageObservable_latticeSinglePointObs N Ls_seq Ls_seq β_seq a_seq K_seq hN
    (fun m => stagePeriodicSide_ge_two (m + 1)) submersion_1d_absolutely_continuous
    (fun m => Nat.cast_nonneg (m + 1)) (fun m => stageSpacing_pos' (m + 1))
    (fun m => stageFrequency_succ_pos N hN submersion_1d_absolutely_continuous m)
  { Δ_phys := 1
    os := iidOS4DStrict
    non_gaussian := fun hG =>
      let ⟨xs, hxs⟩ := iidSchwinger_non_gaussian
      hxs (isGaussian4_connected4_zero iidOS4DStrict.os.Schwinger hG xs)
    Ls_seq := Ls_seq
    Lt_seq := Ls_seq
    Ls_lim := stagePeriodicSide_tendsto_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    Lt_lim := stagePeriodicSide_tendsto_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    β_seq := β_seq
    hβ_nn := fun m => Nat.cast_nonneg (m + 1)
    hβ_lim := tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    obs := obs
    schwinger_conv := fun n xs =>
      (stageObservableSchwinger_tendsto_iid N hN submersion_1d_absolutely_continuous n xs).comp
        (Filter.tendsto_add_atTop_nat 1) }

/-- Strengthened target with explicit OS completion witness. -/
noncomputable def strictClayFromStage (N : ℕ) (hN : 2 ≤ N) :
    ClayYangMillsMassGap4DStrictOnOSCompletion N hN :=
  clay_yang_mills_strict_on_os_completion_from_balaban_and_os N hN
    (iidBalabanHypothesis N hN) iidOSPoincareContinuation

/-- Basic strict target (without completion witness). -/
noncomputable def strictClayBasicFromStage (N : ℕ) (hN : 2 ≤ N) :
    ClayYangMillsMassGap4DStrict N hN :=
  clay_yang_mills_strict_from_balaban_and_os N hN
    (iidBalabanHypothesis N hN) iidOSPoincareContinuation

end YangMills
