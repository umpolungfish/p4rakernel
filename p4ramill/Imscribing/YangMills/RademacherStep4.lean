/-
  Step 4 of the unconditional-closure blueprint: L¹ joint density after the
  probability integral transform.  Standard axioms only.
-/
import Mathlib

set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter

noncomputable section
namespace YangMills

lemma step4_annihilate_1d (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν_ac : ν ≪ volume)
    (F : ℝ → ℝ) (hF_meas : Measurable F)
    (hF_push : Measure.map F ν = volume.restrict (Set.Icc (0 : ℝ) 1))
    (A : Set ℝ) (hA_meas : MeasurableSet A)
    (hA_vol : (volume.restrict (Set.Icc (0 : ℝ) 1)) A = 0) :
    volume (F ⁻¹' A ∩ {t | ν.rnDeriv volume t ≠ 0}) = 0 := by
  have hν_eq : ν = volume.withDensity (ν.rnDeriv volume) := by
    exact (Measure.withDensity_rnDeriv_eq ν volume hν_ac).symm
  have hνpre : ν (F ⁻¹' A) = 0 := by
    rw [← Measure.map_apply hF_meas hA_meas, hF_push]
    exact hA_vol
  have hwd : (volume.withDensity (ν.rnDeriv volume)) (F ⁻¹' A) = 0 := by
    rwa [← hν_eq]
  rw [withDensity_apply _ (hA_meas.preimage hF_meas)] at hwd
  have hmeas_rn : Measurable (ν.rnDeriv volume) := Measure.measurable_rnDeriv ν volume
  have hae : (ν.rnDeriv volume) =ᵐ[volume.restrict (F ⁻¹' A)] (fun _ => (0 : ℝ≥0∞)) :=
    (lintegral_eq_zero_iff hmeas_rn).mp (by simpa using hwd)
  have hz := ae_iff.mp hae
  have hmeas_ne : MeasurableSet {t | ν.rnDeriv volume t ≠ 0} :=
    hmeas_rn (measurableSet_singleton 0).compl
  rw [Measure.restrict_apply hmeas_ne] at hz
  simpa [Set.inter_comm] using hz

lemma step4_annihilate_nd (r : ℕ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν_ac : ν ≪ volume)
    (F : ℝ → ℝ) (hF_meas : Measurable F)
    (hF_push : Measure.map F ν = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    ∀ (E : Set (Fin r → ℝ)), MeasurableSet E →
      (volume.restrict (Set.pi Set.univ (fun _ : Fin r => Set.Icc (0 : ℝ) 1))) E = 0 →
      volume ((fun x : Fin r → ℝ => fun j => F (x j)) ⁻¹' E ∩
        Set.pi Set.univ (fun _ : Fin r =>
          {t : ℝ | ν.rnDeriv volume t ≠ 0} ∩ F ⁻¹' Set.Icc (0 : ℝ) 1)) = 0 := by
  induction r with
  | zero =>
      intro E hE hvol
      have hpi : Set.pi Set.univ (fun _ : Fin 0 => Set.Icc (0 : ℝ) 1) = Set.univ := by
        ext x; simp
      rw [hpi, Measure.restrict_univ] at hvol
      have hdir : (volume : Measure (Fin 0 → ℝ)) =
          Measure.dirac (fun i : Fin 0 => isEmptyElim i) := by
        rw [volume_pi]; exact Measure.pi_of_empty _
      have hnot : (fun i : Fin 0 => isEmptyElim i) ∉ E := by
        intro hm
        have hone : (Measure.dirac (fun i : Fin 0 => isEmptyElim i)) E = 1 := by simp [hm]
        rw [← hdir] at hone
        rw [hone] at hvol
        norm_num at hvol
      have hpre : (fun x : Fin 0 → ℝ => fun j : Fin 0 => F (x j)) ⁻¹' E = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro hx
        apply hnot
        simpa only [Subsingleton.elim (fun j : Fin 0 => F (x j))
          (fun i : Fin 0 => isEmptyElim i)] using hx
      rw [hpre, Set.empty_inter, measure_empty]
  | succ r ih =>
      intro E hE hvol
      let Gr : Set ℝ := {t | ν.rnDeriv volume t ≠ 0} ∩ F ⁻¹' Set.Icc (0 : ℝ) 1
      let Gprod : Set (Fin r → ℝ) := Set.pi Set.univ (fun _ : Fin r => Gr)
      let Tr : Set (Fin r → ℝ) := Set.pi Set.univ (fun _ : Fin r => Set.Icc (0 : ℝ) 1)
      let T : Set (Fin (r + 1) → ℝ) :=
        Set.pi Set.univ (fun _ : Fin (r + 1) => Set.Icc (0 : ℝ) 1)
      let Tprod : Set ((Fin r → ℝ) × ℝ) := Tr ×ˢ Set.Icc (0 : ℝ) 1
      let e0 : (Fin (r + 1) → ℝ) ≃ᵐ (Fin r → ℝ) × ℝ :=
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r)).trans
          MeasurableEquiv.prodComm
      have he0_mp : MeasurePreserving e0 (volume : Measure (Fin (r + 1) → ℝ))
          (volume : Measure ((Fin r → ℝ) × ℝ)) :=
        Measure.measurePreserving_swap.comp
          (volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) (Fin.last r))
      let Γr : (Fin r → ℝ) → (Fin r → ℝ) := fun y j => F (y j)
      let Γp : (Fin r → ℝ) × ℝ → (Fin r → ℝ) × ℝ := fun p => (Γr p.1, F p.2)
      let Γ : (Fin (r + 1) → ℝ) → (Fin (r + 1) → ℝ) := fun x j => F (x j)
      have hΓcomp : e0 ∘ Γ = Γp ∘ e0 := by
        funext x
        ext
        · rename_i j
          dsimp [e0, Γp, Γr, Γ, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
          simp [Fin.init]
        · dsimp [e0, Γp, Γr, Γ, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
      let S : Set ((Fin r → ℝ) × ℝ) := e0 '' (T ∩ E)
      have hTm : MeasurableSet T := by
        change MeasurableSet (Set.pi Set.univ (fun _ : Fin (r + 1) => Set.Icc (0 : ℝ) 1))
        exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
      have hTm0 : MeasurableSet Tr := by
        dsimp [Tr]
        exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
      have hTprod : MeasurableSet Tprod := by
        exact hTm0.prod measurableSet_Icc
      have hSm : MeasurableSet S := (e0.measurableSet_image).mpr (hTm.inter hE)
      have hpreS : e0 ⁻¹' S = T ∩ E := by
        ext x; simp [S]
      have hSvol0 : (volume : Measure ((Fin r → ℝ) × ℝ)) S = 0 := by
        have hmap : (Measure.map e0 (volume : Measure (Fin (r + 1) → ℝ))) S = 0 := by
          rw [Measure.map_apply e0.measurable hSm]
          rw [hpreS]
          have hnull : (volume : Measure (Fin (r + 1) → ℝ)) (T ∩ E) = 0 := by
            simpa [Measure.restrict_apply hTm, T, Set.inter_comm] using hvol
          exact hnull
        rw [he0_mp.map_eq] at hmap
        exact hmap
      have hSvol : (volume.restrict Tprod) S = 0 := by
        rw [Measure.restrict_apply hSm]
        exact measure_mono_null (inter_subset_left) hSvol0
      let B₀ : Set (Fin r → ℝ) :=
        {y | volume {t : ℝ | (y, t) ∈ S} ≠ 0}
      have hB₀meas : MeasurableSet B₀ := by
        exact (measurable_measure_prodMk_left hSm) (measurableSet_singleton 0).compl
      have hB₀vol : volume B₀ = 0 :=
        ae_iff.mp ((Measure.measure_prod_null hSm).mp hSvol0)
      have hihB := ih B₀ hB₀meas (le_antisymm
        (le_trans (Measure.restrict_le_self B₀) (le_of_eq hB₀vol)) (zero_le _))
      have hGr_meas : MeasurableSet Gr := by
        dsimp [Gr]
        exact ((Measure.measurable_rnDeriv ν volume) (measurableSet_singleton 0).compl).inter
          (hF_meas measurableSet_Icc)
      have hprodmeas : MeasurableSet (Γp ⁻¹' S ∩ (Gprod ×ˢ Gr)) :=
        (hSm.preimage (by dsimp [Γp, Γr]; fun_prop)).inter
          ((MeasurableSet.pi Set.countable_univ (fun _ _ => hGr_meas)).prod hGr_meas)
      have hprodzero : ((volume : Measure (Fin r → ℝ)).prod volume)
          (Γp ⁻¹' S ∩ (Gprod ×ˢ Gr)) = 0 := by
        rw [Measure.measure_prod_null hprodmeas]
        have haeB : ∀ᵐ y ∂volume, y ∉ Γr ⁻¹' B₀ ∩ Gprod := by
          rw [ae_iff]
          simpa [B₀] using hihB
        filter_upwards [haeB] with y hyB
        by_cases hyG : y ∈ Gprod
        · have hAyvol : volume {t : ℝ | (Γr y, t) ∈ S} = 0 := by
            have hyNot : Γr y ∉ B₀ := fun h => hyB ⟨h, hyG⟩
            exact not_not.mp (by simpa [B₀] using hyNot)
          have hAyvol' : (volume.restrict (Set.Icc (0 : ℝ) 1))
              {t : ℝ | (Γr y, t) ∈ S} = 0 :=
            le_antisymm (le_trans (Measure.restrict_le_self _) (le_of_eq hAyvol)) (zero_le _)
          have hAymeas : MeasurableSet {t : ℝ | (Γr y, t) ∈ S} :=
            hSm.preimage (measurable_const.prodMk measurable_id)
          have h1d := step4_annihilate_1d ν hν_ac F hF_meas hF_push
            {t : ℝ | (Γr y, t) ∈ S} hAymeas hAyvol'
          change volume (Prod.mk y ⁻¹' (Γp ⁻¹' S ∩ (Gprod ×ˢ Gr))) = 0
          have hslice : Prod.mk y ⁻¹' (Gprod ×ˢ Gr) = Gr := by
            ext t; simp [hyG]
          rw [Set.preimage_inter, hslice]
          have htarget : volume ({t : ℝ | (Γr y, F t) ∈ S} ∩ Gr) = 0 := by
            exact measure_mono_null (by intro t ht; exact ⟨ht.1, ht.2.1⟩) h1d
          simpa [Γp, Γr, Gr] using htarget
        · simp [hyG]

      have himage : e0 '' (Γ ⁻¹' E ∩ Set.pi Set.univ (fun _ : Fin (r + 1) => Gr)) =
          Γp ⁻¹' S ∩ (Gprod ×ˢ Gr) := by
        ext p
        constructor
        · rintro ⟨x, ⟨hxΓ, hxGr⟩, rfl⟩
          refine ⟨?_, ?_, ?_⟩
          · refine ⟨Γ x, ⟨⟨?_, hxΓ⟩, rfl⟩⟩
            intro j hj
            exact (hxGr j (Set.mem_univ j)).2
          · intro j hj
            simpa [e0, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm] using
              hxGr j.castSucc (Set.mem_univ _)
          · simpa [e0, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm] using
              hxGr (Fin.last r) (Set.mem_univ _)
        · rintro ⟨⟨z, ⟨hzT, hzE⟩, hzEq⟩, hpGprod, hpGr⟩
          let x : Fin (r + 1) → ℝ := e0.symm p
          have hxep : e0 x = p := by simp [x]
          have hΓz : Γ x = z := by
            apply e0.injective
            have h1 : Γp (e0 x) = e0 z := by simpa [hxep] using hzEq.symm
            exact (congrFun hΓcomp x).trans h1
          have hxΓmem : x ∈ Γ ⁻¹' E := by
            change Γ x ∈ E
            rw [hΓz]
            exact hzE
          refine ⟨x, ⟨hxΓmem, ?_⟩, ?_⟩
          · intro j hj
            by_cases hlast : j = Fin.last r
            · subst j
              have hh := congrArg Prod.snd hxep
              have hxlast : x (Fin.last r) = p.2 := by
                simpa [e0, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm] using hh
              rw [hxlast]
              exact hpGr
            · have hfst := congrArg Prod.fst hxep
              have hval := congrFun hfst (Fin.castPred j hlast)
              have hxj : x j = p.1 (Fin.castPred j hlast) := by
                simpa [e0, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm, hlast] using hval
              rw [hxj]
              exact hpGprod (Fin.castPred j hlast) (Set.mem_univ _)
          · simp [x]
      have hmainmeas : MeasurableSet (Γ ⁻¹' E ∩ Set.pi Set.univ (fun _ : Fin (r + 1) => Gr)) :=
        (hE.preimage (by dsimp [Γ]; fun_prop)).inter
          (MeasurableSet.pi Set.countable_univ (fun _ _ => hGr_meas))
      let A : Set (Fin (r + 1) → ℝ) :=
        Γ ⁻¹' E ∩ Set.pi Set.univ (fun _ : Fin (r + 1) => Gr)
      have hvolA : (volume : Measure (Fin (r + 1) → ℝ)) A = 0 := by
        have hpre : e0 ⁻¹' (e0 '' A) = A := by ext x; simp [A]
        have htmp2 : (volume : Measure (Fin (r + 1) → ℝ)) (e0 ⁻¹' (e0 '' A)) = 0 := by
          rw [← Measure.map_apply e0.measurable ((e0.measurableSet_image).mpr hmainmeas)]
          rw [he0_mp.map_eq]
          have ht := hprodzero
          rw [← himage] at ht
          exact ht
        rwa [hpre] at htmp2
      exact hvolA



/-- Step 4: the coordinatewise-transformed law is absolutely continuous. -/
lemma step4_map_absolutelyContinuous (r : ℕ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν_ac : ν ≪ volume)
    (F : ℝ → ℝ) (hF_meas : Measurable F)
    (hF_push : Measure.map F ν = volume.restrict (Set.Icc (0 : ℝ) 1))
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ] (hμ_ac : μ ≪ volume)
    (h_marg : ∀ j : Fin r, Measure.map (fun x => x j) μ = ν) :
    (μ.map (fun x j => F (x j))) ≪ (volume : Measure (Fin r → ℝ)) := by
  let G : Set ℝ := {t | ν.rnDeriv volume t ≠ 0} ∩ F ⁻¹' Set.Icc (0 : ℝ) 1
  have hG_meas : MeasurableSet G := by
    dsimp [G]
    exact ((Measure.measurable_rnDeriv ν volume) (measurableSet_singleton 0).compl).inter
      (hF_meas measurableSet_Icc)
  have hν_eq : ν = volume.withDensity (ν.rnDeriv volume) :=
    (Measure.withDensity_rnDeriv_eq ν volume hν_ac).symm
  have hν_zero : ν {t | ν.rnDeriv volume t = 0} = 0 := by
    have hset : {a | ¬ ν.rnDeriv volume a ≠ 0} = {t | ν.rnDeriv volume t = 0} := by
      ext t; simp
    rw [← hset]
    exact ae_iff.mp (by
      filter_upwards [Measure.rnDeriv_pos hν_ac] with t ht
      exact ne_of_gt ht)
  have hIcc_compl : MeasurableSet (F ⁻¹' Set.Icc (0 : ℝ) 1)ᶜ :=
    (hF_meas measurableSet_Icc).compl
  have hν_Icc : ν (F ⁻¹' Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    have hs : MeasurableSet (Set.Icc (0 : ℝ) 1)ᶜ := measurableSet_Icc.compl
    have hpre : F ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ = (F ⁻¹' Set.Icc (0 : ℝ) 1)ᶜ := by
      ext t; simp
    rw [← hpre, ← Measure.map_apply hF_meas hs, hF_push]
    simp
  have hν_Gc : ν Gᶜ = 0 := by
    have hsub : Gᶜ ⊆ {t | ν.rnDeriv volume t = 0} ∪ (F ⁻¹' Set.Icc (0 : ℝ) 1)ᶜ := by
      intro t ht
      by_cases h1 : ν.rnDeriv volume t = 0
      · exact Or.inl h1
      · right
        intro h2
        exact ht ⟨h1, h2⟩
    exact measure_mono_null hsub (measure_union_null hν_zero hν_Icc)
  have hμ_Gc : μ {x | x ∉ Set.pi Set.univ (fun _ : Fin r => G)} = 0 := by
    have hsub : {x | x ∉ Set.pi Set.univ (fun _ : Fin r => G)} ⊆
        ⋃ j : Fin r, {x | x j ∉ G} := by
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hx ⊢
      simp only [Set.mem_pi, Set.mem_univ, forall_const] at hx
      push_neg at hx
      obtain ⟨j, hj⟩ := hx
      exact ⟨j, hj⟩
    refine measure_mono_null hsub ?_
    rw [measure_iUnion_null]
    intro j
    have hmeas : MeasurableSet {x : Fin r → ℝ | x j ∉ G} :=
      hG_meas.compl.preimage (measurable_pi_apply j)
    have hpre : (fun x : Fin r → ℝ => x j) ⁻¹' Gᶜ = {x | x j ∉ G} := rfl
    rw [← hpre, ← Measure.map_apply (measurable_pi_apply j) hG_meas.compl, h_marg j]
    exact hν_Gc
  let Γ : (Fin r → ℝ) → (Fin r → ℝ) := fun x j => F (x j)
  have hΓmeas : Measurable Γ := by
    rw [measurable_pi_iff]; intro j; exact hF_meas.comp (measurable_pi_apply j)
  refine Measure.AbsolutelyContinuous.mk ?_
  intro S hS hSvol
  rw [Measure.map_apply hΓmeas hS]
  let A : Set (Fin r → ℝ) := Γ ⁻¹' S
  have hAmeas : MeasurableSet A := hS.preimage hΓmeas
  have hdecomp : μ A = μ (A ∩ Set.pi Set.univ (fun _ : Fin r => G)) := by
    have hdiff : μ (A ∩ (Set.pi Set.univ (fun _ : Fin r => G))ᶜ) = 0 :=
      measure_mono_null (inter_subset_right) hμ_Gc
    have hpi_meas : MeasurableSet (Set.pi Set.univ (fun _ : Fin r => G)) :=
      MeasurableSet.pi Set.countable_univ (fun _ _ => hG_meas)
    have hunion : A = (A ∩ Set.pi Set.univ (fun _ : Fin r => G)) ∪
        (A ∩ (Set.pi Set.univ (fun _ : Fin r => G))ᶜ) := by
      ext x; by_cases hx : x ∈ Set.pi Set.univ (fun _ : Fin r => G) <;> simp [hx]
    have hdisj : Disjoint (A ∩ Set.pi Set.univ (fun _ : Fin r => G))
        (A ∩ (Set.pi Set.univ (fun _ : Fin r => G))ᶜ) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1.2
    calc
      μ A = μ ((A ∩ Set.pi Set.univ (fun _ : Fin r => G)) ∪
          (A ∩ (Set.pi Set.univ (fun _ : Fin r => G))ᶜ)) := by rw [← hunion]
      _ = μ (A ∩ Set.pi Set.univ (fun _ : Fin r => G)) +
            μ (A ∩ (Set.pi Set.univ (fun _ : Fin r => G))ᶜ) := by
          rw [measure_union hdisj (hAmeas.inter hpi_meas.compl)]
      _ = μ (A ∩ Set.pi Set.univ (fun _ : Fin r => G)) := by rw [hdiff, add_zero]
  rw [hdecomp]
  apply hμ_ac
  apply step4_annihilate_nd r ν hν_ac F hF_meas hF_push
  · exact hS
  · exact le_antisymm (le_trans (Measure.restrict_le_self S) (le_of_eq hSvol)) (zero_le _)


/-- Step 4 conclusion: the transformed law has an L¹ density. -/
theorem step4_L1_density (r : ℕ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν_ac : ν ≪ volume)
    (F : ℝ → ℝ) (hF_meas : Measurable F)
    (hF_push : Measure.map F ν = volume.restrict (Set.Icc (0 : ℝ) 1))
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ] (hμ_ac : μ ≪ volume)
    (h_marg : ∀ j : Fin r, Measure.map (fun x => x j) μ = ν) :
    let ρ : (Fin r → ℝ) → ℝ≥0∞ := (μ.map (fun x j => F (x j))).rnDeriv volume
    Integrable (fun x => (ρ x).toReal) volume ∧
      volume.withDensity ρ = μ.map (fun x j => F (x j)) := by
  let ρ : (Fin r → ℝ) → ℝ≥0∞ := (μ.map (fun x j => F (x j))).rnDeriv volume
  have hac := step4_map_absolutelyContinuous r ν hν_ac F hF_meas hF_push μ hμ_ac h_marg
  have hwd : volume.withDensity ρ = μ.map (fun x j => F (x j)) := by
    exact Measure.withDensity_rnDeriv_eq _ _ hac
  have hlin : (∫⁻ x, ρ x ∂volume) ≠ ⊤ := by
    have hval : (∫⁻ x, ρ x ∂volume) = (μ.map (fun x j => F (x j))) Set.univ := by
      rw [← hwd, withDensity_apply _ MeasurableSet.univ]
      simp
    rw [hval]
    simp
  exact ⟨integrable_toReal_of_lintegral_ne_top
    (Measure.measurable_rnDeriv _ _).aemeasurable hlin, hwd⟩

end YangMills
