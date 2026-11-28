
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Imscribing.YangMills.WilsonHaarCompactness4D

/-!
# Canonical Product Haar Probability Measure on 4D SU(N) Link Configurations
-/

noncomputable section

namespace Imscribing.YangMills.CanonicalHaar4D

open MeasureTheory
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonMeasure4D

private lemma gaugeGroup_coe_inv_star {N : ℕ} (A : GaugeGroup N) :
    ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = star (A : Matrix (Fin N) (Fin N) ℂ) := by
  have h1 : (A : Matrix (Fin N) (Fin N) ℂ) * ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    change ((A * A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = 1
    simp
  have h2 : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp A.prop).1
  calc ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)
      = (star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ)) *
          ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) := by rw [h2, Matrix.one_mul]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) *
          ((A : Matrix (Fin N) (Fin N) ℂ) * ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)) := by
          rw [Matrix.mul_assoc]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) := by rw [h1, Matrix.mul_one]

private def gaugeGroupTopologicalGroup (N : ℕ) : IsTopologicalGroup (GaugeGroup N) where
  continuous_mul := by
    refine Continuous.subtype_mk ?_ _
    exact Continuous.mul (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    have h_eq : (fun A : GaugeGroup N => ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)) =
        fun A : GaugeGroup N => star (A : Matrix (Fin N) (Fin N) ℂ) := funext gaugeGroup_coe_inv_star
    simpa [h_eq] using continuous_star.comp continuous_subtype_val

private noncomputable def gaugePosCompact (N : ℕ) :
    TopologicalSpace.PositiveCompacts (GaugeGroup N) :=
  letI : CompactSpace (GaugeGroup N) := compactSpace_gaugeGroup N
  ⟨⟨Set.univ, isCompact_univ⟩, by
    change (interior (Set.univ : Set (GaugeGroup N))).Nonempty
    rw [interior_univ]; exact ⟨1, Set.mem_univ _⟩⟩

private noncomputable def suHaar (N : ℕ) :
    letI := borel (GaugeGroup N)
    Measure (GaugeGroup N) :=
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : CompactSpace (GaugeGroup N) := compactSpace_gaugeGroup N
  haveI : IsTopologicalGroup (GaugeGroup N) := gaugeGroupTopologicalGroup N
  Measure.haarMeasure (gaugePosCompact N)

private lemma suHaar_isProbability (N : ℕ) :
    letI := borel (GaugeGroup N)
    @IsProbabilityMeasure (GaugeGroup N) _ (suHaar N) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : CompactSpace (GaugeGroup N) := compactSpace_gaugeGroup N
  haveI : IsTopologicalGroup (GaugeGroup N) := gaugeGroupTopologicalGroup N
  refine ⟨?_⟩
  unfold suHaar
  have h : Measure.haarMeasure (gaugePosCompact N) (gaugePosCompact N : Set (GaugeGroup N)) = 1 :=
    Measure.haarMeasure_self
  simpa [gaugePosCompact] using h

/-- Canonical product Haar probability measure on `LinkConfig N L = Lat4 L → Fin 4 → SU(N)`. -/
noncomputable def wilsonHaarLinkMeasure (N L : ℕ) [NeZero L] :
    letI := borel (GaugeGroup N)
    Measure (LinkConfig N L) :=
  letI := borel (GaugeGroup N)
  haveI : IsProbabilityMeasure (suHaar N) := suHaar_isProbability N
  Measure.pi (fun _ : Lat4 L => Measure.pi (fun _ : Fin 4 => suHaar N))

theorem wilsonHaarLinkMeasure_isProbability (N L : ℕ) [NeZero L] :
    letI := borel (GaugeGroup N)
    @IsProbabilityMeasure (LinkConfig N L) _ (wilsonHaarLinkMeasure N L) := by
  letI := borel (GaugeGroup N)
  haveI : IsProbabilityMeasure (suHaar N) := suHaar_isProbability N
  haveI : ∀ _ : Lat4 L,
      IsProbabilityMeasure (Measure.pi (fun _ : Fin 4 => (suHaar N : Measure (GaugeGroup N)))) :=
    fun _ => inferInstance
  unfold wilsonHaarLinkMeasure
  exact inferInstance

private lemma suHaar_left_right_mul_eq (N : ℕ) (a b : GaugeGroup N) :
    letI := borel (GaugeGroup N)
    Measure.map (fun u : GaugeGroup N => a * u * b) (suHaar N) = suHaar N := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : CompactSpace (GaugeGroup N) := compactSpace_gaugeGroup N
  haveI : IsTopologicalGroup (GaugeGroup N) := gaugeGroupTopologicalGroup N
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  haveI : SecondCountableTopology (GaugeGroup N) :=
    Topology.IsInducing.secondCountableTopology
      (⟨rfl⟩ : Topology.IsInducing (Subtype.val : GaugeGroup N → Matrix (Fin N) (Fin N) ℂ))
  haveI : MeasurableMul₂ (GaugeGroup N) := ContinuousMul.measurableMul₂
  haveI : IsProbabilityMeasure (suHaar N) := suHaar_isProbability N
  have h1 : (fun u : GaugeGroup N => a * u * b) =
      (fun v : GaugeGroup N => v * b) ∘ (fun u : GaugeGroup N => a * u) := rfl
  have hm1 : Measurable (fun u : GaugeGroup N => a * u) := measurable_const.mul measurable_id
  have hm2 : Measurable (fun v : GaugeGroup N => v * b) := measurable_id.mul measurable_const
  have hL : Measure.map (fun u : GaugeGroup N => a * u) (suHaar N) = suHaar N := by
    unfold suHaar
    have hinv : (Measure.haarMeasure (gaugePosCompact N)).IsMulLeftInvariant := inferInstance
    exact hinv.map_mul_left_eq_self a
  have hR : Measure.map (fun v : GaugeGroup N => v * b) (suHaar N) = suHaar N := by
    haveI : (suHaar N).IsHaarMeasure := by
      unfold suHaar; exact Measure.isHaarMeasure_haarMeasure _
    haveI : (Measure.map (fun v : GaugeGroup N => v * b) (suHaar N)).IsHaarMeasure := inferInstance
    have h_univ : Measure.map (fun v : GaugeGroup N => v * b) (suHaar N) Set.univ = 1 := by
      rw [Measure.map_apply hm2 MeasurableSet.univ, Set.preimage_univ]
      exact measure_univ
    have h_uniq := Measure.haarMeasure_unique
      (Measure.map (fun v : GaugeGroup N => v * b) (suHaar N)) (gaugePosCompact N)
    unfold suHaar
    simpa [gaugePosCompact, h_univ] using h_uniq
  rw [h1, ← Measure.map_map hm2 hm1, hL, hR]

/-- **Gauge Invariance of `wilsonHaarLinkMeasure`:** -/
theorem wilsonHaar_gaugeInvariant (N L : ℕ) [NeZero L] (g : GaugeTransform N L) :
    letI := borel (GaugeGroup N)
    Measure.map (applyGauge g) (wilsonHaarLinkMeasure N L) = wilsonHaarLinkMeasure N L := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : CompactSpace (GaugeGroup N) := compactSpace_gaugeGroup N
  haveI : IsTopologicalGroup (GaugeGroup N) := gaugeGroupTopologicalGroup N
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  haveI : SecondCountableTopology (GaugeGroup N) :=
    Topology.IsInducing.secondCountableTopology
      (⟨rfl⟩ : Topology.IsInducing (Subtype.val : GaugeGroup N → Matrix (Fin N) (Fin N) ℂ))
  haveI : MeasurableMul₂ (GaugeGroup N) := ContinuousMul.measurableMul₂
  haveI : IsProbabilityMeasure (suHaar N) := suHaar_isProbability N
  haveI : ∀ _ : Lat4 L,
      IsProbabilityMeasure (Measure.pi (fun _ : Fin 4 => (suHaar N : Measure (GaugeGroup N)))) :=
    fun _ => inferInstance
  haveI : IsProbabilityMeasure (wilsonHaarLinkMeasure N L) := wilsonHaarLinkMeasure_isProbability N L
  have hg_meas : Measurable (applyGauge g) := by
    refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun μ => ?_
    exact (measurable_const.mul ((measurable_pi_apply μ).comp
      (measurable_pi_apply x : Measurable fun U : LinkConfig N L => U x))).mul measurable_const
  unfold wilsonHaarLinkMeasure
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hg_meas (MeasurableSet.univ_pi hs)]
  let s' : Lat4 L → Set (Fin 4 → GaugeGroup N) := fun x =>
    (fun (f : Fin 4 → GaugeGroup N) (μ : Fin 4) =>
      g x * f μ * (g (x + stepDir L μ))⁻¹) ⁻¹' s x
  have hpre : applyGauge g ⁻¹' Set.pi Set.univ s = Set.pi Set.univ s' := by
    ext U; simp only [Set.mem_preimage, Set.mem_univ_pi]; rfl
  rw [hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun x _ => ?_
  let φx : (Fin 4 → GaugeGroup N) → (Fin 4 → GaugeGroup N) := fun f μ =>
    g x * f μ * (g (x + stepDir L μ))⁻¹
  have hφx_meas : Measurable φx :=
    measurable_pi_lambda _ fun μ => (measurable_const.mul (measurable_pi_apply μ)).mul measurable_const
  have h_eq_map : Measure.map φx (Measure.pi (fun _ : Fin 4 => (suHaar N : Measure (GaugeGroup N)))) =
      Measure.pi (fun _ : Fin 4 => (suHaar N : Measure (GaugeGroup N))) := by
    symm
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.map_apply hφx_meas (MeasurableSet.univ_pi ht)]
    have hpre_t : φx ⁻¹' Set.pi Set.univ t =
        Set.pi Set.univ (fun μ => (fun u => g x * u * (g (x + stepDir L μ))⁻¹) ⁻¹' t μ) := by
      ext f; simp [φx]
    rw [hpre_t, Measure.pi_pi]
    refine Finset.prod_congr rfl fun μ _ => ?_
    have hm_link : Measurable (fun u : GaugeGroup N => g x * u * (g (x + stepDir L μ))⁻¹) :=
      (measurable_const.mul measurable_id).mul measurable_const
    rw [← Measure.map_apply hm_link (ht μ), suHaar_left_right_mul_eq]
  have h_res : (Measure.pi (fun _ : Fin 4 => (suHaar N : Measure (GaugeGroup N)))) (s' x) =
      (Measure.pi (fun _ : Fin 4 => (suHaar N : Measure (GaugeGroup N)))) (s x) := by
    change (Measure.pi (fun _ : Fin 4 => (suHaar N : Measure (GaugeGroup N)))) (φx ⁻¹' s x) = _
    rw [← Measure.map_apply hφx_meas (hs x), h_eq_map]
  first | exact h_res | exact h_res.symm

end Imscribing.YangMills.CanonicalHaar4D