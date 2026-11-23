/-
  Imscribing/YangMills/SubmersionDensity.lean

  Submersion-to-density rung.  A C^1 injection whose derivative is invertible on a
  measurable set `s` pushes restricted Lebesgue measure forward to a measure that
  is absolutely continuous w.r.t. Lebesgue; Radon--Nikodym then supplies a density.
  For a local submersion this is the local model of the joint-density map.

  Built from Mathlib's Jacobian change-of-variables formula and the
  Radon--Nikodym theorem.  Standard axioms only.
-/
import Mathlib
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Covering.Differentiation

set_option maxHeartbeats 8000000

open MeasureTheory Filter Set
open scoped ENNReal

namespace YangMills

/-- Restricted Lebesgue is absolutely continuous w.r.t. its Jacobian weighting
whenever the Jacobian determinant is nonzero on the set. -/
lemma restrict_ac_jacWeight {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (f' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    (s : Set (Fin n → ℝ)) (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf_det : ∀ x ∈ s, (f' x).det ≠ 0) :
    (volume : Measure (Fin n → ℝ)).restrict s ≪
      ((volume : Measure (Fin n → ℝ)).restrict s).withDensity
        (fun x => ENNReal.ofReal |(f' x).det|) := by
  let w : (Fin n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal |(f' x).det|
  apply withDensity_absolutelyContinuous'
  · exact aemeasurable_ofReal_abs_det_fderivWithin
      (μ := (volume : Measure (Fin n → ℝ))) hs hf'
  · filter_upwards [ae_restrict_mem hs] with x hx
    intro hzero
    exact (not_le.mpr (abs_pos.mpr (hf_det x hx))) (ENNReal.ofReal_eq_zero.mp hzero)

/-- **Submersion ⇒ L¹ joint density.**  If `f` is injective and `C¹` with invertible
derivative on a measurable set `s`, then `f` pushes restricted Lebesgue measure to
an absolutely continuous measure, hence (Radon--Nikodym) to `volume.withDensity g`
for some density `g`.  Since the pushforward is finite, `g` is integrable: an L¹ density. -/
theorem submersion_map_has_L1_density {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (f' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    (s : Set (Fin n → ℝ)) (hs : MeasurableSet s)
    (hsfin : (volume : Measure (Fin n → ℝ)) s < ⊤)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf_det : ∀ x ∈ s, (f' x).det ≠ 0)
    (hf_inj : InjOn f s) :
    ∃ g : (Fin n → ℝ) → ℝ≥0∞,
      Measure.map f ((volume : Measure (Fin n → ℝ)).restrict s) =
        (volume : Measure (Fin n → ℝ)).withDensity g ∧
      (∫⁻ x, g x ∂(volume : Measure (Fin n → ℝ))) < ⊤ := by
  let μ : Measure (Fin n → ℝ) := volume.restrict s
  let w : (Fin n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal |(f' x).det|
  have hac_mu : μ ≪ μ.withDensity w := by
    dsimp [μ, w]
    exact restrict_ac_jacWeight f f' s hs hf' hf_det
  have hf_ae_mu : AEMeasurable f μ := by
    dsimp [μ]
    exact ContinuousOn.aemeasurable₀
      (fun x hx => (hf' x hx).differentiableWithinAt.continuousWithinAt) hs.nullMeasurableSet
  have hf_ae_w : AEMeasurable f (μ.withDensity w) :=
    hf_ae_mu.mono_ac (withDensity_absolutelyContinuous μ w)
  have hmap : Measure.map f (μ.withDensity w) = volume.restrict (f '' s) := by
    dsimp [μ, w]
    exact map_withDensity_abs_det_fderiv_eq_addHaar
      (μ := (volume : Measure (Fin n → ℝ))) hs.nullMeasurableSet hf' hf_inj
  have h_ac : Measure.map f μ ≪ (volume : Measure (Fin n → ℝ)) := by
    intro N hNvol
    let N' : Set (Fin n → ℝ) := toMeasurable volume N
    have hN'm : MeasurableSet N' := measurableSet_toMeasurable volume N
    have hN'vol : volume N' = 0 := by
      rw [measure_toMeasurable]
      exact hNvol
    have himg_meas : MeasurableSet (f '' s) := measurable_image_of_fderivWithin hs hf' hf_inj
    have hNrestrict : (volume.restrict (f '' s)) N' = 0 := by
      rw [Measure.restrict_apply hN'm]
      exact measure_mono_null (by intro y hy; exact hy.1) hN'vol
    have hwd : (μ.withDensity w) (f ⁻¹' N') = 0 := by
      rw [← Measure.map_apply_of_aemeasurable hf_ae_w hN'm, hmap]
      exact hNrestrict
    have hmu : μ (f ⁻¹' N') = 0 := hac_mu hwd
    have hmapN' : (Measure.map f μ) N' = μ (f ⁻¹' N') :=
      Measure.map_apply_of_aemeasurable hf_ae_mu hN'm
    exact measure_mono_null (subset_toMeasurable volume N) (by rw [hmapN', hmu])
  refine ⟨(Measure.map f μ).rnDeriv volume, ?_, ?_⟩
  · simpa [μ] using (Measure.withDensity_rnDeriv_eq (Measure.map f μ) volume h_ac).symm
  · calc
      (∫⁻ x, (Measure.map f μ).rnDeriv volume x ∂volume)
          ≤ (Measure.map f μ) Set.univ := Measure.lintegral_rnDeriv_le
      _ = μ (f ⁻¹' Set.univ) := by
            rw [Measure.map_apply_of_aemeasurable hf_ae_mu MeasurableSet.univ]
      _ = volume s := by simp [μ]
      _ < ⊤ := hsfin

end YangMills
