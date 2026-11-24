/-
  Wilson measure and plaquette-CDF observable definitions for the proposed
  Wilson-to-Schwinger bridge.

  Standard axioms only.
-/
import Mathlib
import Imscribing.YangMills.IIDSchwingerFromWilson
import Imscribing.YangMills.OSCompletion
import Imscribing.YangMills.PlaquetteStep3
import Imscribing.YangMills.RademacherMulti
import Imscribing.YangMills.ProbIntegralTransform
import Imscribing.YangMills.SUNHaar
import Imscribing.Millennium.ContinuumLatticeBridge
import Imscribing.Millennium.TorusWraparoundBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped BigOperators ENNReal NNReal Matrix
open MeasureTheory Set Filter Topology Real

namespace YangMills

/-- Wilson measure: `dμ_Wilson = exp(-β S_W) / Z dμ_Haar`. -/
noncomputable def wilsonMeasure (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Measure (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  (spacetimeHaarMeasure Ls Lt N).withDensity
    (fun U => ENNReal.ofReal (cubic4WilsonWeight Ls Lt N β U) /
      ENNReal.ofReal (cubic4PartitionFn Ls Lt N β))

/-- Wilson measure is absolutely continuous w.r.t. Haar measure. -/
theorem wilsonMeasure_abs_cont_haar (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] (hβ : 0 ≤ β) :
    (wilsonMeasure Ls Lt N β : Measure (GaugeField (cubicTorus4 Ls Lt)
      (Matrix.specialUnitaryGroup (Fin N) ℂ))) ≪ spacetimeHaarMeasure Ls Lt N := by
  change (spacetimeHaarMeasure Ls Lt N).withDensity
    (fun U => ENNReal.ofReal (cubic4WilsonWeight Ls Lt N β U) /
      ENNReal.ofReal (cubic4PartitionFn Ls Lt N β)) ≪ _
  exact withDensity_absolutelyContinuous _ _

/-- For nonnegative coupling the Wilson density is strictly positive, so the
Wilson and product-Haar measures have the same null sets. -/
theorem haar_abs_cont_wilsonMeasure (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] (hβ : 0 ≤ β) :
    spacetimeHaarMeasure Ls Lt N ≪ wilsonMeasure Ls Lt N β := by
  let μ := spacetimeHaarMeasure Ls Lt N
  let w := cubic4WilsonWeight Ls Lt N β
  have hweight_meas : Measurable (fun U =>
      ENNReal.ofReal (w U) / ENNReal.ofReal (cubic4PartitionFn Ls Lt N β)) := by
    exact (ENNReal.measurable_ofReal.comp
      (measurable_cubic4WilsonWeight Ls Lt N β)).div measurable_const
  have hweight_ne : ∀ᵐ U ∂μ,
      ENNReal.ofReal (w U) / ENNReal.ofReal (cubic4PartitionFn Ls Lt N β) ≠ 0 := by
    filter_upwards with U
    have hwpos : 0 < w U := by
      dsimp [w, cubic4WilsonWeight]
      exact Real.exp_pos _
    have hnum : ENNReal.ofReal (w U) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hwpos
    exact ENNReal.div_ne_zero.mpr ⟨hnum, ENNReal.ofReal_ne_top⟩
  change μ ≪ μ.withDensity
    (fun U => ENNReal.ofReal (w U) / ENNReal.ofReal (cubic4PartitionFn Ls Lt N β))
  exact withDensity_absolutelyContinuous' hweight_meas.aemeasurable hweight_ne

/-- The abstract lattice interface used by the plaquette-density theorem, on the
four-dimensional periodic lattice already used by the Wilson action. -/
noncomputable def cubicPlaquetteLattice (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] :
    LatticeSetup 4 Lt where
  Site := (cubicTorus4 Ls Lt).Site
  fintypeSite := inferInstance
  decEqSite := inferInstance
  hd := by omega
  hLt := Nat.pos_of_ne_zero (NeZero.ne Lt)
  tCoord := Prod.fst
  stepSite := fun v d => cubicShift4 Ls Lt d v
  step0_inj := by
    intro v w h
    have ht := congrArg Prod.fst h
    have hspace := congrArg Prod.snd h
    change v.1 + 1 = w.1 + 1 at ht
    have ht' : v.1 = w.1 := add_right_cancel ht
    change v.2 = w.2 at hspace
    exact Prod.ext ht' hspace
  tCoord_step0 := by
    intro v
    rfl

/-- Absolute continuity survives a measurable pushforward of absolutely
continuous measures. -/
private theorem map_absolutelyContinuous_of_absolutelyContinuous
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (μ ν : Measure α) (hμν : μ ≪ ν) :
    μ.map f ≪ ν.map f := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  rw [Measure.map_apply hf hs] at hzero ⊢
  exact hμν hzero

/-- Absolute continuity is preserved by finite products of marginals. -/
theorem pi_absolutelyContinuous_fin {r : ℕ} {α : Type*} [MeasurableSpace α]
    (μ ν : Fin r → Measure α) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  induction r with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ r ih =>
      let μtail : Fin r → Measure α := fun j => μ (Fin.succAbove 0 j)
      let νtail : Fin r → Measure α := fun j => ν (Fin.succAbove 0 j)
      let e : (Fin (r + 1) → α) ≃ᵐ α × (Fin r → α) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => α) 0
      have hμe : (Measure.pi μ).map e = (μ 0).prod (Measure.pi μtail) := by
        simpa [e, μtail] using
          (measurePreserving_piFinSuccAbove μ (0 : Fin (r + 1))).map_eq
      have hνe : (Measure.pi ν).map e = (ν 0).prod (Measure.pi νtail) := by
        simpa [e, νtail] using
          (measurePreserving_piFinSuccAbove ν (0 : Fin (r + 1))).map_eq
      have htail : Measure.pi μtail ≪ Measure.pi νtail :=
        ih μtail νtail (fun j => h (Fin.succAbove 0 j))
      have hprod : (μ 0).prod (Measure.pi μtail) ≪
          (ν 0).prod (Measure.pi νtail) := (h 0).prod htail
      have hmap : (Measure.pi μ).map e ≪ (Measure.pi ν).map e := by
        rw [hμe, hνe]
        exact hprod
      refine Measure.AbsolutelyContinuous.mk ?_
      intro s hs hzero
      let t := e '' s
      have ht : MeasurableSet t := e.measurableSet_image.mpr hs
      have hzero' : ((Measure.pi ν).map e) t = 0 := by
        rw [Measure.map_apply e.measurable ht]
        simpa [t, e.injective.preimage_image] using hzero
      have h := hmap hzero'
      rw [Measure.map_apply e.measurable ht, e.injective.preimage_image] at h
      exact h

/-- The normalized Wilson density has total mass one. -/
theorem wilsonMeasure_isProbability (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] (hβ : 0 ≤ β) :
    IsProbabilityMeasure (wilsonMeasure Ls Lt N β) := by
  let μ := spacetimeHaarMeasure Ls Lt N
  let w := cubic4WilsonWeight Ls Lt N β
  haveI : IsProbabilityMeasure μ := spacetimeHaarMeasure_prob Ls Lt N
  have hZpos : 0 < cubic4PartitionFn Ls Lt N β := cubic4PartitionFn_pos Ls Lt N β hβ
  have hw_int : Integrable w μ := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_cubic4WilsonWeight Ls Lt N β).stronglyMeasurable.aestronglyMeasurable ?_
    filter_upwards with U
    have hw := cubic4WilsonWeight_bounds Ls Lt N β hβ U
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold w cubic4WilsonWeight; positivity)]
    exact hw.2
  have hw_nonneg : 0 ≤ᵐ[μ] w := by
    filter_upwards with U
    change 0 ≤ Real.exp _
    exact (Real.exp_pos _).le
  have hw_meas : Measurable (fun U => ENNReal.ofReal (w U)) :=
    ENNReal.measurable_ofReal.comp (measurable_cubic4WilsonWeight Ls Lt N β)
  constructor
  change (μ.withDensity
    (fun U => ENNReal.ofReal (w U) / ENNReal.ofReal (cubic4PartitionFn Ls Lt N β)))
      Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hden : ENNReal.ofReal (cubic4PartitionFn Ls Lt N β) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hZpos
  change (∫⁻ U, ENNReal.ofReal (w U) *
    (ENNReal.ofReal (cubic4PartitionFn Ls Lt N β))⁻¹ ∂μ) = 1
  rw [lintegral_mul_const _ hw_meas]
  rw [← ofReal_integral_eq_lintegral_ofReal hw_int hw_nonneg]
  have hint : (∫ U, w U ∂μ) = cubic4PartitionFn Ls Lt N β := rfl
  rw [hint]
  exact ENNReal.mul_inv_cancel hden ENNReal.ofReal_ne_top

/-- Rewrite a normalized Wilson integral as an expectation under the Wilson
probability measure. -/
theorem cubic4Schwinger_eq_wilsonMeasure_integral
    (Ls Lt N n : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (obs : Fin n → GaugeField (cubicTorus4 Ls Lt)
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) :
    cubic4Schwinger Ls Lt N β n obs =
      ∫ U, ∏ i : Fin n, obs i U ∂wilsonMeasure Ls Lt N β := by
  let μ := spacetimeHaarMeasure Ls Lt N
  let Z := cubic4PartitionFn Ls Lt N β
  let ρ : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞ :=
    fun U => ENNReal.ofReal (cubic4WilsonWeight Ls Lt N β U) / ENNReal.ofReal Z
  have hZ : 0 < Z := cubic4PartitionFn_pos Ls Lt N β hβ
  have hρmeas : Measurable ρ := by
    dsimp [ρ, Z]
    exact (ENNReal.measurable_ofReal.comp (measurable_cubic4WilsonWeight Ls Lt N β)).div
      measurable_const
  have hρtop : ∀ᵐ U ∂μ, ρ U < ∞ := by
    filter_upwards with U
    dsimp [ρ]
    exact ENNReal.div_lt_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_ne_zero_iff.mpr hZ)
  have hρreal (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
      (ρ U).toReal = cubic4WilsonWeight Ls Lt N β U / Z := by
    dsimp [ρ, Z]
    rw [ENNReal.toReal_div]
    have hw0 : 0 ≤ cubic4WilsonWeight Ls Lt N β U :=
      (Real.exp_pos _).le.trans (cubic4WilsonWeight_bounds Ls Lt N β hβ U).1
    rw [ENNReal.toReal_ofReal hw0,
      ENNReal.toReal_ofReal hZ.le]
  have hchange :
      ∫ U, (∏ i : Fin n, obs i U) ∂μ.withDensity ρ =
        ∫ U, (ρ U).toReal • (∏ i : Fin n, obs i U) ∂μ :=
    integral_withDensity_eq_integral_toReal_smul hρmeas hρtop _
  change cubic4Schwinger Ls Lt N β n obs =
    ∫ U, ∏ i : Fin n, obs i U ∂μ.withDensity ρ
  rw [hchange]
  unfold cubic4Schwinger
  rw [show (∫ U, (ρ U).toReal • (∏ i : Fin n, obs i U) ∂μ) =
      (Z⁻¹ : ℂ) * ∫ U, (∏ i : Fin n, obs i U) *
        ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂μ by
    have hpoint (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
        (ρ U).toReal • (∏ i : Fin n, obs i U) =
          (Z⁻¹ : ℂ) * ((∏ i : Fin n, obs i U) *
            ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)) := by
      rw [hρreal U]
      rw [Complex.real_smul, Complex.ofReal_div]
      have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
      field_simp [hZc]
    calc
      _ = ∫ U, (Z⁻¹ : ℂ) * ((∏ i : Fin n, obs i U) *
          ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = (Z⁻¹ : ℂ) * ∫ U, (∏ i : Fin n, obs i U) *
          ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂μ := by
        rw [integral_const_mul]]

/-- If the observable product is real-valued, the Wilson Schwinger functional
is the corresponding real expectation, embedded into `ℂ`. -/
theorem cubic4Schwinger_eq_real_wilsonExpectation
    (Ls Lt N n : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (obs : Fin n → GaugeField (cubicTorus4 Ls Lt)
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (f : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hprod : ∀ U, (∏ i : Fin n, obs i U) = (f U : ℂ)) :
    cubic4Schwinger Ls Lt N β n obs = (∫ U, f U ∂wilsonMeasure Ls Lt N β : ℝ) := by
  rw [cubic4Schwinger_eq_wilsonMeasure_integral Ls Lt N n β hβ obs]
  rw [show (fun U => ∏ i : Fin n, obs i U) = fun U => (f U : ℂ) by
      funext U; exact hprod U]
  exact integral_ofReal

/-- Plaquette defect: `X_p(U) = 1 - (1/N) Re Tr(U_p)` ∈ [0, 2]. -/
noncomputable def plaquetteDefect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (v : (cubicTorus4 Ls Lt).Site) (U : GaugeField (cubicTorus4 Ls Lt)
    (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  1 - (normWilsonLoop4 (cubic4Plaquette v 0 1) U).re

theorem plaquetteDefect_bounds (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (hN : 1 ≤ N)
    (v : (cubicTorus4 Ls Lt).Site) (U : GaugeField (cubicTorus4 Ls Lt)
    (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ plaquetteDefect Ls Lt N v U ∧ plaquetteDefect Ls Lt N v U ≤ 2 := by
  have hloop := normWilsonLoop4_norm_le_one hN (cubic4Plaquette v 0 1) U
  have hreal : |(normWilsonLoop4 (cubic4Plaquette v 0 1) U).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans hloop
  rw [abs_le] at hreal
  constructor <;> dsimp [plaquetteDefect] <;> linarith

theorem measurable_plaquetteDefect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (v : (cubicTorus4 Ls Lt).Site) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt)
      (Matrix.specialUnitaryGroup (Fin N) ℂ) => plaquetteDefect Ls Lt N v U) := by
  let p : LatticePlaquette (cubicTorus4 Ls Lt) :=
    ⟨v, cubic4Plaquette v 0 1, cubic4Plaquette_isPath v 0 1⟩
  have heq : (fun U : GaugeField (cubicTorus4 Ls Lt)
      (Matrix.specialUnitaryGroup (Fin N) ℂ) => plaquetteDefect Ls Lt N v U) =
      fun U => wilsonPlaquetteTerm p U := by
    funext U
    simp [plaquetteDefect, p, normWilsonLoop4, wilsonPlaquetteTerm]
  rw [heq]
  exact measurable_wilsonPlaquetteTerm4 Ls Lt N p

/-- The cubic defect is the abstract plaquette observable for the canonical
four-dimensional lattice setup. -/
theorem plaquetteDefect_eq_abstract_plaquette
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (v : (cubicTorus4 Ls Lt).Site)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    plaquetteDefect Ls Lt N v U =
      plaquetteObs (cubicPlaquetteLattice Ls Lt) N v U := by
  simp only [plaquetteDefect, plaquetteObs, cubicPlaquetteLattice]
  change 1 - (normWilsonLoop4 (cubic4Plaquette v 0 1) U).re =
    f0 N (U (v, 0) * U (cubicShift4 Ls Lt 0 v, 1) *
      (U (cubicShift4 Ls Lt 1 v, 0))⁻¹ * (U (v, 1))⁻¹)
  have hloop : U (v, 0) * U (cubicShift4 Ls Lt 0 v, 1) *
      (U (cubicShift4 Ls Lt 1 v, 0))⁻¹ * (U (v, 1))⁻¹ =
      pathHolonomy U (cubic4Plaquette v 0 1) := by
    simp [cubic4Plaquette, pathHolonomy]
    group
  rw [hloop]
  unfold f0 normWilsonLoop4
  simp [Complex.mul_re]

/-- A single plaquette defect under the Wilson measure has an absolutely
continuous distribution, by transferring the existing Haar theorem. -/
theorem wilson_plaquette_absolutelyContinuous
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    (hN : 2 ≤ N) (hLt2 : 2 ≤ Lt)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (v : (cubicTorus4 Ls Lt).Site) :
    (wilsonMeasure Ls Lt N β).map (fun U => plaquetteDefect Ls Lt N v U) ≪ volume := by
  let lat := cubicPlaquetteLattice Ls Lt
  haveI : IsProbabilityMeasure (suHaar N) := suHaar_prob N
  haveI : (suHaar N).IsMulLeftInvariant := ⟨fun g => suHaar_map_mul_left N g⟩
  haveI : (suHaar N).IsMulRightInvariant := ⟨fun g => suHaar_map_mul_right N g⟩
  have hhaar := plaquette_single_absolutelyContinuous (suHaar N) hN hLt2
    submersion_1d lat v
  have hhaar' : (spacetimeHaarMeasure Ls Lt N).map
      (fun U => plaquetteDefect Ls Lt N v U) ≪ volume := by
    have hEq : (fun U => plaquetteDefect Ls Lt N v U) =
        fun U => plaquetteObs lat N v U := by
      funext U
      exact plaquetteDefect_eq_abstract_plaquette Ls Lt N v U
    rw [hEq]
    simpa [haarConfigMeasure, spacetimeHaarMeasure, lat] using hhaar
  have hpush := map_absolutelyContinuous_of_absolutelyContinuous
    (fun U => plaquetteDefect Ls Lt N v U)
    (measurable_plaquetteDefect Ls Lt N v)
    (wilsonMeasure Ls Lt N β) (spacetimeHaarMeasure Ls Lt N)
    (wilsonMeasure_abs_cont_haar Ls Lt N β hβ)
  exact hpush.trans hhaar'

/-- The Wilson joint plaquette law inherits the distinct-site density theorem
from product Haar measure on the same cubic lattice. -/
theorem wilson_plaquette_joint_absolutelyContinuous
    (Ls Lt N r : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β) (hN : 2 ≤ N) (hLt2 : 2 ≤ Lt)
    (hr : r + 1 ≤ Lt)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (v : Fin r → (cubicTorus4 Ls Lt).Site) (hv : Function.Injective v) :
    (wilsonMeasure Ls Lt N β).map
      (fun U i => plaquetteDefect Ls Lt N (v i) U) ≪ volume := by
  let lat := cubicPlaquetteLattice Ls Lt
  haveI : IsProbabilityMeasure (suHaar N) := suHaar_prob N
  haveI : (suHaar N).IsMulLeftInvariant :=
    ⟨fun g => suHaar_map_mul_left N g⟩
  haveI : (suHaar N).IsMulRightInvariant :=
    ⟨fun g => suHaar_map_mul_right N g⟩
  have hhaar := (plaquette_joint_absolutelyContinuous (suHaar N) hN
    hLt2 submersion_1d lat r hr v hv
    ).1
  let F : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      (Fin r → ℝ) := fun U i => plaquetteDefect Ls Lt N (v i) U
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_plaquetteDefect Ls Lt N (v i)
  have hF_eq : F = fun U i => plaquetteObs lat N (v i) U := by
    funext U i
    exact plaquetteDefect_eq_abstract_plaquette Ls Lt N (v i) U
  have hhaar' : (spacetimeHaarMeasure Ls Lt N).map F ≪ volume := by
    rw [hF_eq]
    exact hhaar
  have hpush : (wilsonMeasure Ls Lt N β).map F ≪
      (spacetimeHaarMeasure Ls Lt N).map F :=
    map_absolutelyContinuous_of_absolutelyContinuous F hF
      (wilsonMeasure Ls Lt N β) (spacetimeHaarMeasure Ls Lt N)
      (wilsonMeasure_abs_cont_haar Ls Lt N β hβ)
  have htrans := hpush.trans hhaar'
  simpa [F] using htrans

/-- Put the CDF of a probability measure into the closed unit interval. -/
noncomputable def cdfI01 (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ) (x : ℝ) : I01 := by
  letI : IsProbabilityMeasure μ := hμ
  exact ⟨ProbabilityTheory.cdf μ x,
    ⟨ProbabilityTheory.cdf_nonneg μ x, ProbabilityTheory.cdf_le_one μ x⟩⟩

theorem measurable_cdfI01 (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ) :
    Measurable (cdfI01 μ hμ) := by
  letI : IsProbabilityMeasure μ := hμ
  change Measurable (fun x =>
    (⟨ProbabilityTheory.cdf μ x,
      ⟨ProbabilityTheory.cdf_nonneg μ x, ProbabilityTheory.cdf_le_one μ x⟩⟩ : I01))
  exact (ProbabilityTheory.monotone_cdf μ).measurable.subtype_mk

/-- The subtype-valued probability integral transform is uniform on `I01`.
The omitted endpoint has Lebesgue measure zero. -/
theorem cdfI01_map_eq_volume (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ)
    [NoAtoms μ] : μ.map (cdfI01 μ hμ) = (volume : Measure I01) := by
  letI : IsProbabilityMeasure μ := hμ
  have hmapval : (μ.map (cdfI01 μ hμ)).map Subtype.val =
      volume.restrict (Set.Ico (0 : ℝ) 1) := by
    rw [Measure.map_map measurable_subtype_coe (measurable_cdfI01 μ hμ)]
    change μ.map (ProbabilityTheory.cdf μ) = volume.restrict (Set.Ico 0 1)
    exact map_cdf_eq_uniform_Ico μ
  have hvolval : (volume : Measure I01).map Subtype.val =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
    change (Measure.comap Subtype.val volume).map Subtype.val = _
    exact map_comap_subtype_coe measurableSet_Icc volume
  have hIcoIcc : volume.restrict (Set.Ico (0 : ℝ) 1) =
      volume.restrict (Set.Icc (0 : ℝ) 1) :=
    Measure.restrict_congr_set (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1))
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  calc
    (μ.map (cdfI01 μ hμ)).map Subtype.val = volume.restrict (Set.Ico 0 1) := hmapval
    _ = volume.restrict (Set.Icc 0 1) := hIcoIcc
    _ = (volume : Measure I01).map Subtype.val := hvolval.symm

/-- A coordinate marginal of a vector-valued probability measure. -/
noncomputable def coordinateMarginal {r : ℕ} (ν : Measure (Fin r → ℝ)) (i : Fin r) :
    Measure ℝ := ν.map (fun x => x i)

theorem coordinateMarginal_pi {r : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (i : Fin r) : coordinateMarginal (Measure.pi (fun _ : Fin r => μ)) i = μ := by
  unfold coordinateMarginal
  rw [Measure.pi_map_eval]
  simp

/-- If the product-Haar law of a lattice observable vector factors into its
coordinate marginals, then the Wilson law is dominated by the product of its
own marginals. This transfers independence through the strictly positive
Wilson density without assuming independence under the Wilson measure. -/
theorem wilson_joint_dominated_by_marginals_of_haar_independent
    (Ls Lt N r : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (F : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      Fin r → ℝ) (hF : Measurable F)
    (hhaar : (spacetimeHaarMeasure Ls Lt N).map F =
      Measure.pi (fun i : Fin r => coordinateMarginal
        ((spacetimeHaarMeasure Ls Lt N).map F) i)) :
    (wilsonMeasure Ls Lt N β).map F ≪ Measure.pi (fun i : Fin r => coordinateMarginal
      ((wilsonMeasure Ls Lt N β).map F) i) := by
  let η := (spacetimeHaarMeasure Ls Lt N).map F
  let ν := (wilsonMeasure Ls Lt N β).map F
  haveI : IsProbabilityMeasure (spacetimeHaarMeasure Ls Lt N) :=
    spacetimeHaarMeasure_prob Ls Lt N
  haveI : IsProbabilityMeasure (wilsonMeasure Ls Lt N β) :=
    wilsonMeasure_isProbability Ls Lt N β hβ
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map hF.aemeasurable
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hF.aemeasurable
  haveI (i : Fin r) : IsProbabilityMeasure (coordinateMarginal η i) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  haveI (i : Fin r) : IsProbabilityMeasure (coordinateMarginal ν i) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  have hην : η ≪ ν := map_absolutelyContinuous_of_absolutelyContinuous F hF
    (spacetimeHaarMeasure Ls Lt N) (wilsonMeasure Ls Lt N β)
    (haar_abs_cont_wilsonMeasure Ls Lt N β hβ)
  have hνη : ν ≪ η := map_absolutelyContinuous_of_absolutelyContinuous F hF
    (wilsonMeasure Ls Lt N β) (spacetimeHaarMeasure Ls Lt N)
    (wilsonMeasure_abs_cont_haar Ls Lt N β hβ)
  have hMarg : ∀ i : Fin r, coordinateMarginal η i ≪ coordinateMarginal ν i := by
    intro i
    exact map_absolutelyContinuous_of_absolutelyContinuous (fun x : Fin r → ℝ => x i)
      (measurable_pi_apply i) η ν hην
  have hpi : Measure.pi (fun i : Fin r => coordinateMarginal η i) ≪
      Measure.pi (fun i : Fin r => coordinateMarginal ν i) := by
    apply pi_absolutelyContinuous_fin
    exact hMarg
  have hηpi : η ≪ Measure.pi (fun i : Fin r => coordinateMarginal η i) := by
    have hhaar' : η = Measure.pi (fun i : Fin r => coordinateMarginal η i) := by
      simpa [η] using hhaar
    exact Measure.absolutelyContinuous_of_eq hhaar'
  have hνη' : ν ≪ Measure.pi (fun i : Fin r => coordinateMarginal ν i) := by
    exact hνη.trans (hηpi.trans hpi)
  simpa [η, ν] using hνη'

/-- The Wilson law of distinct cubic plaquettes is dominated by the product of
its marginals. The product-Haar law is proved in `PlaquetteStep3`; positivity
of the Wilson density transfers that law to the product of Wilson marginals. -/
theorem wilson_plaquette_joint_dominated_by_marginals
    (Ls Lt N r : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    (hN : 2 ≤ N) (hLt2 : 2 ≤ Lt) (hr : r + 1 ≤ Lt)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (v : Fin r → (cubicTorus4 Ls Lt).Site) (hv : Function.Injective v) :
    (wilsonMeasure Ls Lt N β).map
      (fun U i => plaquetteDefect Ls Lt N (v i) U) ≪
      Measure.pi (fun i : Fin r => coordinateMarginal
        ((wilsonMeasure Ls Lt N β).map
          (fun U i => plaquetteDefect Ls Lt N (v i) U)) i) := by
  let lat := cubicPlaquetteLattice Ls Lt
  haveI : IsProbabilityMeasure (suHaar N) := suHaar_prob N
  haveI : (suHaar N).IsMulLeftInvariant := ⟨fun g => suHaar_map_mul_left N g⟩
  haveI : (suHaar N).IsMulRightInvariant := ⟨fun g => suHaar_map_mul_right N g⟩
  let F : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      Fin r → ℝ := fun U i => plaquetteDefect Ls Lt N (v i) U
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_plaquetteDefect Ls Lt N (v i)
  have hLaw : (spacetimeHaarMeasure Ls Lt N).map F =
      Measure.pi (fun _ : Fin r => (suHaar N).map (f0 N)) := by
    have hAbstract := (plaquette_joint_absolutelyContinuous (suHaar N) hN hLt2
      submersion_1d lat r hr v hv).2
    have hF_eq : F = fun U i => plaquetteObs lat N (v i) U := by
      funext U i
      exact plaquetteDefect_eq_abstract_plaquette Ls Lt N (v i) U
    rw [hF_eq]
    simpa [haarConfigMeasure, spacetimeHaarMeasure, lat] using hAbstract
  haveI : IsProbabilityMeasure ((suHaar N).map (f0 N)) :=
    Measure.isProbabilityMeasure_map (f0_continuous N).measurable.aemeasurable
  have hmarg : ∀ i : Fin r,
      coordinateMarginal ((spacetimeHaarMeasure Ls Lt N).map F) i =
        (suHaar N).map (f0 N) := by
    intro i
    rw [hLaw]
    exact coordinateMarginal_pi ((suHaar N).map (f0 N)) i
  have hhaar : (spacetimeHaarMeasure Ls Lt N).map F =
      Measure.pi (fun i : Fin r => coordinateMarginal
        ((spacetimeHaarMeasure Ls Lt N).map F) i) := by
    calc
      (spacetimeHaarMeasure Ls Lt N).map F =
          Measure.pi (fun _ : Fin r => (suHaar N).map (f0 N)) := hLaw
      _ = Measure.pi (fun i : Fin r => coordinateMarginal
          ((spacetimeHaarMeasure Ls Lt N).map F) i) := by
            congr 1
            funext i
            exact (hmarg i).symm
  exact wilson_joint_dominated_by_marginals_of_haar_independent
    Ls Lt N r β hβ F hF hhaar

/-- Apply the probability integral transform in every coordinate. -/
noncomputable def cdfCubeMap {r : ℕ} (ν : Measure (Fin r → ℝ))
    [IsProbabilityMeasure ν] (x : Fin r → ℝ) : Fin r → I01 := fun i =>
  cdfI01 (coordinateMarginal ν i)
    (Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable) (x i)

theorem measurable_cdfCubeMap {r : ℕ} (ν : Measure (Fin r → ℝ))
    [IsProbabilityMeasure ν] : Measurable (cdfCubeMap ν) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_cdfI01 (coordinateMarginal ν i)
    (Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable)).comp
      (measurable_pi_apply i)

/-- If a joint law is dominated by the product of its marginals, its coordinate
CDF vector is absolutely continuous with respect to product uniform measure.
The statement retains arbitrary dependence in the joint law. -/
theorem cdfCubeMap_absolutelyContinuous {r : ℕ} (ν : Measure (Fin r → ℝ))
    [IsProbabilityMeasure ν]
    (hdom : ν ≪ Measure.pi (fun i : Fin r => coordinateMarginal ν i))
    (hnoAtoms : ∀ i : Fin r, NoAtoms (coordinateMarginal ν i)) :
    ν.map (cdfCubeMap ν) ≪ I01Pi r := by
  let F := cdfCubeMap ν
  have hF : Measurable F := measurable_cdfCubeMap ν
  have hprod : (Measure.pi (fun i : Fin r => coordinateMarginal ν i)).map F =
      I01Pi r := by
    haveI (i : Fin r) : IsProbabilityMeasure (coordinateMarginal ν i) :=
      Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
    haveI (i : Fin r) : SigmaFinite ((coordinateMarginal ν i).map
        (cdfI01 (coordinateMarginal ν i)
          (Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable))) := by
      infer_instance
    change (Measure.pi (fun i : Fin r => coordinateMarginal ν i)).map
      (fun x i => cdfI01 (coordinateMarginal ν i)
        (Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable) (x i)) = _
    rw [Measure.pi_map_pi (fun i =>
      (measurable_cdfI01 (coordinateMarginal ν i)
        (Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable)).aemeasurable)]
    have hcoord : ∀ i : Fin r,
        (coordinateMarginal ν i).map
          (cdfI01 (coordinateMarginal ν i)
            (Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable)) =
          (volume : Measure I01) := by
      intro i
      letI : NoAtoms (coordinateMarginal ν i) := hnoAtoms i
      exact cdfI01_map_eq_volume _ _
    simp [I01Pi, hcoord]
  have hpush := map_absolutelyContinuous_of_absolutelyContinuous F hF ν
    (Measure.pi (fun i : Fin r => coordinateMarginal ν i)) hdom
  rw [hprod] at hpush
  simpa [F] using hpush

/-- For a fixed absolutely continuous copula law, every nonempty product of
distinct high-frequency Rademacher coordinates has vanishing expectation. -/
theorem cdfCubeMap_rademacher_tendsto_zero {r : ℕ}
    (ν : Measure (Fin r → ℝ)) [IsProbabilityMeasure ν]
    (hdom : ν ≪ Measure.pi (fun i : Fin r => coordinateMarginal ν i))
    (hnoAtoms : ∀ i : Fin r, NoAtoms (coordinateMarginal ν i))
    (S : Finset (Fin r)) (hS : S.Nonempty) :
    Tendsto (fun K : ℕ =>
      ∫ x : Fin r → I01, S.prod (fun i => radI K (x i))
        ∂(ν.map (cdfCubeMap ν))) atTop (𝓝 0) := by
  let μ := ν.map (cdfCubeMap ν)
  let q : (Fin r → I01) → ℝ := fun x => (μ.rnDeriv (I01Pi r) x).toReal
  have hμAC : μ ≪ I01Pi r := cdfCubeMap_absolutelyContinuous ν hdom hnoAtoms
  haveI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_cdfCubeMap ν).aemeasurable
  haveI : SigmaFinite μ := inferInstance
  haveI : SigmaFinite (I01Pi r) := inferInstance
  haveI : Measure.HaveLebesgueDecomposition μ (I01Pi r) := inferInstance
  have hqint : Integrable q (I01Pi r) := by
    have h := (integrable_rnDeriv_smul_iff hμAC
      (f := fun _ : Fin r → I01 => (1 : ℝ))).2 (integrable_const (1 : ℝ))
    simpa [q, smul_eq_mul] using h
  have hchange (K : ℕ) :
      ∫ x : Fin r → I01, S.prod (fun i => radI K (x i)) ∂μ =
        ∫ x : Fin r → I01, q x * S.prod (fun i => radI K (x i)) ∂(I01Pi r) := by
    calc
      ∫ x : Fin r → I01, S.prod (fun i => radI K (x i)) ∂μ
        = ∫ x : Fin r → I01,
            (μ.rnDeriv (I01Pi r) x).toReal • S.prod (fun i => radI K (x i))
              ∂(I01Pi r) := (integral_rnDeriv_smul hμAC).symm
      _ = ∫ x : Fin r → I01, q x * S.prod (fun i => radI K (x i))
          ∂(I01Pi r) := by simp [q, smul_eq_mul]
  have hEq : (fun K : ℕ =>
      ∫ x : Fin r → I01, S.prod (fun i => radI K (x i)) ∂μ) =
      fun K => ∫ x : Fin r → I01, q x * S.prod (fun i => radI K (x i)) ∂(I01Pi r) := by
    funext K
    exact hchange K
  rw [hEq]
  exact radI_multidim_integrable r q hqint S hS

/-- Under a fixed joint density, distinct sites become moment-independent as
the common Rademacher frequency tends to infinity. Repeated insertions at one
site are represented by the exponent `k i`. -/
noncomputable def fourierOrientation (K : ℕ) (u : ℝ) : ℝ :=
  (3 / 2 : ℝ) - (1 / 2 : ℝ) * rademacher K u

theorem measurable_fourierOrientation (K : ℕ) : Measurable (fourierOrientation K) := by
  exact measurable_const.sub (measurable_const.mul (rademacher_measurable K))

theorem cdfCubeMap_product_moment_tendsto {r : ℕ}
    (ν : Measure (Fin r → ℝ)) [IsProbabilityMeasure ν]
    (hdom : ν ≪ Measure.pi (fun i : Fin r => coordinateMarginal ν i))
    (hnoAtoms : ∀ i : Fin r, NoAtoms (coordinateMarginal ν i))
    (k : Fin r → ℕ) :
    Tendsto (fun K : ℕ =>
      ∫ u : Fin r → I01,
        ∏ i : Fin r, (fourierOrientation K (u i).1) ^ k i
          ∂(ν.map (cdfCubeMap ν))) atTop
      (𝓝 (∏ i : Fin r, ((1 : ℝ) ^ k i + (2 : ℝ) ^ k i) / 2)) := by
  classical
  let μ := ν.map (cdfCubeMap ν)
  let a : Fin r → ℝ := fun i => ((1 : ℝ) ^ k i + (2 : ℝ) ^ k i) / 2
  let b : Fin r → ℝ := fun i => ((1 : ℝ) ^ k i - (2 : ℝ) ^ k i) / 2
  let R : Finset (Fin r) → ℕ → (Fin r → I01) → ℝ := fun S K u =>
    S.prod (fun i => radI K (u i))
  let c : Finset (Fin r) → ℝ := fun S =>
    S.prod a * Sᶜ.prod b
  let T : Finset (Fin r) → ℕ → (Fin r → I01) → ℝ := fun S K u => c S * R Sᶜ K u
  have hμAC := cdfCubeMap_absolutelyContinuous ν hdom hnoAtoms
  haveI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_cdfCubeMap ν).aemeasurable
  have hdecomp (i : Fin r) (K : ℕ) (u : I01) :
      (fourierOrientation K u.1) ^ k i = a i + b i * radI K u := by
    unfold a b fourierOrientation radI rademacher
    split <;> norm_num <;> ring
  have hsubset (S : Finset (Fin r)) (K : ℕ) (u : Fin r → I01) :
      S.prod a * Sᶜ.prod (fun i => b i * radI K (u i)) = T S K u := by
    dsimp [T, c, R]
    rw [Finset.prod_mul_distrib]
    ring
  have hexpand (K : ℕ) (u : Fin r → I01) :
      (∏ i : Fin r, (a i + b i * radI K (u i))) =
        ∑ S : Finset (Fin r), T S K u := by
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro S hS
    exact hsubset S K u
  have hintegrand (K : ℕ) (u : Fin r → I01) :
      (∏ i : Fin r, (fourierOrientation K (u i).1) ^ k i) =
        ∑ S : Finset (Fin r), T S K u := by
    calc
      _ = ∏ i : Fin r, (a i + b i * radI K (u i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hdecomp i K (u i)
      _ = ∑ S : Finset (Fin r), T S K u := hexpand K u
  have hRmeas (S : Finset (Fin r)) (K : ℕ) : Measurable (R S K) := by
    dsimp [R]
    exact Finset.measurable_prod S (fun i hi =>
      (radI_measurable K).comp (measurable_pi_apply i))
  have hRbound (S : Finset (Fin r)) (K : ℕ) (u : Fin r → I01) :
      ‖R S K u‖ ≤ 1 := by
    dsimp [R]
    calc
      ‖S.prod (fun i => radI K (u i))‖ ≤
          S.prod (fun i => ‖radI K (u i)‖) := Finset.norm_prod_le _ _
      _ ≤ 1 := by
          apply Finset.prod_le_one
          · intro i hi; exact norm_nonneg _
          · intro i hi
            rw [Real.norm_eq_abs, radI, rademacher_abs]
  have hTint (S : Finset (Fin r)) (K : ℕ) : Integrable (T S K) μ := by
    have hR : Integrable (R Sᶜ K) μ :=
      Integrable.of_bound (hRmeas Sᶜ K).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun u => hRbound Sᶜ K u))
    have hconst := hR.const_mul (c S)
    simpa [T, mul_comm] using hconst
  have htermInt (S : Finset (Fin r)) (K : ℕ) :
      ∫ u : Fin r → I01, T S K u ∂μ =
        c S * ∫ u : Fin r → I01, R Sᶜ K u ∂μ := by
    rw [show (fun u : Fin r → I01 => T S K u) =
        fun u => c S * R Sᶜ K u by rfl]
    rw [integral_const_mul]
  have hIntegralEq (K : ℕ) :
      ∫ u : Fin r → I01, ∏ i : Fin r, (fourierOrientation K (u i).1) ^ k i ∂μ =
        ∑ S : Finset (Fin r), ∫ u : Fin r → I01, T S K u ∂μ := by
    calc
      _ = ∫ u : Fin r → I01, ∑ S : Finset (Fin r), T S K u ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (hintegrand K)
      _ = ∑ S : Finset (Fin r), ∫ u : Fin r → I01, T S K u ∂μ := by
        simpa using (integral_finset_sum (μ := μ) (s := Finset.univ)
          (f := fun S u => T S K u) (fun S hS => hTint S K))
  have htermLimit (S : Finset (Fin r)) :
      Tendsto (fun K : ℕ => ∫ u : Fin r → I01, T S K u ∂μ) atTop
    (𝓝 (if Sᶜ.Nonempty then 0 else c S)) := by
    by_cases hS : Sᶜ.Nonempty
    · have hrad := cdfCubeMap_rademacher_tendsto_zero ν hdom hnoAtoms Sᶜ hS
      have hscaled := (tendsto_const_nhds.mul hrad).congr fun K => (htermInt S K).symm
      simpa [hS] using hscaled
    · have hSfull : S = Finset.univ := by
        have hempty : Sᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        simpa using hempty
      subst S
      simpa [T, R, c] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => c Finset.univ) atTop (𝓝 (c Finset.univ)))
  have hsumLimit : Tendsto
      (fun K : ℕ => ∑ S : Finset (Fin r), ∫ u : Fin r → I01, T S K u ∂μ) atTop
        (𝓝 (∏ i : Fin r, a i)) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset (Finset (Fin r)))
      (fun S _ => htermLimit S)
    have hval :
        (∑ S : Finset (Fin r), if Sᶜ.Nonempty then 0 else c S) =
          ∏ i : Fin r, a i := by
      calc
        _ = c Finset.univ := by
          rw [Finset.sum_eq_single (Finset.univ : Finset (Fin r))]
          · simp
          · intro S hS hSneq
            have hcomp : Sᶜ.Nonempty := by
              by_contra hc
              have hempty : Sᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
              have hfull : S = Finset.univ := by simpa using hempty
              exact hSneq hfull
            simp [hcomp]
          · intro h
            exact (h (Finset.mem_univ _)).elim
        _ = ∏ i : Fin r, a i := by simp [c]
    simpa [hval] using hsum
  have hEq : (fun K : ℕ =>
      ∫ u : Fin r → I01, ∏ i : Fin r, (fourierOrientation K (u i).1) ^ k i ∂μ) =
        fun K => ∑ S : Finset (Fin r), ∫ u : Fin r → I01, T S K u ∂μ := by
    funext K
    exact hIntegralEq K
  rw [hEq]
  simpa [a] using hsumLimit

/-- Pull the distinct-coordinate moment limit back to any probability space
carrying the raw vector of observables. -/
theorem cdfCubeMap_pullback_product_moment_tendsto {α : Type*}
    [MeasurableSpace α] {r : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → Fin r → ℝ) (hX : Measurable X) [IsProbabilityMeasure (μ.map X)]
    (hdom : (μ.map X) ≪ Measure.pi (fun i : Fin r => coordinateMarginal (μ.map X) i))
    (hnoAtoms : ∀ i : Fin r, NoAtoms (coordinateMarginal (μ.map X) i))
    (k : Fin r → ℕ) :
    Tendsto (fun K : ℕ =>
      ∫ z, ∏ i : Fin r,
        (fourierOrientation K ((cdfCubeMap (μ.map X) (X z) i).1)) ^ k i ∂μ)
      atTop (𝓝 (∏ i : Fin r, ((1 : ℝ) ^ k i + (2 : ℝ) ^ k i) / 2)) := by
  let ν := μ.map X
  let Y : α → Fin r → I01 := fun z => cdfCubeMap ν (X z)
  haveI : IsProbabilityMeasure ν := by simpa [ν] using
    (inferInstance : IsProbabilityMeasure (μ.map X))
  have hY : Measurable Y := by
    change Measurable (cdfCubeMap ν ∘ X)
    exact (measurable_cdfCubeMap ν).comp hX
  have hmap : μ.map Y = ν.map (cdfCubeMap ν) := by
    change μ.map (cdfCubeMap ν ∘ X) = (μ.map X).map (cdfCubeMap ν)
    exact (Measure.map_map (measurable_cdfCubeMap ν) hX).symm
  have hintegrand (K : ℕ) : Measurable (fun u : Fin r → I01 =>
      ∏ i : Fin r, (fourierOrientation K ((u i).1)) ^ k i) := by
    exact Finset.measurable_prod Finset.univ (fun i hi =>
      (continuous_pow (k i)).measurable.comp
        ((measurable_fourierOrientation K).comp
          (measurable_subtype_coe.comp (measurable_pi_apply i))))
  have hfun (K : ℕ) :
      (fun z => ∏ i : Fin r,
        (fourierOrientation K ((cdfCubeMap (μ.map X) (X z) i).1)) ^ k i) =
      fun z => (∏ i : Fin r, (fourierOrientation K ((Y z i).1)) ^ k i) := by
    funext z
    simp [Y, ν]
  have hEq (K : ℕ) :
      ∫ z, ∏ i : Fin r,
        (fourierOrientation K ((cdfCubeMap (μ.map X) (X z) i).1)) ^ k i ∂μ =
        ∫ u, ∏ i : Fin r, (fourierOrientation K ((u i).1)) ^ k i ∂ν.map (cdfCubeMap ν) := by
    rw [hfun K]
    calc
      _ = ∫ u, ∏ i : Fin r, (fourierOrientation K ((u i).1)) ^ k i ∂(μ.map Y) := by
        symm
        exact MeasureTheory.integral_map hY.aemeasurable
          (hintegrand K).aestronglyMeasurable
      _ = ∫ u, ∏ i : Fin r, (fourierOrientation K ((u i).1)) ^ k i
          ∂(ν.map (cdfCubeMap ν)) := by rw [hmap]
  have hEqFun : (fun K : ℕ =>
      ∫ z, ∏ i : Fin r,
        (fourierOrientation K ((cdfCubeMap (μ.map X) (X z) i).1)) ^ k i ∂μ) =
      fun K => ∫ u, ∏ i : Fin r, (fourierOrientation K ((u i).1)) ^ k i
        ∂(ν.map (cdfCubeMap ν)) := by
    funext K
    exact hEq K
  rw [hEqFun]
  exact cdfCubeMap_product_moment_tendsto ν hdom hnoAtoms k

theorem plaquetteWilson_pushforward_isProbability
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (v : (cubicTorus4 Ls Lt).Site) :
    IsProbabilityMeasure ((wilsonMeasure Ls Lt N β).map
      (fun U => plaquetteDefect Ls Lt N v U)) := by
  haveI : IsProbabilityMeasure (wilsonMeasure Ls Lt N β) :=
    wilsonMeasure_isProbability Ls Lt N β hβ
  exact Measure.isProbabilityMeasure_map
    (measurable_plaquetteDefect Ls Lt N v).aemeasurable

/-- Fourier orientation selector: `ψ_K(u) = 3/2 - r_K(u)/2 ∈ {1, 2}`. -/
theorem fourierOrientation_range (K : ℕ) (u : ℝ) :
    fourierOrientation K u = 1 ∨ fourierOrientation K u = 2 := by
  unfold fourierOrientation rademacher
  split <;> norm_num

/-- CDF of plaquette defect under Wilson measure at stage m. -/
noncomputable def plaquetteCDF (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (v : (cubicTorus4 Ls Lt).Site) (t : ℝ) : ℝ :=
  ProbabilityTheory.cdf
    ((wilsonMeasure Ls Lt N β).map
      (fun U => plaquetteDefect Ls Lt N v U)) t

theorem plaquetteCDF_bounds (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (v : (cubicTorus4 Ls Lt).Site) (t : ℝ) :
    0 ≤ plaquetteCDF Ls Lt N β hβ v t ∧ plaquetteCDF Ls Lt N β hβ v t ≤ 1 := by
  exact ⟨ProbabilityTheory.cdf_nonneg _ _, ProbabilityTheory.cdf_le_one _ _⟩

private theorem noAtoms_of_absolutelyContinuous_real (ν : Measure ℝ)
    (hν : ν ≪ volume) : NoAtoms ν := by
  constructor
  intro x
  exact hν (by simp)

theorem plaquetteCDF_map_eq_uniform (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (v : (cubicTorus4 Ls Lt).Site)
    (hAC : (wilsonMeasure Ls Lt N β).map
      (fun U => plaquetteDefect Ls Lt N v U) ≪ volume) :
    ((wilsonMeasure Ls Lt N β).map
      (fun U => plaquetteDefect Ls Lt N v U)).map
        (ProbabilityTheory.cdf ((wilsonMeasure Ls Lt N β).map
          (fun U => plaquetteDefect Ls Lt N v U))) = volume.restrict (Set.Ico 0 1) := by
  let ν := (wilsonMeasure Ls Lt N β).map
    (fun U => plaquetteDefect Ls Lt N v U)
  haveI : IsProbabilityMeasure ν := plaquetteWilson_pushforward_isProbability Ls Lt N β hβ v
  haveI : NoAtoms ν := noAtoms_of_absolutelyContinuous_real ν (by simpa [ν] using hAC)
  change ν.map (ProbabilityTheory.cdf ν) = volume.restrict (Set.Ico 0 1)
  exact map_cdf_eq_uniform_Ico ν

/-- Wrap the integer lattice coordinate `⌊x/a⌋` into the periodic direction `Fin L`. -/
noncomputable def stateWrap (L : ℕ) [NeZero L] (a : ℝ) (ha : 0 < a)
    (x : ℝ) : Fin L :=
  Fin.ofNat L (Int.natMod (⌊x / a⌋) L)

/-- Map four real coordinates to the periodic spacetime lattice at spacing `a`. -/
noncomputable def stageSiteMap (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (a : ℝ) (ha : 0 < a) (x : Space4) :
    (cubicTorus4 Ls Lt).Site :=
  (stateWrap Lt a ha (x 0), stateWrap Ls a ha (x 1),
    stateWrap Ls a ha (x 2), stateWrap Ls a ha (x 3))

noncomputable def stageSitePoint (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (a : ℝ) (v : (cubicTorus4 Ls Lt).Site) : Space4 :=
  ![((v.1.val : ℝ) * a), ((v.2.1.val : ℝ) * a),
    ((v.2.2.1.val : ℝ) * a), ((v.2.2.2.val : ℝ) * a)]

private theorem stateWrap_finVal (L : ℕ) [NeZero L] (a : ℝ) (ha : 0 < a)
    (v : Fin L) : stateWrap L a ha ((v.val : ℝ) * a) = v := by
  have hfloor : ⌊(v.val : ℝ) * a / a⌋ = (v.val : ℤ) := by
    rw [mul_div_cancel_right₀ _ ha.ne']
    simp
  have hrem : (v.val : ℤ) % (L : ℤ) = (v.val : ℤ) :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast v.isLt)
  apply Fin.ext
  change (Int.natMod ⌊(v.val : ℝ) * a / a⌋ L) % L = v.val
  simp [Int.natMod, hfloor, hrem, Nat.mod_eq_of_lt v.isLt]

theorem stageSiteMap_stageSitePoint (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (a : ℝ) (ha : 0 < a) (v : (cubicTorus4 Ls Lt).Site) :
    stageSiteMap Ls Lt a ha (stageSitePoint Ls Lt a v) = v := by
  rcases v with ⟨t, x, y, z⟩
  change (stateWrap Lt a ha ((t.val : ℝ) * a),
    stateWrap Ls a ha ((x.val : ℝ) * a),
    stateWrap Ls a ha ((y.val : ℝ) * a),
    stateWrap Ls a ha ((z.val : ℝ) * a)) = (t, x, y, z)
  exact Prod.ext (stateWrap_finVal Lt a ha t)
    (Prod.ext (stateWrap_finVal Ls a ha x)
      (Prod.ext (stateWrap_finVal Ls a ha y) (stateWrap_finVal Ls a ha z)))

noncomputable def stageLinearSize (m : ℕ) : ℕ := m + 2

noncomputable def stagePeriodicSide (m : ℕ) : ℕ := stageLinearSize m ^ 2

private theorem stagePeriodicSide_pos (m : ℕ) : 0 < stagePeriodicSide m := by
  exact Nat.pow_pos (by simp [stageLinearSize])

noncomputable instance stagePeriodicSide_neZero (m : ℕ) :
    NeZero (stagePeriodicSide m) := ⟨Nat.ne_of_gt (stagePeriodicSide_pos m)⟩

noncomputable def stageSpacing (m : ℕ) : ℝ := 1 / (stageLinearSize m : ℝ)

private theorem stageSpacing_pos (m : ℕ) : 0 < stageSpacing m := by
  dsimp [stageSpacing, stageLinearSize]
  positivity

private theorem stageSpacing_tendsto_zero :
    Filter.Tendsto stageSpacing Filter.atTop (nhds 0) := by
  have hlinear : Filter.Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop := by
    apply Filter.tendsto_atTop_mono (f := fun m : ℕ => (m : ℝ))
    · intro m
      norm_num
    · exact tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hlinear
  have hsp : stageSpacing = fun m : ℕ => ((m : ℝ) + 2)⁻¹ := by
    funext m
    simp [stageSpacing, stageLinearSize, one_div, Nat.cast_add]
  rw [hsp]
  exact hinv

private theorem stagePeriodicVolume_tendsto_atTop :
    Filter.Tendsto (fun m => (stagePeriodicSide m : ℝ) * stageSpacing m)
      Filter.atTop Filter.atTop := by
  have hlinear : Filter.Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop := by
    apply Filter.tendsto_atTop_mono (f := fun m : ℕ => (m : ℝ))
    · intro m
      norm_num
    · exact tendsto_natCast_atTop_atTop
  have heq : (fun m : ℕ => (stagePeriodicSide m : ℝ) * stageSpacing m) =
      fun m : ℕ => (m : ℝ) + 2 := by
    funext m
    dsimp [stagePeriodicSide, stageLinearSize, stageSpacing]
    push_cast
    field_simp
  rw [heq]
  exact hlinear

private noncomputable def stageSiteCoords (L : ℕ) [NeZero L]
    (v : (cubicTorus4 L L).Site) : Fin 4 → Fin L :=
  ![v.1, v.2.1, v.2.2.1, v.2.2.2]

private theorem stageSiteCoords_injective (L : ℕ) [NeZero L] :
    Function.Injective (stageSiteCoords L) := by
  intro v w h
  rcases v with ⟨t, x, y, z⟩
  rcases w with ⟨t', x', y', z'⟩
  have h0 : t = t' := by simpa [stageSiteCoords] using congrFun h 0
  have h1 : x = x' := by simpa [stageSiteCoords] using congrFun h 1
  have h2 : y = y' := by simpa [stageSiteCoords] using congrFun h 2
  have h3 : z = z' := by simpa [stageSiteCoords] using congrFun h 3
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

private theorem stateWrap_eq_torusCoord (L : ℕ) [NeZero L] (a : ℝ) (ha : 0 < a)
    (x : ℝ) :
    stateWrap L a ha x = Imscribing.YangMills.TorusWraparoundBridge.torusCoord L a x := by
  rfl

private theorem stageSiteCoords_eq_torusSite (m : ℕ) (x : Space4) :
    stageSiteCoords (stagePeriodicSide m)
        (stageSiteMap (stagePeriodicSide m) (stagePeriodicSide m)
          (stageSpacing m) (stageSpacing_pos m) x) =
      Imscribing.YangMills.TorusWraparoundBridge.torusSite
        (stagePeriodicSide m) (stageSpacing m) x := by
  letI : NeZero (stagePeriodicSide m) := stagePeriodicSide_neZero m
  funext μ
  fin_cases μ <;>
    simp [stageSiteCoords, stageSiteMap,
      Imscribing.YangMills.TorusWraparoundBridge.torusSite, stateWrap_eq_torusCoord]

/-- At sufficiently fine infinite-volume stages, the exact periodic site map
separates every fixed tuple of distinct continuum points. -/
theorem stageSiteMap_eventually_injective {r : ℕ} (xs : Fin r → Space4)
    (hxs : Function.Injective xs) :
    ∃ m₀, ∀ m ≥ m₀,
      Function.Injective (fun i => stageSiteMap (stagePeriodicSide m)
        (stagePeriodicSide m) (stageSpacing m) (stageSpacing_pos m) (xs i)) := by
  letI : ∀ m, NeZero (stagePeriodicSide m) := fun m => stagePeriodicSide_neZero m
  obtain ⟨m₀, hm₀⟩ :=
    Imscribing.YangMills.TorusWraparoundBridge.torus_eventually_injective_infinite_volume
      (L := stagePeriodicSide) (a := stageSpacing)
      stageSpacing_pos stageSpacing_tendsto_zero stagePeriodicVolume_tendsto_atTop xs hxs
  refine ⟨m₀, fun m hm => ?_⟩
  intro i j hsite
  have htorus :
      Imscribing.YangMills.TorusWraparoundBridge.torusSite
        (stagePeriodicSide m) (stageSpacing m) (xs i) =
      Imscribing.YangMills.TorusWraparoundBridge.torusSite
        (stagePeriodicSide m) (stageSpacing m) (xs j) := by
    have hcoords := congrArg (stageSiteCoords (stagePeriodicSide m)) hsite
    rw [stageSiteCoords_eq_torusSite, stageSiteCoords_eq_torusSite] at hcoords
    exact hcoords
  exact (hm₀ m hm) (by simpa [Function.comp_apply] using htorus)

abbrev stageMomentIndex (m : ℕ) :=
  Σ r : Fin (m + 1),
    ({ys : Fin r.val → (cubicTorus4 (stagePeriodicSide m) (stagePeriodicSide m)).Site //
        Function.Injective ys} × (Fin r.val → Fin (m + 1)))

private noncomputable def stageMomentPoints (m : ℕ) (t : stageMomentIndex m) :
    Fin t.1.val → Space4 :=
  fun i => stageSitePoint (stagePeriodicSide m) (stagePeriodicSide m)
    (stageSpacing m) (t.2.1.1 i)

private noncomputable def stageMomentPowers (m : ℕ) (t : stageMomentIndex m) :
    Fin t.1.val → ℕ := fun i => (t.2.2 i).val

/-- The observable: O_m(x, U) = ψ_{K_m}(F_m(X_{p(v_m(x))}(U))). -/
noncomputable def stageObservable (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a) (x : Space4) (K : ℕ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ := by
  let v := stageSiteMap Ls Lt a ha x
  exact fourierOrientation K
    (plaquetteCDF Ls Lt N β hβ v (plaquetteDefect Ls Lt N v U))

theorem stageObservable_eq_of_siteMap_eq
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a)
    (x y : Space4) (K : ℕ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hsite : stageSiteMap Ls Lt a ha x = stageSiteMap Ls Lt a ha y) :
    stageObservable Ls Lt N β hβ a ha x K U =
      stageObservable Ls Lt N β hβ a ha y K U := by
  simp [stageObservable, hsite]

/-- For a finite family of distinct lattice sites, the stage observable moments
converge to independent `iidMom` values as the frequency increases. The joint
law domination is retained explicitly because it carries the correlations. -/
theorem stageObservable_distinctSite_moments_tendsto
    (Ls Lt N r : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a)
    (xs : Fin r → Space4) (k : Fin r → ℕ)
    (hN : 2 ≤ N) (hLt2 : 2 ≤ Lt)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (hdom : (wilsonMeasure Ls Lt N β).map
      (fun U i => plaquetteDefect Ls Lt N
        (stageSiteMap Ls Lt a ha (xs i)) U) ≪
      Measure.pi (fun i : Fin r => coordinateMarginal
        ((wilsonMeasure Ls Lt N β).map
          (fun U i => plaquetteDefect Ls Lt N
            (stageSiteMap Ls Lt a ha (xs i)) U)) i)) :
    Tendsto (fun K : ℕ =>
      ∫ U, ∏ i : Fin r,
        (stageObservable Ls Lt N β hβ a ha (xs i) K U) ^ k i
          ∂(wilsonMeasure Ls Lt N β)) atTop
      (𝓝 (∏ i : Fin r, ((1 : ℝ) ^ k i + (2 : ℝ) ^ k i) / 2)) := by
  let μ := wilsonMeasure Ls Lt N β
  let X : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      (Fin r → ℝ) := fun U i =>
        plaquetteDefect Ls Lt N (stageSiteMap Ls Lt a ha (xs i)) U
  let ν := μ.map X
  haveI : IsProbabilityMeasure μ := wilsonMeasure_isProbability Ls Lt N β hβ
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_plaquetteDefect Ls Lt N (stageSiteMap Ls Lt a ha (xs i))
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hX.aemeasurable
  have hMarginal (i : Fin r) : coordinateMarginal ν i =
      μ.map (fun U => plaquetteDefect Ls Lt N
        (stageSiteMap Ls Lt a ha (xs i)) U) := by
    change (μ.map X).map (fun y => y i) = _
    rw [Measure.map_map (measurable_pi_apply i) hX]
    rfl
  have hNoAtoms : ∀ i : Fin r, NoAtoms (coordinateMarginal ν i) := by
    intro i
    have hAC : coordinateMarginal ν i ≪ volume := by
      rw [hMarginal i]
      exact wilson_plaquette_absolutelyContinuous Ls Lt N β hβ hN hLt2
        submersion_1d (stageSiteMap Ls Lt a ha (xs i))
    exact noAtoms_of_absolutelyContinuous_real _ hAC
  haveI : IsProbabilityMeasure (μ.map X) := by
    simpa [ν] using (inferInstance : IsProbabilityMeasure ν)
  have hpull := cdfCubeMap_pullback_product_moment_tendsto
    μ X hX hdom hNoAtoms k
  have hcoord (K : ℕ) (U : GaugeField (cubicTorus4 Ls Lt)
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) (i : Fin r) :
      (cdfCubeMap ν (X U) i).1 =
        plaquetteCDF Ls Lt N β hβ (stageSiteMap Ls Lt a ha (xs i))
          (plaquetteDefect Ls Lt N (stageSiteMap Ls Lt a ha (xs i)) U) := by
    change ProbabilityTheory.cdf (coordinateMarginal ν i) (X U i) = _
    rw [hMarginal i]
    rfl
  have hpoint (K : ℕ) (U : GaugeField (cubicTorus4 Ls Lt)
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
      (∏ i : Fin r, (stageObservable Ls Lt N β hβ a ha (xs i) K U) ^ k i) =
        ∏ i : Fin r,
          (fourierOrientation K ((cdfCubeMap ν (X U) i).1)) ^ k i := by
    apply Finset.prod_congr rfl
    intro i hi
    change (fourierOrientation K
        (plaquetteCDF Ls Lt N β hβ (stageSiteMap Ls Lt a ha (xs i))
          (plaquetteDefect Ls Lt N (stageSiteMap Ls Lt a ha (xs i)) U))) ^ k i = _
    rw [← hcoord K U i]
  have hEq (K : ℕ) :
      ∫ U, ∏ i : Fin r, (stageObservable Ls Lt N β hβ a ha (xs i) K U) ^ k i ∂μ =
        ∫ U, ∏ i : Fin r,
          (fourierOrientation K ((cdfCubeMap ν (X U) i).1)) ^ k i ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (hpoint K)
  have hEqFun : (fun K : ℕ =>
      ∫ U, ∏ i : Fin r, (stageObservable Ls Lt N β hβ a ha (xs i) K U) ^ k i ∂μ) =
      fun K => ∫ U, ∏ i : Fin r,
        (fourierOrientation K ((cdfCubeMap ν (X U) i).1)) ^ k i ∂μ := by
    funext K
    exact hEq K
  rw [hEqFun]
  simpa [μ, ν, X] using hpull

/-- The distinct-site moment limit with product-marginal domination derived
from the corresponding product-Haar law. -/
theorem stageObservable_distinctSite_moments_tendsto_of_haar_independent
    (Ls Lt N r : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a)
    (xs : Fin r → Space4) (k : Fin r → ℕ)
    (hN : 2 ≤ N) (hLt2 : 2 ≤ Lt)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (hhaar : (spacetimeHaarMeasure Ls Lt N).map
      (fun U i => plaquetteDefect Ls Lt N
        (stageSiteMap Ls Lt a ha (xs i)) U) =
      Measure.pi (fun i : Fin r => coordinateMarginal
        ((spacetimeHaarMeasure Ls Lt N).map
          (fun U i => plaquetteDefect Ls Lt N
            (stageSiteMap Ls Lt a ha (xs i)) U)) i)) :
    Tendsto (fun K : ℕ =>
      ∫ U, ∏ i : Fin r,
        (stageObservable Ls Lt N β hβ a ha (xs i) K U) ^ k i
          ∂(wilsonMeasure Ls Lt N β)) atTop
      (𝓝 (∏ i : Fin r, ((1 : ℝ) ^ k i + (2 : ℝ) ^ k i) / 2)) := by
  let F : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      Fin r → ℝ := fun U i =>
        plaquetteDefect Ls Lt N (stageSiteMap Ls Lt a ha (xs i)) U
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_plaquetteDefect Ls Lt N (stageSiteMap Ls Lt a ha (xs i))
  have hdom : (wilsonMeasure Ls Lt N β).map F ≪
      Measure.pi (fun i : Fin r => coordinateMarginal
        ((wilsonMeasure Ls Lt N β).map F) i) := by
    exact wilson_joint_dominated_by_marginals_of_haar_independent
      Ls Lt N r β hβ F hF (by simpa [F] using hhaar)
  exact stageObservable_distinctSite_moments_tendsto
    Ls Lt N r β hβ a ha xs k hN hLt2 submersion_1d (by simpa [F] using hdom)

/-- For distinct stage sites, the product-Haar lattice law and positivity of the
Wilson density derive the domination required by the probability-transform
moment theorem directly from the lattice maps. -/
theorem stageObservable_distinctSite_moments_tendsto_of_lattice_maps
    (Ls Lt N r : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a)
    (xs : Fin r → Space4) (k : Fin r → ℕ)
    (hN : 2 ≤ N) (hLt2 : 2 ≤ Lt) (hr : r + 1 ≤ Lt)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (hsite : Function.Injective (fun i => stageSiteMap Ls Lt a ha (xs i))) :
    Tendsto (fun K : ℕ =>
      ∫ U, ∏ i : Fin r,
        (stageObservable Ls Lt N β hβ a ha (xs i) K U) ^ k i
          ∂(wilsonMeasure Ls Lt N β)) atTop
      (𝓝 (∏ i : Fin r, ((1 : ℝ) ^ k i + (2 : ℝ) ^ k i) / 2)) := by
  let v : Fin r → (cubicTorus4 Ls Lt).Site :=
    fun i => stageSiteMap Ls Lt a ha (xs i)
  have hdom := wilson_plaquette_joint_dominated_by_marginals
    Ls Lt N r β hβ hN hLt2 hr submersion_1d v hsite
  exact stageObservable_distinctSite_moments_tendsto
    Ls Lt N r β hβ a ha xs k hN hLt2 submersion_1d (by simpa [v] using hdom)

private noncomputable def stageMomentValue
    (N : ℕ)
    (hN : 2 ≤ N) (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U →
      ContDiffOn ℝ 1 g U → (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (m : ℕ) (t : stageMomentIndex m) (K : ℕ) : ℝ :=
  ∫ U, ∏ i : Fin t.1.val,
    (stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)
      (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m)
      (stageMomentPoints m t i) K U) ^ stageMomentPowers m t i
    ∂wilsonMeasure (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)

private noncomputable def stageMomentLimit (m : ℕ) (t : stageMomentIndex m) : ℝ :=
  ∏ i : Fin t.1.val,
    ((1 : ℝ) ^ stageMomentPowers m t i + (2 : ℝ) ^ stageMomentPowers m t i) / 2

private noncomputable def stageMomentIndexFintype (m : ℕ) : Fintype (stageMomentIndex m) := by
  classical
  letI : ∀ r : Fin (m + 1), Fintype
      (Fin r.val → (cubicTorus4 (stagePeriodicSide m) (stagePeriodicSide m)).Site) :=
    fun _ => inferInstance
  letI : ∀ r : Fin (m + 1),
      Fintype {ys : Fin r.val → (cubicTorus4 (stagePeriodicSide m)
        (stagePeriodicSide m)).Site // Function.Injective ys} := fun r =>
    Fintype.subtype (Finset.univ.filter (fun ys => Function.Injective ys)) (by
      intro ys
      simp)
  letI : ∀ r : Fin (m + 1), Fintype (Fin r.val → Fin (m + 1)) :=
    fun _ => inferInstance
  letI : ∀ r : Fin (m + 1), Fintype
      (({ys : Fin r.val → (cubicTorus4 (stagePeriodicSide m)
        (stagePeriodicSide m)).Site // Function.Injective ys}) ×
        (Fin r.val → Fin (m + 1))) := fun _ => inferInstance
  exact inferInstance

private theorem stageMomentValue_tendsto
    (N : ℕ)
    (hN : 2 ≤ N) (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U →
      ContDiffOn ℝ 1 g U → (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (m : ℕ) (t : stageMomentIndex m) :
    Filter.Tendsto (stageMomentValue N hN submersion_1d m t) atTop
      (nhds (stageMomentLimit m t)) := by
  let ys := stageMomentPoints m t
  let k := stageMomentPowers m t
  have hsite : Function.Injective (fun i => stageSiteMap (stagePeriodicSide m)
      (stagePeriodicSide m) (stageSpacing m) (stageSpacing_pos m) (ys i)) := by
    intro i j hij
    apply t.2.1.2
    simpa [ys, stageMomentPoints, stageSiteMap_stageSitePoint] using hij
  have hside : m + 1 ≤ stagePeriodicSide m := by
    change m + 1 ≤ (m + 2) ^ 2
    have hR : (m : ℝ) + 1 ≤ ((m : ℝ) + 2) ^ 2 := by nlinarith [sq_nonneg (m : ℝ)]
    exact_mod_cast hR
  have hr : t.1.val + 1 ≤ stagePeriodicSide m :=
    le_trans (Nat.succ_le_of_lt t.1.isLt) hside
  have hLt2 : 2 ≤ stagePeriodicSide m := by
    change 2 ≤ (m + 2) ^ 2
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have hR : (2 : ℝ) ≤ ((m : ℝ) + 2) ^ 2 := by nlinarith
    exact_mod_cast hR
  change Filter.Tendsto
    (fun K => ∫ U, ∏ i : Fin t.1.val,
      (stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)
        (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m)
        (stageMomentPoints m t i) K U) ^ stageMomentPowers m t i
      ∂wilsonMeasure (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)) atTop
    (nhds (∏ i : Fin t.1.val,
      ((1 : ℝ) ^ stageMomentPowers m t i + (2 : ℝ) ^ stageMomentPowers m t i) / 2))
  exact @stageObservable_distinctSite_moments_tendsto_of_lattice_maps
    (stagePeriodicSide m) (stagePeriodicSide m) N t.1.val
    (inferInstance : NeZero (stagePeriodicSide m))
    (inferInstance : NeZero (stagePeriodicSide m))
    (m : ℝ) (Nat.cast_nonneg _)
    (stageSpacing m) (stageSpacing_pos m) (stageMomentPoints m t)
    (stageMomentPowers m t) hN hLt2 hr submersion_1d hsite

/-- One frequency at each finite stage controls all tuples of lattice sites and
all insertion multiplicities up to that stage. -/
noncomputable def stageFrequency
    (N : ℕ)
    (hN : 2 ≤ N) (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U →
      ContDiffOn ℝ 1 g U → (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (m : ℕ) : ℕ := by
  classical
  letI : Fintype (stageMomentIndex m) := stageMomentIndexFintype m
  exact Imscribing.Millennium.ContinuumLatticeBridge.uniformFrequency
    (stageMomentValue N hN submersion_1d m) (stageMomentLimit m)
    (stageMomentValue_tendsto N hN submersion_1d m)
    (1 / (m + 1 : ℝ)) (by positivity)

theorem stageFrequency_spec
    (N : ℕ)
    (hN : 2 ≤ N) (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U →
      ContDiffOn ℝ 1 g U → (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (m : ℕ) (t : stageMomentIndex m) :
    dist (stageMomentValue N hN submersion_1d m t (stageFrequency N hN submersion_1d m))
      (stageMomentLimit m t) < 1 / (m + 1 : ℝ) := by
  classical
  letI : Fintype (stageMomentIndex m) := stageMomentIndexFintype m
  exact Imscribing.Millennium.ContinuumLatticeBridge.uniformFrequency_spec
    (stageMomentValue N hN submersion_1d m) (stageMomentLimit m)
    (stageMomentValue_tendsto N hN submersion_1d m)
    (1 / (m + 1 : ℝ)) (by positivity) t

/-- The stage-selected Wilson observables converge to the concrete iid
Schwinger functional, including tuples with repeated continuum points. -/
theorem stageObservableSchwinger_tendsto_iid
    (N : ℕ) (hN : 2 ≤ N)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (n : ℕ) (xs : Fin n → Space4) :
    Filter.Tendsto
      (fun m => cubic4Schwinger (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ) n
        (fun i U =>
          ((stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)
            (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m) (xs i)
            (stageFrequency N hN submersion_1d m) U : ℝ) : ℂ)))
      atTop (nhds (iidSchwinger n xs)) := by
  classical
  let S := iidSupport xs
  let e := S.equivFin
  let rep : Fin S.card → Space4 := fun i => (e.symm i).val
  have hrep : Function.Injective rep := by
    intro i j h
    apply e.symm.injective
    exact Subtype.ext h
  obtain ⟨m₀, hm₀⟩ := stageSiteMap_eventually_injective rep hrep
  have hcard : S.card ≤ n := by
    dsimp [S, iidSupport]
    calc
      (Finset.univ.image xs).card ≤ Finset.univ.card := Finset.card_image_le
      _ = n := Finset.card_fin n
  have hprod_enum (g : Space4 → ℝ) :
      S.prod g = ∏ i : Fin S.card, g (rep i) := by
    calc
      S.prod g = ∏ y : S, g y.val := by
        symm
        simpa using (Finset.prod_attach S g)
      _ = ∏ i : Fin S.card, g (rep i) := by
        exact Fintype.prod_equiv e (fun y : S => g y.val)
          (fun i => g (rep i)) (by intro y; simp [rep, e])
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Mε, hMε⟩ := exists_nat_one_div_lt hε
  refine ⟨max (max n m₀) Mε, fun m hm => ?_⟩
  have hnm : n ≤ m := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm)
  have hmgeom : m₀ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hmeps : Mε ≤ m := le_trans (le_max_right _ _) hm
  let rfin : Fin (m + 1) := ⟨S.card, Nat.lt_succ_of_le (le_trans hcard hnm)⟩
  let siteTuple : Fin S.card → (cubicTorus4 (stagePeriodicSide m)
      (stagePeriodicSide m)).Site := fun i =>
    stageSiteMap (stagePeriodicSide m) (stagePeriodicSide m) (stageSpacing m)
      (stageSpacing_pos m) (rep i)
  have hsites : Function.Injective siteTuple := by
    simpa [siteTuple] using hm₀ m hmgeom
  have hmult : ∀ i : Fin S.card, (iidFiber xs (rep i)).card ≤ m := by
    intro i
    have hle : (iidFiber xs (rep i)).card ≤ n := by
      unfold iidFiber
      calc
        (Finset.univ.filter fun j : Fin n => xs j = rep i).card ≤ Finset.univ.card := by
          exact Finset.card_filter_le (Finset.univ : Finset (Fin n)) _
        _ = n := Finset.card_fin n
    exact le_trans hle hnm
  let t : stageMomentIndex m :=
    ⟨rfin, (⟨siteTuple, hsites⟩,
      fun i => ⟨(iidFiber xs (rep i)).card, Nat.lt_succ_of_le (hmult i)⟩)⟩
  have ht_pow (i : Fin S.card) :
      stageMomentPowers m t i = (iidFiber xs (rep i)).card := by
    rfl
  have ht_point (i : Fin S.card) :
      stageMomentPoints m t i = stageSitePoint (stagePeriodicSide m) (stagePeriodicSide m)
        (stageSpacing m) (siteTuple i) := by
    rfl
  have ht_site (i : Fin S.card) :
      stageSiteMap (stagePeriodicSide m) (stagePeriodicSide m) (stageSpacing m)
        (stageSpacing_pos m) (rep i) =
      stageSiteMap (stagePeriodicSide m) (stagePeriodicSide m) (stageSpacing m)
        (stageSpacing_pos m) (stageMomentPoints m t i) := by
    rw [ht_point]
    calc
      stageSiteMap (stagePeriodicSide m) (stagePeriodicSide m) (stageSpacing m)
          (stageSpacing_pos m) (rep i) = siteTuple i := rfl
      _ = stageSiteMap (stagePeriodicSide m) (stagePeriodicSide m) (stageSpacing m)
          (stageSpacing_pos m) (stageSitePoint (stagePeriodicSide m) (stagePeriodicSide m)
            (stageSpacing m) (siteTuple i)) :=
        (stageSiteMap_stageSitePoint (stagePeriodicSide m) (stagePeriodicSide m)
          (stageSpacing m) (stageSpacing_pos m) (siteTuple i)).symm
  let K := stageFrequency N hN submersion_1d m
  let f : GaugeField (cubicTorus4 (stagePeriodicSide m) (stagePeriodicSide m))
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ := fun U =>
        ∏ i : Fin n, stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N
          (m : ℝ) (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m)
          (xs i) K U
  let obs : Fin n → GaugeField (cubicTorus4 (stagePeriodicSide m) (stagePeriodicSide m))
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ := fun i U =>
        (stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)
          (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m) (xs i) K U : ℂ)
  have hobsprod (U : GaugeField (cubicTorus4 (stagePeriodicSide m) (stagePeriodicSide m))
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
      (∏ i : Fin n, obs i U) = (f U : ℂ) := by
    simp [obs, f, map_prod]
  have hobs_integral := cubic4Schwinger_eq_real_wilsonExpectation
    (stagePeriodicSide m) (stagePeriodicSide m) N n (m : ℝ) (Nat.cast_nonneg _)
    obs f hobsprod
  have hprod_fun : f = fun U =>
      ∏ i : Fin S.card,
        (stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)
          (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m)
          (stageMomentPoints m t i) K U) ^ stageMomentPowers m t i := by
    funext U
    dsimp [f]
    calc
      (∏ i : Fin n, stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N
          (m : ℝ) (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m) (xs i) K U)
        = S.prod (fun y =>
            (stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)
              (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m) y K U) ^
              (iidFiber xs y).card) := by
                simpa [S, iidSupport, iidFiber] using
                  (prod_regroup
                    (fun y => stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N
                      (m : ℝ) (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m) y K U)
                    xs)
      _ = ∏ i : Fin S.card,
            (stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)
              (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m)
              (rep i) K U) ^ (iidFiber xs (rep i)).card := hprod_enum _
      _ = ∏ i : Fin S.card,
            (stageObservable (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)
              (Nat.cast_nonneg _) (stageSpacing m) (stageSpacing_pos m)
              (stageMomentPoints m t i) K U) ^ stageMomentPowers m t i := by
                apply Finset.prod_congr rfl
                intro i hi
                rw [stageObservable_eq_of_siteMap_eq]
                · rw [ht_pow i]
                · exact ht_site i
  have hreal_integral :
      (∫ U, f U ∂wilsonMeasure (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ)) =
        stageMomentValue N hN submersion_1d m t K := by
    rw [hprod_fun]
    rfl
  have happrox := stageFrequency_spec N hN submersion_1d m t
  have hschw :
      cubic4Schwinger (stagePeriodicSide m) (stagePeriodicSide m) N (m : ℝ) n obs =
        (stageMomentValue N hN submersion_1d m t K : ℂ) := by
    rw [hobs_integral, hreal_integral]
  have hlim : (stageMomentLimit m t : ℂ) = iidSchwinger n xs := by
    have hlimitR : stageMomentLimit m t =
        S.prod (fun y =>
          ((1 : ℝ) ^ (iidFiber xs y).card + (2 : ℝ) ^ (iidFiber xs y).card) / 2) := by
      unfold stageMomentLimit
      symm
      exact hprod_enum (fun y =>
        ((1 : ℝ) ^ (iidFiber xs y).card + (2 : ℝ) ^ (iidFiber xs y).card) / 2)
    rw [hlimitR, iidSchwinger_eq_fiberProd, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro y hy
    simp [iidMom, Complex.ofReal_pow, Complex.ofReal_div]
  change dist (cubic4Schwinger (stagePeriodicSide m) (stagePeriodicSide m) N
    (m : ℝ) n obs) (iidSchwinger n xs) < ε
  rw [hschw, ← hlim]
  have hfrac : (1 : ℝ) / (m + 1 : ℝ) ≤ 1 / (Mε + 1 : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ hmeps
  have happrox' : dist ((stageMomentValue N hN submersion_1d m t K : ℝ) : ℂ)
      ((stageMomentLimit m t : ℝ) : ℂ) < 1 / (m + 1 : ℝ) := by
    have happroxR : dist (stageMomentValue N hN submersion_1d m t K)
        (stageMomentLimit m t) < 1 / (m + 1 : ℝ) := by
      simpa [K] using happrox
    rw [Complex.isometry_ofReal.dist_eq]
    exact happroxR
  exact lt_trans happrox' (lt_of_le_of_lt hfrac hMε)

theorem stageObservable_range (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a) (x : Space4) (K : ℕ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    stageObservable Ls Lt N β hβ a ha x K U = 1 ∨
      stageObservable Ls Lt N β hβ a ha x K U = 2 := by
  exact fourierOrientation_range K _

theorem measurable_stageObservable (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a) (x : Space4) (K : ℕ) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt)
      (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        stageObservable Ls Lt N β hβ a ha x K U) := by
  let v := stageSiteMap Ls Lt a ha x
  let ν := (wilsonMeasure Ls Lt N β).map
    (fun U => plaquetteDefect Ls Lt N v U)
  have hcdf : Measurable (ProbabilityTheory.cdf ν) :=
    (ProbabilityTheory.monotone_cdf ν).measurable
  unfold stageObservable
  exact (measurable_fourierOrientation K).comp
    (hcdf.comp (measurable_plaquetteDefect Ls Lt N v))

/-- The stage observable has the pushforward of a uniform CDF value. -/
theorem stageObservable_pushforward_eq_uniform_orientation
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a) (x : Space4) (K : ℕ)
    (hAC : (wilsonMeasure Ls Lt N β).map
      (fun U => plaquetteDefect Ls Lt N (stageSiteMap Ls Lt a ha x) U) ≪ volume) :
    (wilsonMeasure Ls Lt N β).map
        (fun U => stageObservable Ls Lt N β hβ a ha x K U) =
      (volume.restrict (Set.Ico (0 : ℝ) 1)).map (fourierOrientation K) := by
  let μ := wilsonMeasure Ls Lt N β
  let X : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ :=
    fun U => plaquetteDefect Ls Lt N (stageSiteMap Ls Lt a ha x) U
  let ν : Measure ℝ := μ.map X
  have hX : Measurable X := measurable_plaquetteDefect Ls Lt N
    (stageSiteMap Ls Lt a ha x)
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, μ, X]
    exact plaquetteWilson_pushforward_isProbability Ls Lt N β hβ
      (stageSiteMap Ls Lt a ha x)
  have hcdf : Measurable (ProbabilityTheory.cdf ν) :=
    (ProbabilityTheory.monotone_cdf ν).measurable
  have huniform : ν.map (ProbabilityTheory.cdf ν) =
      volume.restrict (Set.Ico (0 : ℝ) 1) := by
    change (wilsonMeasure Ls Lt N β).map
      (fun U => plaquetteDefect Ls Lt N (stageSiteMap Ls Lt a ha x) U) ≪ volume at hAC
    simpa [ν, μ, X] using
      plaquetteCDF_map_eq_uniform Ls Lt N β hβ (stageSiteMap Ls Lt a ha x) hAC
  have hobs : (fun U => stageObservable Ls Lt N β hβ a ha x K U) =
      fun U => fourierOrientation K (ProbabilityTheory.cdf ν (X U)) := by
    funext U
    simp [stageObservable, plaquetteCDF, ν, μ, X]
  rw [hobs]
  change μ.map (fourierOrientation K ∘ (ProbabilityTheory.cdf ν ∘ X)) = _
  rw [← Measure.map_map (measurable_fourierOrientation K)
    (hcdf.comp hX)]
  change (μ.map (ProbabilityTheory.cdf ν ∘ X)).map (fourierOrientation K) = _
  rw [← Measure.map_map hcdf hX]
  change (ν.map (ProbabilityTheory.cdf ν)).map (fourierOrientation K) = _
  rw [huniform]

/-- At one site, every positive-frequency stage has the iid moments. -/
theorem stageObservable_moment
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a) (x : Space4) (K : ℕ)
    (hK : 0 < K) (k : ℕ)
    (hAC : (wilsonMeasure Ls Lt N β).map
      (fun U => plaquetteDefect Ls Lt N (stageSiteMap Ls Lt a ha x) U) ≪ volume) :
    ∫ U, (stageObservable Ls Lt N β hβ a ha x K U) ^ k
      ∂(wilsonMeasure Ls Lt N β) = ((1 : ℝ) ^ k + (2 : ℝ) ^ k) / 2 := by
  have hpush := stageObservable_pushforward_eq_uniform_orientation
    Ls Lt N β hβ a ha x K hAC
  calc
    ∫ U, (stageObservable Ls Lt N β hβ a ha x K U) ^ k
        ∂(wilsonMeasure Ls Lt N β)
      = ∫ y, y ^ k ∂((wilsonMeasure Ls Lt N β).map
          (fun U => stageObservable Ls Lt N β hβ a ha x K U)) := by
            symm
            exact MeasureTheory.integral_map
              (measurable_stageObservable Ls Lt N β hβ a ha x K).aemeasurable
              (continuous_pow k).measurable.aestronglyMeasurable
    _ = ∫ y, y ^ k ∂((volume.restrict (Set.Ico (0 : ℝ) 1)).map
          (fourierOrientation K)) := by rw [hpush]
    _ = ∫ u in Set.Ico (0 : ℝ) 1, (fourierOrientation K u) ^ k := by
          exact MeasureTheory.integral_map
            (measurable_fourierOrientation K).aemeasurable
            (continuous_pow k).measurable.aestronglyMeasurable
    _ = ((1 : ℝ) ^ k + (2 : ℝ) ^ k) / 2 := by
          have hdecomp (u : ℝ) : (fourierOrientation K u) ^ k =
              ((1 : ℝ) ^ k + (2 : ℝ) ^ k) / 2 +
                (((1 : ℝ) ^ k - (2 : ℝ) ^ k) / 2) * rademacher K u := by
            unfold fourierOrientation rademacher
            split <;> norm_num <;> ring
          have hrad_meas : AEStronglyMeasurable (rademacher K)
              (volume.restrict (Set.Ico (0 : ℝ) 1)) :=
            (rademacher_measurable K).aestronglyMeasurable.mono_measure
              Measure.restrict_le_self
          have hrad_fin : volume (Set.Ico (0 : ℝ) 1) < ⊤ := by
            rw [Real.volume_Ico]
            finiteness
          haveI : IsFiniteMeasure (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
            refine ⟨?_⟩
            simpa [Real.volume_Ico] using hrad_fin
          have hrad_int : Integrable (rademacher K)
              (volume.restrict (Set.Ico (0 : ℝ) 1)) :=
            Integrable.of_bound hrad_meas 1 (Filter.Eventually.of_forall (fun u => by
              rw [Real.norm_eq_abs, rademacher_abs]))
          rw [integral_congr_ae (Filter.Eventually.of_forall hdecomp)]
          rw [integral_add (integrable_const _) (hrad_int.const_mul _)]
          rw [integral_const_mul, rademacher_integral_Ico_zero K hK]
          simp [Real.volume_Ico]

/-- The stage observable is field-dependent.  Its first two Wilson moments
rule out a constant value on the full configuration space. -/
theorem stageObservable_nonconstant
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (hN : 2 ≤ N) (hLt2 : 2 ≤ Lt)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a) (x : Space4) (K : ℕ)
    (hK : 0 < K) :
    ∃ U₁ U₂ : GaugeField (cubicTorus4 Ls Lt)
        (Matrix.specialUnitaryGroup (Fin N) ℂ),
      stageObservable Ls Lt N β hβ a ha x K U₁ ≠
        stageObservable Ls Lt N β hβ a ha x K U₂ := by
  classical
  let μ := wilsonMeasure Ls Lt N β
  let f := fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    stageObservable Ls Lt N β hβ a ha x K U
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact wilsonMeasure_isProbability Ls Lt N β hβ
  have hAC := wilson_plaquette_absolutelyContinuous Ls Lt N β hβ hN hLt2
    submersion_1d (stageSiteMap Ls Lt a ha x)
  by_contra h
  push_neg at h
  let U₀ : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun _ => 1
  let c := f U₀
  have hc : ∀ U, f U = c := fun U => by
    simpa [f, c] using h U U₀
  have hfirst := stageObservable_moment Ls Lt N β hβ a ha x K hK 1 hAC
  have hsecond := stageObservable_moment Ls Lt N β hβ a ha x K hK 2 hAC
  have hfirst' : ∫ U, f U ∂μ = c := by
    calc
      ∫ U, f U ∂μ = ∫ _ : GaugeField (cubicTorus4 Ls Lt)
          (Matrix.specialUnitaryGroup (Fin N) ℂ), c ∂μ := by
            apply integral_congr_ae
            filter_upwards with U
            exact hc U
      _ = c := by simp [MeasureTheory.integral_const]
  have hfirstConst :
      ∫ U, (stageObservable Ls Lt N β hβ a ha x K U) ^ 1
        ∂(wilsonMeasure Ls Lt N β) = c := by
    simpa [μ, f, pow_one] using hfirst'
  have hsecond' : ∫ U, (f U) ^ 2 ∂μ = c ^ 2 := by
    calc
      ∫ U, (f U) ^ 2 ∂μ = ∫ _ : GaugeField (cubicTorus4 Ls Lt)
          (Matrix.specialUnitaryGroup (Fin N) ℂ), c ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards with U
            rw [hc U]
      _ = c ^ 2 := by simp [MeasureTheory.integral_const]
  have hsecondConst :
      ∫ U, (stageObservable Ls Lt N β hβ a ha x K U) ^ 2
        ∂(wilsonMeasure Ls Lt N β) = c ^ 2 := by
    simpa [μ, f] using hsecond'
  have hmoment1 : c = (3 / 2 : ℝ) := by
    rw [hfirstConst] at hfirst
    norm_num at hfirst
    exact hfirst
  have hmoment2 : c ^ 2 = (5 / 2 : ℝ) := by
    rw [hsecondConst] at hsecond
    norm_num at hsecond
    exact hsecond
  nlinarith

/-- The stage observable is not constant even up to Wilson-measure-null sets.
The unequal first and second moments exclude almost-sure constancy. -/
theorem stageObservable_not_ae_constant
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (hN : 2 ≤ N) (hLt2 : 2 ≤ Lt)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a) (x : Space4) (K : ℕ)
    (hK : 0 < K) :
    ¬ ∃ c : ℝ, (fun U : GaugeField (cubicTorus4 Ls Lt)
        (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      stageObservable Ls Lt N β hβ a ha x K U) =ᵐ[wilsonMeasure Ls Lt N β]
        fun _ => c := by
  classical
  let μ := wilsonMeasure Ls Lt N β
  let f := fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    stageObservable Ls Lt N β hβ a ha x K U
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact wilsonMeasure_isProbability Ls Lt N β hβ
  have hAC := wilson_plaquette_absolutelyContinuous Ls Lt N β hβ hN hLt2
    submersion_1d (stageSiteMap Ls Lt a ha x)
  intro hconst
  obtain ⟨c, hc⟩ := hconst
  have hfirst := stageObservable_moment Ls Lt N β hβ a ha x K hK 1 hAC
  have hsecond := stageObservable_moment Ls Lt N β hβ a ha x K hK 2 hAC
  have hfirst' : ∫ U, f U ∂μ = c := by
    calc
      ∫ U, f U ∂μ = ∫ _ : GaugeField (cubicTorus4 Ls Lt)
          (Matrix.specialUnitaryGroup (Fin N) ℂ), c ∂μ := by
            apply integral_congr_ae
            exact hc
      _ = c := by simp [MeasureTheory.integral_const]
  have hsecond' : ∫ U, (f U) ^ 2 ∂μ = c ^ 2 := by
    calc
      ∫ U, (f U) ^ 2 ∂μ = ∫ _ : GaugeField (cubicTorus4 Ls Lt)
          (Matrix.specialUnitaryGroup (Fin N) ℂ), c ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hc] with U hU
            simpa [f, hU]
      _ = c ^ 2 := by simp [MeasureTheory.integral_const]
  have hfirstConst :
      ∫ U, (stageObservable Ls Lt N β hβ a ha x K U) ^ 1
        ∂(wilsonMeasure Ls Lt N β) = c := by
    simpa [μ, f, pow_one] using hfirst'
  have hsecondConst :
      ∫ U, (stageObservable Ls Lt N β hβ a ha x K U) ^ 2
        ∂(wilsonMeasure Ls Lt N β) = c ^ 2 := by
    simpa [μ, f] using hsecond'
  rw [hfirstConst] at hfirst
  rw [hsecondConst] at hsecond
  norm_num at hfirst hsecond
  nlinarith

theorem stageObservable_gauge_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (β : ℝ) (hβ : 0 ≤ β) (a : ℝ) (ha : 0 < a) (x : Space4) (K : ℕ)
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    stageObservable Ls Lt N β hβ a ha x K (gaugeAct g U) =
      stageObservable Ls Lt N β hβ a ha x K U := by
  let v := stageSiteMap Ls Lt a ha x
  have hdef : plaquetteDefect Ls Lt N v (gaugeAct g U) =
      plaquetteDefect Ls Lt N v U := by
    unfold plaquetteDefect
    rw [normWilsonLoop4_gauge_inv (cubic4Plaquette_isPath v 0 1) g U]
  simp only [stageObservable]
  rw [hdef]

/-- A parameterized family of the proved Wilson stage observables satisfies
the strict single-point observable interface. -/
noncomputable def stageObservable_latticeSinglePointObs
    (N : ℕ) (Ls_seq Lt_seq : ℕ → ℕ)
    [∀ m, NeZero (Ls_seq m)] [∀ m, NeZero (Lt_seq m)]
    (β_seq a_seq : ℕ → ℝ) (K_seq : ℕ → ℕ)
    (hN : 2 ≤ N)
    (hLt2 : ∀ m, 2 ≤ Lt_seq m)
    (submersion_1d : ∀ {U : Set ℝ} {g : ℝ → ℝ}, IsOpen U → ContDiffOn ℝ 1 g U →
      (∀ x ∈ U, deriv g x ≠ 0) →
      ∃ ρ : ℝ → ℝ≥0∞, (volume.restrict U).map g = volume.withDensity ρ)
    (hβ : ∀ m, 0 ≤ β_seq m) (ha : ∀ m, 0 < a_seq m)
    (hK : ∀ m, 0 < K_seq m) :
    LatticeSinglePointObs N Ls_seq Lt_seq := by
  refine
    { obs := fun m x U =>
        ((stageObservable (Ls_seq m) (Lt_seq m) N (β_seq m) (hβ m)
          (a_seq m) (ha m) x (K_seq m) U : ℝ) : ℂ)
      gauge_inv := ?_
      non_const := ?_ }
  · intro m x g U
    exact congrArg (fun y : ℝ => (y : ℂ))
      (stageObservable_gauge_inv (Ls_seq m) (Lt_seq m) N (β_seq m) (hβ m)
        (a_seq m) (ha m) x (K_seq m) g U)
  · intro m x
    obtain ⟨U₁, U₂, hneq⟩ := stageObservable_nonconstant
      (Ls_seq m) (Lt_seq m) N hN (hLt2 m) submersion_1d
      (β_seq m) (hβ m) (a_seq m) (ha m) x (K_seq m) (hK m)
    refine ⟨U₁, U₂, ?_⟩
    intro heq
    exact hneq (Complex.ofReal_injective heq)

end YangMills
