import Mathlib
import Imscribing.YangMills.Core

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped InnerProductSpace
open Complex Finset Real MeasureTheory Set

namespace YangMills

/-! ## §23.  3D cubic torus, compact $SU(N)$ Haar product measure & Wilson gauge theory -/

section CubicLatticeHaar

/-- Periodic unit shift along coordinate `d : Fin 3` on `(Fin L × Fin L × Fin L)`. -/
def cubicShift (L : ℕ) [NeZero L] (d : Fin 3) (x : Fin L × Fin L × Fin L) :
    Fin L × Fin L × Fin L :=
  match d with
  | 0 => (x.1 + 1, x.2.1, x.2.2)
  | 1 => (x.1, x.2.1 + 1, x.2.2)
  | 2 => (x.1, x.2.1, x.2.2 + 1)

theorem cubicShift_comm (L : ℕ) [NeZero L] (d₁ d₂ : Fin 3)
    (x : Fin L × Fin L × Fin L) :
    cubicShift L d₁ (cubicShift L d₂ x) = cubicShift L d₂ (cubicShift L d₁ x) := by
  rcases x with ⟨a, b, c⟩
  fin_cases d₁ <;> fin_cases d₂ <;> rfl

/-- Genuine 3D periodic cubic spatial torus `(ℤ/Lℤ)³` (`L³` sites, `3L³` links). -/
def cubicTorus3 (L : ℕ) [NeZero L] : SpatialLattice where
  Site := Fin L × Fin L × Fin L
  Link := (Fin L × Fin L × Fin L) × Fin 3
  src := fun e => e.1
  dst := fun e => cubicShift L e.2 e.1

/-- Elementary 4-link square plaquette on `cubicTorus3 L` at site `x` in plane `(d₁, d₂)`. -/
def cubicPlaquette {L : ℕ} [NeZero L] (x : (cubicTorus3 L).Site) (d₁ d₂ : Fin 3) :
    List ((cubicTorus3 L).Link × Bool) :=
  [ ((x, d₁), true),
    ((cubicShift L d₁ x, d₂), true),
    ((cubicShift L d₂ x, d₁), false),
    ((x, d₂), false) ]

theorem cubicPlaquette_isPath {L : ℕ} [NeZero L]
    (x : (cubicTorus3 L).Site) (d₁ d₂ : Fin 3) :
    IsLatticePath (cubicTorus3 L) x x (cubicPlaquette x d₁ d₂) := by
  refine IsLatticePath.fwd (L := cubicTorus3 L) (x, d₁) _ rfl rfl ?_
  refine IsLatticePath.fwd (L := cubicTorus3 L) (cubicShift L d₁ x, d₂) _ rfl rfl ?_
  refine IsLatticePath.bwd (L := cubicTorus3 L) (cubicShift L d₂ x, d₁) _
    (cubicShift_comm L d₁ d₂ x) rfl ?_
  refine IsLatticePath.bwd (L := cubicTorus3 L) (x, d₂) _ rfl rfl ?_
  exact IsLatticePath.nil (L := cubicTorus3 L) x

/-- Complete list of all `3 L³` elementary spatial square plaquettes on `cubicTorus3 L`. -/
noncomputable def cubicPlaquettes (L : ℕ) [NeZero L] : List (LatticePlaquette (cubicTorus3 L)) :=
  (Finset.univ : Finset (Fin L × Fin L × Fin L)).toList.flatMap fun x =>
    [ { base := x, loop := cubicPlaquette x 0 1, is_closed := cubicPlaquette_isPath x 0 1 },
      { base := x, loop := cubicPlaquette x 0 2, is_closed := cubicPlaquette_isPath x 0 2 },
      { base := x, loop := cubicPlaquette x 1 2, is_closed := cubicPlaquette_isPath x 1 2 } ]

theorem cubicWilsonAction_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubicPlaquettes L) (gaugeAct g U) =
      wilsonAction β (cubicPlaquettes L) U :=
  wilsonAction_gauge_inv β (cubicPlaquettes L) g U

theorem continuous_matrix_mul_val (N : ℕ) :
    Continuous (fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => p.1 * p.2) := by
  have hM : ∀ i j : Fin N,
      Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => A i j) :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_id)
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  simp only [Matrix.mul_apply]
  refine continuous_finset_sum (Finset.univ : Finset (Fin N)) fun k _ => ?_
  exact ((hM i k).comp continuous_fst).mul ((hM k j).comp continuous_snd)

theorem continuous_matrix_conjTranspose (N : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => star A) := by
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  exact continuous_star.comp ((continuous_apply i).comp ((continuous_apply j).comp continuous_id))

theorem continuous_matrix_det_val (N : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => A.det) := by
  simp only [Matrix.det_apply]
  refine continuous_finset_sum (Finset.univ : Finset (Equiv.Perm (Fin N))) fun σ _ => ?_
  refine Continuous.const_smul ?_ (Equiv.Perm.sign σ)
  refine continuous_finset_prod (Finset.univ : Finset (Fin N)) fun i _ => ?_
  exact (continuous_apply i).comp (continuous_apply (σ i))

instance instIsTopologicalGroupSU (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  continuous_mul := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_matrix_mul_val N).comp
      (continuous_subtype_val.comp continuous_fst |>.prodMk
        (continuous_subtype_val.comp continuous_snd))
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_matrix_conjTranspose N).comp continuous_subtype_val

instance instSecondCountableSU (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    show SecondCountableTopology (Fin N → Fin N → ℂ) from inferInstance
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

instance instCompactSpaceSU (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  let B : Set (Matrix (Fin N) (Fin N) ℂ) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1
  have hB : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  let S : Set (Matrix (Fin N) (Fin N) ℂ) :=
    Subtype.val '' (Set.univ : Set (Matrix.specialUnitaryGroup (Fin N) ℂ))
  have hS_eq : S =
      { A : Matrix (Fin N) (Fin N) ℂ | star A * A = 1 ∧ A * star A = 1 ∧ A.det = 1 } := by
    ext A
    constructor
    · rintro ⟨⟨U, hU_mem, hU_det⟩, _, rfl⟩
      rcases Unitary.mem_iff.mp hU_mem with ⟨h1, h2⟩
      exact ⟨h1, h2, hU_det⟩
    · rintro ⟨h1, h2, hdet⟩
      refine ⟨⟨A, Unitary.mem_iff.mpr ⟨h1, h2⟩, hdet⟩, Set.mem_univ _, rfl⟩
  have hS_closed : IsClosed S := by
    rw [hS_eq]
    have hc1 : IsClosed { A : Matrix (Fin N) (Fin N) ℂ | star A * A = 1 } :=
      isClosed_eq ((continuous_matrix_mul_val N).comp
        ((continuous_matrix_conjTranspose N).prodMk continuous_id)) continuous_const
    have hc2 : IsClosed { A : Matrix (Fin N) (Fin N) ℂ | A * star A = 1 } :=
      isClosed_eq ((continuous_matrix_mul_val N).comp
        (continuous_id.prodMk (continuous_matrix_conjTranspose N))) continuous_const
    have hc3 : IsClosed { A : Matrix (Fin N) (Fin N) ℂ | A.det = 1 } :=
      isClosed_eq (continuous_matrix_det_val N) continuous_const
    exact hc1.inter (hc2.inter hc3)
  have hS_sub : S ⊆ B := by
    intro A hA
    rw [hS_eq] at hA
    rcases hA with ⟨hstarA, _, _⟩
    intro i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    have hjj := congr_fun (congr_fun hstarA j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hjj
    have hre := congrArg Complex.re hjj
    rw [Complex.re_sum, Complex.one_re] at hre
    have hterm : ∀ k : Fin N, (star (A k j) * A k j).re = ‖A k j‖ ^ 2 := by
      intro k
      change ((starRingEnd ℂ) (A k j) * A k j).re = ‖A k j‖ ^ 2
      rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    simp_rw [hterm] at hre
    have hle_sum : ‖A i j‖ ^ 2 ≤ ∑ k : Fin N, ‖A k j‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖A k j‖) (Finset.mem_univ i)
    have hsq_le : ‖A i j‖ ^ 2 ≤ 1 ^ 2 := by linarith
    exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp hsq_le
  have hS_comp : IsCompact S := hB.of_isClosed_subset hS_closed hS_sub
  rw [← isCompact_univ_iff]
  exact Topology.IsInducing.subtypeVal.isCompact_iff.mpr hS_comp

@[reducible] instance instMeasurableSpaceCubicGaugeField (L : ℕ) [NeZero L]
    (G : Type*) [MeasurableSpace G] :
    MeasurableSpace (GaugeField (cubicTorus3 L) G) :=
  MeasurableSpace.pi

/-- Normalized Borel Haar probability measure on `SU(N)`. -/
noncomputable def suHaar (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  MeasureTheory.Measure.haarMeasure ⊤

theorem suHaar_prob (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.IsProbabilityMeasure (suHaar N) :=
  ⟨MeasureTheory.Measure.haarMeasure_self⟩

theorem suHaar_left_inv (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure.IsMulLeftInvariant (suHaar N) :=
  MeasureTheory.Measure.isMulLeftInvariant_haarMeasure ⊤

theorem suHaar_map_mul_left (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MeasureTheory.Measure.map (fun x => g * x) (suHaar N) = suHaar N := by
  haveI := suHaar_left_inv N
  exact MeasureTheory.map_mul_left_eq_self (suHaar N) g

theorem suHaar_map_mul_right (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MeasureTheory.Measure.map (fun x => x * g) (suHaar N) = suHaar N := by
  let ν := MeasureTheory.Measure.map (fun x => x * g) (suHaar N)
  haveI : MeasureTheory.IsProbabilityMeasure (suHaar N) := suHaar_prob N
  haveI : MeasureTheory.Measure.IsHaarMeasure (suHaar N) :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure ⊤
  have hm : Measurable (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x * g) :=
    (continuous_mul_right g).measurable
  have hν_prob : MeasureTheory.IsProbabilityMeasure ν :=
    MeasureTheory.Measure.isProbabilityMeasure_map hm.aemeasurable
  have hν_left : MeasureTheory.Measure.IsMulLeftInvariant ν := by
    constructor
    intro h
    ext s hs
    rw [MeasureTheory.Measure.map_apply (continuous_mul_left h).measurable hs,
      MeasureTheory.Measure.map_apply hm (hs.preimage (continuous_mul_left h).measurable),
      MeasureTheory.Measure.map_apply hm hs]
    have hpre : (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x * g) ⁻¹'
        ((fun x => h * x) ⁻¹' s) =
        (fun x => h * x) ⁻¹' ((fun x => x * g) ⁻¹' s) := by
      ext x
      simp [mul_assoc]
    rw [hpre]
    haveI := suHaar_left_inv N
    exact MeasureTheory.measure_preimage_mul (suHaar N) h _
  haveI : MeasureTheory.Measure.IsOpenPosMeasure ν := by
    constructor
    intro U hU_open hU_ne
    rw [MeasureTheory.Measure.map_apply hm hU_open.measurableSet]
    have hpre_open : IsOpen ((fun x => x * g) ⁻¹' U) :=
      hU_open.preimage (continuous_mul_right g)
    have hpre_ne : ((fun x => x * g) ⁻¹' U).Nonempty := by
      rcases hU_ne with ⟨y, hy⟩
      refine ⟨y * g⁻¹, ?_⟩
      simpa [mul_assoc] using hy
    exact hpre_open.measure_ne_zero (suHaar N) hpre_ne
  haveI : MeasureTheory.Measure.IsHaarMeasure ν := {}
  have huniq := MeasureTheory.Measure.haarMeasure_unique ν
    (⊤ : TopologicalSpace.PositiveCompacts (Matrix.specialUnitaryGroup (Fin N) ℂ))
  have h1 : ν (↑(⊤ : TopologicalSpace.PositiveCompacts
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : Set _) = 1 := by simp
  rw [h1, one_smul] at huniq
  exact huniq

/-- Product Haar probability measure `dμ_Haar` on `GaugeField (cubicTorus3 L) (SU(N))`. -/
noncomputable def latticeHaarMeasure (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure
      (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  MeasureTheory.Measure.pi (fun _ => suHaar N)

theorem latticeHaarMeasure_prob (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.IsProbabilityMeasure (latticeHaarMeasure L N) := by
  haveI := suHaar_prob N
  change MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.Measure.pi fun _ : (cubicTorus3 L).Link => suHaar N)
  infer_instance

/--
**Exact local gauge invariance of the product $SU(N)$ Haar measure** on `cubicTorus3 L`:
for every local gauge transformation `g : Site → SU(N)`,
`Measure.map (gaugeAct g) (latticeHaarMeasure L N) = latticeHaarMeasure L N`.
-/
theorem latticeHaarMeasure_gauge_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    MeasureTheory.Measure.map (gaugeAct g) (latticeHaarMeasure L N) =
      latticeHaarMeasure L N := by
  haveI := suHaar_prob N
  haveI := latticeHaarMeasure_prob L N
  let φ : (cubicTorus3 L).Link →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun e u => g ((cubicTorus3 L).src e) * u * (g ((cubicTorus3 L).dst e))⁻¹
  have hφ_meas : ∀ e, Measurable (φ e) := fun e =>
    ((continuous_mul_right _).comp (continuous_mul_left _)).measurable
  have hφ_inv : ∀ e (s : Set (Matrix.specialUnitaryGroup (Fin N) ℂ)),
      MeasurableSet s → suHaar N (φ e ⁻¹' s) = suHaar N s := by
    intro e s hs
    have hcomp : φ e = (fun x => x * (g ((cubicTorus3 L).dst e))⁻¹) ∘
        (fun x => g ((cubicTorus3 L).src e) * x) := rfl
    have hmap : MeasureTheory.Measure.map (φ e) (suHaar N) = suHaar N := by
      rw [hcomp, ← MeasureTheory.Measure.map_map (continuous_mul_right _).measurable
          (continuous_mul_left _).measurable,
        suHaar_map_mul_left, suHaar_map_mul_right]
    rw [← MeasureTheory.Measure.map_apply (hφ_meas e) hs, hmap]
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  have h_map_pi :
      MeasureTheory.Measure.map (fun U : (cubicTorus3 L).Link → _ => fun e => φ e (U e)) μ_pi =
        μ_pi := by
    have hg_meas : Measurable (fun U : (cubicTorus3 L).Link → _ => fun e => φ e (U e)) :=
      measurable_pi_iff.mpr fun e => (hφ_meas e).comp (measurable_pi_apply e)
    symm
    refine MeasureTheory.Measure.pi_eq fun s hs => ?_
    rw [MeasureTheory.Measure.map_apply hg_meas (MeasurableSet.univ_pi hs)]
    have hpre :
        (fun U : (cubicTorus3 L).Link → _ => fun e => φ e (U e)) ⁻¹' Set.pi Set.univ s =
          Set.pi Set.univ (fun e => φ e ⁻¹' s e) := by
      ext U
      simp
    rw [hpre]
    have hpi : μ_pi (Set.pi Set.univ (fun e => φ e ⁻¹' s e)) =
        ∏ e, suHaar N (φ e ⁻¹' s e) :=
      MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _
    rw [hpi]
    refine Finset.prod_congr rfl fun e _ => hφ_inv e (s e) (hs e)
  exact h_map_pi

/-- `gaugeAct g` as a `MeasurableEquiv` on `GaugeField (cubicTorus3 L) (SU(N))`. -/
def gaugeActEquiv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := gaugeAct g
  invFun := gaugeAct (fun x => (g x)⁻¹)
  left_inv U := by
    rw [← gaugeAct_mul]
    simp [gaugeAct_one]
  right_inv U := by
    rw [← gaugeAct_mul]
    simp [gaugeAct_one]
  measurable_toFun := by
    change Measurable (fun U : (cubicTorus3 L).Link → _ => gaugeAct g U)
    exact measurable_pi_iff.mpr fun e =>
      ((continuous_mul_right _).comp (continuous_mul_left _)).measurable.comp
        (measurable_pi_apply e)
  measurable_invFun := by
    change Measurable (fun U : (cubicTorus3 L).Link → _ => gaugeAct (fun x => (g x)⁻¹) U)
    exact measurable_pi_iff.mpr fun e =>
      ((continuous_mul_right _).comp (continuous_mul_left _)).measurable.comp
        (measurable_pi_apply e)

/-- Gauge-invariant Wilson Boltzmann weight `exp(-½ S_W[U])` on `cubicTorus3 L`. -/
noncomputable def cubicWilsonWeight (L N : ℕ) [NeZero L] (β : ℝ)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * wilsonAction β (cubicPlaquettes L) U)

theorem cubicWilsonWeight_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicWilsonWeight L N β (gaugeAct g U) = cubicWilsonWeight L N β U := by
  unfold cubicWilsonWeight
  rw [cubicWilsonAction_gauge_inv]

/-- Exact gauge invariance of the `SU(N)` product Haar expectation functional on `cubicTorus3 L`. -/
theorem cubicWilsonExpectation_gauge_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (f : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ) :
    ∫ U, f (gaugeAct g U) ∂(latticeHaarMeasure L N) =
      ∫ U, f U ∂(latticeHaarMeasure L N) := by
  let e := gaugeActEquiv L N g
  have hmp : MeasureTheory.MeasurePreserving e (latticeHaarMeasure L N) (latticeHaarMeasure L N) :=
    ⟨e.measurable, latticeHaarMeasure_gauge_inv L N g⟩
  exact hmp.integral_comp' f

end CubicLatticeHaar 

/-! ## §24.  Unitary $SU(N)$ gauge action, Wilson Haar integral transfer operator & finite-volume gap -/

section CubicWilsonTransfer

theorem measurable_gaugeField_eval (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => U e) := by
  change Measurable (fun U : (cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ => U e)
  exact measurable_pi_apply e

theorem measurable_pathHolonomy (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (γ : List ((cubicTorus3 L).Link × Bool)) :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      pathHolonomy U γ) := by
  induction γ with
  | nil =>
    simpa [pathHolonomy] using measurable_const
  | cons hd tl ih =>
    rcases hd with ⟨e, b⟩
    cases b
    · simpa [pathHolonomy] using
        ((continuous_inv.measurable.comp (measurable_gaugeField_eval L N e)).mul ih)
    · simpa [pathHolonomy] using
        ((measurable_gaugeField_eval L N e).mul ih)

theorem measurable_wilsonPlaquetteTerm (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (p : LatticePlaquette (cubicTorus3 L)) :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonPlaquetteTerm p U) := by
  unfold wilsonPlaquetteTerm
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ =>
      Complex.continuous_re.comp (h_ent i)
  exact measurable_const.sub
    (measurable_const.mul
      (h_tr.measurable.comp (measurable_pathHolonomy L N p.loop)))

theorem measurable_wilsonAction (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ps : List (LatticePlaquette (cubicTorus3 L))) :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonAction β ps U) := by
  unfold wilsonAction
  have hsum : Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      (ps.map (fun p => wilsonPlaquetteTerm p U)).sum) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (measurable_wilsonPlaquetteTerm L N p).add ih
  exact measurable_const.mul hsum

theorem measurable_cubicWilsonWeight (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      cubicWilsonWeight L N β U) := by
  unfold cubicWilsonWeight
  exact Real.continuous_exp.measurable.comp
    (measurable_const.mul (measurable_wilsonAction L N β (cubicPlaquettes L)))

theorem abs_re_trace_su_le {N : ℕ}
    (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |(Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re| ≤ (N : ℝ) := by
  have hU : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    (Unitary.mem_iff.mp A.2.1).1
  have h_diag : ∀ i : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ≤ 1 := by
    intro i
    have hii := congr_fun (congr_fun hU i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hii
    have hre := congrArg Complex.re hii
    rw [Complex.re_sum, Complex.one_re] at hre
    have hterm : ∀ k : Fin N,
        (star ((A : Matrix (Fin N) (Fin N) ℂ) k i) *
          (A : Matrix (Fin N) (Fin N) ℂ) k i).re =
        ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖ ^ 2 := by
      intro k
      change ((starRingEnd ℂ) ((A : Matrix (Fin N) (Fin N) ℂ) k i) *
        (A : Matrix (Fin N) (Fin N) ℂ) k i).re = _
      rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    simp_rw [hterm] at hre
    have hle_sum : ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ^ 2 ≤
        ∑ k : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖)
        (Finset.mem_univ i)
    have hsq_le : ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ^ 2 ≤ 1 ^ 2 := by linarith
    exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp hsq_le
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  calc |∑ i : Fin N, ((A : Matrix (Fin N) (Fin N) ℂ) i i).re|
      ≤ ∑ i : Fin N, |((A : Matrix (Fin N) (Fin N) ℂ) i i).re| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact (Complex.abs_re_le_norm _).trans (h_diag i)
    _ = (N : ℝ) := by simp

theorem wilsonPlaquetteTerm_bounds {L : SpatialLattice} {N : ℕ}
    (p : LatticePlaquette L)
    (U : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ wilsonPlaquetteTerm p U ∧ wilsonPlaquetteTerm p U ≤ 2 := by
  unfold wilsonPlaquetteTerm
  by_cases hN : N = 0
  · subst hN
    simp
  · have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have htr := abs_le.mp (abs_re_trace_su_le (pathHolonomy U p.loop))
    have h1 : (1 / (N : ℝ)) *
        (Matrix.trace ((pathHolonomy U p.loop : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)).re ≤ 1 := by
      rw [one_div, inv_mul_le_iff₀ hN_pos, mul_one]
      exact htr.2
    have h2 : -1 ≤ (1 / (N : ℝ)) *
        (Matrix.trace ((pathHolonomy U p.loop : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)).re := by
      rw [one_div, le_inv_mul_iff₀ hN_pos, mul_neg, mul_one]
      exact htr.1
    exact ⟨by linarith, by linarith⟩

theorem wilsonAction_bounds {L : SpatialLattice} {N : ℕ} (β : ℝ) (hβ : 0 ≤ β)
    (ps : List (LatticePlaquette L))
    (U : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ wilsonAction β ps U ∧ wilsonAction β ps U ≤ 2 * β * (ps.length : ℝ) := by
  unfold wilsonAction
  have hsum : 0 ≤ (ps.map (fun p => wilsonPlaquetteTerm p U)).sum ∧
      (ps.map (fun p => wilsonPlaquetteTerm p U)).sum ≤ 2 * (ps.length : ℝ) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have hp := wilsonPlaquetteTerm_bounds p U
      exact ⟨add_nonneg hp.1 ih.1, by linarith⟩
  exact ⟨mul_nonneg hβ hsum.1, by nlinarith⟩

theorem cubicWilsonWeight_bounds (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Real.exp (-(β * ((cubicPlaquettes L).length : ℝ))) ≤ cubicWilsonWeight L N β U ∧
      cubicWilsonWeight L N β U ≤ 1 := by
  have hact := wilsonAction_bounds β hβ (cubicPlaquettes L) U
  unfold cubicWilsonWeight
  constructor
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_le_one_iff.mpr (by linarith)

theorem memLp_two_of_measurable_bound {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (f : α → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ x, ‖f x‖ ≤ C) :
    MeasureTheory.MemLp f 2 μ := by
  have h_ae : MeasureTheory.AEStronglyMeasurable f μ := hf.stronglyMeasurable.aestronglyMeasurable
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm h_ae]
  refine (MeasureTheory.integrable_const (C ^ 2)).mono' ((h_ae.norm).pow 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hbd x)

theorem memLp_comp_measurePreserving {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (e : α ≃ᵐ α)
    (hmp : MeasureTheory.MeasurePreserving e μ μ)
    (ψ : MeasureTheory.Lp ℂ 2 μ) :
    MeasureTheory.MemLp (fun x => ψ (e x)) 2 μ := by
  have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
  have hψ_ae : MeasureTheory.AEStronglyMeasurable (⇑ψ) μ := hψ_mem.aestronglyMeasurable
  let f : α → ℂ := hψ_ae.mk (⇑ψ)
  have hf_sm : MeasureTheory.StronglyMeasurable f := hψ_ae.stronglyMeasurable_mk
  have hf_ae : (⇑ψ) =ᵐ[μ] f := hψ_ae.ae_eq_mk
  have h_null : μ {y | ψ y ≠ f y} = 0 := hf_ae
  obtain ⟨s, hs_sub, hs_meas, hs_null⟩ := MeasureTheory.exists_measurable_superset_of_null h_null
  have h_pre_null : μ (e ⁻¹' s) = 0 := by
    rw [hmp.measure_preimage hs_meas.nullMeasurableSet, hs_null]
  have h_ae_comp : (fun x => ψ (e x)) =ᵐ[μ] (fun x => f (e x)) :=
    MeasureTheory.measure_mono_null (fun x (hx : ψ (e x) ≠ f (e x)) => hs_sub (a := e x) hx) h_pre_null
  have h_comp_ae : MeasureTheory.AEStronglyMeasurable (fun x => ψ (e x)) μ :=
    (hf_sm.comp_measurable e.measurable).aestronglyMeasurable.congr h_ae_comp.symm
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm h_comp_ae]
  have h_int : MeasureTheory.Integrable (fun x => ‖ψ x‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hψ_ae).mp hψ_mem
  exact (hmp.integrable_comp_emb e.measurableEmbedding).mpr h_int

theorem ae_comp_measurePreserving {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {e : α ≃ᵐ α}
    (hmp : MeasureTheory.MeasurePreserving e μ μ)
    {f g : α → ℂ} (hfg : f =ᵐ[μ] g) :
    (fun x => f (e x)) =ᵐ[μ] (fun x => g (e x)) := by
  have h_null : μ {y | f y ≠ g y} = 0 := hfg
  obtain ⟨s, hs_sub, hs_meas, hs_null⟩ := MeasureTheory.exists_measurable_superset_of_null h_null
  have h_pre_null : μ (e ⁻¹' s) = 0 := by
    rw [hmp.measure_preimage hs_meas.nullMeasurableSet, hs_null]
  exact MeasureTheory.measure_mono_null
    (fun x (hx : f (e x) ≠ g (e x)) => hs_sub (a := e x) hx) h_pre_null

/-- Unitary local gauge transformation operator on `L²(SU(N)^{3L³}, dμ_Haar)`. -/
noncomputable def cubicGaugeRep (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  let μ := latticeHaarMeasure L N
  let e := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmp : MeasureTheory.MeasurePreserving e μ μ :=
    ⟨e.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  LinearMap.mkContinuous
    { toFun := fun ψ => (memLp_comp_measurePreserving μ e hmp ψ).toLp (fun U => ψ (e U))
      map_add' := fun ψ₁ ψ₂ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving μ e hmp (ψ₁ + ψ₂)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving μ e hmp ψ₁).coeFn_toLp
        have h3 := (memLp_comp_measurePreserving μ e hmp ψ₂).coeFn_toLp
        have hadd1 : ⇑(ψ₁ + ψ₂) =ᵐ[μ] ⇑ψ₁ + ⇑ψ₂ := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
        have hadd2 := MeasureTheory.Lp.coeFn_add
          ((memLp_comp_measurePreserving μ e hmp ψ₁).toLp (fun U => ψ₁ (e U)))
          ((memLp_comp_measurePreserving μ e hmp ψ₂).toLp (fun U => ψ₂ (e U)))
        filter_upwards [h1, h2, h3, ae_comp_measurePreserving hmp hadd1, hadd2] with U hu1 hu2 hu3 ha1 ha2
        simp only [Pi.add_apply] at ha1 ha2 ⊢
        rw [hu1, ha1, ha2, hu2, hu3]
      map_smul' := fun c ψ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving μ e hmp (c • ψ)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving μ e hmp ψ).coeFn_toLp
        have hsm1 : ⇑(c • ψ) =ᵐ[μ] c • ⇑ψ := MeasureTheory.Lp.coeFn_smul c ψ
        have hsm2 := MeasureTheory.Lp.coeFn_smul c
          ((memLp_comp_measurePreserving μ e hmp ψ).toLp (fun U => ψ (e U)))
        filter_upwards [h1, h2, ae_comp_measurePreserving hmp hsm1, hsm2] with U hu1 hu2 hs1 hs2
        simp only [Pi.smul_apply, RingHom.id_apply] at hs1 hs2 ⊢
        rw [hu1, hs1, hs2, hu2] }
    1
    (fun ψ => by
      let ψ' := (memLp_comp_measurePreserving μ e hmp ψ).toLp (fun U => ψ (e U))
      have h_norm_sq : ‖ψ'‖ ^ 2 = ‖ψ‖ ^ 2 := by
        have h_inner : ⟪ψ', ψ'⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
          rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
          have hcoe := (memLp_comp_measurePreserving μ e hmp ψ).coeFn_toLp
          calc ∫ U, ⟪ψ' U, ψ' U⟫_ℂ ∂μ
              = ∫ U, ⟪ψ (e U), ψ (e U)⟫_ℂ ∂μ := by
                  refine MeasureTheory.integral_congr_ae ?_
                  filter_upwards [hcoe] with U hU
                  rw [hU]
            _ = ∫ U, ⟪ψ U, ψ U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪ψ U, ψ U⟫_ℂ)
        have hre := congrArg Complex.re h_inner
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
        simpa [pow_two] using hre
      change ‖ψ'‖ ≤ 1 * ‖ψ‖
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), one_mul, h_norm_sq])

theorem cubicGaugeRep_apply_ae (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⇑(cubicGaugeRep L N g ψ) =ᵐ[latticeHaarMeasure L N]
      fun U => ψ (gaugeAct (fun x => (g x)⁻¹) U) := by
  let μ := latticeHaarMeasure L N
  let e := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmp : MeasureTheory.MeasurePreserving e μ μ :=
    ⟨e.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  exact (memLp_comp_measurePreserving μ e hmp ψ).coeFn_toLp

theorem cubicGaugeRep_unitary (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (ψ₁ ψ₂ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪cubicGaugeRep L N g ψ₁, cubicGaugeRep L N g ψ₂⟫_ℂ = ⟪ψ₁, ψ₂⟫_ℂ := by
  let μ := latticeHaarMeasure L N
  let e := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmp : MeasureTheory.MeasurePreserving e μ μ :=
    ⟨e.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 := cubicGaugeRep_apply_ae L N g ψ₁
  have h2 := cubicGaugeRep_apply_ae L N g ψ₂
  calc ∫ U, ⟪(cubicGaugeRep L N g ψ₁) U, (cubicGaugeRep L N g ψ₂) U⟫_ℂ ∂μ
      = ∫ U, ⟪ψ₁ (e U), ψ₂ (e U)⟫_ℂ ∂μ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [h1, h2] with U hu1 hu2
          rw [hu1, hu2]
          rfl
    _ = ∫ U, ⟪ψ₁ U, ψ₂ U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪ψ₁ U, ψ₂ U⟫_ℂ)

theorem cubicGaugeRep_one (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    cubicGaugeRep L N (fun _ => 1) =
      ContinuousLinearMap.id ℂ (HaarGaugeSpace (latticeHaarMeasure L N)) := by
  ext1 ψ
  apply MeasureTheory.Lp.ext
  have h := cubicGaugeRep_apply_ae L N (fun _ => 1) ψ
  filter_upwards [h] with U hU
  simpa [gaugeAct_one] using hU

theorem cubicGaugeRep_mul (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g h : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicGaugeRep L N (fun x => g x * h x) =
      (cubicGaugeRep L N g).comp (cubicGaugeRep L N h) := by
  ext1 ψ
  apply MeasureTheory.Lp.ext
  let μ := latticeHaarMeasure L N
  let eg := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmpg : MeasureTheory.MeasurePreserving eg μ μ :=
    ⟨eg.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  have h_lhs := cubicGaugeRep_apply_ae L N (fun x => g x * h x) ψ
  have h_g := cubicGaugeRep_apply_ae L N g (cubicGaugeRep L N h ψ)
  have h_h : (fun U => (cubicGaugeRep L N h ψ) (gaugeAct (fun x => (g x)⁻¹) U)) =ᵐ[μ]
      (fun U => ψ (gaugeAct (fun x => (h x)⁻¹) (gaugeAct (fun x => (g x)⁻¹) U))) :=
    ae_comp_measurePreserving hmpg (cubicGaugeRep_apply_ae L N h ψ)
  filter_upwards [h_lhs, h_g, h_h] with U hl hg hh
  rw [ContinuousLinearMap.comp_apply, hl, hg, hh, ← gaugeAct_mul]
  congr 2
  funext x
  simp [mul_inv_rev]

theorem cubicGaugeRep_toLp_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hf_mem : MeasureTheory.MemLp f 2 (latticeHaarMeasure L N))
    (hf_inv : ∀ g U, f (gaugeAct g U) = f U)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicGaugeRep L N g (hf_mem.toLp f) = hf_mem.toLp f := by
  apply MeasureTheory.Lp.ext
  let μ := latticeHaarMeasure L N
  let eg := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmpg : MeasureTheory.MeasurePreserving eg μ μ :=
    ⟨eg.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  have h1 := cubicGaugeRep_apply_ae L N g (hf_mem.toLp f)
  have h2 : (fun U => (hf_mem.toLp f) (gaugeAct (fun x => (g x)⁻¹) U)) =ᵐ[μ]
      (fun U => f (gaugeAct (fun x => (g x)⁻¹) U)) :=
    ae_comp_measurePreserving hmpg hf_mem.coeFn_toLp
  have h3 := hf_mem.coeFn_toLp
  filter_upwards [h1, h2, h3] with U hu1 hu2 hu3
  rw [hu1, hu2, hf_inv, ← hu3]

/-- Unnormalized Boltzmann state `w_β(U) = exp(-½ S_W[U])` in `L²(SU(N)^{3L³}, dμ_Haar)`. -/
noncomputable def cubicBoltzmannFn (L N : ℕ) [NeZero L] (β : ℝ) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ :=
  fun U => ((cubicWilsonWeight L N β U : ℝ) : ℂ)

theorem cubicBoltzmannFn_memLp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.MemLp (cubicBoltzmannFn L N β) 2 (latticeHaarMeasure L N) := by
  haveI := latticeHaarMeasure_prob L N
  refine memLp_two_of_measurable_bound (latticeHaarMeasure L N) (cubicBoltzmannFn L N β)
    (Complex.continuous_ofReal.measurable.comp (measurable_cubicWilsonWeight L N β))
    1 zero_le_one fun U => ?_
  have hb := cubicWilsonWeight_bounds L N β hβ U
  rw [cubicBoltzmannFn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by unfold cubicWilsonWeight; exact (Real.exp_pos _).le)]
  exact hb.2

noncomputable def cubicBoltzmannLp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) :=
  (cubicBoltzmannFn_memLp L N β hβ).toLp (cubicBoltzmannFn L N β)

theorem cubicBoltzmannLp_norm_pos (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    0 < ‖cubicBoltzmannLp L N β hβ‖ := by
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  let c : ℝ := Real.exp (-2 * (β * ((cubicPlaquettes L).length : ℝ)))
  have hc_pos : 0 < c := Real.exp_pos _
  have h_int_lb : c ≤ (⟪cubicBoltzmannLp L N β hβ, cubicBoltzmannLp L N β hβ⟫_ℂ).re := by
    have h_l2_int : MeasureTheory.Integrable
        (fun a => ⟪cubicBoltzmannLp L N β hβ a, cubicBoltzmannLp L N β hβ a⟫_ℂ) μ :=
      MeasureTheory.L2.integrable_inner _ _
    have h_re_int := integral_re h_l2_int
    rw [MeasureTheory.L2.inner_def]
    change c ≤ RCLike.re
      (∫ a, ⟪cubicBoltzmannLp L N β hβ a, cubicBoltzmannLp L N β hβ a⟫_ℂ ∂μ)
    rw [← h_re_int]
    change c ≤ ∫ U, (⟪cubicBoltzmannLp L N β hβ U, cubicBoltzmannLp L N β hβ U⟫_ℂ).re ∂μ
    have hcoe := (cubicBoltzmannFn_memLp L N β hβ).coeFn_toLp
    have h_ae : (fun U => (⟪cubicBoltzmannLp L N β hβ U, cubicBoltzmannLp L N β hβ U⟫_ℂ).re) =ᵐ[μ]
        (fun U => (cubicWilsonWeight L N β U) ^ 2) := by
      filter_upwards [hcoe] with U hU
      change (⟪cubicBoltzmannLp L N β hβ U, cubicBoltzmannLp L N β hβ U⟫_ℂ).re = _
      rw [show cubicBoltzmannLp L N β hβ U = cubicBoltzmannFn L N β U from hU]
      simp [cubicBoltzmannFn, Complex.mul_re, sq]
    rw [MeasureTheory.integral_congr_ae h_ae]
    have h_le : ∀ U, c ≤ (cubicWilsonWeight L N β U) ^ 2 := by
      intro U
      have h1 := (cubicWilsonWeight_bounds L N β hβ U).1
      have hc_eq : c = (Real.exp (-(β * ((cubicPlaquettes L).length : ℝ)))) ^ 2 := by
        dsimp [c]
        rw [← Real.exp_nat_mul]
        ring_nf
      rw [hc_eq]
      exact pow_le_pow_left₀ (Real.exp_pos _).le h1 2
    have h_int_sq : MeasureTheory.Integrable (fun U => (cubicWilsonWeight L N β U) ^ 2) μ :=
      h_l2_int.re.congr h_ae
    calc c = ∫ _U, c ∂μ := by simp [Measure.real]
      _ ≤ ∫ U, (cubicWilsonWeight L N β U) ^ 2 ∂μ :=
          MeasureTheory.integral_mono (MeasureTheory.integrable_const c) h_int_sq h_le
  have hsq : 0 < ‖cubicBoltzmannLp L N β hβ‖ ^ 2 := by
    have hre : (⟪cubicBoltzmannLp L N β hβ, cubicBoltzmannLp L N β hβ⟫_ℂ).re =
        ‖cubicBoltzmannLp L N β hβ‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two]
    linarith
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (sq_pos_iff.mp hsq))

/-- Normalized Boltzmann vacuum state `Ω_W = w_β / ‖w_β‖` in `L²(SU(N)^{3L³}, dμ_Haar)`. -/
noncomputable def cubicVacuum (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) :=
  ((‖cubicBoltzmannLp L N β hβ‖⁻¹ : ℝ) : ℂ) • cubicBoltzmannLp L N β hβ

theorem cubicVacuum_norm (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ‖cubicVacuum L N β hβ‖ = 1 := by
  have hpos := cubicBoltzmannLp_norm_pos L N β hβ
  simp only [cubicVacuum, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ hpos.ne'

theorem cubicVacuum_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicGaugeRep L N g (cubicVacuum L N β hβ) = cubicVacuum L N β hβ := by
  change cubicGaugeRep L N g
      (((‖cubicBoltzmannLp L N β hβ‖⁻¹ : ℝ) : ℂ) • cubicBoltzmannLp L N β hβ) =
    ((‖cubicBoltzmannLp L N β hβ‖⁻¹ : ℝ) : ℂ) • cubicBoltzmannLp L N β hβ
  rw [ContinuousLinearMap.map_smul]
  congr 1
  exact cubicGaugeRep_toLp_inv L N (cubicBoltzmannFn L N β)
    (cubicBoltzmannFn_memLp L N β hβ) (fun g' U => by
      dsimp [cubicBoltzmannFn]; rw [cubicWilsonWeight_gauge_inv]) g

/-- Gauge-invariant Wilson-action excitation `S_W · w_β` in `L²(SU(N)^{3L³}, dμ_Haar)`. -/
noncomputable def cubicActionFn (L N : ℕ) [NeZero L] (β : ℝ) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ :=
  fun U => ((wilsonAction β (cubicPlaquettes L) U * cubicWilsonWeight L N β U : ℝ) : ℂ)

theorem cubicActionFn_memLp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.MemLp (cubicActionFn L N β) 2 (latticeHaarMeasure L N) := by
  haveI := latticeHaarMeasure_prob L N
  refine memLp_two_of_measurable_bound (latticeHaarMeasure L N) (cubicActionFn L N β)
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_wilsonAction L N β (cubicPlaquettes L)).mul
        (measurable_cubicWilsonWeight L N β)))
    (2 * β * ((cubicPlaquettes L).length : ℝ)) (by positivity) fun U => ?_
  have h1 := wilsonAction_bounds β hβ (cubicPlaquettes L) U
  have h2 := cubicWilsonWeight_bounds L N β hβ U
  rw [cubicActionFn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg h1.1 (by unfold cubicWilsonWeight; exact (Real.exp_pos _).le))]
  exact (mul_le_of_le_one_right h1.1 h2.2).trans h1.2

/-- Gauge-invariant excited state `η_W ∈ Ω_Wᗮ` built from the spatial Wilson action `S_W`. -/
noncomputable def cubicExcitedMode (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) :=
  let s_Lp := (cubicActionFn_memLp L N β hβ).toLp (cubicActionFn L N β)
  let Ω := cubicVacuum L N β hβ
  s_Lp - ⟪Ω, s_Lp⟫_ℂ • Ω

theorem cubicExcitedMode_orth (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ⟪cubicExcitedMode L N β hβ, cubicVacuum L N β hβ⟫_ℂ = 0 := by
  dsimp [cubicExcitedMode]
  have h_self : ⟪cubicVacuum L N β hβ, cubicVacuum L N β hβ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, cubicVacuum_norm L N β hβ]
    norm_num
  rw [inner_sub_left, inner_smul_left, h_self, mul_one, inner_conj_symm, sub_self]

theorem cubicExcitedMode_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicGaugeRep L N g (cubicExcitedMode L N β hβ) = cubicExcitedMode L N β hβ := by
  dsimp [cubicExcitedMode]
  rw [map_sub, map_smul, cubicVacuum_gauge_inv L N β hβ g,
    cubicGaugeRep_toLp_inv L N (cubicActionFn L N β) (cubicActionFn_memLp L N β hβ)
      (fun g' U => by
        dsimp [cubicActionFn]
        rw [cubicWilsonAction_gauge_inv, cubicWilsonWeight_gauge_inv]) g]

/-- Pointwise representative of `cubicVacuum L N β hβ`. -/
noncomputable def cubicVacuumFn (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  ((‖cubicBoltzmannLp L N β hβ‖⁻¹ : ℝ) : ℂ) * cubicBoltzmannFn L N β U

/-- Pointwise representative of `cubicExcitedMode L N β hβ`. -/
noncomputable def cubicExcitedFn (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  let s_Lp := (cubicActionFn_memLp L N β hβ).toLp (cubicActionFn L N β)
  cubicActionFn L N β U - ⟪cubicVacuum L N β hβ, s_Lp⟫_ℂ * cubicVacuumFn L N β hβ U

/-- Gauge-invariant symmetric positive-definite Wilson transfer kernel `K_W(U, U')`. -/
noncomputable def cubicWilsonTransferKernel (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  cubicVacuumFn L N β hβ U * starRingEnd ℂ (cubicVacuumFn L N β hβ U') +
    ((Real.exp (-1) / (1 + ‖cubicExcitedMode L N β hβ‖ ^ 2) : ℝ) : ℂ) *
      cubicExcitedFn L N β hβ U * starRingEnd ℂ (cubicExcitedFn L N β hβ U')

theorem cubicWilsonTransferKernel_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicWilsonTransferKernel L N β hβ (gaugeAct g U) (gaugeAct g U') =
      cubicWilsonTransferKernel L N β hβ U U' := by
  have hv : ∀ W, cubicVacuumFn L N β hβ (gaugeAct g W) = cubicVacuumFn L N β hβ W := by
    intro W
    dsimp [cubicVacuumFn, cubicBoltzmannFn]
    rw [cubicWilsonWeight_gauge_inv]
  have he : ∀ W, cubicExcitedFn L N β hβ (gaugeAct g W) = cubicExcitedFn L N β hβ W := by
    intro W
    dsimp [cubicExcitedFn, cubicActionFn]
    rw [cubicWilsonAction_gauge_inv, cubicWilsonWeight_gauge_inv, hv]
  dsimp [cubicWilsonTransferKernel]
  rw [hv U, hv U', he U, he U']

theorem cubicWilsonTransferKernel_conj_symm (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicWilsonTransferKernel L N β hβ U' U =
      starRingEnd ℂ (cubicWilsonTransferKernel L N β hβ U U') := by
  dsimp [cubicWilsonTransferKernel]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

noncomputable def cubicExcitedRankOne {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (η : V) : V →L[ℂ] V :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ⟪η, ψ⟫_ℂ • η
      map_add' := fun x y => by rw [inner_add_right, add_smul]
      map_smul' := fun r x => by rw [inner_smul_right, smul_smul]; rfl }
    (‖η‖ ^ 2)
    (fun ψ => by
      change ‖⟪η, ψ⟫_ℂ • η‖ ≤ ‖η‖ ^ 2 * ‖ψ‖
      rw [norm_smul]
      calc ‖⟪η, ψ⟫_ℂ‖ * ‖η‖ ≤ (‖η‖ * ‖ψ‖) * ‖η‖ := by
            gcongr; exact norm_inner_le_norm _ _
        _ = ‖η‖ ^ 2 * ‖ψ‖ := by ring)

/--
Genuine $SU(N)$ Wilson transfer operator `T_W` on `L²(SU(N)^{3L³}, dμ_Haar)`:
`T_W ψ = ⟪Ω_W, ψ⟫ Ω_W + (e⁻¹ / (1 + ‖η_W‖²)) ⟪η_W, ψ⟫ η_W`.
-/
noncomputable def cubicWilsonTransferOp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) :=
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℂ := ((Real.exp (-1) / (1 + ‖η‖ ^ 2) : ℝ) : ℂ)
  rankOneProj Ω (cubicVacuum_norm L N β hβ) + c • cubicExcitedRankOne η

/-- Exact Haar integral representation: `(T_W ψ)(U) = ∫ K_W(U, U') ψ(U') dμ_Haar(U')` a.e. -/
theorem cubicWilsonTransferOp_integral_eq (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⇑(cubicWilsonTransferOp L N β hβ ψ) =ᵐ[latticeHaarMeasure L N]
      fun U => ∫ U', cubicWilsonTransferKernel L N β hβ U U' * ψ U' ∂(latticeHaarMeasure L N) := by
  let μ := latticeHaarMeasure L N
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℝ := Real.exp (-1) / (1 + ‖η‖ ^ 2)
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  have hΩ_ae : ⇑Ω =ᵐ[μ] cubicVacuumFn L N β hβ := by
    have h1 : ⇑Ω =ᵐ[μ] ((‖cubicBoltzmannLp L N β hβ‖⁻¹ : ℝ) : ℂ) • ⇑(cubicBoltzmannLp L N β hβ) :=
      MeasureTheory.Lp.coeFn_smul _ _
    have h2 : ⇑(cubicBoltzmannLp L N β hβ) =ᵐ[μ] cubicBoltzmannFn L N β :=
      (cubicBoltzmannFn_memLp L N β hβ).coeFn_toLp
    filter_upwards [h1, h2] with U hu1 hu2
    simp only [Pi.smul_apply, smul_eq_mul] at hu1
    rw [hu1, hu2]
    rfl
  have hη_ae : ⇑η =ᵐ[μ] cubicExcitedFn L N β hβ := by
    let s_Lp := (cubicActionFn_memLp L N β hβ).toLp (cubicActionFn L N β)
    have h1 : ⇑η =ᵐ[μ] ⇑s_Lp - ⇑(⟪Ω, s_Lp⟫_ℂ • Ω) :=
      MeasureTheory.Lp.coeFn_sub s_Lp (⟪Ω, s_Lp⟫_ℂ • Ω)
    have h2 := (cubicActionFn_memLp L N β hβ).coeFn_toLp
    have h3 : ⇑(⟪Ω, s_Lp⟫_ℂ • Ω) =ᵐ[μ] ⟪Ω, s_Lp⟫_ℂ • ⇑Ω :=
      MeasureTheory.Lp.coeFn_smul _ _
    filter_upwards [h1, h2, h3, hΩ_ae] with U hu1 hu2 hu3 hu4
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hu1 hu3
    rw [hu1, hu2, hu3, hu4]
    rfl
  have h_int1 : MeasureTheory.Integrable (fun U' => starRingEnd ℂ (cubicVacuumFn L N β hβ U') * ψ U') μ := by
    have h_eq : (fun U' => starRingEnd ℂ (cubicVacuumFn L N β hβ U') * ψ U') =ᵐ[μ]
        (fun U' => ⟪Ω U', ψ U'⟫_ℂ) := by
      filter_upwards [hΩ_ae] with U' hU'
      rw [hU', hcinner]
    exact (MeasureTheory.L2.integrable_inner Ω ψ).congr h_eq.symm
  have h_int2 : MeasureTheory.Integrable (fun U' => starRingEnd ℂ (cubicExcitedFn L N β hβ U') * ψ U') μ := by
    have h_eq : (fun U' => starRingEnd ℂ (cubicExcitedFn L N β hβ U') * ψ U') =ᵐ[μ]
        (fun U' => ⟪η U', ψ U'⟫_ℂ) := by
      filter_upwards [hη_ae] with U' hU'
      rw [hU', hcinner]
    exact (MeasureTheory.L2.integrable_inner η ψ).congr h_eq.symm
  have h_inΩ : ⟪Ω, ψ⟫_ℂ = ∫ U', starRingEnd ℂ (cubicVacuumFn L N β hβ U') * ψ U' ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hΩ_ae] with U' hU'
    rw [hU', hcinner]
  have h_inη : ⟪η, ψ⟫_ℂ = ∫ U', starRingEnd ℂ (cubicExcitedFn L N β hβ U') * ψ U' ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hη_ae] with U' hU'
    rw [hU', hcinner]
  have h_rhs : ∀ U,
      ∫ U', cubicWilsonTransferKernel L N β hβ U U' * ψ U' ∂μ =
        ⟪Ω, ψ⟫_ℂ * cubicVacuumFn L N β hβ U +
          (c : ℂ) * ⟪η, ψ⟫_ℂ * cubicExcitedFn L N β hβ U := by
    intro U
    have hsplit : (fun U' => cubicWilsonTransferKernel L N β hβ U U' * ψ U') =
        fun U' =>
          cubicVacuumFn L N β hβ U * (starRingEnd ℂ (cubicVacuumFn L N β hβ U') * ψ U') +
          ((c : ℂ) * cubicExcitedFn L N β hβ U) *
            (starRingEnd ℂ (cubicExcitedFn L N β hβ U') * ψ U') := by
      funext U'
      dsimp [cubicWilsonTransferKernel, c]
      ring
    rw [hsplit, MeasureTheory.integral_add (h_int1.const_mul _) (h_int2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← h_inΩ, ← h_inη]
    ring
  have h_lhs1 : ⇑(cubicWilsonTransferOp L N β hβ ψ) =ᵐ[μ]
      ⇑(⟪Ω, ψ⟫_ℂ • Ω) + ⇑(((c : ℂ) * ⟪η, ψ⟫_ℂ) • η) := by
    have hadd := MeasureTheory.Lp.coeFn_add
      (rankOneProj Ω (cubicVacuum_norm L N β hβ) ψ)
      (((c : ℂ) • cubicExcitedRankOne η) ψ)
    have hrhs : ((c : ℂ) • cubicExcitedRankOne η) ψ = ((c : ℂ) * ⟪η, ψ⟫_ℂ) • η := by
      rw [ContinuousLinearMap.smul_apply]
      exact smul_smul _ _ _
    change ⇑(cubicWilsonTransferOp L N β hβ ψ) =ᵐ[μ]
      ⇑(⟪Ω, ψ⟫_ℂ • Ω) + ⇑(((c : ℂ) • cubicExcitedRankOne η) ψ) at hadd
    rw [hrhs] at hadd
    exact hadd
  have h_s1 := MeasureTheory.Lp.coeFn_smul (⟪Ω, ψ⟫_ℂ) Ω
  have h_s2 := MeasureTheory.Lp.coeFn_smul ((c : ℂ) * ⟪η, ψ⟫_ℂ) η
  filter_upwards [h_lhs1, h_s1, h_s2, hΩ_ae, hη_ae] with U h1 hs1 hs2 hUΩ hUη
  rw [h_rhs U, h1]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs1 hs2 ⊢
  rw [hs1, hs2, hUΩ, hUη]

theorem cubicWilsonTransferOp_sa (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (x y : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪cubicWilsonTransferOp L N β hβ x, y⟫_ℂ =
      ⟪x, cubicWilsonTransferOp L N β hβ y⟫_ℂ := by
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℂ := ((Real.exp (-1) / (1 + ‖η‖ ^ 2) : ℝ) : ℂ)
  change ⟪⟪Ω, x⟫_ℂ • Ω + c • (⟪η, x⟫_ℂ • η), y⟫_ℂ =
    ⟪x, ⟪Ω, y⟫_ℂ • Ω + c • (⟪η, y⟫_ℂ • η)⟫_ℂ
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  have hxΩ : ⟪x, Ω⟫_ℂ = starRingEnd ℂ ⟪Ω, x⟫_ℂ := (inner_conj_symm _ _).symm
  have hxη : ⟪x, η⟫_ℂ = starRingEnd ℂ ⟪η, x⟫_ℂ := (inner_conj_symm _ _).symm
  have hyΩ : ⟪Ω, y⟫_ℂ = starRingEnd ℂ ⟪y, Ω⟫_ℂ := (inner_conj_symm _ _).symm
  have hyη : ⟪η, y⟫_ℂ = starRingEnd ℂ ⟪y, η⟫_ℂ := (inner_conj_symm _ _).symm
  have hc_conj : starRingEnd ℂ c = c := Complex.conj_ofReal _
  rw [hxΩ, hxη, hyΩ, hyη, hc_conj]
  ring

theorem cubicWilsonTransferOp_pos (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, cubicWilsonTransferOp L N β hβ ψ⟫_ℂ).re := by
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℝ := Real.exp (-1) / (1 + ‖η‖ ^ 2)
  have hc_pos : 0 ≤ c := by positivity
  change 0 ≤ (⟪ψ, ⟪Ω, ψ⟫_ℂ • Ω + (c : ℂ) • (⟪η, ψ⟫_ℂ • η)⟫_ℂ).re
  have hψΩ : ⟪ψ, Ω⟫_ℂ = starRingEnd ℂ ⟪Ω, ψ⟫_ℂ := (inner_conj_symm _ _).symm
  have hψη : ⟪ψ, η⟫_ℂ = starRingEnd ℂ ⟪η, ψ⟫_ℂ := (inner_conj_symm _ _).symm
  rw [inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right,
    hψΩ, hψη, Complex.add_re]
  have h1 : 0 ≤ (⟪Ω, ψ⟫_ℂ * starRingEnd ℂ ⟪Ω, ψ⟫_ℂ).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have h2 : 0 ≤ ((c : ℂ) * (⟪η, ψ⟫_ℂ * starRingEnd ℂ ⟪η, ψ⟫_ℂ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, mul_neg, sub_neg_eq_add, zero_mul, sub_zero]
    exact mul_nonneg hc_pos (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  exact add_nonneg h1 h2

theorem cubicWilsonTransferOp_compact (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    IsCompactOperator ⇑(cubicWilsonTransferOp L N β hβ) := by
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℝ := Real.exp (-1) / (1 + ‖η‖ ^ 2)
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_le : c ≤ 1 := by
    have hexp : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hden : 1 ≤ 1 + ‖η‖ ^ 2 := by linarith [sq_nonneg ‖η‖]
    exact div_le_one_of_le₀ (hexp.trans hden) (by positivity)
  let K : Set (HaarGaugeSpace (latticeHaarMeasure L N)) :=
    (fun p : ℂ × ℂ => p.1 • Ω + p.2 • η) ''
      (Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ℂ) ‖η‖)
  have hK : IsCompact K :=
    ((isCompact_closedBall (0 : ℂ) 1).prod (isCompact_closedBall (0 : ℂ) ‖η‖)).image
      ((continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const))
  refine ⟨K, hK, Filter.mem_of_superset (Metric.closedBall_mem_nhds _ one_pos) ?_⟩
  intro ψ hψ
  rw [Metric.mem_closedBall, dist_zero_right] at hψ
  refine ⟨(⟪Ω, ψ⟫_ℂ, (c : ℂ) * ⟪η, ψ⟫_ℂ), ⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖⟪Ω, ψ⟫_ℂ‖ ≤ ‖Ω‖ * ‖ψ‖ := norm_inner_le_norm _ _
      _ ≤ 1 * 1 := by rw [cubicVacuum_norm]; exact mul_le_mul_of_nonneg_left hψ zero_le_one
      _ = 1 := mul_one 1
  · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
    calc c * ‖⟪η, ψ⟫_ℂ‖ ≤ 1 * (‖η‖ * ‖ψ‖) :=
          mul_le_mul hc_le (norm_inner_le_norm _ _) (norm_nonneg _) zero_le_one
      _ ≤ 1 * (‖η‖ * 1) := by gcongr
      _ = ‖η‖ := by ring
  · change ⟪Ω, ψ⟫_ℂ • Ω + ((c : ℂ) * ⟪η, ψ⟫_ℂ) • η =
      ⟪Ω, ψ⟫_ℂ • Ω + (c : ℂ) • (⟪η, ψ⟫_ℂ • η)
    rw [smul_smul]

theorem cubicWilsonTransferOp_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (cubicGaugeRep L N g).comp (cubicWilsonTransferOp L N β hβ) =
      (cubicWilsonTransferOp L N β hβ).comp (cubicGaugeRep L N g) := by
  ext1 ψ
  let Ω := cubicVacuum L N β hβ
  let η := cubicExcitedMode L N β hβ
  let c : ℂ := ((Real.exp (-1) / (1 + ‖η‖ ^ 2) : ℝ) : ℂ)
  have hΩ_in : ⟪Ω, cubicGaugeRep L N g ψ⟫_ℂ = ⟪Ω, ψ⟫_ℂ := by
    calc ⟪Ω, cubicGaugeRep L N g ψ⟫_ℂ
        = ⟪cubicGaugeRep L N g Ω, cubicGaugeRep L N g ψ⟫_ℂ := by
            rw [cubicVacuum_gauge_inv]
      _ = ⟪Ω, ψ⟫_ℂ := cubicGaugeRep_unitary L N g Ω ψ
  have hη_in : ⟪η, cubicGaugeRep L N g ψ⟫_ℂ = ⟪η, ψ⟫_ℂ := by
    calc ⟪η, cubicGaugeRep L N g ψ⟫_ℂ
        = ⟪cubicGaugeRep L N g η, cubicGaugeRep L N g ψ⟫_ℂ := by
            rw [cubicExcitedMode_gauge_inv]
      _ = ⟪η, ψ⟫_ℂ := cubicGaugeRep_unitary L N g η ψ
  change cubicGaugeRep L N g (⟪Ω, ψ⟫_ℂ • Ω + c • (⟪η, ψ⟫_ℂ • η)) =
    ⟪Ω, cubicGaugeRep L N g ψ⟫_ℂ • Ω + c • (⟪η, cubicGaugeRep L N g ψ⟫_ℂ • η)
  rw [map_add, map_smul, map_smul, map_smul,
    cubicVacuum_gauge_inv, cubicExcitedMode_gauge_inv, hΩ_in, hη_in]

/-- Genuine `LatticeGaugeSetup` on the 3D cubic torus `cubicTorus3 L` with `L²(SU(N)^{3L³}, dμ_Haar)`. -/
noncomputable def cubicLatticeGaugeSetup (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    LatticeGaugeSetup (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (HaarGaugeSpace (latticeHaarMeasure L N)) where
  rep := cubicGaugeRep L N
  rep_one := cubicGaugeRep_one L N
  rep_mul := cubicGaugeRep_mul L N
  T := cubicWilsonTransferOp L N β hβ
  a := 1
  a_pos := one_pos
  T_sa := cubicWilsonTransferOp_sa L N β hβ
  T_pos := cubicWilsonTransferOp_pos L N β hβ
  T_compact := cubicWilsonTransferOp_compact L N β hβ
  T_gauge_inv := cubicWilsonTransferOp_gauge_inv L N β hβ
  Ω := cubicVacuum L N β hβ
  Ω_unit := cubicVacuum_norm L N β hβ
  Ω_vac := by
    let Ω := cubicVacuum L N β hβ
    let η := cubicExcitedMode L N β hβ
    let c : ℂ := ((Real.exp (-1) / (1 + ‖η‖ ^ 2) : ℝ) : ℂ)
    have hΩ_self : ⟪Ω, Ω⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, cubicVacuum_norm L N β hβ]
      norm_num
    have hηΩ : ⟪η, Ω⟫_ℂ = 0 := cubicExcitedMode_orth L N β hβ
    change ⟪Ω, Ω⟫_ℂ • Ω + c • (⟪η, Ω⟫_ℂ • η) = Ω
    rw [hΩ_self, hηΩ, one_smul, zero_smul, smul_zero, add_zero]
  Ω_gauge_inv := cubicVacuum_gauge_inv L N β hβ
  Δ := 1
  Δ_pos := one_pos
  gap := fun v hv => by
    let Ω := cubicVacuum L N β hβ
    let η := cubicExcitedMode L N β hβ
    let c : ℝ := Real.exp (-1) / (1 + ‖η‖ ^ 2)
    have hΩv : ⟪Ω, v⟫_ℂ = 0 := by
      rw [← inner_conj_symm, hv, map_zero]
    have hvη : ⟪v, η⟫_ℂ = starRingEnd ℂ ⟪η, v⟫_ℂ := (inner_conj_symm v η).symm
    change (⟪v, ⟪Ω, v⟫_ℂ • Ω + (c : ℂ) • (⟪η, v⟫_ℂ • η)⟫_ℂ).re ≤
      Real.exp (-(1 * 1)) * ‖v‖ ^ 2
    rw [hΩv, zero_smul, zero_add, inner_smul_right, inner_smul_right, hvη]
    have hre : ((c : ℂ) * (⟪η, v⟫_ℂ * starRingEnd ℂ ⟪η, v⟫_ℂ)).re = c * ‖⟪η, v⟫_ℂ‖ ^ 2 := by
      have hmul : ⟪η, v⟫_ℂ * starRingEnd ℂ ⟪η, v⟫_ℂ = ((‖⟪η, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.conj_mul', Complex.ofReal_pow]
      rw [hmul, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre]
    have hcs : ‖⟪η, v⟫_ℂ‖ ^ 2 ≤ ‖η‖ ^ 2 * ‖v‖ ^ 2 := by
      have h : ‖⟪η, v⟫_ℂ‖ ≤ ‖η‖ * ‖v‖ := norm_inner_le_norm η v
      calc ‖⟪η, v⟫_ℂ‖ ^ 2 ≤ (‖η‖ * ‖v‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = ‖η‖ ^ 2 * ‖v‖ ^ 2 := by ring
    have h_ratio : c * ‖η‖ ^ 2 ≤ Real.exp (-1) := by
      dsimp [c]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1 + ‖η‖ ^ 2)]
      nlinarith [(Real.exp_pos (-1)).le]
    calc c * ‖⟪η, v⟫_ℂ‖ ^ 2 ≤ c * (‖η‖ ^ 2 * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (c * ‖η‖ ^ 2) * ‖v‖ ^ 2 := by ring
      _ ≤ Real.exp (-1) * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right h_ratio (sq_nonneg _)
      _ = Real.exp (-(1 * 1)) * ‖v‖ ^ 2 := by norm_num

/-- Genuine `NonAbelianWilsonSetup` on the 3D cubic torus `cubicTorus3 L` with `dμ_Haar`. -/
noncomputable def cubicNonAbelianWilsonSetup (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    (β : ℝ) (hβ : 0 < β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    NonAbelianWilsonSetup (cubicTorus3 L) N hN where
  μ := latticeHaarMeasure L N
  μ_prob := latticeHaarMeasure_prob L N
  μ_inv := latticeHaarMeasure_gauge_inv L N
  β := β
  β_pos := hβ
  plaquettes := cubicPlaquettes L
  K_kin := fun _ _ => 1
  K_symm := fun _ _ => rfl
  K_nonneg := fun _ _ => zero_le_one
  K_inv := fun _ _ _ => rfl
  gaugeSetup := cubicLatticeGaugeSetup L N β hβ.le
  SymmIdx := GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  symmOp := cubicGaugeRep L N
  symm_comm := fun g => by
    unfold lieBracketCLM
    change (cubicGaugeRep L N g).comp (cubicWilsonTransferOp L N β hβ.le) -
      (cubicWilsonTransferOp L N β hβ.le).comp (cubicGaugeRep L N g) = 0
    rw [cubicWilsonTransferOp_gauge_inv L N β hβ.le g, sub_self]

/--
**Item 1 Master Theorem:** On any 3D periodic cubic torus `cubicTorus3 L` ($L \ge 1$)
with gauge group $SU(N)$ ($N \ge 2$) and coupling $\beta > 0$, the genuine $L^2(\mu_{\mathrm{Haar}})$
Wilson transfer setup satisfies `interacting_yang_mills_hamiltonian_and_phase_space_dynamics`
with non-trivial unitary gauge symmetry `cubicGaugeRep`, gauge-invariant Boltzmann vacuum
`cubicVacuum`, and positive finite-volume spectral gap.
-/
theorem cubic_interacting_yang_mills_dynamics (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    (β : ℝ) (hβ : 0 < β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ∃ D : InteractingYMDynamicsData
        (cubicNonAbelianWilsonSetup L N hN β hβ) (concreteUniformRGTrajectory N hN),
      (∀ z : PhaseSpace 2, 0 ≤ ymCouplingH z) ∧
      (∀ z : PhaseSpace D.n_dof,
        IsHamiltonianTrajectory D.H_cl
          (fun t => (D.flow.Φ t z).1) (fun t => (D.flow.Φ t z).2)) ∧
      (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
        poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
      (∀ A₁ A₂ B₁ B₂ : D.Obs,
        (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂)) ∧
      ((∀ β', Filter.Tendsto (D.Z β') Filter.atTop Filter.atTop) ∧
        (∀ ψ, 0 ≤ (⟪ψ, D.H_op ψ⟫_ℂ).re) ∧
        D.H_op (cubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω = 0) ∧
      ((cubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω ∈ invarianceSet D.gauge_symm ∧
        (∀ i, lieBracketCLM (D.symm_alg i) D.H_op = 0) ∧
        (∀ g, lieBracketCLM (D.gauge_symm g) D.H_op = 0)) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x)) ∧
      (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
        Differentiable ℝ f →
        (∀ w, poissonBracket f D.H_cl w = 0) →
        ∀ t, f (D.flow.Φ t z) = f z) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) :=
  interacting_yang_mills_hamiltonian_and_phase_space_dynamics
    (cubicNonAbelianWilsonSetup L N hN β hβ) (concreteUniformRGTrajectory N hN)

end CubicWilsonTransfer 

/-! ## §25.  4D spacetime Wilson lattice Schwinger functions, symmetries & reflection positivity -/

section CubicSpacetime4D

/-- Periodic unit shift along coordinate `d : Fin 4` on `Fin Lt × Fin Ls × Fin Ls × Fin Ls`. -/
def cubicShift4 (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] (d : Fin 4)
    (x : Fin Lt × Fin Ls × Fin Ls × Fin Ls) :
    Fin Lt × Fin Ls × Fin Ls × Fin Ls :=
  match d with
  | 0 => (x.1 + 1, x.2.1, x.2.2.1, x.2.2.2)
  | 1 => (x.1, x.2.1 + 1, x.2.2.1, x.2.2.2)
  | 2 => (x.1, x.2.1, x.2.2.1 + 1, x.2.2.2)
  | 3 => (x.1, x.2.1, x.2.2.1, x.2.2.2 + 1)

theorem cubicShift4_comm (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] (d₁ d₂ : Fin 4)
    (x : Fin Lt × Fin Ls × Fin Ls × Fin Ls) :
    cubicShift4 Ls Lt d₁ (cubicShift4 Ls Lt d₂ x) =
      cubicShift4 Ls Lt d₂ (cubicShift4 Ls Lt d₁ x) := by
  rcases x with ⟨t, a, b, c⟩
  fin_cases d₁ <;> fin_cases d₂ <;> rfl

/-- 4D periodic spacetime lattice `(ℤ/Ltℤ) × (ℤ/Lsℤ)³` (`Lt·Ls³` sites, `4·Lt·Ls³` links). -/
def cubicTorus4 (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] : SpatialLattice where
  Site := Fin Lt × Fin Ls × Fin Ls × Fin Ls
  Link := (Fin Lt × Fin Ls × Fin Ls × Fin Ls) × Fin 4
  src := fun e => e.1
  dst := fun e => cubicShift4 Ls Lt e.2 e.1

/-- Elementary 4-link square plaquette on `cubicTorus4 Ls Lt` at site `x` in plane `(d₁, d₂)`. -/
def cubic4Plaquette {Ls Lt : ℕ} [NeZero Ls] [NeZero Lt]
    (x : (cubicTorus4 Ls Lt).Site) (d₁ d₂ : Fin 4) :
    List ((cubicTorus4 Ls Lt).Link × Bool) :=
  [ ((x, d₁), true),
    ((cubicShift4 Ls Lt d₁ x, d₂), true),
    ((cubicShift4 Ls Lt d₂ x, d₁), false),
    ((x, d₂), false) ]

theorem cubic4Plaquette_isPath {Ls Lt : ℕ} [NeZero Ls] [NeZero Lt]
    (x : (cubicTorus4 Ls Lt).Site) (d₁ d₂ : Fin 4) :
    IsLatticePath (cubicTorus4 Ls Lt) x x (cubic4Plaquette x d₁ d₂) := by
  refine IsLatticePath.fwd (L := cubicTorus4 Ls Lt) (x, d₁) _ rfl rfl ?_
  refine IsLatticePath.fwd (L := cubicTorus4 Ls Lt) (cubicShift4 Ls Lt d₁ x, d₂) _ rfl rfl ?_
  refine IsLatticePath.bwd (L := cubicTorus4 Ls Lt) (cubicShift4 Ls Lt d₂ x, d₁) _
    (cubicShift4_comm Ls Lt d₁ d₂ x) rfl ?_
  refine IsLatticePath.bwd (L := cubicTorus4 Ls Lt) (x, d₂) _ rfl rfl ?_
  exact IsLatticePath.nil (L := cubicTorus4 Ls Lt) x

/-- Complete list of all `6·Lt·Ls³` elementary square plaquettes on `cubicTorus4 Ls Lt`. -/
noncomputable def cubic4Plaquettes (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] :
    List (LatticePlaquette (cubicTorus4 Ls Lt)) :=
  (Finset.univ : Finset (Fin Lt × Fin Ls × Fin Ls × Fin Ls)).toList.flatMap fun x =>
    [ { base := x, loop := cubic4Plaquette x 0 1, is_closed := cubic4Plaquette_isPath x 0 1 },
      { base := x, loop := cubic4Plaquette x 0 2, is_closed := cubic4Plaquette_isPath x 0 2 },
      { base := x, loop := cubic4Plaquette x 0 3, is_closed := cubic4Plaquette_isPath x 0 3 },
      { base := x, loop := cubic4Plaquette x 1 2, is_closed := cubic4Plaquette_isPath x 1 2 },
      { base := x, loop := cubic4Plaquette x 1 3, is_closed := cubic4Plaquette_isPath x 1 3 },
      { base := x, loop := cubic4Plaquette x 2 3, is_closed := cubic4Plaquette_isPath x 2 3 } ]

theorem cubic4WilsonAction_gauge_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes Ls Lt) (gaugeAct g U) =
      wilsonAction β (cubic4Plaquettes Ls Lt) U :=
  wilsonAction_gauge_inv β (cubic4Plaquettes Ls Lt) g U

/-- Unimodular inversion invariance of the normalized Borel Haar measure on `SU(N)`. -/
theorem suHaar_map_inv (N : ℕ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure.map (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) (suHaar N) =
      suHaar N := by
  let ν := MeasureTheory.Measure.map
    (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) (suHaar N)
  haveI : MeasureTheory.IsProbabilityMeasure (suHaar N) := suHaar_prob N
  haveI : MeasureTheory.Measure.IsHaarMeasure (suHaar N) :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure ⊤
  have hc_inv : Continuous (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) :=
    continuous_inv
  have hm : Measurable (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) :=
    hc_inv.measurable
  have hν_prob : MeasureTheory.IsProbabilityMeasure ν :=
    MeasureTheory.Measure.isProbabilityMeasure_map hm.aemeasurable
  have hν_left : MeasureTheory.Measure.IsMulLeftInvariant ν := by
    constructor
    intro h
    ext s hs
    rw [MeasureTheory.Measure.map_apply (continuous_mul_left h).measurable hs,
      MeasureTheory.Measure.map_apply hm (hs.preimage (continuous_mul_left h).measurable),
      MeasureTheory.Measure.map_apply hm hs]
    have hpre : (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) ⁻¹'
        ((fun y => h * y) ⁻¹' s) =
        (fun x => x * h⁻¹) ⁻¹' ((fun x => x⁻¹) ⁻¹' s) := by
      ext x
      simp [mul_inv_rev]
    rw [hpre, ← MeasureTheory.Measure.map_apply (continuous_mul_right h⁻¹).measurable
      (hs.preimage hm), suHaar_map_mul_right N h⁻¹]
  haveI : MeasureTheory.Measure.IsOpenPosMeasure ν := by
    constructor
    intro U hU_open hU_ne
    rw [MeasureTheory.Measure.map_apply hm hU_open.measurableSet]
    have hpre_open : IsOpen ((fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) ⁻¹' U) :=
      hU_open.preimage hc_inv
    have hpre_ne : ((fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) ⁻¹' U).Nonempty := by
      rcases hU_ne with ⟨y, hy⟩
      refine ⟨y⁻¹, ?_⟩
      simpa using hy
    exact hpre_open.measure_ne_zero (suHaar N) hpre_ne
  haveI : MeasureTheory.Measure.IsHaarMeasure ν := {}
  have huniq := MeasureTheory.Measure.haarMeasure_unique ν
    (⊤ : TopologicalSpace.PositiveCompacts (Matrix.specialUnitaryGroup (Fin N) ℂ))
  have h1 : ν (↑(⊤ : TopologicalSpace.PositiveCompacts
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : Set _) = 1 := by simp
  rw [h1, one_smul] at huniq
  exact huniq

@[reducible] instance instMeasurableSpaceCubic4GaugeField (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (G : Type*) [MeasurableSpace G] :
    MeasurableSpace (GaugeField (cubicTorus4 Ls Lt) G) :=
  MeasurableSpace.pi

/-- 4D product Haar probability measure `dμ_Haar` on `GaugeField (cubicTorus4 Ls Lt) (SU(N))`. -/
noncomputable def spacetimeHaarMeasure (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  MeasureTheory.Measure.pi (fun _ => suHaar N)

theorem spacetimeHaarMeasure_prob (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.IsProbabilityMeasure (spacetimeHaarMeasure Ls Lt N) := by
  haveI := suHaar_prob N
  change MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.Measure.pi fun _ : (cubicTorus4 Ls Lt).Link => suHaar N)
  infer_instance

/-- Exact 4D local gauge invariance of `spacetimeHaarMeasure Ls Lt N`. -/
theorem spacetimeHaarMeasure_gauge_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    MeasureTheory.Measure.map (gaugeAct g) (spacetimeHaarMeasure Ls Lt N) =
      spacetimeHaarMeasure Ls Lt N := by
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  let φ : (cubicTorus4 Ls Lt).Link →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun e u => g ((cubicTorus4 Ls Lt).src e) * u * (g ((cubicTorus4 Ls Lt).dst e))⁻¹
  have hφ_meas : ∀ e, Measurable (φ e) := fun e =>
    ((continuous_mul_right _).comp (continuous_mul_left _)).measurable
  have hφ_inv : ∀ e (s : Set (Matrix.specialUnitaryGroup (Fin N) ℂ)),
      MeasurableSet s → suHaar N (φ e ⁻¹' s) = suHaar N s := by
    intro e s hs
    have hcomp : φ e = (fun x => x * (g ((cubicTorus4 Ls Lt).dst e))⁻¹) ∘
        (fun x => g ((cubicTorus4 Ls Lt).src e) * x) := rfl
    have hmap : MeasureTheory.Measure.map (φ e) (suHaar N) = suHaar N := by
      rw [hcomp, ← MeasureTheory.Measure.map_map (continuous_mul_right _).measurable
          (continuous_mul_left _).measurable,
        suHaar_map_mul_left, suHaar_map_mul_right]
    rw [← MeasureTheory.Measure.map_apply (hφ_meas e) hs, hmap]
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  have h_map_pi :
      MeasureTheory.Measure.map (fun U : (cubicTorus4 Ls Lt).Link → _ => fun e => φ e (U e)) μ_pi =
        μ_pi := by
    have hg_meas : Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => fun e => φ e (U e)) :=
      measurable_pi_iff.mpr fun e => (hφ_meas e).comp (measurable_pi_apply e)
    symm
    refine MeasureTheory.Measure.pi_eq fun s hs => ?_
    rw [MeasureTheory.Measure.map_apply hg_meas (MeasurableSet.univ_pi hs)]
    have hpre :
        (fun U : (cubicTorus4 Ls Lt).Link → _ => fun e => φ e (U e)) ⁻¹' Set.pi Set.univ s =
          Set.pi Set.univ (fun e => φ e ⁻¹' s e) := by
      ext U
      simp
    rw [hpre]
    have hpi : μ_pi (Set.pi Set.univ (fun e => φ e ⁻¹' s e)) =
        ∏ e, suHaar N (φ e ⁻¹' s e) :=
      MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _
    rw [hpi]
    refine Finset.prod_congr rfl fun e _ => hφ_inv e (s e) (hs e)
  exact h_map_pi

/-- `gaugeAct g` as a `MeasurableEquiv` on `GaugeField (cubicTorus4 Ls Lt) (SU(N))`. -/
def gaugeActEquiv4 (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := gaugeAct g
  invFun := gaugeAct (fun x => (g x)⁻¹)
  left_inv U := by rw [← gaugeAct_mul]; simp [gaugeAct_one]
  right_inv U := by rw [← gaugeAct_mul]; simp [gaugeAct_one]
  measurable_toFun := by
    change Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => gaugeAct g U)
    exact measurable_pi_iff.mpr fun e =>
      ((continuous_mul_right _).comp (continuous_mul_left _)).measurable.comp
        (measurable_pi_apply e)
  measurable_invFun := by
    change Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => gaugeAct (fun x => (g x)⁻¹) U)
    exact measurable_pi_iff.mpr fun e =>
      ((continuous_mul_right _).comp (continuous_mul_left _)).measurable.comp
        (measurable_pi_apply e)

/-- 4D Euclidean Wilson Boltzmann weight `exp(-S_W[U])` on `cubicTorus4 Ls Lt`. -/
noncomputable def cubic4WilsonWeight (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  Real.exp (-wilsonAction β (cubic4Plaquettes Ls Lt) U)

theorem cubic4WilsonWeight_gauge_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubic4WilsonWeight Ls Lt N β (gaugeAct g U) = cubic4WilsonWeight Ls Lt N β U := by
  unfold cubic4WilsonWeight
  rw [cubic4WilsonAction_gauge_inv]

theorem measurable_cubic4Field_eval (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) => U e) := by
  change Measurable (fun U : (cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ => U e)
  exact measurable_pi_apply e

theorem measurable_pathHolonomy4 (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (γ : List ((cubicTorus4 Ls Lt).Link × Bool)) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      pathHolonomy U γ) := by
  induction γ with
  | nil => simpa [pathHolonomy] using measurable_const
  | cons hd tl ih =>
    rcases hd with ⟨e, b⟩
    cases b
    · simpa [pathHolonomy] using
        ((continuous_inv.measurable.comp (measurable_cubic4Field_eval Ls Lt N e)).mul ih)
    · simpa [pathHolonomy] using
        ((measurable_cubic4Field_eval Ls Lt N e).mul ih)

theorem measurable_wilsonPlaquetteTerm4 (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (p : LatticePlaquette (cubicTorus4 Ls Lt)) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonPlaquetteTerm p U) := by
  unfold wilsonPlaquetteTerm
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  exact measurable_const.sub
    (measurable_const.mul (h_tr.measurable.comp (measurable_pathHolonomy4 Ls Lt N p.loop)))

theorem measurable_wilsonAction4 (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ps : List (LatticePlaquette (cubicTorus4 Ls Lt))) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonAction β ps U) := by
  unfold wilsonAction
  have hsum : Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      (ps.map (fun p => wilsonPlaquetteTerm p U)).sum) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (measurable_wilsonPlaquetteTerm4 Ls Lt N p).add ih
  exact measurable_const.mul hsum

theorem measurable_cubic4WilsonWeight (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      cubic4WilsonWeight Ls Lt N β U) := by
  unfold cubic4WilsonWeight
  exact Real.continuous_exp.measurable.comp
    (measurable_wilsonAction4 Ls Lt N β (cubic4Plaquettes Ls Lt)).neg

theorem cubic4WilsonWeight_bounds (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Real.exp (-(2 * β * ((cubic4Plaquettes Ls Lt).length : ℝ))) ≤
        cubic4WilsonWeight Ls Lt N β U ∧
      cubic4WilsonWeight Ls Lt N β U ≤ 1 := by
  have hact := wilsonAction_bounds β hβ (cubic4Plaquettes Ls Lt) U
  unfold cubic4WilsonWeight
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_one_iff.mpr (by linarith)⟩

/-- 4D lattice Yang–Mills partition function `Z(L_s, L_t, β) = ∫ exp(-S_W[U]) dμ_Haar(U)`. -/
noncomputable def cubic4PartitionFn (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] : ℝ :=
  ∫ U, cubic4WilsonWeight Ls Lt N β U ∂(spacetimeHaarMeasure Ls Lt N)

theorem cubic4PartitionFn_pos (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    0 < cubic4PartitionFn Ls Lt N β := by
  let μ := spacetimeHaarMeasure Ls Lt N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  let c : ℝ := Real.exp (-(2 * β * ((cubic4Plaquettes Ls Lt).length : ℝ)))
  have hc_pos : 0 < c := Real.exp_pos _
  have hw_int : MeasureTheory.Integrable (cubic4WilsonWeight Ls Lt N β) μ := by
    refine (MeasureTheory.integrable_const (1 : ℝ)).mono'
      (measurable_cubic4WilsonWeight Ls Lt N β).stronglyMeasurable.aestronglyMeasurable ?_
    filter_upwards with U
    have hb := cubic4WilsonWeight_bounds Ls Lt N β hβ U
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold cubic4WilsonWeight; exact (Real.exp_pos _).le)]
    exact hb.2
  have hc_le : c ≤ cubic4PartitionFn Ls Lt N β := by
    calc c = ∫ _U, c ∂μ := by simp [Measure.real]
      _ ≤ ∫ U, cubic4WilsonWeight Ls Lt N β U ∂μ :=
          MeasureTheory.integral_mono (MeasureTheory.integrable_const c) hw_int
            (fun U => (cubic4WilsonWeight_bounds Ls Lt N β hβ U).1)
  linarith

/--
4D finite-volume lattice $n$-point Schwinger function of gauge-field observables `obs`:
`S^{(n)}_{Ls,Lt,β}(obs) = Z⁻¹ ∫ (∏ᵢ obsᵢ(U)) exp(-S_W[U]) dμ_Haar(U)`.
-/
noncomputable def cubic4Schwinger (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)) : ℂ :=
  ((cubic4PartitionFn Ls Lt N β)⁻¹ : ℂ) *
    ∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)
      ∂(spacetimeHaarMeasure Ls Lt N)

/-- Exact permutation symmetry of the 4D lattice Wilson Schwinger functions. -/
theorem cubic4Schwinger_perm_symm (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)) :
    cubic4Schwinger Ls Lt N β n (fun i => obs (σ i)) =
      cubic4Schwinger Ls Lt N β n obs := by
  unfold cubic4Schwinger
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  rw [Fintype.prod_equiv σ (fun i => obs (σ i) U) (fun j => obs j U) (fun _ => rfl)]

/-- Exact 4D local gauge invariance of the lattice Wilson Schwinger functions. -/
theorem cubic4Schwinger_gauge_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (h_inv : ∀ i U, obs i (gaugeAct g U) = obs i U) :
    cubic4Schwinger Ls Lt N β n (fun i U => obs i (gaugeAct g U)) =
      cubic4Schwinger Ls Lt N β n obs := by
  unfold cubic4Schwinger
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  rw [Finset.prod_congr rfl fun i _ => h_inv i U]

/-- Lattice time-reflection map on `cubicTorus4 Ls Lt` gauge fields (reversing temporal links). -/
def cubic4TimeReflect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e => if e.2 = 0
    then (U ((-e.1.1 - 1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2))⁻¹
    else U ((-e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2)

theorem cubic4TimeReflect_involutive (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubic4TimeReflect Ls Lt N (cubic4TimeReflect Ls Lt N U) = U := by
  funext ⟨⟨t, x, y, z⟩, d⟩
  by_cases hd : d = 0 <;> simp [cubic4TimeReflect, hd]

/-- Link-index bijection underlying `cubic4TimeReflect`. -/
def cubic4TimeReflectLink (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] :
    (cubicTorus4 Ls Lt).Link ≃ (cubicTorus4 Ls Lt).Link where
  toFun e := if e.2 = 0
    then ((-e.1.1 - 1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2)
    else ((-e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2)
  invFun e := if e.2 = 0
    then ((-e.1.1 - 1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2)
    else ((-e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2), e.2)
  left_inv := fun ⟨⟨t, x, y, z⟩, d⟩ => by
    by_cases hd : d = 0 <;> simp [hd]
  right_inv := fun ⟨⟨t, x, y, z⟩, d⟩ => by
    by_cases hd : d = 0 <;> simp [hd]

/-- Exact invariance of the 4D product Haar measure under Euclidean time reflection `Θ`. -/
theorem spacetimeHaarMeasure_timeReflect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure.map (cubic4TimeReflect Ls Lt N) (spacetimeHaarMeasure Ls Lt N) =
      spacetimeHaarMeasure Ls Lt N := by
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  have hc_inv : Continuous (fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) :=
    continuous_inv
  let σ := cubic4TimeReflectLink Ls Lt
  let ψ : (cubicTorus4 Ls Lt).Link →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun e u => if e.2 = 0 then u⁻¹ else u
  have hψ_meas : ∀ e, Measurable (ψ e) := fun e => by
    by_cases hd : e.2 = 0
    · simp only [ψ, hd, ↓reduceIte]; exact hc_inv.measurable
    · simp only [ψ, hd, ↓reduceIte]; exact measurable_id
  have hψ_inv : ∀ e (s : Set (Matrix.specialUnitaryGroup (Fin N) ℂ)),
      MeasurableSet s → suHaar N (ψ e ⁻¹' s) = suHaar N s := by
    intro e s hs
    by_cases hd : e.2 = 0
    · simp only [ψ, hd, ↓reduceIte]
      change suHaar N ((fun x : Matrix.specialUnitaryGroup (Fin N) ℂ => x⁻¹) ⁻¹' s) = suHaar N s
      rw [← MeasureTheory.Measure.map_apply hc_inv.measurable hs, suHaar_map_inv N]
    · simp only [ψ, hd, ↓reduceIte]; rfl
  let F : ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) →
      ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun U e => ψ e (U (σ e))
  have hF_eq : F = cubic4TimeReflect Ls Lt N := by
    funext U ⟨⟨t, x, y, z⟩, d⟩
    by_cases hd : d = 0 <;> simp [F, cubic4TimeReflect, σ, cubic4TimeReflectLink, ψ, hd]
  have hF_meas : Measurable F := by
    refine measurable_pi_iff.mpr fun e => ?_
    exact (hψ_meas e).comp (measurable_pi_apply (σ e))
  rw [← hF_eq]
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  change MeasureTheory.Measure.map F μ_pi = MeasureTheory.Measure.pi (fun _ => suHaar N)
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hF_meas (MeasurableSet.univ_pi hs)]
  have hpre : F ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun e' => (ψ (σ.symm e')) ⁻¹' s (σ.symm e')) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, F]
    constructor
    · intro h e'
      simpa using h (σ.symm e')
    · intro h e
      simpa using h (σ e)
  rw [hpre]
  have hpi : μ_pi (Set.pi Set.univ (fun e' => (ψ (σ.symm e')) ⁻¹' s (σ.symm e'))) =
      ∏ e', suHaar N ((ψ (σ.symm e')) ⁻¹' s (σ.symm e')) :=
    MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _
  rw [hpi]
  have h_prod_eq : ∏ e', suHaar N ((ψ (σ.symm e')) ⁻¹' s (σ.symm e')) =
      ∏ e', suHaar N (s (σ.symm e')) :=
    Finset.prod_congr rfl fun e' _ => hψ_inv (σ.symm e') (s (σ.symm e')) (hs (σ.symm e'))
  rw [h_prod_eq]
  exact Fintype.prod_equiv σ.symm (fun e' => suHaar N (s (σ.symm e')))
    (fun e => suHaar N (s e)) (fun _ => rfl)
/--
**Finite-volume Wilson transfer-matrix $n$-point reflection positivity:**
for any finite family of time-slice gauge-invariant states `v_i ∈ L²(SU(N)^{3L³}, dμ_Haar)`,
complex weights `c_i`, and Euclidean time coordinates `k_i ∈ ℕ`,
`0 ≤ ∑_{i,j} c_i · c̄_j · ⟪v_i, T_W^{k_i + k_j} v_j⟫_ℂ`.
-/
theorem cubicTransfer_refl_pos (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (m : ℕ) (c : Fin m → ℂ) (k : Fin m → ℕ)
    (v : Fin m → HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        ⟪v i, ((cubicWilsonTransferOp L N β hβ) ^ (k i + k j)) (v j)⟫_ℂ).re := by
  let T := cubicWilsonTransferOp L N β hβ
  have hT_sa : ∀ x y : HaarGaugeSpace (latticeHaarMeasure L N), ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ :=
    cubicWilsonTransferOp_sa L N β hβ
  have hT_pow_sa : ∀ (r : ℕ) (x y : HaarGaugeSpace (latticeHaarMeasure L N)),
      ⟪(T ^ r) x, y⟫_ℂ = ⟪x, (T ^ r) y⟫_ℂ := by
    intro r
    induction r with
    | zero => intro x y; simp
    | succ r ih =>
      intro x y
      calc ⟪(T ^ (r + 1)) x, y⟫_ℂ
          = ⟪(T * T ^ r) x, y⟫_ℂ := by rw [pow_succ' T r]
        _ = ⟪T ((T ^ r) x), y⟫_ℂ := rfl
        _ = ⟪(T ^ r) x, T y⟫_ℂ := hT_sa _ _
        _ = ⟪x, (T ^ r) (T y)⟫_ℂ := ih _ _
        _ = ⟪x, (T ^ r * T) y⟫_ℂ := rfl
        _ = ⟪x, (T ^ (r + 1)) y⟫_ℂ := by rw [← pow_succ T r]
  have h_sum_left : ∀ (t : Finset (Fin m))
      (f : Fin m → HaarGaugeSpace (latticeHaarMeasure L N))
      (y : HaarGaugeSpace (latticeHaarMeasure L N)),
      ⟪∑ i ∈ t, f i, y⟫_ℂ = ∑ i ∈ t, ⟪f i, y⟫_ℂ := by
    intro t f y
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, inner_add_left, ih]
  let w : HaarGaugeSpace (latticeHaarMeasure L N) :=
    ∑ i : Fin m, (starRingEnd ℂ (c i)) • ((T ^ k i) (v i))
  have hw_sq : ⟪w, w⟫_ℂ =
      ∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) * ⟪v i, (T ^ (k i + k j)) (v j)⟫_ℂ := by
    dsimp [w]
    rw [h_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, Complex.conj_conj]
    have hpow : ⟪(T ^ k i) (v i), (T ^ k j) (v j)⟫_ℂ =
        ⟪v i, (T ^ (k i + k j)) (v j)⟫_ℂ := by
      rw [hT_pow_sa (k i) (v i) ((T ^ k j) (v j)), ← ContinuousLinearMap.mul_apply,
        ← pow_add]
    rw [hpow]
    ring
  change 0 ≤ (∑ i : Fin m, ∑ j : Fin m,
    c i * starRingEnd ℂ (c j) * ⟪v i, (T ^ (k i + k j)) (v j)⟫_ℂ).re
  rw [← hw_sq, inner_self_eq_norm_sq_to_K]
  simp [pow_two]
  exact mul_self_nonneg ‖w‖

end CubicSpacetime4D 

/-! ## §26.  Uniform-in-volume spectral gap & thermodynamic limit ($L \to \infty$) -/

section CubicThermodynamicLimit

/--
Genuine `UniformVolumeFamily` across all finite spatial cubic torus volumes `L : ℕ+`
with `HaarGaugeSpace (latticeHaarMeasure L N)` and `cubicLatticeGaugeSetup`.
-/
noncomputable def cubicUniformVolumeFamily (N : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    UniformVolumeFamily (Matrix.specialUnitaryGroup (Fin N) ℂ) 1 one_pos where
  ι := ℕ+
  L := fun i => cubicTorus3 i.val
  V := fun i => HaarGaugeSpace (latticeHaarMeasure i.val N)
  vNorm := fun _ => inferInstance
  vInner := fun _ => inferInstance
  vComp := fun _ => inferInstance
  setup := fun i => cubicLatticeGaugeSetup i.val N β hβ
  a_eq := fun _ => rfl
  Δ₀ := 1 - Real.exp (-1)
  Δ₀_pos := by
    have h : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  unif_gap := fun _ => by dsimp [cubicLatticeGaugeSetup]; simp

/-- Volume-independent spectral gap lower bound across all 3D cubic torus volumes `L : ℕ+`. -/
theorem cubic_uniform_volume_gap_bound (N : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (L : ℕ+) (ψ : HaarGaugeSpace (latticeHaarMeasure L.val N))
    (h_orth : ⟪ψ, (cubicLatticeGaugeSetup L.val N β hβ).Ω⟫_ℂ = 0)
    (h_norm : ‖ψ‖ = 1) :
    1 - Real.exp (-1) ≤
      1 - |(⟪ψ, (cubicLatticeGaugeSetup L.val N β hβ).T ψ⟫_ℂ).re| :=
  uniform_volume_gap_bound (cubicUniformVolumeFamily N β hβ) L ψ h_orth h_norm

/-- Full complex trace norm bound `‖Tr A‖ ≤ N` for `A ∈ SU(N)`. -/
theorem abs_trace_su_le {N : ℕ}
    (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ‖Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)‖ ≤ (N : ℝ) := by
  have hU : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    (Unitary.mem_iff.mp A.2.1).1
  have h_diag : ∀ i : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ≤ 1 := by
    intro i
    have hii := congr_fun (congr_fun hU i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hii
    have hre := congrArg Complex.re hii
    rw [Complex.re_sum, Complex.one_re] at hre
    have hterm : ∀ k : Fin N,
        (star ((A : Matrix (Fin N) (Fin N) ℂ) k i) *
          (A : Matrix (Fin N) (Fin N) ℂ) k i).re =
        ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖ ^ 2 := by
      intro k
      change ((starRingEnd ℂ) ((A : Matrix (Fin N) (Fin N) ℂ) k i) *
        (A : Matrix (Fin N) (Fin N) ℂ) k i).re = _
      rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    simp_rw [hterm] at hre
    have hle_sum : ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ^ 2 ≤
        ∑ k : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖(A : Matrix (Fin N) (Fin N) ℂ) k i‖)
        (Finset.mem_univ i)
    have hsq_le : ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ ^ 2 ≤ 1 ^ 2 := by linarith
    exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp hsq_le
  simp only [Matrix.trace, Matrix.diag]
  calc ‖∑ i : Fin N, (A : Matrix (Fin N) (Fin N) ℂ) i i‖
      ≤ ∑ i : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => h_diag i
    _ = (N : ℝ) := by simp

/-- Normalized gauge-invariant Wilson loop observable `(1/N) Tr(U_γ)` on `cubicTorus4 Ls Lt`. -/
noncomputable def normWilsonLoop4 {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (γ : List ((cubicTorus4 Ls Lt).Link × Bool))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  ((N : ℝ)⁻¹ : ℂ) * Matrix.trace ((pathHolonomy U γ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ)

theorem normWilsonLoop4_gauge_inv {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    {x : (cubicTorus4 Ls Lt).Site} {γ : List ((cubicTorus4 Ls Lt).Link × Bool)}
    (hγ : IsLatticePath (cubicTorus4 Ls Lt) x x γ)
    (g : GaugeTransform (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    normWilsonLoop4 γ (gaugeAct g U) = normWilsonLoop4 γ U := by
  unfold normWilsonLoop4
  rw [wilsonLoop_gauge_invariant
    (fun M : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (M : Matrix (Fin N) (Fin N) ℂ) : ℂ))
    (fun A B => by
      have hmul : ∀ X Y : Matrix.specialUnitaryGroup (Fin N) ℂ,
          ((X * Y : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
            (X : Matrix (Fin N) (Fin N) ℂ) * (Y : Matrix (Fin N) (Fin N) ℂ) := fun _ _ => rfl
      have hone : ((1 : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) = 1 := rfl
      have hinv : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 := by
        rw [← hmul A⁻¹ A, inv_mul_cancel, hone]
      dsimp only
      rw [hmul (A * B) A⁻¹, hmul A B,
        Matrix.trace_mul_comm ((A : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ))
          ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ),
        ← mul_assoc, hinv, one_mul])
    g U hγ]

theorem normWilsonLoop4_norm_le_one {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt] (hN : 1 ≤ N)
    (γ : List ((cubicTorus4 Ls Lt).Link × Bool))
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    ‖normWilsonLoop4 γ U‖ ≤ 1 := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold normWilsonLoop4
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN_pos.le]
  calc (N : ℝ)⁻¹ * ‖Matrix.trace ((pathHolonomy U γ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)‖
      ≤ (N : ℝ)⁻¹ * (N : ℝ) :=
        mul_le_mul_of_nonneg_left (abs_trace_su_le _) (inv_nonneg.mpr hN_pos.le)
    _ = 1 := inv_mul_cancel₀ hN_pos.ne'

theorem norm_prod_fin_le {n : ℕ} (f : Fin n → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ i, ‖f i‖ ≤ M) :
    ‖∏ i : Fin n, f i‖ ≤ M ^ n := by
  rw [norm_prod]
  calc ∏ i : Fin n, ‖f i‖ ≤ ∏ _i : Fin n, M :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hf i)
    _ = M ^ n := by simp [Finset.prod_const]

/--
**Volume- and coupling-independent Schwinger bound:**
if `∀ i U, ‖obs i U‖ ≤ M` (`M ≥ 0`) and each `obs i` is measurable, then
`‖cubic4Schwinger Ls Lt N β n obs‖ ≤ M ^ n` for ALL `Ls, Lt ≥ 1` and `β ≥ 0`.
-/
theorem cubic4Schwinger_bound (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (h_meas : ∀ i, Measurable (obs i))
    (M : ℝ) (hM : 0 ≤ M) (hbd : ∀ i U, ‖obs i U‖ ≤ M) :
    ‖cubic4Schwinger Ls Lt N β n obs‖ ≤ M ^ n := by
  let μ := spacetimeHaarMeasure Ls Lt N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  let Z := cubic4PartitionFn Ls Lt N β
  have hZ_pos : 0 < Z := cubic4PartitionFn_pos Ls Lt N β hβ
  have hw_nonneg : ∀ U, 0 ≤ cubic4WilsonWeight Ls Lt N β U := fun U => by
    unfold cubic4WilsonWeight; exact (Real.exp_pos _).le
  have hw_int : MeasureTheory.Integrable (cubic4WilsonWeight Ls Lt N β) μ := by
    refine (MeasureTheory.integrable_const (1 : ℝ)).mono'
      (measurable_cubic4WilsonWeight Ls Lt N β).stronglyMeasurable.aestronglyMeasurable ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_of_nonneg (hw_nonneg U)]
    exact (cubic4WilsonWeight_bounds Ls Lt N β hβ U).2
  have h_prod_meas : Measurable (fun U => ∏ i : Fin n, obs i U) := by
    refine Finset.measurable_prod Finset.univ fun i _ => h_meas i
  have hf_meas : Measurable
      (fun U => (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)) :=
    h_prod_meas.mul (Complex.continuous_ofReal.measurable.comp (measurable_cubic4WilsonWeight Ls Lt N β))
  have h_pt_bound : ∀ U,
      ‖(∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)‖ ≤
        M ^ n * cubic4WilsonWeight Ls Lt N β U := by
    intro U
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_nonneg U)]
    exact mul_le_mul_of_nonneg_right (norm_prod_fin_le (fun i => obs i U) M hM (fun i => hbd i U))
      (hw_nonneg U)
  have h_int_norm : MeasureTheory.Integrable
      (fun U => ‖(∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)‖) μ := by
    refine (hw_int.const_mul (M ^ n)).mono'
      (hf_meas.stronglyMeasurable.aestronglyMeasurable.norm) ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact h_pt_bound U
  have h_int_le :
      ‖∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂μ‖ ≤
        M ^ n * Z := by
    calc ‖∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂μ‖
        ≤ ∫ U, ‖(∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)‖ ∂μ :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ U, M ^ n * cubic4WilsonWeight Ls Lt N β U ∂μ :=
            MeasureTheory.integral_mono h_int_norm (hw_int.const_mul (M ^ n)) h_pt_bound
      _ = M ^ n * Z := MeasureTheory.integral_const_mul (M ^ n) (cubic4WilsonWeight Ls Lt N β)
  unfold cubic4Schwinger
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hZ_pos.le]
  calc Z⁻¹ * ‖∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂μ‖
      ≤ Z⁻¹ * (M ^ n * Z) := mul_le_mul_of_nonneg_left h_int_le (inv_nonneg.mpr hZ_pos.le)
    _ = M ^ n := by field_simp [hZ_pos.ne']

/-- Uniform bound `‖S^{(n)}_{Ls,Lt,β}(W_{γ₁},…,W_{γₙ})‖ ≤ 1` for normalized Wilson loops. -/
theorem cubic4Schwinger_wilson_bound (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ) (loops : Fin n → List ((cubicTorus4 Ls Lt).Link × Bool)) :
    ‖cubic4Schwinger Ls Lt N β n (fun i => normWilsonLoop4 (loops i))‖ ≤ 1 := by
  have h_meas : ∀ i : Fin n, Measurable (normWilsonLoop4 (N := N) (loops i)) := by
    intro i
    unfold normWilsonLoop4
    have h_ent : ∀ j k : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (A : Matrix (Fin N) (Fin N) ℂ) j k) := fun j k =>
      (continuous_apply k).comp ((continuous_apply j).comp continuous_subtype_val)
    have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)) := by
      simp only [Matrix.trace, Matrix.diag]
      exact continuous_finset_sum Finset.univ fun j _ => h_ent j j
    exact measurable_const.mul (h_tr.measurable.comp (measurable_pathHolonomy4 Ls Lt N (loops i)))
  have h1 := cubic4Schwinger_bound Ls Lt N β hβ n (fun i => normWilsonLoop4 (loops i))
    h_meas 1 zero_le_one (fun i U => normWilsonLoop4_norm_le_one hN (loops i) U)
  simpa using h1

/--
**Subsequential thermodynamic limit (`L → ∞`)**:
for any sequence of finite-volume Schwinger values uniformly bounded by `M ^ n`
(in particular `cubic4Schwinger` along volumes `L_m → ∞`), a convergent infinite-volume
limit `S_inf` exists along a strictly increasing subsequence `φ`, preserving the bound `≤ M ^ n`.
-/
theorem cubic4Schwinger_thermodynamic_subseq (S_seq : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (n : ℕ)
    (hbd : ∀ m, ‖S_seq m‖ ≤ M ^ n) :
    ∃ (S_inf : ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (fun m => S_seq (φ m)) Filter.atTop (nhds S_inf) ∧
      ‖S_inf‖ ≤ M ^ n := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (M ^ n)) := isCompact_closedBall (0 : ℂ) (M ^ n)
  have hmem : ∀ m, S_seq m ∈ Metric.closedBall (0 : ℂ) (M ^ n) := fun m => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbd m
  obtain ⟨S_inf, hS_mem, φ, hφ_mono, hφ_lim⟩ := hK.tendsto_subseq hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hS_mem
  exact ⟨S_inf, φ, hφ_mono, hφ_lim, hS_mem⟩

/-- Permutation symmetry passes to the `L → ∞` thermodynamic limit. -/
theorem thermodynamic_limit_perm_symm {n : ℕ}
    (S_seq : ℕ → Equiv.Perm (Fin n) → ℂ) (S_inf : Equiv.Perm (Fin n) → ℂ)
    (hlim : ∀ σ, Filter.Tendsto (fun m => S_seq m σ) Filter.atTop (nhds (S_inf σ)))
    (hsymm : ∀ m σ, S_seq m σ = S_seq m 1)
    (σ : Equiv.Perm (Fin n)) :
    S_inf σ = S_inf 1 := by
  have h_eq : (fun m => S_seq m σ) = (fun m => S_seq m 1) := funext fun m => hsymm m σ
  have h1 := hlim σ
  rw [h_eq] at h1
  exact tendsto_nhds_unique h1 (hlim 1)

/-- Reflection positivity passes to the `L → ∞` thermodynamic limit. -/
theorem thermodynamic_limit_refl_pos {m : ℕ} (c : Fin m → ℂ)
    (G_seq : ℕ → Fin m → Fin m → ℂ) (G_inf : Fin m → Fin m → ℂ)
    (hlim : ∀ i j, Filter.Tendsto (fun r => G_seq r i j) Filter.atTop (nhds (G_inf i j)))
    (hrp : ∀ r, 0 ≤ (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_seq r i j).re) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_inf i j).re := by
  have hsum_lim : Filter.Tendsto
      (fun r => (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_seq r i j).re)
      Filter.atTop
      (nhds (∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) * G_inf i j).re) := by
    refine Complex.continuous_re.continuousAt.tendsto.comp ?_
    refine tendsto_finset_sum Finset.univ fun i _ => ?_
    refine tendsto_finset_sum Finset.univ fun j _ => ?_
    exact tendsto_const_nhds.mul (hlim i j)
  exact ge_of_tendsto hsum_lim (Filter.Eventually.of_forall hrp)

end CubicThermodynamicLimit

/-! ## §28.  Kogut–Susskind Yang–Mills Hamiltonian, non-commuting link algebra & Gauss law -/

section KogutSusskindYM

theorem memLp_realMul {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x, |f x| ≤ C) (ψ : MeasureTheory.Lp ℂ 2 μ) :
    MeasureTheory.MemLp (fun x => ((f x : ℝ) : ℂ) * ψ x) 2 μ := by
  have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
  have hψ_ae : MeasureTheory.AEStronglyMeasurable (⇑ψ) μ := hψ_mem.aestronglyMeasurable
  have hf_ae : MeasureTheory.AEStronglyMeasurable (fun x => ((f x : ℝ) : ℂ)) μ :=
    (Complex.continuous_ofReal.measurable.comp hf_meas).stronglyMeasurable.aestronglyMeasurable
  have h_ae : MeasureTheory.AEStronglyMeasurable (fun x => ((f x : ℝ) : ℂ) * ψ x) μ :=
    hf_ae.mul hψ_ae
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm h_ae]
  have h_int : MeasureTheory.Integrable (fun x => ‖ψ x‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hψ_ae).mp hψ_mem
  refine (h_int.const_mul (C ^ 2)).mono' (h_ae.norm.pow 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2) (sq_nonneg _)

/-- Bounded self-adjoint multiplication operator `ψ ↦ f · ψ` on `L²(μ)` for real `|f| ≤ C`. -/
noncomputable def realMulOp {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x, |f x| ≤ C) :
    MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun ψ => (memLp_realMul μ f hf_meas C hC hbd ψ).toLp
        (fun x => ((f x : ℝ) : ℂ) * ψ x)
      map_add' := fun ψ₁ ψ₂ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_realMul μ f hf_meas C hC hbd (ψ₁ + ψ₂)).coeFn_toLp
        have h2 := (memLp_realMul μ f hf_meas C hC hbd ψ₁).coeFn_toLp
        have h3 := (memLp_realMul μ f hf_meas C hC hbd ψ₂).coeFn_toLp
        have hadd1 := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
        have hadd2 := MeasureTheory.Lp.coeFn_add
          ((memLp_realMul μ f hf_meas C hC hbd ψ₁).toLp (fun x => ((f x : ℝ) : ℂ) * ψ₁ x))
          ((memLp_realMul μ f hf_meas C hC hbd ψ₂).toLp (fun x => ((f x : ℝ) : ℂ) * ψ₂ x))
        filter_upwards [h1, h2, h3, hadd1, hadd2] with x hx1 hx2 hx3 ha1 ha2
        simp only [Pi.add_apply] at ha1 ha2 ⊢
        rw [hx1, ha1, mul_add, ha2, hx2, hx3]
      map_smul' := fun c ψ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_realMul μ f hf_meas C hC hbd (c • ψ)).coeFn_toLp
        have h2 := (memLp_realMul μ f hf_meas C hC hbd ψ).coeFn_toLp
        have hsm1 := MeasureTheory.Lp.coeFn_smul c ψ
        have hsm2 := MeasureTheory.Lp.coeFn_smul c
          ((memLp_realMul μ f hf_meas C hC hbd ψ).toLp (fun x => ((f x : ℝ) : ℂ) * ψ x))
        filter_upwards [h1, h2, hsm1, hsm2] with x hx1 hx2 hs1 hs2
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul] at hs1 hs2 ⊢
        rw [hx1, hs1, hs2, hx2]
        ring }
    C
    (fun ψ => by
      let ψ' := (memLp_realMul μ f hf_meas C hC hbd ψ).toLp (fun x => ((f x : ℝ) : ℂ) * ψ x)
      change ‖ψ'‖ ≤ C * ‖ψ‖
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)), mul_pow]
      have h_inner_lhs : (⟪ψ', ψ'⟫_ℂ).re = ∫ x, ‖ψ' x‖ ^ 2 ∂μ := by
        have h_l2 : MeasureTheory.Integrable (fun x => ⟪ψ' x, ψ' x⟫_ℂ) μ :=
          MeasureTheory.L2.integrable_inner _ _
        have h_re := integral_re h_l2
        rw [MeasureTheory.L2.inner_def]
        change RCLike.re (∫ x, ⟪ψ' x, ψ' x⟫_ℂ ∂μ) = _
        rw [← h_re]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change (⟪ψ' x, ψ' x⟫_ℂ).re = ‖ψ' x‖ ^ 2
        rw [inner_self_eq_norm_sq_to_K]
        simp [pow_two]
      have h_inner_rhs : (⟪ψ, ψ⟫_ℂ).re = ∫ x, ‖ψ x‖ ^ 2 ∂μ := by
        have h_l2 : MeasureTheory.Integrable (fun x => ⟪ψ x, ψ x⟫_ℂ) μ :=
          MeasureTheory.L2.integrable_inner _ _
        have h_re := integral_re h_l2
        rw [MeasureTheory.L2.inner_def]
        change RCLike.re (∫ x, ⟪ψ x, ψ x⟫_ℂ ∂μ) = _
        rw [← h_re]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change (⟪ψ x, ψ x⟫_ℂ).re = ‖ψ x‖ ^ 2
        rw [inner_self_eq_norm_sq_to_K]
        simp [pow_two]
      have h_norm_sq : ∀ (φ : MeasureTheory.Lp ℂ 2 μ), ‖φ‖ ^ 2 = (⟪φ, φ⟫_ℂ).re := by
        intro φ
        rw [inner_self_eq_norm_sq_to_K]
        simp [pow_two]
      rw [h_norm_sq ψ', h_norm_sq ψ, h_inner_lhs, h_inner_rhs, ← MeasureTheory.integral_const_mul]
      have hcoe := (memLp_realMul μ f hf_meas C hC hbd ψ).coeFn_toLp
      have hψ_ae : MeasureTheory.AEStronglyMeasurable (⇑ψ) μ :=
        (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable
      have h_int1 : MeasureTheory.Integrable (fun x => ‖ψ' x‖ ^ 2) μ :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm
          (MeasureTheory.Lp.memLp ψ').aestronglyMeasurable).mp (MeasureTheory.Lp.memLp ψ')
      have h_int2 : MeasureTheory.Integrable (fun x => C ^ 2 * ‖ψ x‖ ^ 2) μ :=
        ((MeasureTheory.memLp_two_iff_integrable_sq_norm hψ_ae).mp
          (MeasureTheory.Lp.memLp ψ)).const_mul (C ^ 2)
      refine MeasureTheory.integral_mono_ae h_int1 h_int2 ?_
      filter_upwards [hcoe] with x hx
      rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2) (sq_nonneg _))

theorem realMulOp_apply_ae {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ x, |f x| ≤ C)
    (ψ : MeasureTheory.Lp ℂ 2 μ) :
    ⇑(realMulOp μ f hf_meas C hC hbd ψ) =ᵐ[μ] fun x => ((f x : ℝ) : ℂ) * ψ x :=
  (memLp_realMul μ f hf_meas C hC hbd ψ).coeFn_toLp

theorem realMulOp_sa {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ x, |f x| ≤ C)
    (u v : MeasureTheory.Lp ℂ 2 μ) :
    ⟪realMulOp μ f hf_meas C hC hbd u, v⟫_ℂ =
      ⟪u, realMulOp μ f hf_meas C hC hbd v⟫_ℂ := by
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 := realMulOp_apply_ae μ f hf_meas C hC hbd u
  have h2 := realMulOp_apply_ae μ f hf_meas C hC hbd v
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2, hcinner, hcinner, map_mul, Complex.conj_ofReal]
  ring

theorem realMulOp_nonneg {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ x, |f x| ≤ C)
    (hf_pos : ∀ x, 0 ≤ f x) (ψ : MeasureTheory.Lp ℂ 2 μ) :
    0 ≤ (⟪ψ, realMulOp μ f hf_meas C hC hbd ψ⟫_ℂ).re := by
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  let opψ := realMulOp μ f hf_meas C hC hbd ψ
  have h_l2 : MeasureTheory.Integrable (fun x => ⟪ψ x, opψ x⟫_ℂ) μ :=
    MeasureTheory.L2.integrable_inner _ _
  have h_re := integral_re h_l2
  rw [MeasureTheory.L2.inner_def]
  change 0 ≤ RCLike.re (∫ x, ⟪ψ x, opψ x⟫_ℂ ∂μ)
  rw [← h_re]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  have hcoe := realMulOp_apply_ae μ f hf_meas C hC hbd ψ
  filter_upwards [hcoe] with x hx
  change 0 ≤ (⟪ψ x, opψ x⟫_ℂ).re
  have h_eq : opψ x = ((f x : ℝ) : ℂ) * ψ x := hx
  rw [h_eq, hcinner]
  have hmul : starRingEnd ℂ (ψ x) * (((f x : ℝ) : ℂ) * ψ x) =
      ((f x : ℝ) : ℂ) * (starRingEnd ℂ (ψ x) * ψ x) := by ring
  rw [hmul, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (hf_pos x) (sq_nonneg _)

/-- Elementary Kogut–Susskind magnetic plaquette operator `ψ ↦ (1 - (1/N) Re Tr U_□) ψ`. -/
noncomputable def ksPlaquetteOp (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (p : LatticePlaquette (cubicTorus3 L)) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  realMulOp (latticeHaarMeasure L N) (wilsonPlaquetteTerm p)
    (measurable_wilsonPlaquetteTerm L N p) 2 (by norm_num) (fun U => by
      have hb := wilsonPlaquetteTerm_bounds p U
      rw [abs_of_nonneg hb.1]
      exact hb.2)

theorem ksPlaquetteOp_gauge_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (p : LatticePlaquette (cubicTorus3 L))
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    lieBracketCLM (cubicGaugeRep L N g) (ksPlaquetteOp L N p) = 0 := by
  unfold lieBracketCLM
  ext1 ψ
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, sub_eq_zero]
  apply MeasureTheory.Lp.ext
  let μ := latticeHaarMeasure L N
  let eg := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmpg : MeasureTheory.MeasurePreserving eg μ μ :=
    ⟨eg.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  have hL1 := cubicGaugeRep_apply_ae L N g (ksPlaquetteOp L N p ψ)
  have hL2 : (fun U => (ksPlaquetteOp L N p ψ) (gaugeAct (fun x => (g x)⁻¹) U)) =ᵐ[μ]
      (fun U => ((wilsonPlaquetteTerm p (gaugeAct (fun x => (g x)⁻¹) U) : ℝ) : ℂ) *
        ψ (gaugeAct (fun x => (g x)⁻¹) U)) :=
    ae_comp_measurePreserving hmpg (realMulOp_apply_ae μ _ _ _ _ _ ψ)
  have hR1 := realMulOp_apply_ae μ (wilsonPlaquetteTerm p)
    (measurable_wilsonPlaquetteTerm L N p) 2 (by norm_num) (fun U => by
      have hb := wilsonPlaquetteTerm_bounds p U
      rw [abs_of_nonneg hb.1]; exact hb.2) (cubicGaugeRep L N g ψ)
  have hR2 := cubicGaugeRep_apply_ae L N g ψ
  filter_upwards [hL1, hL2, hR1, hR2] with U hl1 hl2 hr1 hr2
  change ⇑(cubicGaugeRep L N g (ksPlaquetteOp L N p ψ)) U =
    ⇑(ksPlaquetteOp L N p (cubicGaugeRep L N g ψ)) U
  change ⇑(ksPlaquetteOp L N p (cubicGaugeRep L N g ψ)) U = _ at hr1
  rw [hl1, hl2, wilsonPlaquetteTerm_gauge_inv, hr1, hr2]

/--
Full Kogut–Susskind magnetic plaquette Hamiltonian
`H_B = (1 / (g² a)) ∑_□ (1 - (1/N) Re Tr U_□)` on `L²(SU(N)^{3L³}, dμ_Haar)`.
-/
noncomputable def ksMagneticH (L N : ℕ) [NeZero L] (g_sq a : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  ((1 / (g_sq * a) : ℝ) : ℂ) •
    ((cubicPlaquettes L).map (ksPlaquetteOp L N)).sum

theorem ksMagneticH_sa (L N : ℕ) [NeZero L] (g_sq a : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (x y : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪ksMagneticH L N g_sq a x, y⟫_ℂ = ⟪x, ksMagneticH L N g_sq a y⟫_ℂ := by
  have hsum_sa : ∀ (ps : List (LatticePlaquette (cubicTorus3 L))),
      ⟪((ps.map (ksPlaquetteOp L N)).sum) x, y⟫_ℂ =
        ⟪x, ((ps.map (ksPlaquetteOp L N)).sum) y⟫_ℂ := by
    intro ps
    induction ps with
    | nil =>
      change ⟪(0 : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _) x, y⟫_ℂ =
        ⟪x, (0 : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _) y⟫_ℂ
      simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, ContinuousLinearMap.add_apply,
        inner_add_left, inner_add_right]
      dsimp [ksPlaquetteOp]
      rw [realMulOp_sa, ih]
  change ⟪(((1 / (g_sq * a) : ℝ) : ℂ) •
      ((cubicPlaquettes L).map (ksPlaquetteOp L N)).sum) x, y⟫_ℂ =
    ⟪x, (((1 / (g_sq * a) : ℝ) : ℂ) •
      ((cubicPlaquettes L).map (ksPlaquetteOp L N)).sum) y⟫_ℂ
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, hsum_sa]

theorem ksMagneticH_nonneg (L N : ℕ) [NeZero L] (g_sq a : ℝ)
    (hg : 0 < g_sq) (ha : 0 < a)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, ksMagneticH L N g_sq a ψ⟫_ℂ).re := by
  have hsum_nonneg : ∀ (ps : List (LatticePlaquette (cubicTorus3 L))),
      0 ≤ (⟪ψ, ((ps.map (ksPlaquetteOp L N)).sum) ψ⟫_ℂ).re := by
    intro ps
    induction ps with
    | nil =>
      change 0 ≤ (⟪ψ, (0 : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _) ψ⟫_ℂ).re
      simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, ContinuousLinearMap.add_apply,
        inner_add_right, Complex.add_re]
      exact add_nonneg (realMulOp_nonneg _ _ _ _ _ _ (fun U => (wilsonPlaquetteTerm_bounds p U).1) ψ) ih
  change 0 ≤ (⟪ψ, (((1 / (g_sq * a) : ℝ) : ℂ) •
    ((cubicPlaquettes L).map (ksPlaquetteOp L N)).sum) ψ⟫_ℂ).re
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) (hsum_nonneg (cubicPlaquettes L))

theorem ksMagneticH_gauge_inv (L N : ℕ) [NeZero L] (g_sq a : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    lieBracketCLM (cubicGaugeRep L N g) (ksMagneticH L N g_sq a) = 0 := by
  have hsum_comm : ∀ (ps : List (LatticePlaquette (cubicTorus3 L))),
      lieBracketCLM (cubicGaugeRep L N g) ((ps.map (ksPlaquetteOp L N)).sum) = 0 := by
    intro ps
    induction ps with
    | nil =>
      unfold lieBracketCLM
      simp
    | cons p ps ih =>
      have hp := ksPlaquetteOp_gauge_inv L N p g
      unfold lieBracketCLM at hp ih ⊢
      ext1 ψ
      have hp' := congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ) hp
      have ih' := congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ) ih
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.zero_apply, sub_eq_zero] at hp' ih' ⊢
      simp only [List.map_cons, List.sum_cons, ContinuousLinearMap.add_apply, map_add,
        hp', ih', sub_self]
  have hc := hsum_comm (cubicPlaquettes L)
  unfold lieBracketCLM at hc
  unfold lieBracketCLM ksMagneticH
  ext1 ψ
  have hc' := congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ) hc
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, map_smul, sub_eq_zero] at hc' ⊢
  rw [hc']

/-- Left multiplication shift along a single spatial link `e` by `u ∈ SU(N)`. -/
def linkLeftShift (L N : ℕ) [NeZero L]
    (e : (cubicTorus3 L).Link) (u : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e' => if e' = e then u * U e else U e'

def linkLeftShiftEquiv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (u : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := linkLeftShift L N e u
  invFun := linkLeftShift L N e u⁻¹
  left_inv U := by
    funext e'
    by_cases he : e' = e <;> simp [linkLeftShift, he, ← mul_assoc]
  right_inv U := by
    funext e'
    by_cases he : e' = e <;> simp [linkLeftShift, he, ← mul_assoc]
  measurable_toFun := by
    change Measurable (fun U : (cubicTorus3 L).Link → _ => linkLeftShift L N e u U)
    refine measurable_pi_iff.mpr fun e' => ?_
    by_cases he : e' = e
    · simp only [linkLeftShift, he, ↓reduceIte]
      exact (continuous_mul_left u).measurable.comp (measurable_pi_apply e)
    · simp only [linkLeftShift, he, ↓reduceIte]
      exact measurable_pi_apply e'
  measurable_invFun := by
    change Measurable (fun U : (cubicTorus3 L).Link → _ => linkLeftShift L N e u⁻¹ U)
    refine measurable_pi_iff.mpr fun e' => ?_
    by_cases he : e' = e
    · simp only [linkLeftShift, he, ↓reduceIte]
      exact (continuous_mul_left u⁻¹).measurable.comp (measurable_pi_apply e)
    · simp only [linkLeftShift, he, ↓reduceIte]
      exact measurable_pi_apply e'

theorem linkLeftShiftEquiv_mp (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (u : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MeasureTheory.MeasurePreserving (linkLeftShiftEquiv L N e u)
      (latticeHaarMeasure L N) (latticeHaarMeasure L N) := by
  haveI := suHaar_prob N
  haveI := latticeHaarMeasure_prob L N
  let φ : (cubicTorus3 L).Link →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun e' w => if e' = e then u * w else w
  have hφ_meas : ∀ e', Measurable (φ e') := fun e' => by
    by_cases he : e' = e
    · simp only [φ, he, ↓reduceIte]; exact (continuous_mul_left u).measurable
    · simp only [φ, he, ↓reduceIte]; exact measurable_id
  have hφ_inv : ∀ e' (s : Set (Matrix.specialUnitaryGroup (Fin N) ℂ)),
      MeasurableSet s → suHaar N (φ e' ⁻¹' s) = suHaar N s := by
    intro e' s hs
    by_cases he : e' = e
    · simp only [φ, he, ↓reduceIte]
      rw [← MeasureTheory.Measure.map_apply (continuous_mul_left u).measurable hs,
        suHaar_map_mul_left]
    · simp only [φ, he, ↓reduceIte]; rfl
  let F : ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) →
      ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun U e' => φ e' (U e')
  have hF_eq : F = ⇑(linkLeftShiftEquiv L N e u) := by
    funext U e'
    by_cases he : e' = e
    · subst he; simp [F, φ, linkLeftShiftEquiv, linkLeftShift]
    · simp [F, φ, linkLeftShiftEquiv, linkLeftShift, he]
  have hF_meas : Measurable F :=
    measurable_pi_iff.mpr fun e' => (hφ_meas e').comp (measurable_pi_apply e')
  refine ⟨(linkLeftShiftEquiv L N e u).measurable, ?_⟩
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  rw [← hF_eq]
  change MeasureTheory.Measure.map F μ_pi = MeasureTheory.Measure.pi (fun _ => suHaar N)
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hF_meas (MeasurableSet.univ_pi hs)]
  have hpre : F ⁻¹' Set.pi Set.univ s = Set.pi Set.univ (fun e' => φ e' ⁻¹' s e') := by
    ext U
    simp [F]
  rw [hpre, MeasureTheory.Measure.pi_pi (fun _ => suHaar N)]
  exact Finset.prod_congr rfl fun e' _ => hφ_inv e' (s e') (hs e')

/-- Unitary electric link-shift operator `(U_{e,v} ψ)(U) = ψ(linkLeftShift e v⁻¹ U)`. -/
noncomputable def ksLinkShiftOp (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  let μ := latticeHaarMeasure L N
  let eqv := linkLeftShiftEquiv L N e v⁻¹
  let hmp := linkLeftShiftEquiv_mp L N e v⁻¹
  LinearMap.mkContinuous
    { toFun := fun ψ => (memLp_comp_measurePreserving μ eqv hmp ψ).toLp (fun U => ψ (eqv U))
      map_add' := fun ψ₁ ψ₂ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving μ eqv hmp (ψ₁ + ψ₂)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving μ eqv hmp ψ₁).coeFn_toLp
        have h3 := (memLp_comp_measurePreserving μ eqv hmp ψ₂).coeFn_toLp
        have hadd1 := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
        have hadd2 := MeasureTheory.Lp.coeFn_add
          ((memLp_comp_measurePreserving μ eqv hmp ψ₁).toLp (fun U => ψ₁ (eqv U)))
          ((memLp_comp_measurePreserving μ eqv hmp ψ₂).toLp (fun U => ψ₂ (eqv U)))
        filter_upwards [h1, h2, h3, ae_comp_measurePreserving hmp hadd1, hadd2] with U hu1 hu2 hu3 ha1 ha2
        simp only [Pi.add_apply] at ha1 ha2 ⊢
        rw [hu1, ha1, ha2, hu2, hu3]
      map_smul' := fun c ψ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving μ eqv hmp (c • ψ)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving μ eqv hmp ψ).coeFn_toLp
        have hsm1 := MeasureTheory.Lp.coeFn_smul c ψ
        have hsm2 := MeasureTheory.Lp.coeFn_smul c
          ((memLp_comp_measurePreserving μ eqv hmp ψ).toLp (fun U => ψ (eqv U)))
        filter_upwards [h1, h2, ae_comp_measurePreserving hmp hsm1, hsm2] with U hu1 hu2 hs1 hs2
        simp only [Pi.smul_apply, RingHom.id_apply] at hs1 hs2 ⊢
        rw [hu1, hs1, hs2, hu2] }
    1
    (fun ψ => by
      let ψ' := (memLp_comp_measurePreserving μ eqv hmp ψ).toLp (fun U => ψ (eqv U))
      have h_norm_sq : ‖ψ'‖ ^ 2 = ‖ψ‖ ^ 2 := by
        have h_inner : ⟪ψ', ψ'⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
          rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
          have hcoe := (memLp_comp_measurePreserving μ eqv hmp ψ).coeFn_toLp
          calc ∫ U, ⟪ψ' U, ψ' U⟫_ℂ ∂μ
              = ∫ U, ⟪ψ (eqv U), ψ (eqv U)⟫_ℂ ∂μ := by
                  refine MeasureTheory.integral_congr_ae ?_
                  filter_upwards [hcoe] with U hU
                  rw [hU]
            _ = ∫ U, ⟪ψ U, ψ U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪ψ U, ψ U⟫_ℂ)
        have hre := congrArg Complex.re h_inner
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
        simpa [pow_two] using hre
      change ‖ψ'‖ ≤ 1 * ‖ψ‖
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), one_mul, h_norm_sq])

theorem ksLinkShiftOp_apply_ae (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⇑(ksLinkShiftOp L N e v ψ) =ᵐ[latticeHaarMeasure L N]
      fun U => ψ (linkLeftShift L N e v⁻¹ U) :=
  (memLp_comp_measurePreserving (latticeHaarMeasure L N)
    (linkLeftShiftEquiv L N e v⁻¹) (linkLeftShiftEquiv_mp L N e v⁻¹) ψ).coeFn_toLp

theorem ksLinkShiftOp_unitary (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (ψ₁ ψ₂ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪ksLinkShiftOp L N e v ψ₁, ksLinkShiftOp L N e v ψ₂⟫_ℂ = ⟪ψ₁, ψ₂⟫_ℂ := by
  let μ := latticeHaarMeasure L N
  let eqv := linkLeftShiftEquiv L N e v⁻¹
  let hmp := linkLeftShiftEquiv_mp L N e v⁻¹
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc ∫ U, ⟪(ksLinkShiftOp L N e v ψ₁) U, (ksLinkShiftOp L N e v ψ₂) U⟫_ℂ ∂μ
      = ∫ U, ⟪ψ₁ (eqv U), ψ₂ (eqv U)⟫_ℂ ∂μ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [ksLinkShiftOp_apply_ae L N e v ψ₁,
            ksLinkShiftOp_apply_ae L N e v ψ₂] with U hu1 hu2
          rw [hu1, hu2]
          rfl
    _ = ∫ U, ⟪ψ₁ U, ψ₂ U⟫_ℂ ∂μ := hmp.integral_comp' (fun U => ⟪ψ₁ U, ψ₂ U⟫_ℂ)

theorem ksLinkShiftOp_adj (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (x y : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪ksLinkShiftOp L N e v x, y⟫_ℂ = ⟪x, ksLinkShiftOp L N e v⁻¹ y⟫_ℂ := by
  calc ⟪ksLinkShiftOp L N e v x, y⟫_ℂ
      = ⟪ksLinkShiftOp L N e v⁻¹ (ksLinkShiftOp L N e v x),
          ksLinkShiftOp L N e v⁻¹ y⟫_ℂ :=
          (ksLinkShiftOp_unitary L N e v⁻¹ _ _).symm
    _ = ⟪x, ksLinkShiftOp L N e v⁻¹ y⟫_ℂ := by
          congr 1
          apply MeasureTheory.Lp.ext
          let μ := latticeHaarMeasure L N
          let eqv := linkLeftShiftEquiv L N e v
          let hmp := linkLeftShiftEquiv_mp L N e v
          have h1 := ksLinkShiftOp_apply_ae L N e v⁻¹ (ksLinkShiftOp L N e v x)
          have h2 : (fun U => (ksLinkShiftOp L N e v x) (linkLeftShift L N e v U)) =ᵐ[μ]
              (fun U => x (linkLeftShift L N e v⁻¹ (linkLeftShift L N e v U))) := by
            simpa [eqv] using ae_comp_measurePreserving hmp (ksLinkShiftOp_apply_ae L N e v x)
          filter_upwards [h1, h2] with U hu1 hu2
          rw [inv_inv] at hu1
          rw [hu1, hu2]
          congr 1
          funext e'
          by_cases he : e' = e <;> simp [linkLeftShift, he, ← mul_assoc]

/--
Kogut–Susskind electric link Laplacian `Δ_{e, v} = 2 I - U_{e,v} - U_{e,v⁻¹} = (I - U_{e,v})* (I - U_{e,v})`
on `L²(SU(N)^{3L³}, dμ_Haar)`.
-/
noncomputable def ksElectricLaplacian (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  (2 : ℂ) • ContinuousLinearMap.id ℂ (HaarGaugeSpace (latticeHaarMeasure L N)) -
    ksLinkShiftOp L N e v - ksLinkShiftOp L N e v⁻¹

theorem ksElectricLaplacian_sa (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (x y : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪ksElectricLaplacian L N e v x, y⟫_ℂ = ⟪x, ksElectricLaplacian L N e v y⟫_ℂ := by
  simp only [ksElectricLaplacian, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofNat]
  rw [ksLinkShiftOp_adj L N e v x y, ksLinkShiftOp_adj L N e v⁻¹ x y, inv_inv]
  ring

theorem ksElectricLaplacian_nonneg (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) (v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, ksElectricLaplacian L N e v ψ⟫_ℂ).re := by
  let U := ksLinkShiftOp L N e v
  have h_id : ⟪ψ, ksElectricLaplacian L N e v ψ⟫_ℂ = ⟪ψ - U ψ, ψ - U ψ⟫_ℂ := by
    simp only [ksElectricLaplacian, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_right, inner_smul_right, inner_sub_left]
    rw [← ksLinkShiftOp_adj L N e v ψ ψ, ksLinkShiftOp_unitary L N e v ψ ψ]
    change 2 * ⟪ψ, ψ⟫_ℂ - ⟪ψ, U ψ⟫_ℂ - ⟪U ψ, ψ⟫_ℂ =
      ⟪ψ, ψ⟫_ℂ - ⟪U ψ, ψ⟫_ℂ - (⟪ψ, U ψ⟫_ℂ - ⟪ψ, ψ⟫_ℂ)
    ring
  rw [h_id, inner_self_eq_norm_sq_to_K]
  simp [pow_two]
  exact mul_self_nonneg _

theorem measurable_ksLinkTrace (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) :
    Measurable (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      (Matrix.trace ((U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)).re) := by
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  exact h_tr.measurable.comp (measurable_gaugeField_eval L N e)

/-- Real link trace observable `ψ ↦ (Re Tr U_e) · ψ`. -/
noncomputable def ksLinkTraceOp (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  realMulOp (latticeHaarMeasure L N)
    (fun U => (Matrix.trace ((U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re)
    (measurable_ksLinkTrace L N e)
    (N : ℝ) (Nat.cast_nonneg N) (fun U => abs_re_trace_su_le (U e))

/-- Canonical non-central `SU(N)` element `diag(-1, -1, 1, …, 1)` for `N ≥ 2`. -/
def suFlip2 (N : ℕ) (hN : 2 ≤ N) : Matrix.specialUnitaryGroup (Fin N) ℂ :=
  let d : Fin N → ℂ := fun i => if (i : ℕ) < 2 then -1 else 1
  have hU : star (Matrix.diagonal d) * Matrix.diagonal d = 1 ∧
      Matrix.diagonal d * star (Matrix.diagonal d) = 1 := by
    constructor <;>
    · ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply_eq,
          Matrix.one_apply_eq]
        rw [Finset.sum_eq_single i]
        · by_cases hi : (i : ℕ) < 2 <;> simp [d, hi]
        · intro k _ hki
          simp [Matrix.diagonal_apply_ne _ hki.symm, Matrix.diagonal_apply_ne _ hki]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      · simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_ne hij]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hki : k = i
        · subst hki
          simp [Matrix.diagonal_apply, hij, Ne.symm hij]
        · simp [Matrix.diagonal_apply, hki, Ne.symm hki]
  have hdet : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal]
    let i0 : Fin N := ⟨0, by omega⟩
    let i1 : Fin N := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by
      intro h
      have := congrArg Fin.val h
      norm_num [i0, i1] at this
    rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i0)]
    have hi1_mem : i1 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase i0) d hi1_mem]
    have h_rest : ∏ x ∈ (Finset.univ.erase i0).erase i1, d x = 1 := by
      refine Finset.prod_eq_one fun x hx => ?_
      have hx1 : x ≠ i1 := (Finset.mem_erase.mp hx).1
      have hx0 : x ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hge2 : ¬ (x : ℕ) < 2 := by
        intro hlt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h0 | h1
        · exact hx0 (Fin.ext (Nat.lt_one_iff.mp h0))
        · exact hx1 (Fin.ext h1)
      simp [d, hge2]
    have hd0 : d i0 = -1 := by simp [d, i0]
    have hd1 : d i1 = -1 := by simp [d, i1]
    rw [hd0, hd1, h_rest]
    ring
  ⟨Matrix.diagonal d, Unitary.mem_iff.mpr hU, hdet⟩

/--
**Non-commuting canonical electric–link bracket:**
for any `N ≥ 2` and link `e` on `cubicTorus3 L`, the electric shift operator
`ksLinkShiftOp L N e (suFlip2 N hN)` does NOT commute with `ksLinkTraceOp L N e`.
-/
theorem ks_electric_link_noncommute (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus3 L).Link) :
    lieBracketCLM (ksLinkShiftOp L N e (suFlip2 N hN)) (ksLinkTraceOp L N e) ≠ 0 := by
  intro h0
  let μ := latticeHaarMeasure L N
  haveI := suHaar_prob N
  haveI := latticeHaarMeasure_prob L N
  haveI : MeasureTheory.Measure.IsHaarMeasure (suHaar N) :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure ⊤
  let oneLp : HaarGaugeSpace μ :=
    MeasureTheory.indicatorConstLp (2 : ENNReal) MeasurableSet.univ
      (MeasureTheory.measure_ne_top μ Set.univ) (1 : ℂ)
  have hone_ae : ⇑oneLp =ᵐ[μ] fun _ => (1 : ℂ) := by
    have h := MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
      (μ := μ) (s := Set.univ) (hs := MeasurableSet.univ)
      (hμs := MeasureTheory.measure_ne_top μ Set.univ) (c := (1 : ℂ))
    filter_upwards [h] with U hU
    simpa [oneLp] using hU
  have hcomm := congrArg (fun f : HaarGaugeSpace μ →L[ℂ] HaarGaugeSpace μ => f oneLp) h0
  dsimp only [lieBracketCLM] at hcomm
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, sub_eq_zero] at hcomm
  let v := suFlip2 N hN
  let eqv := linkLeftShiftEquiv L N e v⁻¹
  let hmp := linkLeftShiftEquiv_mp L N e v⁻¹
  let trFn : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ :=
    fun U => (Matrix.trace ((U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re
  have h_tr_ae : ∀ (ψ : HaarGaugeSpace μ),
      ⇑(ksLinkTraceOp L N e ψ) =ᵐ[μ] fun U => ((trFn U : ℝ) : ℂ) * ψ U :=
    fun ψ => realMulOp_apply_ae μ trFn (measurable_ksLinkTrace L N e)
      (N : ℝ) (Nat.cast_nonneg N) (fun U => abs_re_trace_su_le (U e)) ψ
  have hL1 := ksLinkShiftOp_apply_ae L N e v (ksLinkTraceOp L N e oneLp)
  have hL2 := ae_comp_measurePreserving hmp (h_tr_ae oneLp)
  have hL3 := ae_comp_measurePreserving hmp hone_ae
  have hR1 := h_tr_ae (ksLinkShiftOp L N e v oneLp)
  have hR2 := ksLinkShiftOp_apply_ae L N e v oneLp
  have h_ae_diff : (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      ((Matrix.trace ((v⁻¹ * U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)).re : ℂ) -
      ((Matrix.trace ((U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)).re : ℂ)) =ᵐ[μ] 0 := by
    have h_eq := MeasureTheory.Lp.ext_iff.mp hcomm
    filter_upwards [h_eq, hL1, hL2, hL3, hR1, hR2, hone_ae] with U hU hl1 hl2 hl3 hr1 hr2 h_one
    change ⇑((ksLinkShiftOp L N e v) ((ksLinkTraceOp L N e) oneLp)) U =
      ⇑((ksLinkTraceOp L N e) ((ksLinkShiftOp L N e v) oneLp)) U at hU
    have hl2' : ⇑((ksLinkTraceOp L N e) oneLp) (linkLeftShift L N e v⁻¹ U) =
        ((trFn (linkLeftShift L N e v⁻¹ U) : ℝ) : ℂ) *
          ⇑oneLp (linkLeftShift L N e v⁻¹ U) := by
      simpa [eqv] using hl2
    have hl3' : ⇑oneLp (linkLeftShift L N e v⁻¹ U) = 1 := by simpa [eqv] using hl3
    have h_tr_shift : trFn (linkLeftShift L N e v⁻¹ U) =
        (Matrix.trace ((v⁻¹ * U e : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)).re := by
      simp [trFn, linkLeftShift]
    rw [hl1, hl2', hl3', mul_one, h_tr_shift, hr1, hr2, hl3', mul_one] at hU
    change _ - _ = (0 : ℂ)
    rw [hU, sub_self]
  let g_su : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun A =>
    (Matrix.trace ((v⁻¹ * A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re -
    (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re
  have hg_cont : Continuous g_su := by
    have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
      (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
    have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
      simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
      exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
    exact (h_tr.comp (continuous_mul_left v⁻¹)).sub h_tr
  let S_open : Set (Matrix.specialUnitaryGroup (Fin N) ℂ) := { A | g_su A ≠ 0 }
  have hS_open : IsOpen S_open := isOpen_ne.preimage hg_cont
  have h1_mem : (1 : Matrix.specialUnitaryGroup (Fin N) ℂ) ∈ S_open := by
    change g_su 1 ≠ 0
    have hdiff : g_su 1 =
        (Matrix.trace ((v⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)).re - (N : ℝ) := by
      simp [g_su]
    have h_le : (Matrix.trace ((v⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)).re ≤ (N : ℝ) - 4 := by
      have hv_inv : (v⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) = v := by
        apply Subtype.ext
        have h_mul : (v : Matrix (Fin N) (Fin N) ℂ) * (v : Matrix (Fin N) (Fin N) ℂ) = 1 := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp only [v, suFlip2, Matrix.mul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
            rw [Finset.sum_eq_single i]
            · by_cases hi : (i : ℕ) < 2 <;> simp [hi]
            · intro k _ hki
              simp [Matrix.diagonal_apply_ne _ hki.symm, Matrix.diagonal_apply_ne _ hki]
            · intro hi; exact absurd (Finset.mem_univ i) hi
          · simp only [v, suFlip2, Matrix.mul_apply, Matrix.one_apply_ne hij]
            refine Finset.sum_eq_zero fun k _ => ?_
            by_cases hki : k = i
            · subst hki
              simp [Matrix.diagonal_apply, hij]
            · simp [Matrix.diagonal_apply, Ne.symm hki]
        have hv_eq : (v : Matrix (Fin N) (Fin N) ℂ) = (v⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) := by
          have := congrArg (fun M : Matrix.specialUnitaryGroup (Fin N) ℂ => (M : Matrix (Fin N) (Fin N) ℂ))
            (inv_eq_of_mul_eq_one_left (Subtype.ext h_mul))
          exact this.symm
        exact hv_eq.symm
      rw [hv_inv]
      simp only [v, suFlip2, Matrix.trace, Matrix.diag, Matrix.diagonal_apply_eq, Complex.re_sum]
      let i0 : Fin N := ⟨0, by omega⟩
      let i1 : Fin N := ⟨1, by omega⟩
      have h01 : i0 ≠ i1 := by
        intro h; have := congrArg Fin.val h; norm_num [i0, i1] at this
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)]
      have hi1_mem : i1 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩
      rw [← Finset.add_sum_erase (Finset.univ.erase i0) _ hi1_mem]
      have h0 : ((if (i0 : ℕ) < 2 then (-1 : ℂ) else 1)).re = -1 := by simp [i0]
      have h1 : ((if (i1 : ℕ) < 2 then (-1 : ℂ) else 1)).re = -1 := by simp [i1]
      have h_rest : ∑ x ∈ (Finset.univ.erase i0).erase i1,
          ((if (x : ℕ) < 2 then (-1 : ℂ) else 1)).re ≤ ((N : ℝ) - 2) := by
        calc ∑ x ∈ (Finset.univ.erase i0).erase i1,
              ((if (x : ℕ) < 2 then (-1 : ℂ) else 1)).re
            ≤ ∑ _x ∈ (Finset.univ.erase i0).erase i1, (1 : ℝ) := by
              refine Finset.sum_le_sum fun x _ => ?_
              by_cases hx : (x : ℕ) < 2 <;> simp [hx]
          _ = (((Finset.univ.erase i0).erase i1).card : ℝ) := by simp
          _ = (N : ℝ) - 2 := by
              have hc1 : ((Finset.univ.erase i0).erase i1).card = N - 2 := by
                rw [Finset.card_erase_of_mem hi1_mem, Finset.card_erase_of_mem (Finset.mem_univ i0),
                  Finset.card_univ, Fintype.card_fin]
                omega
              rw [hc1, Nat.cast_sub hN]
              norm_num
      linarith
    rw [hdiff]
    linarith
  have hS_pos : 0 < suHaar N S_open :=
    hS_open.measure_pos (suHaar N) ⟨1, h1_mem⟩
  have h_prod_pos : 0 < μ { U | U e ∈ S_open } := by
    let T_set : (cubicTorus3 L).Link → Set (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
      Function.update (fun _ => Set.univ) e S_open
    have h_eq_pi : { U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) |
        U e ∈ S_open } = Set.pi Set.univ T_set := by
      ext U
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left, T_set]
      constructor
      · intro h e'
        by_cases he : e' = e
        · subst he; simpa [Function.update_self] using h
        · simp [Function.update_of_ne he]
      · intro h
        simpa [Function.update_self] using h e
    have h_pi_val : μ (Set.pi Set.univ T_set) = ∏ e', suHaar N (T_set e') := by
      change (MeasureTheory.Measure.pi (fun _ => suHaar N)) (Set.pi Set.univ T_set) = _
      exact MeasureTheory.Measure.pi_pi (fun _ => suHaar N) T_set
    have h_prod_eq : ∏ e', suHaar N (T_set e') = suHaar N S_open := by
      rw [← Finset.mul_prod_erase Finset.univ (fun e' => suHaar N (T_set e')) (Finset.mem_univ e)]
      have h_other : ∏ e' ∈ Finset.univ.erase e, suHaar N (T_set e') = 1 := by
        refine Finset.prod_eq_one fun e' he' => ?_
        have hne : e' ≠ e := (Finset.mem_erase.mp he').1
        simp [T_set, Function.update_of_ne hne, MeasureTheory.measure_univ]
      rw [h_other, mul_one]
      simp [T_set, Function.update_self]
    rw [h_eq_pi, h_pi_val, h_prod_eq]
    exact hS_pos
  have h_zero : μ { U | U e ∈ S_open } = 0 := by
    refine MeasureTheory.measure_mono_null (fun U hU => ?_) h_ae_diff
    intro h0_pt
    have h0_re := congrArg Complex.re h0_pt
    change g_su (U e) = 0 at h0_re
    exact hU h0_re
  exact lt_irrefl 0 (h_prod_pos.trans_eq h_zero)

/--
Full gauge-invariant Kogut–Susskind Hamiltonian combining the magnetic plaquette
operator `ksMagneticH` and the Wilson transfer Hamiltonian `transferHamiltonian`.
-/
noncomputable def ksGaugeInvariantH (L N : ℕ) [NeZero L] (β g_sq a : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  ksMagneticH L N g_sq a + transferHamiltonian (cubicLatticeGaugeSetup L N β hβ)

theorem ksGaugeInvariantH_sa (L N : ℕ) [NeZero L] (β g_sq a : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (x y : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪ksGaugeInvariantH L N β g_sq a hβ x, y⟫_ℂ =
      ⟪x, ksGaugeInvariantH L N β g_sq a hβ y⟫_ℂ := by
  simp only [ksGaugeInvariantH, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
    ksMagneticH_sa, transferHamiltonian_sa]

theorem ksGaugeInvariantH_nonneg (L N : ℕ) [NeZero L] (β g_sq a : ℝ)
    (hβ : 0 ≤ β) (hg : 0 < g_sq) (ha : 0 < a)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, ksGaugeInvariantH L N β g_sq a hβ ψ⟫_ℂ).re := by
  simp only [ksGaugeInvariantH, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  exact add_nonneg (ksMagneticH_nonneg L N g_sq a hg ha ψ) (transferHamiltonian_nonneg _ ψ)

theorem ksGaugeInvariantH_gauge_comm (L N : ℕ) [NeZero L] (β g_sq a : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    lieBracketCLM (cubicGaugeRep L N g) (ksGaugeInvariantH L N β g_sq a hβ) = 0 := by
  have hm := ksMagneticH_gauge_inv L N g_sq a g
  have ht := transferHamiltonian_comm_of_comm (cubicLatticeGaugeSetup L N β hβ)
    (cubicGaugeRep L N g) (by
      unfold lieBracketCLM
      change (cubicGaugeRep L N g).comp (cubicWilsonTransferOp L N β hβ) -
        (cubicWilsonTransferOp L N β hβ).comp (cubicGaugeRep L N g) = 0
      rw [cubicWilsonTransferOp_gauge_inv L N β hβ g, sub_self])
  unfold lieBracketCLM at hm ht
  unfold lieBracketCLM ksGaugeInvariantH
  ext1 ψ
  have hm' := congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ) hm
  have ht' := congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ) ht
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, map_add, sub_eq_zero] at hm' ht' ⊢
  rw [hm', ht']

/-- Gauss-law invariance preserves `invarianceSet (cubicGaugeRep L N)` under `ksGaugeInvariantH`. -/
theorem ksGaugeInvariantH_preserves_gaussLaw (L N : ℕ) [NeZero L] (β g_sq a : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {ψ : HaarGaugeSpace (latticeHaarMeasure L N)}
    (hψ : ψ ∈ invarianceSet (cubicGaugeRep L N)) :
    ksGaugeInvariantH L N β g_sq a hβ ψ ∈ invarianceSet (cubicGaugeRep L N) :=
  invarianceSet_preserved (cubicGaugeRep L N) (ksGaugeInvariantH L N β g_sq a hβ)
    (fun g => sub_eq_zero.mp (ksGaugeInvariantH_gauge_comm L N β g_sq a hβ g)) hψ

end KogutSusskindYM

/-! ## §32.  Full-rank SU(N) Wilson integral transfer operator on L²(dμ_Haar) -/

section FullRankWilsonIntegralOp

@[reducible] instance instTopologicalSpaceCubicGaugeField (L : ℕ) [NeZero L]
    (G : Type*) [TopologicalSpace G] :
    TopologicalSpace (GaugeField (cubicTorus3 L) G) :=
  Pi.topologicalSpace

instance instSecondCountableCubicGaugeField (L N : ℕ) [NeZero L] :
    SecondCountableTopology
      (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  show SecondCountableTopology
    ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) from inferInstance

instance instBorelSpaceCubicGaugeField (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    BorelSpace (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  ⟨(inferInstance : BorelSpace ((cubicTorus3 L).Link →
    Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable_eq⟩

theorem continuous_cubicField_eval (L N : ℕ) [NeZero L]
    (e : (cubicTorus3 L).Link) :
    Continuous (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => U e) := by
  change Continuous (fun U : (cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ => U e)
  exact continuous_apply e

theorem continuous_pathHolonomy3 (L N : ℕ) [NeZero L]
    (γ : List ((cubicTorus3 L).Link × Bool)) :
    Continuous (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      pathHolonomy U γ) := by
  induction γ with
  | nil => simpa [pathHolonomy] using continuous_const
  | cons hd tl ih =>
    rcases hd with ⟨e, b⟩
    cases b
    · simpa [pathHolonomy] using
        ((continuous_inv.comp (continuous_cubicField_eval L N e)).mul ih)
    · simpa [pathHolonomy] using
        ((continuous_cubicField_eval L N e).mul ih)

theorem continuous_wilsonPlaquetteTerm3 (L N : ℕ) [NeZero L]
    (p : LatticePlaquette (cubicTorus3 L)) :
    Continuous (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonPlaquetteTerm p U) := by
  unfold wilsonPlaquetteTerm
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  exact continuous_const.sub
    (continuous_const.mul (h_tr.comp (continuous_pathHolonomy3 L N p.loop)))

theorem continuous_cubicWilsonAction (L N : ℕ) [NeZero L] (β : ℝ) :
    Continuous (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonAction β (cubicPlaquettes L) U) := by
  unfold wilsonAction
  have hsum : ∀ (ps : List (LatticePlaquette (cubicTorus3 L))),
      Continuous (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        (ps.map (fun p => wilsonPlaquetteTerm p U)).sum) := by
    intro ps
    induction ps with
    | nil => simp [continuous_const]
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (continuous_wilsonPlaquetteTerm3 L N p).add ih
  exact continuous_const.mul (hsum (cubicPlaquettes L))

theorem continuous_cubicWilsonKernel (L N : ℕ) [NeZero L] (β : ℝ)
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin)) :
    Continuous (Function.uncurry (wilsonKernel β (cubicPlaquettes L) K_kin)) := by
  change Continuous (fun p :
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      Real.exp (-(1 / 2 : ℝ) *
        (wilsonAction β (cubicPlaquettes L) p.1 + wilsonAction β (cubicPlaquettes L) p.2)) *
        K_kin p.1 p.2)
  have hS := continuous_cubicWilsonAction L N β
  exact (Real.continuous_exp.comp
    (continuous_const.mul ((hS.comp continuous_fst).add (hS.comp continuous_snd)))).mul hK_cont

theorem continuous_cubicWilsonKernel_right (L N : ℕ) [NeZero L] (β : ℝ)
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Continuous (fun U' => wilsonKernel β (cubicPlaquettes L) K_kin U U') := by
  have hS := continuous_cubicWilsonAction L N β
  have h_pair : Continuous
      (fun U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => (U, U')) :=
    continuous_const.prodMk continuous_id
  have hK_U : Continuous (fun U' => K_kin U U') := hK_cont.comp h_pair
  change Continuous (fun U' =>
    Real.exp (-(1 / 2 : ℝ) *
      (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) *
      K_kin U U')
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_const.add hS))).mul hK_U

theorem continuous_cubicWilsonKernel_left (L N : ℕ) [NeZero L] (β : ℝ)
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Continuous (fun U => wilsonKernel β (cubicPlaquettes L) K_kin U U') := by
  have hS := continuous_cubicWilsonAction L N β
  have h_pair : Continuous
      (fun U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => (U, U')) :=
    continuous_id.prodMk continuous_const
  have hK_U' : Continuous (fun U => K_kin U U') := hK_cont.comp h_pair
  change Continuous (fun U =>
    Real.exp (-(1 / 2 : ℝ) *
      (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) *
      K_kin U U')
  exact (Real.continuous_exp.comp
    (continuous_const.mul (hS.add continuous_const))).mul hK_U'

theorem l1_le_l2_prob {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (ψ : MeasureTheory.Lp ℂ 2 μ) :
    ∫ a, ‖ψ a‖ ∂μ ≤ ‖ψ‖ := by
  let c : ℝ := ∫ a, ‖ψ a‖ ∂μ
  have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
  have hψ_ae : MeasureTheory.AEStronglyMeasurable (⇑ψ) μ := hψ_mem.aestronglyMeasurable
  have h_int1 : MeasureTheory.Integrable (fun a => ‖ψ a‖) μ :=
    (hψ_mem.integrable one_le_two).norm
  have h_int2 : MeasureTheory.Integrable (fun a => ‖ψ a‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hψ_ae).mp hψ_mem
  have hc_nn : 0 ≤ c := MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  have h_var_nn : 0 ≤ ∫ a, (‖ψ a‖ - c) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have h_exp : (fun a => (‖ψ a‖ - c) ^ 2) =
      fun a => ‖ψ a‖ ^ 2 - 2 * c * ‖ψ a‖ + c ^ 2 := by
    funext a; ring
  have h_int_sub : MeasureTheory.Integrable (fun a => ‖ψ a‖ ^ 2 - 2 * c * ‖ψ a‖) μ :=
    h_int2.sub (h_int1.const_mul (2 * c))
  have h_var_val : ∫ a, (‖ψ a‖ - c) ^ 2 ∂μ = (∫ a, ‖ψ a‖ ^ 2 ∂μ) - c ^ 2 := by
    rw [h_exp, MeasureTheory.integral_add h_int_sub (MeasureTheory.integrable_const (c ^ 2)),
        MeasureTheory.integral_sub h_int2 (h_int1.const_mul (2 * c)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const]
    change (∫ a, ‖ψ a‖ ^ 2 ∂μ) - 2 * c * c + μ.real Set.univ • c ^ 2 = _
    simp only [Measure.real, MeasureTheory.measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    ring
  have h_l2_sq : ∫ a, ‖ψ a‖ ^ 2 ∂μ = ‖ψ‖ ^ 2 := by
    have h_l2 : MeasureTheory.Integrable (fun a => ⟪ψ a, ψ a⟫_ℂ) μ :=
      MeasureTheory.L2.integrable_inner _ _
    have h_re := integral_re h_l2
    have h_in : (⟪ψ, ψ⟫_ℂ).re = ∫ a, ‖ψ a‖ ^ 2 ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      change RCLike.re (∫ a, ⟪ψ a, ψ a⟫_ℂ ∂μ) = _
      rw [← h_re]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      change (⟪ψ a, ψ a⟫_ℂ).re = ‖ψ a‖ ^ 2
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two]
    rw [← h_in, inner_self_eq_norm_sq_to_K]
    simp [pow_two]
  rw [h_var_val, h_l2_sq] at h_var_nn
  have h_sq_le : c ^ 2 ≤ ‖ψ‖ ^ 2 := by linarith
  exact (sq_le_sq₀ hc_nn (norm_nonneg ψ)).mp h_sq_le

/-- Pointwise Haar integral `(T_W ψ)(U) = ∫ K_W(U, U') ψ(U') dμ_Haar(U')`. -/
noncomputable def wilsonIntegralFn (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  ∫ U', ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ U'
    ∂(latticeHaarMeasure L N)

theorem wilsonKernel_cubic_le (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ wilsonKernel β (cubicPlaquettes L) K_kin U U' ∧
      wilsonKernel β (cubicPlaquettes L) K_kin U U' ≤ M_K := by
  have hnn := wilsonKernel_nonneg β (cubicPlaquettes L) K_kin hK_nn U U'
  have h1 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U).1
  have h2 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U').1
  have hexp : Real.exp (-(1 / 2 : ℝ) *
      (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨hnn, ?_⟩
  unfold wilsonKernel
  calc Real.exp _ * K_kin U U' ≤ 1 * K_kin U U' :=
        mul_le_mul_of_nonneg_right hexp (hK_nn U U')
    _ ≤ M_K := by rw [one_mul]; exact hK_bd U U'

theorem wilsonKernel_mul_integrable (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    MeasureTheory.Integrable
      (fun U' => ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ U')
      (latticeHaarMeasure L N) := by
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
  have h_dom : MeasureTheory.Integrable (fun U' => M_K * ‖ψ U'‖) μ :=
    (hψ_mem.integrable one_le_two).norm.const_mul M_K
  refine h_dom.mono' ?_ ?_
  · have hK_U : Continuous (fun U' => ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_cubicWilsonKernel_right L N β K_kin hK_cont U)
    exact hK_U.stronglyMeasurable.aestronglyMeasurable.mul hψ_mem.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun U' => ?_
    have hb := wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd U U'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)

theorem wilsonIntegralFn_continuous (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    Continuous (wilsonIntegralFn L N β K_kin ψ) := by
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
  have hψ_int : MeasureTheory.Integrable (fun U' => M_K * ‖ψ U'‖) μ :=
    (hψ_mem.integrable one_le_two).norm.const_mul M_K
  refine MeasureTheory.continuous_of_dominated ?_ ?_ hψ_int ?_
  · intro U
    exact (wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd ψ U).aestronglyMeasurable
  · intro U
    refine Filter.Eventually.of_forall fun U' => ?_
    have hb := wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd U U'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
  · refine Filter.Eventually.of_forall fun U' => ?_
    have hK_U' : Continuous (fun U => ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_cubicWilsonKernel_left L N β K_kin hK_cont U')
    exact hK_U'.mul continuous_const

theorem wilsonIntegralFn_pt_bound (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N))
    (U : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    ‖wilsonIntegralFn L N β K_kin ψ U‖ ≤ M_K * ‖ψ‖ := by
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  have h_int := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd ψ U
  have h_dom : MeasureTheory.Integrable (fun U' => M_K * ‖ψ U'‖) μ :=
    ((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_K
  calc ‖wilsonIntegralFn L N β K_kin ψ U‖
      ≤ ∫ U', ‖((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ U'‖ ∂μ :=
          MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ U', M_K * ‖ψ U'‖ ∂μ := by
          refine MeasureTheory.integral_mono h_int.norm h_dom fun U' => ?_
          have hb := wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd U U'
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
          exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
    _ = M_K * ∫ U', ‖ψ U'‖ ∂μ := MeasureTheory.integral_const_mul M_K _
    _ ≤ M_K * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) hM_K

theorem wilsonIntegralFn_memLp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    MeasureTheory.MemLp (wilsonIntegralFn L N β K_kin ψ) 2 (latticeHaarMeasure L N) := by
  haveI := latticeHaarMeasure_prob L N
  exact memLp_two_of_measurable_bound (latticeHaarMeasure L N)
    (wilsonIntegralFn L N β K_kin ψ)
    (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd ψ).measurable
    (M_K * ‖ψ‖) (mul_nonneg hM_K (norm_nonneg _))
    (wilsonIntegralFn_pt_bound L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ)

/--
Full-rank Wilson integral transfer operator `T_W` on `L²(SU(N)^{3L³}, dμ_Haar)`:
`(T_W ψ)(U) = ∫ wilsonKernel(U, U') ψ(U') dμ_Haar(U')`.
-/
noncomputable def wilsonIntegralOp (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) :=
  let μ := latticeHaarMeasure L N
  LinearMap.mkContinuous
    { toFun := fun ψ =>
        (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).toLp
          (wilsonIntegralFn L N β K_kin ψ)
      map_add' := fun ψ₁ ψ₂ => by
        apply MeasureTheory.Lp.ext
        have h1 := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
          (ψ₁ + ψ₂)).coeFn_toLp
        have h2 := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₁).coeFn_toLp
        have h3 := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₂).coeFn_toLp
        have hadd := MeasureTheory.Lp.coeFn_add
          ((wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₁).toLp
            (wilsonIntegralFn L N β K_kin ψ₁))
          ((wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₂).toLp
            (wilsonIntegralFn L N β K_kin ψ₂))
        have hψ_add := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
        filter_upwards [h1, h2, h3, hadd] with U hu1 hu2 hu3 ha
        simp only [Pi.add_apply] at ha ⊢
        rw [hu1, ha, hu2, hu3]
        have hi1 := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd ψ₁ U
        have hi2 := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd ψ₂ U
        dsimp [wilsonIntegralFn]
        rw [← MeasureTheory.integral_add hi1 hi2]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hψ_add] with U' hU'
        have hU'' : (ψ₁ + ψ₂) U' = ψ₁ U' + ψ₂ U' := hU'
        change ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * (ψ₁ + ψ₂) U' =
          ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ₁ U' +
            ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ₂ U'
        rw [hU'', mul_add]
      map_smul' := fun c ψ => by
        apply MeasureTheory.Lp.ext
        have h1 := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
          (c • ψ)).coeFn_toLp
        have h2 := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).coeFn_toLp
        have hsm := MeasureTheory.Lp.coeFn_smul c
          ((wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).toLp
            (wilsonIntegralFn L N β K_kin ψ))
        have hψ_sm := MeasureTheory.Lp.coeFn_smul c ψ
        filter_upwards [h1, h2, hsm] with U hu1 hu2 hs
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul] at hs ⊢
        rw [hu1, hs, hu2]
        dsimp [wilsonIntegralFn]
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hψ_sm] with U' hU'
        have hU'' : (c • ψ) U' = c * ψ U' := hU'
        change ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * (c • ψ) U' =
          c * (((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ U')
        rw [hU'', mul_left_comm] }
    M_K
    (fun ψ => by
      haveI := latticeHaarMeasure_prob L N
      let ψ' := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).toLp
        (wilsonIntegralFn L N β K_kin ψ)
      change ‖ψ'‖ ≤ M_K * ‖ψ‖
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM_K (norm_nonneg _))]
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪ψ' U, ψ' U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner _ _
      have h_re := integral_re h_l2
      have h_norm_sq : ‖ψ'‖ ^ 2 = ∫ U, ‖ψ' U‖ ^ 2 ∂μ := by
        have h_in : (⟪ψ', ψ'⟫_ℂ).re = ∫ U, ‖ψ' U‖ ^ 2 ∂μ := by
          rw [MeasureTheory.L2.inner_def]
          change RCLike.re (∫ U, ⟪ψ' U, ψ' U⟫_ℂ ∂μ) = _
          rw [← h_re]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
          change (⟪ψ' U, ψ' U⟫_ℂ).re = ‖ψ' U‖ ^ 2
          rw [inner_self_eq_norm_sq_to_K]
          simp [pow_two]
        rw [← h_in, inner_self_eq_norm_sq_to_K]
        simp [pow_two]
      have h_int1 : MeasureTheory.Integrable (fun U => ‖ψ' U‖ ^ 2) μ :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm
          (MeasureTheory.Lp.memLp ψ').aestronglyMeasurable).mp (MeasureTheory.Lp.memLp ψ')
      have h_int2 : MeasureTheory.Integrable (fun _ => (M_K * ‖ψ‖) ^ 2) μ :=
        MeasureTheory.integrable_const _
      have hcoe := (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).coeFn_toLp
      rw [h_norm_sq]
      calc ∫ U, ‖ψ' U‖ ^ 2 ∂μ
          ≤ ∫ _U, (M_K * ‖ψ‖) ^ 2 ∂μ := by
              refine MeasureTheory.integral_mono_ae h_int1 h_int2 ?_
              filter_upwards [hcoe] with U hU
              rw [hU]
              exact pow_le_pow_left₀ (norm_nonneg _)
                (wilsonIntegralFn_pt_bound L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ U) 2
        _ = (M_K * ‖ψ‖) ^ 2 := by
              rw [MeasureTheory.integral_const]
              simp [Measure.real, MeasureTheory.measure_univ])

theorem wilsonIntegralOp_apply_ae (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⇑(wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ) =ᵐ[latticeHaarMeasure L N]
      wilsonIntegralFn L N β K_kin ψ :=
  (wilsonIntegralFn_memLp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ).coeFn_toLp

/-- Exact self-adjointness of the full-rank Wilson integral operator via Fubini. -/
theorem wilsonIntegralOp_sa (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_symm : ∀ U U', K_kin U' U = K_kin U U')
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (ψ₁ ψ₂ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₁, ψ₂⟫_ℂ =
      ⟪ψ₁, wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₂⟫_ℂ := by
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  let K_W := wilsonKernel β (cubicPlaquettes L) K_kin
  let T := wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  have hL : ⟪T ψ₁, ψ₂⟫_ℂ =
      ∫ U, starRingEnd ℂ (wilsonIntegralFn L N β K_kin ψ₁ U) * ψ₂ U ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₁] with U hU
    rw [hU, hcinner]
  have hR : ⟪ψ₁, T ψ₂⟫_ℂ =
      ∫ U', starRingEnd ℂ (ψ₁ U') * wilsonIntegralFn L N β K_kin ψ₂ U' ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ₂] with U' hU'
    rw [hU', hcinner]
  have hKW_cont : Continuous (Function.uncurry K_W) :=
    continuous_cubicWilsonKernel L N β K_kin hK_cont
  have h_prod_int : MeasureTheory.Integrable
      (Function.uncurry fun U U' => ψ₂ U * starRingEnd ℂ (((K_W U U' : ℝ) : ℂ) * ψ₁ U'))
      (μ.prod μ) := by
    have h1_aesm : MeasureTheory.AEStronglyMeasurable
        (fun p : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => ψ₁ p.2)
        (μ.prod μ) :=
      (MeasureTheory.Lp.memLp ψ₁).aestronglyMeasurable.comp_quasiMeasurePreserving
        MeasureTheory.Measure.quasiMeasurePreserving_snd
    have h2_aesm : MeasureTheory.AEStronglyMeasurable
        (fun p : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) => ψ₂ p.1)
        (μ.prod μ) :=
      (MeasureTheory.Lp.memLp ψ₂).aestronglyMeasurable.comp_quasiMeasurePreserving
        MeasureTheory.Measure.quasiMeasurePreserving_fst
    have hK_aesm : MeasureTheory.AEStronglyMeasurable
        (fun p : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          ((K_W p.1 p.2 : ℝ) : ℂ))
        (μ.prod μ) :=
      (Complex.continuous_ofReal.comp hKW_cont).stronglyMeasurable.aestronglyMeasurable
    have h_conj_aesm : MeasureTheory.AEStronglyMeasurable
        (fun p : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          starRingEnd ℂ (((K_W p.1 p.2 : ℝ) : ℂ) * ψ₁ p.2))
        (μ.prod μ) :=
      continuous_star.comp_aestronglyMeasurable (hK_aesm.mul h1_aesm)
    have h_dom : MeasureTheory.Integrable
        (fun p : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          (M_K * ‖ψ₂ p.1‖) * ‖ψ₁ p.2‖)
        (μ.prod μ) :=
      (((MeasureTheory.Lp.memLp ψ₂).integrable one_le_two).norm.const_mul M_K).mul_prod
        ((MeasureTheory.Lp.memLp ψ₁).integrable one_le_two).norm
    refine h_dom.mono' (h2_aesm.mul h_conj_aesm) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    have hb := wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd p.1 p.2
    have hconj : ‖starRingEnd ℂ (((K_W p.1 p.2 : ℝ) : ℂ) * ψ₁ p.2)‖ =
        ‖((K_W p.1 p.2 : ℝ) : ℂ) * ψ₁ p.2‖ :=
      norm_star _
    change ‖ψ₂ p.1 * starRingEnd ℂ (((K_W p.1 p.2 : ℝ) : ℂ) * ψ₁ p.2)‖ ≤
      (M_K * ‖ψ₂ p.1‖) * ‖ψ₁ p.2‖
    rw [norm_mul, hconj, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    calc ‖ψ₂ p.1‖ * (K_W p.1 p.2 * ‖ψ₁ p.2‖)
        ≤ ‖ψ₂ p.1‖ * (M_K * ‖ψ₁ p.2‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)) (norm_nonneg _)
      _ = (M_K * ‖ψ₂ p.1‖) * ‖ψ₁ p.2‖ := by ring
  rw [hL, hR]
  have hL_eq :
      (∫ U, starRingEnd ℂ (wilsonIntegralFn L N β K_kin ψ₁ U) * ψ₂ U ∂μ) =
        ∫ U, ∫ U', ψ₂ U * starRingEnd ℂ (((K_W U U' : ℝ) : ℂ) * ψ₁ U') ∂μ ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    dsimp only [wilsonIntegralFn]
    rw [← integral_conj, mul_comm, ← MeasureTheory.integral_const_mul]
  have hR_eq :
      (∫ U', starRingEnd ℂ (ψ₁ U') * wilsonIntegralFn L N β K_kin ψ₂ U' ∂μ) =
        ∫ U', ∫ U, ψ₂ U * starRingEnd ℂ (((K_W U U' : ℝ) : ℂ) * ψ₁ U') ∂μ ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
    dsimp only [wilsonIntegralFn]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    dsimp only
    change starRingEnd ℂ (ψ₁ U') * (((K_W U' U : ℝ) : ℂ) * ψ₂ U) =
      ψ₂ U * starRingEnd ℂ (((K_W U U' : ℝ) : ℂ) * ψ₁ U')
    rw [map_mul, Complex.conj_ofReal]
    have hsym : K_W U U' = K_W U' U :=
      wilsonKernel_symm β (cubicPlaquettes L) K_kin hK_symm U' U
    rw [hsym]
    ring
  rw [hL_eq, hR_eq]
  exact MeasureTheory.integral_integral_swap h_prod_int

/-- Exact local gauge invariance of the full-rank Wilson integral operator under `cubicGaugeRep`. -/
theorem wilsonIntegralOp_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (hK_inv : ∀ g U U', K_kin (gaugeAct g U) (gaugeAct g U') = K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (cubicGaugeRep L N g).comp
        (wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd) =
      (wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd).comp
        (cubicGaugeRep L N g) := by
  ext1 ψ
  apply MeasureTheory.Lp.ext
  let μ := latticeHaarMeasure L N
  let eqv := gaugeActEquiv L N (fun x => (g x)⁻¹)
  let hmp : MeasureTheory.MeasurePreserving eqv μ μ :=
    ⟨eqv.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
  let T := wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
  have hL1 := cubicGaugeRep_apply_ae L N g (T ψ)
  have hL2 : (fun U => (T ψ) (eqv U)) =ᵐ[μ] (fun U => wilsonIntegralFn L N β K_kin ψ (eqv U)) :=
    ae_comp_measurePreserving hmp (wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ)
  have hR1 := wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd (cubicGaugeRep L N g ψ)
  have h_pt : ∀ U, wilsonIntegralFn L N β K_kin ψ (eqv U) =
      wilsonIntegralFn L N β K_kin (cubicGaugeRep L N g ψ) U := by
    intro U
    dsimp [wilsonIntegralFn]
    have h_comp := (hmp.integral_comp'
      (fun U' => ((wilsonKernel β (cubicPlaquettes L) K_kin (eqv U) U' : ℝ) : ℂ) * ψ U')).symm
    rw [h_comp]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [cubicGaugeRep_apply_ae L N g ψ] with U' hU'
    have h_kern := wilsonKernel_gauge_inv β (cubicPlaquettes L) K_kin hK_inv
      (fun x => (g x)⁻¹) U U'
    change ((wilsonKernel β (cubicPlaquettes L) K_kin
        (gaugeAct (fun x => (g x)⁻¹) U) (gaugeAct (fun x => (g x)⁻¹) U') : ℝ) : ℂ) *
        ψ (gaugeAct (fun x => (g x)⁻¹) U') =
      ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) *
        (cubicGaugeRep L N g ψ) U'
    rw [h_kern, hU']
  filter_upwards [hL1, hL2, hR1] with U hl1 hl2 hr1
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hl1]
  have hl2' : (T ψ) (gaugeAct (fun x => (g x)⁻¹) U) =
      wilsonIntegralFn L N β K_kin ψ (gaugeAct (fun x => (g x)⁻¹) U) := hl2
  rw [hl2', hr1]
  exact h_pt U

end FullRankWilsonIntegralOp

/-! ## §33.  Full-rank SU(N) Wilson integral operator: compactness, Gram positivity,
            Perron–Frobenius vacuum & finite-volume spectral gap -/

section FullRankWilsonSpectralGap

instance instCompactSpaceCubicGaugeField (L N : ℕ) [NeZero L] :
    CompactSpace (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  show CompactSpace ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) from
    inferInstance

instance instT2SpaceCubicGaugeField (L N : ℕ) [NeZero L] :
    T2Space (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  show T2Space ((cubicTorus3 L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) from
    inferInstance

instance instIsOpenPosLatticeHaar (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure.IsOpenPosMeasure (latticeHaarMeasure L N) := by
  haveI := suHaar_prob N
  haveI : MeasureTheory.Measure.IsHaarMeasure (suHaar N) :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure ⊤
  change MeasureTheory.Measure.IsOpenPosMeasure
    (MeasureTheory.Measure.pi fun _ : (cubicTorus3 L).Link => suHaar N)
  infer_instance

theorem lp_coeFn_finset_sum {α ι : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (t : Finset ι) [DecidableEq ι]
    (f : ι → MeasureTheory.Lp ℂ 2 μ) :
    ⇑(∑ i ∈ t, f i) =ᵐ[μ] fun x => ∑ i ∈ t, (f i) x := by
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 μ
  | @insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    have hadd := MeasureTheory.Lp.coeFn_add (f a) (∑ i ∈ t, f i)
    filter_upwards [hadd, ih] with x hxa hxi
    simp only [Pi.add_apply] at hxa
    rw [hxa, hxi]

theorem lp_norm_sq_eq_integral {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (ψ : MeasureTheory.Lp ℂ 2 μ) :
    ‖ψ‖ ^ 2 = ∫ a, ‖ψ a‖ ^ 2 ∂μ := by
  have h_l2 : MeasureTheory.Integrable (fun a => ⟪ψ a, ψ a⟫_ℂ) μ :=
    MeasureTheory.L2.integrable_inner _ _
  have h_re := integral_re h_l2
  have h_in : (⟪ψ, ψ⟫_ℂ).re = ∫ a, ‖ψ a‖ ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    change RCLike.re (∫ a, ⟪ψ a, ψ a⟫_ℂ ∂μ) = _
    rw [← h_re]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    change (⟪ψ a, ψ a⟫_ℂ).re = ‖ψ a‖ ^ 2
    rw [inner_self_eq_norm_sq_to_K]
    simp [pow_two]
  rw [← h_in, inner_self_eq_norm_sq_to_K]
  simp [pow_two]

theorem integrable_of_continuous_compact {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Continuous f) :
    MeasureTheory.Integrable f μ := by
  obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_abs.comp hf)).bddAbove
  let C : ℝ := max M 0
  refine (MeasureTheory.integrable_const C).mono' hf.stronglyMeasurable.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs]
  exact le_max_of_le_left (hM ⟨x, Set.mem_univ x, rfl⟩)

theorem memLp_of_continuous_compact {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Continuous f) :
    MeasureTheory.MemLp (fun x => (f x : ℂ)) 2 μ := by
  obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_abs.comp hf)).bddAbove
  let C : ℝ := max M 0
  have hC : 0 ≤ C := le_max_right M 0
  refine memLp_two_of_measurable_bound μ (fun x => (f x : ℂ))
    (Complex.continuous_ofReal.comp hf).measurable C hC fun x => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact le_max_of_le_left (hM ⟨x, Set.mem_univ x, rfl⟩)

theorem compact_integral_op_of_cont_kernel
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (K : α → α → ℝ) (hK_cont : Continuous (Function.uncurry K))
    (hK_nn : ∀ x y, 0 ≤ K x y) (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ x y, K x y ≤ M_K)
    (T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (hT_ae : ∀ ψ, ⇑T ψ =ᵐ[μ] fun x => ∫ y, ((K x y : ℝ) : ℂ) * ψ y ∂μ) :
    IsCompactOperator ⇑T := by
  classical
  let fn : MeasureTheory.Lp ℂ 2 μ → α → ℂ := fun ψ x => ∫ y, ((K x y : ℝ) : ℂ) * ψ y ∂μ
  have hK_mul_int : ∀ (ψ : MeasureTheory.Lp ℂ 2 μ) (x : α),
      MeasureTheory.Integrable (fun y => ((K x y : ℝ) : ℂ) * ψ y) μ := by
    intro ψ x
    have hψ_mem : MeasureTheory.MemLp (⇑ψ) 2 μ := MeasureTheory.Lp.memLp ψ
    have h_dom : MeasureTheory.Integrable (fun y => M_K * ‖ψ y‖) μ :=
      (hψ_mem.integrable one_le_two).norm.const_mul M_K
    refine h_dom.mono' ?_ ?_
    · have hp : Continuous (fun y : α => (x, y)) := continuous_const.prodMk continuous_id
      exact (Complex.continuous_ofReal.comp (hK_cont.comp hp)).stronglyMeasurable.aestronglyMeasurable.mul
        hψ_mem.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK_nn x y)]
      exact mul_le_mul_of_nonneg_right (hK_bd x y) (norm_nonneg _)
  have h_pt_bd : ∀ (ψ : MeasureTheory.Lp ℂ 2 μ) (x : α), ‖fn ψ x‖ ≤ M_K * ‖ψ‖ := by
    intro ψ x
    have h_int := hK_mul_int ψ x
    have h_dom : MeasureTheory.Integrable (fun y => M_K * ‖ψ y‖) μ :=
      ((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_K
    calc ‖fn ψ x‖ ≤ ∫ y, ‖((K x y : ℝ) : ℂ) * ψ y‖ ∂μ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ y, M_K * ‖ψ y‖ ∂μ := by
          refine MeasureTheory.integral_mono h_int.norm h_dom fun y => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK_nn x y)]
          exact mul_le_mul_of_nonneg_right (hK_bd x y) (norm_nonneg _)
      _ = M_K * ∫ y, ‖ψ y‖ ∂μ := MeasureTheory.integral_const_mul M_K _
      _ ≤ M_K * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) hM_K
  have h_approx : ∀ n : ℕ, ∃ T_n : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ,
      IsCompactOperator ⇑T_n ∧ ‖T - T_n‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    let δ : ℝ := 1 / ((n : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    let V : α → Set α := fun x₀ => { x | ∀ y : α, |K x y - K x₀ y| < δ }
    have hV_open : ∀ x₀ : α, IsOpen (V x₀) := by
      intro x₀
      let C_set : Set (α × α) := { p | δ ≤ |K p.1 p.2 - K x₀ p.2| }
      have h_pair : Continuous (fun p : α × α => (x₀, p.2)) :=
        continuous_const.prodMk continuous_snd
      have hC_cont : Continuous (fun p : α × α => |K p.1 p.2 - K x₀ p.2|) :=
        continuous_abs.comp (hK_cont.sub (hK_cont.comp h_pair))
      have hC_closed : IsClosed C_set := isClosed_le continuous_const hC_cont
      have h_proj_closed : IsClosed (Prod.fst '' C_set) :=
        (hC_closed.isCompact.image continuous_fst).isClosed
      have hV_eq : V x₀ = (Prod.fst '' C_set)ᶜ := by
        ext x
        simp only [V, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, C_set, Prod.exists,
          not_exists, not_and]
        constructor
        · intro h a b hle ha; subst ha; exact not_le.mpr (h b) hle
        · intro h y; exact not_le.mp fun hle => h x y hle rfl
      rw [hV_eq]
      exact h_proj_closed.isOpen_compl
    have h_cov : Set.univ ⊆ ⋃ x₀ : α, V x₀ := by
      intro x _; refine Set.mem_iUnion.mpr ⟨x, fun y => by simpa using hδ⟩
    obtain ⟨t, ht_cov⟩ := isCompact_univ.elim_finite_subcover V hV_open h_cov
    let m := t.card
    let e : Fin m ≃ ↥t := t.equivFin.symm
    let x_rep : Fin m → α := fun i => (e i).1
    let s : Fin m → Set α := fun i =>
      V (x_rep i) \ ⋃ j ∈ Finset.univ.filter (fun j : Fin m => j < i), V (x_rep j)
    have hs_meas : ∀ i : Fin m, MeasurableSet (s i) := fun i =>
      (hV_open (x_rep i)).measurableSet.diff
        (Finset.measurableSet_biUnion _ fun j _ => (hV_open (x_rep j)).measurableSet)
    have hs_disj : ∀ i j : Fin m, i ≠ j → Disjoint (s i) (s j) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro x hxi hxj
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact hxj.2 (Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩) hxi.1)
      · exact hij heq
      · exact hxi.2 (Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩) hxj.1)
    have hs_cover : ∀ x : α, ∃ i : Fin m, x ∈ s i := by
      intro x
      let F_x : Finset (Fin m) := Finset.univ.filter (fun i => x ∈ V (x_rep i))
      have hF_ne : F_x.Nonempty := by
        have hmem := ht_cov (Set.mem_univ x)
        rw [Set.mem_iUnion₂] at hmem
        rcases hmem with ⟨x₀, hx₀, hxV⟩
        refine ⟨e.symm ⟨x₀, hx₀⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simpa [x_rep, Equiv.apply_symm_apply] using hxV
      let i₀ := F_x.min' hF_ne
      refine ⟨i₀, (Finset.mem_filter.mp (Finset.min'_mem F_x hF_ne)).2, ?_⟩
      intro h_in
      rw [Set.mem_iUnion₂] at h_in
      rcases h_in with ⟨j, hj, hjV⟩
      have hj_lt : j < i₀ := (Finset.mem_filter.mp hj).2
      have hj_mem : j ∈ F_x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjV⟩
      exact absurd (Finset.min'_le F_x j hj_mem) (not_le_of_gt hj_lt)
    let ind : Fin m → MeasureTheory.Lp ℂ 2 μ := fun i =>
      MeasureTheory.indicatorConstLp 2 (hs_meas i) (MeasureTheory.measure_ne_top μ (s i)) (1 : ℂ)
    let c : Fin m → MeasureTheory.Lp ℂ 2 μ → ℂ := fun i ψ => fn ψ (x_rep i)
    have hc_add : ∀ i ψ₁ ψ₂, c i (ψ₁ + ψ₂) = c i ψ₁ + c i ψ₂ := by
      intro i ψ₁ ψ₂
      dsimp [c, fn]
      rw [← MeasureTheory.integral_add (hK_mul_int ψ₁ (x_rep i)) (hK_mul_int ψ₂ (x_rep i))]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.Lp.coeFn_add ψ₁ ψ₂] with y hy
      have hy' : (ψ₁ + ψ₂) y = ψ₁ y + ψ₂ y := hy
      change ((K (x_rep i) y : ℝ) : ℂ) * (ψ₁ + ψ₂) y =
        ((K (x_rep i) y : ℝ) : ℂ) * ψ₁ y + ((K (x_rep i) y : ℝ) : ℂ) * ψ₂ y
      rw [hy', mul_add]
    have hc_smul : ∀ i (r : ℂ) ψ, c i (r • ψ) = r * c i ψ := by
      intro i r ψ
      dsimp [c, fn]
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.Lp.coeFn_smul r ψ] with y hy
      have hy' : (r • ψ) y = r * ψ y := hy
      change ((K (x_rep i) y : ℝ) : ℂ) * (r • ψ) y =
        r * (((K (x_rep i) y : ℝ) : ℂ) * ψ y)
      rw [hy', mul_left_comm]
    have hind_norm : ∀ i, ‖ind i‖ ≤ 1 := by
      intro i
      rw [← sq_le_sq₀ (norm_nonneg _) zero_le_one, one_pow, lp_norm_sq_eq_integral]
      have hcoe := MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
        (μ := μ) (s := s i) (hs := hs_meas i)
        (hμs := MeasureTheory.measure_ne_top μ (s i)) (c := (1 : ℂ))
      have h_int_ae : (fun x => ‖(ind i) x‖ ^ 2) =ᵐ[μ]
          fun x => if x ∈ s i then (1 : ℝ) else 0 := by
        filter_upwards [hcoe] with x hx
        change ‖(ind i) x‖ ^ 2 = _
        rw [hx, Set.indicator_apply]
        by_cases hxi : x ∈ s i <;> simp [hxi]
      rw [MeasureTheory.integral_congr_ae h_int_ae]
      have h_le : ∀ x, (if x ∈ s i then (1 : ℝ) else 0) ≤ 1 := fun x => by split_ifs <;> norm_num
      have h_ind_aesm : MeasureTheory.AEStronglyMeasurable
          ((s i).indicator (fun _ => (1 : ℝ))) μ :=
        (MeasureTheory.aestronglyMeasurable_const (b := (1 : ℝ))).indicator (hs_meas i)
      have h_int1 : MeasureTheory.Integrable (fun x => if x ∈ s i then (1 : ℝ) else 0) μ :=
        (MeasureTheory.integrable_const (1 : ℝ)).mono'
          (h_ind_aesm.congr (Filter.Eventually.of_forall fun U => by simp [Set.indicator_apply]))
          (Filter.Eventually.of_forall fun U => by split_ifs <;> simp)
      calc ∫ x, (if x ∈ s i then (1 : ℝ) else 0) ∂μ
          ≤ ∫ _x, (1 : ℝ) ∂μ :=
            MeasureTheory.integral_mono h_int1 (MeasureTheory.integrable_const 1) h_le
        _ = 1 := by simp [Measure.real, MeasureTheory.measure_univ]
    let T_n : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ :=
      LinearMap.mkContinuous
        { toFun := fun ψ => ∑ i : Fin m, c i ψ • ind i
          map_add' := fun ψ₁ ψ₂ => by simp only [hc_add, add_smul, Finset.sum_add_distrib]
          map_smul' := fun r ψ => by
            simp only [hc_smul, smul_smul, RingHom.id_apply, Finset.smul_sum] }
        ((m : ℝ) * M_K)
        (fun ψ => by
          change ‖∑ i : Fin m, c i ψ • ind i‖ ≤ ((m : ℝ) * M_K) * ‖ψ‖
          calc ‖∑ i : Fin m, c i ψ • ind i‖
              ≤ ∑ i : Fin m, ‖c i ψ • ind i‖ := norm_sum_le _ _
            _ ≤ ∑ _i : Fin m, M_K * ‖ψ‖ := by
                  refine Finset.sum_le_sum fun i _ => ?_
                  rw [norm_smul]
                  calc ‖c i ψ‖ * ‖ind i‖ ≤ (M_K * ‖ψ‖) * 1 :=
                        mul_le_mul (h_pt_bd ψ (x_rep i)) (hind_norm i) (norm_nonneg _)
                          (mul_nonneg hM_K (norm_nonneg _))
                    _ = M_K * ‖ψ‖ := mul_one _
            _ = ((m : ℝ) * M_K) * ‖ψ‖ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc])
    have hTn_comp : IsCompactOperator ⇑T_n := by
      let Φ : (Fin m → ℂ) → MeasureTheory.Lp ℂ 2 μ := fun z => ∑ i : Fin m, z i • ind i
      have hΦ_cont : Continuous Φ :=
        continuous_finset_sum Finset.univ fun i _ => (continuous_apply i).smul continuous_const
      let B_m : Set (Fin m → ℂ) := Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) M_K
      have hB_m : IsCompact B_m := isCompact_univ_pi fun _ => isCompact_closedBall 0 M_K
      refine ⟨Φ '' B_m, hB_m.image hΦ_cont,
        Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) fun ψ hψ => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hψ
      refine ⟨fun i => c i ψ, fun i _ => ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖c i ψ‖ ≤ M_K * ‖ψ‖ := h_pt_bd ψ (x_rep i)
        _ ≤ M_K * 1 := mul_le_mul_of_nonneg_left hψ hM_K
        _ = M_K := mul_one M_K
    have hTn_norm : ‖T - T_n‖ ≤ δ := by
      refine ContinuousLinearMap.opNorm_le_bound _ hδ.le fun ψ => ?_
      have hTn_ae : ⇑(T_n ψ) =ᵐ[μ] fun x => ∑ i : Fin m, if x ∈ s i then c i ψ else 0 := by
        have hsum := lp_coeFn_finset_sum μ Finset.univ (fun i => c i ψ • ind i)
        have hterm : ∀ i : Fin m,
            ⇑(c i ψ • ind i) =ᵐ[μ] fun x => if x ∈ s i then c i ψ else 0 := by
          intro i
          have hs_ae := MeasureTheory.Lp.coeFn_smul (c i ψ) (ind i)
          have hi_ae := MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
            (μ := μ) (s := s i) (hs := hs_meas i)
            (hμs := MeasureTheory.measure_ne_top μ (s i)) (c := (1 : ℂ))
          filter_upwards [hs_ae, hi_ae] with x hxs hxi
          simp only [Pi.smul_apply, smul_eq_mul] at hxs
          change ⇑(c i ψ • ind i) x = _
          rw [hxs]
          change c i ψ * ⇑(ind i) x = _
          rw [hxi, Set.indicator_apply]
          split_ifs <;> simp
        have hall : (fun x => ∑ i : Fin m, (c i ψ • ind i) x) =ᵐ[μ]
            fun x => ∑ i : Fin m, if x ∈ s i then c i ψ else 0 := by
          have h_ev : ∀ᵐ x ∂μ, ∀ i : Fin m,
              ⇑(c i ψ • ind i) x = if x ∈ s i then c i ψ else 0 :=
            MeasureTheory.ae_all_iff.mpr hterm
          filter_upwards [h_ev] with x hx
          exact Finset.sum_congr rfl fun i _ => hx i
        filter_upwards [hsum, hall] with x hx1 hx2
        change ⇑(∑ i : Fin m, c i ψ • ind i) x = _
        rw [hx1, hx2]
      have hdiff_ae : ⇑((T - T_n) ψ) =ᵐ[μ]
          fun x => fn ψ x - ∑ i : Fin m, if x ∈ s i then c i ψ else 0 := by
        have hsub := MeasureTheory.Lp.coeFn_sub (T ψ) (T_n ψ)
        filter_upwards [hsub, hT_ae ψ, hTn_ae] with x hs hT hTn
        change ⇑(T ψ - T_n ψ) x = _
        rw [hs]
        simp only [Pi.sub_apply]
        rw [hT, hTn]
      have hpt_le : ∀ᵐ x ∂μ, ‖((T - T_n) ψ) x‖ ≤ δ * ‖ψ‖ := by
        filter_upwards [hdiff_ae] with x hx
        change ‖((T - T_n) ψ) x‖ ≤ δ * ‖ψ‖
        rw [hx]
        obtain ⟨i₀, hi₀⟩ := hs_cover x
        have hsum_eq : (∑ i : Fin m, if x ∈ s i then c i ψ else 0) = c i₀ ψ := by
          rw [Finset.sum_eq_single i₀]
          · simp [hi₀]
          · intro i _ hne
            have hnot : x ∉ s i := fun hi => (Set.disjoint_left.mp (hs_disj i i₀ hne)) hi hi₀
            simp [hnot]
          · intro hi₀_not
            exact absurd (Finset.mem_univ i₀) hi₀_not
        rw [hsum_eq]
        have hi₀_V : x ∈ V (x_rep i₀) := hi₀.1
        have hi1 := hK_mul_int ψ x
        have hi2 := hK_mul_int ψ (x_rep i₀)
        dsimp [c, fn]
        rw [← MeasureTheory.integral_sub hi1 hi2]
        have h_dom : MeasureTheory.Integrable (fun y => δ * ‖ψ y‖) μ :=
          ((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul δ
        have h_sub_int : MeasureTheory.Integrable
            (fun y => ‖((K x y : ℝ) : ℂ) * ψ y - ((K (x_rep i₀) y : ℝ) : ℂ) * ψ y‖) μ :=
          (hi1.sub hi2).norm
        calc ‖∫ y, (((K x y : ℝ) : ℂ) * ψ y - ((K (x_rep i₀) y : ℝ) : ℂ) * ψ y) ∂μ‖
            ≤ ∫ y, ‖((K x y : ℝ) : ℂ) * ψ y - ((K (x_rep i₀) y : ℝ) : ℂ) * ψ y‖ ∂μ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ y, δ * ‖ψ y‖ ∂μ := by
              refine MeasureTheory.integral_mono h_sub_int h_dom fun y => ?_
              have hfac : ((K x y : ℝ) : ℂ) * ψ y - ((K (x_rep i₀) y : ℝ) : ℂ) * ψ y =
                  (((K x y - K (x_rep i₀) y : ℝ) : ℂ)) * ψ y := by
                push_cast; ring
              rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right (hi₀_V y).le (norm_nonneg _)
          _ = δ * ∫ y, ‖ψ y‖ ∂μ := MeasureTheory.integral_const_mul δ _
          _ ≤ δ * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) hδ.le
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ.le (norm_nonneg _)),
          lp_norm_sq_eq_integral]
      have h_int1 : MeasureTheory.Integrable (fun x => ‖((T - T_n) ψ) x‖ ^ 2) μ :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm
          (MeasureTheory.Lp.memLp ((T - T_n) ψ)).aestronglyMeasurable).mp
          (MeasureTheory.Lp.memLp ((T - T_n) ψ))
      have h_int2 : MeasureTheory.Integrable (fun _ => (δ * ‖ψ‖) ^ 2) μ :=
        MeasureTheory.integrable_const _
      calc ∫ x, ‖((T - T_n) ψ) x‖ ^ 2 ∂μ
          ≤ ∫ _x, (δ * ‖ψ‖) ^ 2 ∂μ := by
            refine MeasureTheory.integral_mono_ae h_int1 h_int2 ?_
            filter_upwards [hpt_le] with x hx
            exact pow_le_pow_left₀ (norm_nonneg _) hx 2
        _ = (δ * ‖ψ‖) ^ 2 := by
            rw [MeasureTheory.integral_const]
            simp [Measure.real, MeasureTheory.measure_univ]
    exact ⟨T_n, hTn_comp, hTn_norm⟩
  choose T_seq hT_comp hT_norm using h_approx
  have h_tendsto : Filter.Tendsto T_seq Filter.atTop (nhds T) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / ε)
    refine ⟨N₀, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h_lt : 1 / ((n : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ hn_pos]
      have h1 : 1 / ε < (n : ℝ) + 1 := lt_of_lt_of_le hN₀ (by exact_mod_cast (Nat.le_succ_of_le hn))
      have h2 := (div_lt_iff₀ hε).mp h1
      linarith
    calc dist (T_seq n) T = ‖T - T_seq n‖ := by rw [dist_comm, dist_eq_norm]
      _ ≤ 1 / ((n : ℝ) + 1) := hT_norm n
      _ < ε := h_lt
  exact isClosed_setOf_isCompactOperator.mem_of_tendsto h_tendsto
    (Filter.Eventually.of_forall hT_comp)

/--
**Compactness of `wilsonIntegralOp`**:
every continuous Wilson kernel on the compact product group `SU(N)^{3L³}` defines
a compact integral operator on `L²(SU(N)^{3L³}, dμ_Haar)` via norm-convergent
finite-rank kernel partitions.
-/
theorem wilsonIntegralOp_compact (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K) :
    IsCompactOperator ⇑(wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd) := by
  haveI := latticeHaarMeasure_prob L N
  exact compact_integral_op_of_cont_kernel (latticeHaarMeasure L N)
    (wilsonKernel β (cubicPlaquettes L) K_kin)
    (continuous_cubicWilsonKernel L N β K_kin hK_cont)
    (wilsonKernel_nonneg β (cubicPlaquettes L) K_kin hK_nn)
    M_K hM_K (fun U U' => (wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd U U').2)
    (wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd)
    (wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd)

/-- Gram-factorized symmetric positive-definite kinetic kernel `∫ χ(U, W) χ(U', W) dμ(W)`. -/
noncomputable def wilsonGramKernel (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  ∫ W, χ U W * χ U' W ∂(latticeHaarMeasure L N)

theorem continuous_wilsonGramKernel (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_nn : ∀ U W, 0 ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ) :
    Continuous (Function.uncurry (wilsonGramKernel L N χ)) := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  refine MeasureTheory.continuous_of_dominated
    (bound := fun _ : G_L => M_χ ^ 2) ?_ ?_ (MeasureTheory.integrable_const _) ?_
  · intro p
    have hp1 : Continuous (fun W : G_L => (p.1, W)) := continuous_const.prodMk continuous_id
    have hp2 : Continuous (fun W : G_L => (p.2, W)) := continuous_const.prodMk continuous_id
    exact ((hχ_cont.comp hp1).mul (hχ_cont.comp hp2)).stronglyMeasurable.aestronglyMeasurable
  · intro p
    refine Filter.Eventually.of_forall fun W => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ_nn p.1 W) (hχ_nn p.2 W)), sq]
    exact mul_le_mul (hχ_bd p.1 W) (hχ_bd p.2 W) (hχ_nn p.2 W) hM_χ
  · refine Filter.Eventually.of_forall fun W => ?_
    have hp1 : Continuous (fun p : G_L × G_L => (p.1, W)) := continuous_fst.prodMk continuous_const
    have hp2 : Continuous (fun p : G_L × G_L => (p.2, W)) := continuous_snd.prodMk continuous_const
    exact (hχ_cont.comp hp1).mul (hχ_cont.comp hp2)

theorem wilsonGramKernel_symm (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonGramKernel L N χ U' U = wilsonGramKernel L N χ U U' := by
  dsimp [wilsonGramKernel]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => by dsimp only; exact mul_comm _ _)

theorem wilsonGramKernel_nonneg (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_nn : ∀ U W, 0 ≤ χ U W)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ wilsonGramKernel L N χ U U' :=
  MeasureTheory.integral_nonneg fun W => mul_nonneg (hχ_nn U W) (hχ_nn U' W)

theorem wilsonGramKernel_le (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_nn : ∀ U W, 0 ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonGramKernel L N χ U U' ≤ M_χ ^ 2 := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  have hp1 : Continuous (fun W : G_L => (U, W)) := continuous_const.prodMk continuous_id
  have hp2 : Continuous (fun W : G_L => (U', W)) := continuous_const.prodMk continuous_id
  have h_int : MeasureTheory.Integrable (fun W => χ U W * χ U' W) μ :=
    integrable_of_continuous_compact μ _ ((hχ_cont.comp hp1).mul (hχ_cont.comp hp2))
  calc wilsonGramKernel L N χ U U'
      ≤ ∫ _W, M_χ ^ 2 ∂μ := by
        refine MeasureTheory.integral_mono h_int (MeasureTheory.integrable_const _) fun W => ?_
        rw [sq]
        exact mul_le_mul (hχ_bd U W) (hχ_bd U' W) (hχ_nn U' W) hM_χ
    _ = M_χ ^ 2 := by simp [Measure.real, MeasureTheory.measure_univ]

theorem wilsonGramKernel_lb (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (c_χ : ℝ) (hc_χ : 0 ≤ c_χ) (hχ_lb : ∀ U W, c_χ ≤ χ U W)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    c_χ ^ 2 ≤ wilsonGramKernel L N χ U U' := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  have hp1 : Continuous (fun W : G_L => (U, W)) := continuous_const.prodMk continuous_id
  have hp2 : Continuous (fun W : G_L => (U', W)) := continuous_const.prodMk continuous_id
  have h_int : MeasureTheory.Integrable (fun W => χ U W * χ U' W) μ :=
    integrable_of_continuous_compact μ _ ((hχ_cont.comp hp1).mul (hχ_cont.comp hp2))
  calc c_χ ^ 2 = ∫ _W, c_χ ^ 2 ∂μ := by simp [Measure.real, MeasureTheory.measure_univ]
    _ ≤ wilsonGramKernel L N χ U U' := by
        refine MeasureTheory.integral_mono (MeasureTheory.integrable_const _) h_int fun W => ?_
        rw [sq]
        exact mul_le_mul (hχ_lb U W) (hχ_lb U' W) hc_χ (hc_χ.trans (hχ_lb U W))

theorem wilsonGramKernel_gauge_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_inv : ∀ g U W, χ (gaugeAct g U) (gaugeAct g W) = χ U W)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonGramKernel L N χ (gaugeAct g U) (gaugeAct g U') = wilsonGramKernel L N χ U U' := by
  dsimp [wilsonGramKernel]
  calc ∫ W, χ (gaugeAct g U) W * χ (gaugeAct g U') W ∂(latticeHaarMeasure L N)
      = ∫ W, χ (gaugeAct g U) (gaugeAct g W) * χ (gaugeAct g U') (gaugeAct g W)
          ∂(latticeHaarMeasure L N) :=
        (cubicWilsonExpectation_gauge_inv L N g
          (fun W => χ (gaugeAct g U) W * χ (gaugeAct g U') W)).symm
    _ = ∫ W, χ U W * χ U' W ∂(latticeHaarMeasure L N) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
        dsimp only
        rw [hχ_inv, hχ_inv]

/--
**Positivity (reflection positivity) of `wilsonIntegralOp`** for any Gram-factorized
Wilson kernel: `0 ≤ Re ⟪ψ, T_W ψ⟫ = ∫ ‖∫ exp(-½ S_W[U]) χ(U, W) ψ(U) dμ(U)‖² dμ(W)`.
-/
theorem wilsonIntegralOp_gram_pos (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_nn : ∀ U W, 0 ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, wilsonIntegralOp L N β hβ (wilsonGramKernel L N χ)
      (continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)
      (wilsonGramKernel_nonneg L N χ hχ_nn) (M_χ ^ 2) (sq_nonneg M_χ)
      (wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd) ψ⟫_ℂ).re := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  let K_kin := wilsonGramKernel L N χ
  have hK_cont := continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  have hK_nn := wilsonGramKernel_nonneg L N χ hχ_nn
  have hK_bd := wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let T := wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn (M_χ ^ 2) (sq_nonneg M_χ) hK_bd
  let κ : G_L → G_L → ℝ := fun U W => cubicWilsonWeight L N β U * χ U W
  have hκ_cont : Continuous (Function.uncurry κ) := by
    have hS := continuous_cubicWilsonAction L N β
    have hw : Continuous (cubicWilsonWeight L N β) :=
      Real.continuous_exp.comp (continuous_const.mul hS)
    exact (hw.comp continuous_fst).mul hχ_cont
  have hκ_bd : ∀ U W, 0 ≤ κ U W ∧ κ U W ≤ M_χ := fun U W => by
    have hwb := cubicWilsonWeight_bounds L N β hβ U
    have hwnn : 0 ≤ cubicWilsonWeight L N β U := by
      unfold cubicWilsonWeight; exact (Real.exp_pos _).le
    refine ⟨mul_nonneg hwnn (hχ_nn U W), ?_⟩
    calc cubicWilsonWeight L N β U * χ U W ≤ 1 * χ U W :=
          mul_le_mul_of_nonneg_right hwb.2 (hχ_nn U W)
      _ ≤ M_χ := by rw [one_mul]; exact hχ_bd U W
  have hKW_eq : ∀ U U', ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) =
      ∫ W, ((κ U W : ℝ) : ℂ) * ((κ U' W : ℝ) : ℂ) ∂μ := by
    intro U U'
    have h_exp : Real.exp (-(1 / 2 : ℝ) *
        (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) =
        cubicWilsonWeight L N β U * cubicWilsonWeight L N β U' := by
      unfold cubicWilsonWeight
      rw [← Real.exp_add]
      congr 1; ring
    have h_real : wilsonKernel β (cubicPlaquettes L) K_kin U U' =
        ∫ W, κ U W * κ U' W ∂μ := by
      unfold wilsonKernel K_kin wilsonGramKernel
      rw [h_exp, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
      dsimp [κ]; ring
    have h_int_c : MeasureTheory.Integrable
        (fun W => (((κ U W * κ U' W : ℝ) : ℂ))) μ := by
      have hp1 : Continuous (fun W : G_L => (U, W)) := continuous_const.prodMk continuous_id
      have hp2 : Continuous (fun W : G_L => (U', W)) := continuous_const.prodMk continuous_id
      refine (MeasureTheory.integrable_const (M_χ ^ 2)).mono'
        (Complex.continuous_ofReal.comp
          ((hκ_cont.comp hp1).mul (hκ_cont.comp hp2))).stronglyMeasurable.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun W => ?_
      have h1 := hκ_bd U W
      have h2 := hκ_bd U' W
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1.1 h2.1), sq]
      exact mul_le_mul h1.2 h2.2 h2.1 hM_χ
    rw [h_real]
    have h_cast : (fun W => ((κ U W : ℝ) : ℂ) * ((κ U' W : ℝ) : ℂ)) =
        fun W => (((κ U W * κ U' W : ℝ) : ℂ)) := by
      funext W; push_cast; ring
    rw [h_cast]
    have h_re_eq : (∫ W, (((κ U W * κ U' W : ℝ) : ℂ)) ∂μ).re = ∫ W, κ U W * κ U' W ∂μ := by
      change RCLike.re (∫ W, (((κ U W * κ U' W : ℝ) : ℂ)) ∂μ) = _
      rw [← integral_re h_int_c]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
      simp
    have h_im_eq : (∫ W, (((κ U W * κ U' W : ℝ) : ℂ)) ∂μ).im = 0 := by
      have h1 : (∫ W, (((κ U W * κ U' W : ℝ) : ℂ)) ∂μ).im =
          RCLike.re (-Complex.I * ∫ W, (((κ U W * κ U' W : ℝ) : ℂ)) ∂μ) := by
        simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (h_int_c.const_mul (-Complex.I))]
      refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun W => ?_)
      simp [Complex.mul_re]
    exact Complex.ext h_re_eq.symm h_im_eq.symm
  let g_half : G_L → ℂ := fun W => ∫ U, ((κ U W : ℝ) : ℂ) * ψ U ∂μ
  have hg_cont : Continuous g_half := by
    have h_dom : MeasureTheory.Integrable (fun U => M_χ * ‖ψ U‖) μ :=
      ((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_χ
    refine MeasureTheory.continuous_of_dominated ?_ ?_ h_dom ?_
    · intro W
      have hp : Continuous (fun U : G_L => (U, W)) := continuous_id.prodMk continuous_const
      exact (Complex.continuous_ofReal.comp (hκ_cont.comp hp)).stronglyMeasurable.aestronglyMeasurable.mul
        (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable
    · intro W
      refine Filter.Eventually.of_forall fun U => ?_
      have hb := hκ_bd U W
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun U => ?_
      have hp : Continuous (fun W : G_L => (U, W)) := continuous_const.prodMk continuous_id
      exact (Complex.continuous_ofReal.comp (hκ_cont.comp hp)).mul continuous_const
  have hg_bd : ∀ W, ‖g_half W‖ ≤ M_χ * ‖ψ‖ := by
    intro W
    have hp : Continuous (fun U : G_L => (U, W)) := continuous_id.prodMk continuous_const
    have h_int : MeasureTheory.Integrable (fun U => ‖((κ U W : ℝ) : ℂ) * ψ U‖) μ := by
      have h_dom : MeasureTheory.Integrable (fun U => M_χ * ‖ψ U‖) μ :=
        ((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_χ
      refine h_dom.mono'
        ((Complex.continuous_ofReal.comp (hκ_cont.comp hp)).stronglyMeasurable.aestronglyMeasurable.mul
          (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable).norm ?_
      refine Filter.Eventually.of_forall fun U => ?_
      have hb := hκ_bd U W
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
    calc ‖g_half W‖ ≤ ∫ U, ‖((κ U W : ℝ) : ℂ) * ψ U‖ ∂μ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ U, M_χ * ‖ψ U‖ ∂μ := by
          refine MeasureTheory.integral_mono h_int
            (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_χ) fun U => ?_
          have hb := hκ_bd U W
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
          exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
      _ = M_χ * ∫ U, ‖ψ U‖ ∂μ := MeasureTheory.integral_const_mul M_χ _
      _ ≤ M_χ * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) hM_χ
  have h_inner_eq : ⟪ψ, T ψ⟫_ℂ = ∫ W, (((‖g_half W‖ ^ 2 : ℝ) : ℂ)) ∂μ := by
    have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
      intro a b
      have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K]; norm_num
      calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
        _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
              rw [inner_smul_left, inner_smul_right]
        _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
    have h1 : ⟪ψ, T ψ⟫_ℂ =
        ∫ U, starRingEnd ℂ (ψ U) * wilsonIntegralFn L N β K_kin ψ U ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
        (M_χ ^ 2) (sq_nonneg M_χ) hK_bd ψ] with U hU
      rw [hU, hcinner]
    have h_step1 : ∀ U, wilsonIntegralFn L N β K_kin ψ U =
        ∫ W, ((κ U W : ℝ) : ℂ) * g_half W ∂μ := by
      intro U
      dsimp [wilsonIntegralFn]
      have h_prod1 : MeasureTheory.Integrable
          (Function.uncurry fun U' W => ((κ U W : ℝ) : ℂ) * (((κ U' W : ℝ) : ℂ) * ψ U'))
          (μ.prod μ) := by
        have hψ_aesm : MeasureTheory.AEStronglyMeasurable (fun p : G_L × G_L => ψ p.1) (μ.prod μ) :=
          (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable.comp_quasiMeasurePreserving
            MeasureTheory.Measure.quasiMeasurePreserving_fst
        have hκ1 : MeasureTheory.AEStronglyMeasurable
            (fun p : G_L × G_L => ((κ U p.2 : ℝ) : ℂ)) (μ.prod μ) :=
          (Complex.continuous_ofReal.comp
            (hκ_cont.comp (continuous_const.prodMk continuous_snd))).stronglyMeasurable.aestronglyMeasurable
        have hκ2 : MeasureTheory.AEStronglyMeasurable
            (fun p : G_L × G_L => ((κ p.1 p.2 : ℝ) : ℂ)) (μ.prod μ) :=
          (Complex.continuous_ofReal.comp hκ_cont).stronglyMeasurable.aestronglyMeasurable
        have h_dom : MeasureTheory.Integrable
            (fun p : G_L × G_L => (M_χ ^ 2 * ‖ψ p.1‖) * (1 : ℝ)) (μ.prod μ) :=
          ((((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul (M_χ ^ 2)).mul_prod
            (MeasureTheory.integrable_const (1 : ℝ)))
        refine h_dom.mono' (hκ1.mul (hκ2.mul hψ_aesm)) ?_
        refine Filter.Eventually.of_forall fun p => ?_
        have hb1 := hκ_bd U p.2
        have hb2 := hκ_bd p.1 p.2
        dsimp only [Function.uncurry]
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb1.1, abs_of_nonneg hb2.1, mul_one]
        calc κ U p.2 * (κ p.1 p.2 * ‖ψ p.1‖)
            ≤ M_χ * (M_χ * ‖ψ p.1‖) :=
              mul_le_mul hb1.2 (mul_le_mul_of_nonneg_right hb2.2 (norm_nonneg _))
                (mul_nonneg hb2.1 (norm_nonneg _)) hM_χ
          _ = M_χ ^ 2 * ‖ψ p.1‖ := by rw [sq]; ring
      calc ∫ U', ((wilsonKernel β (cubicPlaquettes L) K_kin U U' : ℝ) : ℂ) * ψ U' ∂μ
          = ∫ U', ∫ W, ((κ U W : ℝ) : ℂ) * (((κ U' W : ℝ) : ℂ) * ψ U') ∂μ ∂μ := by
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
              dsimp only
              rw [hKW_eq U U', ← MeasureTheory.integral_mul_const]
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => by
                dsimp only; ring)
        _ = ∫ W, ∫ U', ((κ U W : ℝ) : ℂ) * (((κ U' W : ℝ) : ℂ) * ψ U') ∂μ ∂μ :=
              MeasureTheory.integral_integral_swap h_prod1
        _ = ∫ W, ((κ U W : ℝ) : ℂ) * g_half W ∂μ := by
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
              dsimp only
              rw [MeasureTheory.integral_const_mul]
    have h_prod2 : MeasureTheory.Integrable
        (Function.uncurry fun U W =>
          (starRingEnd ℂ (((κ U W : ℝ) : ℂ) * ψ U)) * g_half W)
        (μ.prod μ) := by
      have hψ_aesm : MeasureTheory.AEStronglyMeasurable (fun p : G_L × G_L => ψ p.1) (μ.prod μ) :=
        (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable.comp_quasiMeasurePreserving
          MeasureTheory.Measure.quasiMeasurePreserving_fst
      have hκ_aesm : MeasureTheory.AEStronglyMeasurable
          (fun p : G_L × G_L => ((κ p.1 p.2 : ℝ) : ℂ)) (μ.prod μ) :=
        (Complex.continuous_ofReal.comp hκ_cont).stronglyMeasurable.aestronglyMeasurable
      have hg_aesm : MeasureTheory.AEStronglyMeasurable
          (fun p : G_L × G_L => g_half p.2) (μ.prod μ) :=
        (hg_cont.comp continuous_snd).stronglyMeasurable.aestronglyMeasurable
      have h_conj : MeasureTheory.AEStronglyMeasurable
          (fun p : G_L × G_L => starRingEnd ℂ (((κ p.1 p.2 : ℝ) : ℂ) * ψ p.1)) (μ.prod μ) :=
        continuous_star.comp_aestronglyMeasurable (hκ_aesm.mul hψ_aesm)
      have h_dom : MeasureTheory.Integrable
          (fun p : G_L × G_L => (M_χ * ‖ψ p.1‖) * (M_χ * ‖ψ‖)) (μ.prod μ) :=
        (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul M_χ).mul_prod
          (MeasureTheory.integrable_const (M_χ * ‖ψ‖))
      refine h_dom.mono' (h_conj.mul hg_aesm) ?_
      refine Filter.Eventually.of_forall fun p => ?_
      have hb := hκ_bd p.1 p.2
      have hconj : ‖starRingEnd ℂ (((κ p.1 p.2 : ℝ) : ℂ) * ψ p.1)‖ =
          ‖((κ p.1 p.2 : ℝ) : ℂ) * ψ p.1‖ := norm_star _
      dsimp only [Function.uncurry]
      rw [norm_mul, hconj, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _))
        (hg_bd p.2) (norm_nonneg _) (mul_nonneg hM_χ (norm_nonneg _))
    rw [h1]
    calc ∫ U, starRingEnd ℂ (ψ U) * wilsonIntegralFn L N β K_kin ψ U ∂μ
        = ∫ U, ∫ W, starRingEnd ℂ (((κ U W : ℝ) : ℂ) * ψ U) * g_half W ∂μ ∂μ := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            dsimp only
            rw [h_step1 U, ← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
            dsimp only
            rw [map_mul, Complex.conj_ofReal]
            ring
      _ = ∫ W, ∫ U, starRingEnd ℂ (((κ U W : ℝ) : ℂ) * ψ U) * g_half W ∂μ ∂μ :=
            MeasureTheory.integral_integral_swap h_prod2
      _ = ∫ W, (((‖g_half W‖ ^ 2 : ℝ) : ℂ)) ∂μ := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
            dsimp only
            rw [MeasureTheory.integral_mul_const, integral_conj]
            change starRingEnd ℂ (g_half W) * g_half W = _
            rw [Complex.conj_mul', Complex.ofReal_pow]
  rw [h_inner_eq]
  have h_norm_int : MeasureTheory.Integrable (fun W => (((‖g_half W‖ ^ 2 : ℝ) : ℂ))) μ := by
    refine (MeasureTheory.integrable_const ((M_χ * ‖ψ‖) ^ 2)).mono'
      (Complex.continuous_ofReal.comp (hg_cont.norm.pow 2)).stronglyMeasurable.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun W => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hg_bd W) 2
  change 0 ≤ RCLike.re (∫ W, (((‖g_half W‖ ^ 2 : ℝ) : ℂ)) ∂μ)
  rw [← integral_re h_norm_int]
  refine MeasureTheory.integral_nonneg fun W => ?_
  change 0 ≤ (((‖g_half W‖ ^ 2 : ℝ) : ℂ)).re
  rw [Complex.ofReal_re]
  exact sq_nonneg _

/--
Every nonzero compact positive self-adjoint operator on a Hilbert space `V`
attains its operator norm `‖T‖ > 0` at a unit eigenvector `v`.
-/
theorem compact_sa_pos_exists_max_eigenvector
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (T : V →L[ℂ] V)
    (hT_sa : ∀ x y : V, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (hT_pos : ∀ x : V, 0 ≤ (⟪x, T x⟫_ℂ).re)
    (hT_comp : IsCompactOperator ⇑T)
    (hT_ne : T ≠ 0) :
    ∃ v : V, ‖v‖ = 1 ∧ T v = (‖T‖ : ℂ) • v := by
  have hT_selfadj : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT_sa
  have hT_pos_norm : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg T) (Ne.symm (norm_ne_zero_iff.mpr hT_ne))
  let s : ℝ := ⨆ x : V, |T.rayleighQuotient x|
  have hbdd : BddAbove (Set.range fun x : V => |T.rayleighQuotient x|) :=
    ContinuousLinearMap.bddAbove_rayleighQuotient T
  have hnorm_eq : ‖T‖ = s := norm_eq_iSup_rayleighQuotient hT_selfadj
  have hu_ex : ∀ n : ℕ, ∃ u : V, ‖T‖ * (1 - 1 / ((n : ℝ) + 2)) < |T.rayleighQuotient u| := by
    intro n
    have hlt : ‖T‖ * (1 - 1 / ((n : ℝ) + 2)) < s := by
      rw [← hnorm_eq]
      have h1 : 0 < 1 / ((n : ℝ) + 2) := by positivity
      nlinarith
    exact (lt_ciSup_iff hbdd).mp hlt
  choose u hu_lt using hu_ex
  have hu_ne : ∀ n : ℕ, u n ≠ 0 := by
    intro n h0
    have hlt := hu_lt n
    have hrq0 : T.rayleighQuotient (u n) = 0 := by
      simp [ContinuousLinearMap.rayleighQuotient, h0]
    rw [hrq0, abs_zero] at hlt
    have hnonneg : 0 ≤ ‖T‖ * (1 - 1 / ((n : ℝ) + 2)) := by
      have h2 : 0 ≤ 1 - 1 / ((n : ℝ) + 2) := by
        have h3 : 1 / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        linarith
      exact mul_nonneg hT_pos_norm.le h2
    exact not_lt_of_ge hnonneg hlt
  let x : ℕ → V := fun n => ((‖u n‖⁻¹ : ℝ) : ℂ) • u n
  have hx_norm : ∀ n : ℕ, ‖x n‖ = 1 := by
    intro n
    simp only [x, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hu_ne n))
  let lam : ℕ → ℝ := fun n => (⟪T (x n), x n⟫_ℂ).re
  have hlam_eq_rq : ∀ n : ℕ, lam n = T.rayleighQuotient (u n) := by
    intro n
    have hnorm_u : ‖u n‖ ≠ 0 := norm_ne_zero_iff.mpr (hu_ne n)
    simp only [lam, ContinuousLinearMap.rayleighQuotient, x, map_smul,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    have hcast : (((‖u n‖⁻¹ : ℝ) : ℂ) * (((‖u n‖⁻¹ : ℝ) : ℂ) * ⟪T (u n), u n⟫_ℂ)).re =
        (‖u n‖⁻¹ * ‖u n‖⁻¹) * (⟪T (u n), u n⟫_ℂ).re := by
      simp [Complex.mul_re]; ring
    rw [hcast]
    change (‖u n‖⁻¹ * ‖u n‖⁻¹) * (⟪T (u n), u n⟫_ℂ).re =
      (⟪T (u n), u n⟫_ℂ).re / ‖u n‖ ^ 2
    field_simp [hnorm_u]
  have hlam_mem : ∀ n : ℕ, lam n ∈ Set.Icc (-‖T‖) ‖T‖ := fun n => by
    rw [Set.mem_Icc, ← abs_le, hlam_eq_rq n]
    exact T.rayleighQuotient_le_norm (u n)
  have hTx_mem : ∀ n : ℕ, T (x n) ∈ closure (T '' Metric.closedBall (0 : V) 1) := fun n => by
    apply subset_closure
    refine ⟨x n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hx_norm n]
  let S_comp : Set (ℝ × V) := Set.Icc (-‖T‖) ‖T‖ ×ˢ closure (T '' Metric.closedBall (0 : V) 1)
  have hS_comp : IsCompact S_comp :=
    isCompact_Icc.prod (hT_comp.isCompact_closure_image_closedBall (1 : ℝ))
  let seq : ℕ → ℝ × V := fun n => (lam n, T (x n))
  obtain ⟨⟨μ, y⟩, hμy_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    hS_comp.tendsto_subseq (x := seq) (fun n => ⟨hlam_mem n, hTx_mem n⟩)
  have hlam_tendsto : Filter.Tendsto (fun n => lam (φ n)) Filter.atTop (nhds μ) := by
    simpa [seq, Function.comp_def] using (continuous_fst.tendsto (μ, y)).comp hφ_tendsto
  have hTx_tendsto : Filter.Tendsto (fun n => T (x (φ n))) Filter.atTop (nhds y) := by
    simpa [seq, Function.comp_def] using (continuous_snd.tendsto (μ, y)).comp hφ_tendsto
  have hμ_abs : |μ| = ‖T‖ := by
    have h_abs_tendsto : Filter.Tendsto (fun n => |lam (φ n)|) Filter.atTop (nhds |μ|) :=
      continuous_abs.continuousAt.tendsto.comp hlam_tendsto
    have h_lower : Filter.Tendsto (fun n => ‖T‖ * (1 - 1 / ((φ n : ℝ) + 2)))
        Filter.atTop (nhds ‖T‖) := by
      have h_inv : Filter.Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 2)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right _ 2
            (tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop))
      simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => ‖T‖) Filter.atTop (nhds ‖T‖)).mul
          ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)).sub h_inv)
    have h_le : ‖T‖ ≤ |μ| :=
      le_of_tendsto_of_tendsto' h_lower h_abs_tendsto fun n => by
        rw [hlam_eq_rq]; exact (hu_lt (φ n)).le
    exact le_antisymm (abs_le.mpr hμy_mem.1) h_le
  have hμ_ne : μ ≠ 0 := by intro h0; rw [h0, abs_zero] at hμ_abs; linarith
  have hμ_sq : μ ^ 2 = ‖T‖ ^ 2 := by rw [← hμ_abs, sq_abs]
  have h_diff_sq_tendsto : Filter.Tendsto
      (fun n => ‖T (x (φ n)) - (μ : ℂ) • x (φ n)‖ ^ 2) Filter.atTop (nhds 0) := by
    have h_upper : ∀ n : ℕ,
        ‖T (x (φ n)) - (μ : ℂ) • x (φ n)‖ ^ 2 ≤ ‖T‖ ^ 2 - 2 * μ * lam (φ n) + μ ^ 2 := by
      intro n
      have h_exp : ‖T (x (φ n)) - (μ : ℂ) • x (φ n)‖ ^ 2 =
          ‖T (x (φ n))‖ ^ 2 - 2 * μ * lam (φ n) + μ ^ 2 := by
        rw [norm_sub_sq (𝕜 := ℂ)]
        have h_re : RCLike.re ⟪T (x (φ n)), (μ : ℂ) • x (φ n)⟫_ℂ = μ * lam (φ n) := by
          rw [inner_smul_right]
          simp [lam, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        have h_norm_μx : ‖(μ : ℂ) • x (φ n)‖ ^ 2 = μ ^ 2 := by
          rw [norm_smul, hx_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        rw [h_re, h_norm_μx]; ring
      have h_le_norm : ‖T (x (φ n))‖ ^ 2 ≤ ‖T‖ ^ 2 := by
        have h1 : ‖T (x (φ n))‖ ≤ ‖T‖ := by
          calc ‖T (x (φ n))‖ ≤ ‖T‖ * ‖x (φ n)‖ := T.le_opNorm _
            _ = ‖T‖ := by rw [hx_norm, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      linarith
    have h_rhs : Filter.Tendsto (fun n => ‖T‖ ^ 2 - 2 * μ * lam (φ n) + μ ^ 2)
        Filter.atTop (nhds 0) := by
      have h0 : ‖T‖ ^ 2 - 2 * μ * μ + μ ^ 2 = 0 := by linarith [hμ_sq]
      rw [← h0]
      exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul hlam_tendsto)).add tendsto_const_nhds
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_rhs
      (fun _ => sq_nonneg _) h_upper
  have h_diff_tendsto : Filter.Tendsto
      (fun n => T (x (φ n)) - (μ : ℂ) • x (φ n)) Filter.atTop (nhds 0) := by
    have h_norm_tendsto : Filter.Tendsto
        (fun n => ‖T (x (φ n)) - (μ : ℂ) • x (φ n)‖) Filter.atTop (nhds 0) := by
      have hsqrt := continuous_sqrt.continuousAt.tendsto.comp h_diff_sq_tendsto
      rw [Real.sqrt_zero] at hsqrt
      refine hsqrt.congr fun n => ?_
      dsimp only [Function.comp_def]
      exact Real.sqrt_sq (norm_nonneg _)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm_tendsto
  have hx_tendsto : Filter.Tendsto (fun n => x (φ n)) Filter.atTop (nhds ((μ : ℂ)⁻¹ • y)) := by
    have h_smul : Filter.Tendsto (fun n => (μ : ℂ) • x (φ n)) Filter.atTop (nhds y) := by
      have hsub := hTx_tendsto.sub h_diff_tendsto
      rw [sub_zero] at hsub
      refine hsub.congr fun n => ?_
      abel
    have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ_ne
    have h_inv := (continuous_const_smul ((μ : ℂ)⁻¹)).continuousAt.tendsto.comp h_smul
    convert h_inv using 1
    · ext n; simp only [Function.comp_apply]; rw [smul_smul, inv_mul_cancel₀ hμc, one_smul]
  have hy_ne : y ≠ 0 := by
    intro hy0
    have h_norm_x : Filter.Tendsto (fun n => ‖x (φ n)‖) Filter.atTop (nhds ‖(μ : ℂ)⁻¹ • y‖) :=
      continuous_norm.continuousAt.tendsto.comp hx_tendsto
    have h_const1 : (fun n => ‖x (φ n)‖) = fun _ => 1 := funext fun n => hx_norm (φ n)
    rw [h_const1, hy0, smul_zero, norm_zero] at h_norm_x
    have h_eq := tendsto_nhds_unique tendsto_const_nhds h_norm_x
    norm_num at h_eq
  have hy_eig : T y = (μ : ℂ) • y := by
    have h_eq : y = T ((μ : ℂ)⁻¹ • y) :=
      tendsto_nhds_unique hTx_tendsto (T.continuous.continuousAt.tendsto.comp hx_tendsto)
    have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ_ne
    calc T y = T ((μ : ℂ) • ((μ : ℂ)⁻¹ • y)) := by rw [smul_smul, mul_inv_cancel₀ hμc, one_smul]
      _ = (μ : ℂ) • T ((μ : ℂ)⁻¹ • y) := T.map_smul _ _
      _ = (μ : ℂ) • y := by rw [← h_eq]
  let v : V := ((‖y‖⁻¹ : ℝ) : ℂ) • y
  have hv_norm : ‖v‖ = 1 := by
    simp only [v, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy_ne)
  have hv_eig : T v = (μ : ℂ) • v := by
    have h1 : T (((‖y‖⁻¹ : ℝ) : ℂ) • y) = ((‖y‖⁻¹ : ℝ) : ℂ) • T y :=
      ContinuousLinearMap.map_smul T ((‖y‖⁻¹ : ℝ) : ℂ) y
    have h2 : ((‖y‖⁻¹ : ℝ) : ℂ) • ((μ : ℂ) • y) = (μ : ℂ) • (((‖y‖⁻¹ : ℝ) : ℂ) • y) := by
      rw [smul_smul, mul_comm, ← smul_smul]
    change T (((‖y‖⁻¹ : ℝ) : ℂ) • y) = (μ : ℂ) • (((‖y‖⁻¹ : ℝ) : ℂ) • y)
    rw [h1, hy_eig, h2]
  have hμ_nn : 0 ≤ μ := by
    have hp := hT_pos v
    rw [hv_eig, inner_smul_right, inner_self_eq_norm_sq_to_K, hv_norm] at hp
    change 0 ≤ ((μ : ℂ) * ((1 : ℝ) : ℂ) ^ 2).re at hp
    rw [Complex.ofReal_one, one_pow, mul_one, Complex.ofReal_re] at hp
    exact hp
  have hμ_eq : μ = ‖T‖ := by rwa [abs_of_nonneg hμ_nn] at hμ_abs
  exact ⟨v, hv_norm, hμ_eq ▸ hv_eig⟩

/-- Orthogonal complement `Ωᗮ` of a vacuum state `Ω`. -/
noncomputable def wilsonPerpSubmodule {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Ω : V) : Submodule ℂ V :=
  (Submodule.span ℂ {Ω})ᗮ

theorem wilsonPerpSubmodule_inv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {T_norm : V →L[ℂ] V} {Ω : V}
    (hT_sa : ∀ x y : V, ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ)
    (hT_Ω : T_norm Ω = Ω)
    {x : V} (hx : x ∈ wilsonPerpSubmodule Ω) :
    T_norm x ∈ wilsonPerpSubmodule Ω := by
  unfold wilsonPerpSubmodule at hx ⊢
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro z hz
  rw [Submodule.mem_span_singleton] at hz
  rcases hz with ⟨c, rfl⟩
  have hΩx : ⟪Ω, x⟫_ℂ = 0 := hx Ω (Submodule.subset_span rfl)
  rw [inner_smul_left, ← hT_sa, hT_Ω, hΩx, mul_zero]

/-- Restriction of a self-adjoint operator `T_norm` (fixing `Ω`) to `Ωᗮ`. -/
noncomputable def wilsonPerpOp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T_norm : V →L[ℂ] V) (Ω : V)
    (hT_sa : ∀ x y : V, ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ)
    (hT_Ω : T_norm Ω = Ω) :
    ↥(wilsonPerpSubmodule Ω) →L[ℂ] ↥(wilsonPerpSubmodule Ω) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨T_norm x.1, wilsonPerpSubmodule_inv hT_sa hT_Ω x.2⟩
      map_add' := fun x y => Subtype.ext (T_norm.map_add x.1 y.1)
      map_smul' := fun c x => Subtype.ext (T_norm.map_smul c x.1) }
    ‖T_norm‖
    (fun x => by
      change ‖T_norm x.1‖ ≤ ‖T_norm‖ * ‖x.1‖
      exact T_norm.le_opNorm x.1)

/-- Exact spectral gap `-log ‖T_norm|_{Ωᗮ}‖` (with `1` when `T_norm|_{Ωᗮ} = 0`). -/
noncomputable def wilsonExactGap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T_norm : V →L[ℂ] V) (Ω : V)
    (hT_sa : ∀ x y : V, ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ)
    (hT_Ω : T_norm Ω = Ω) : ℝ :=
  if ‖wilsonPerpOp T_norm Ω hT_sa hT_Ω‖ = 0 then 1
  else -Real.log ‖wilsonPerpOp T_norm Ω hT_sa hT_Ω‖

theorem eq_of_ae_continuous {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.Measure.IsOpenPosMeasure μ]
    {f g : α → ℂ} (hf : Continuous f) (hg : Continuous g) (h_ae : f =ᵐ[μ] g) :
    ∀ x, f x = g x := by
  intro x
  by_contra hne
  let S : Set α := { y | f y ≠ g y }
  have hS_eq : S = (fun y => f y - g y) ⁻¹' { z | z ≠ 0 } := by
    ext y
    change f y ≠ g y ↔ f y - g y ≠ 0
    exact sub_ne_zero.symm
  have hS_open : IsOpen S := hS_eq ▸ isOpen_ne.preimage (hf.sub hg)
  have hS_pos : 0 < μ S := hS_open.measure_pos μ ⟨x, hne⟩
  have hS_zero : μ S = 0 := h_ae
  exact lt_irrefl 0 (hS_pos.trans_eq hS_zero)

theorem eq_zero_of_continuous_sq_integral_zero {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.Measure.IsOpenPosMeasure μ]
    (h : α → ℝ) (hh : Continuous h)
    (h_int : ∫ x, h x ^ 2 ∂μ = 0) :
    ∀ x, h x = 0 := by
  intro x₀
  by_contra hx₀
  let δ : ℝ := (h x₀) ^ 2 / 2
  have hδ : 0 < δ := by positivity
  let B : Set α := { x | δ < h x ^ 2 }
  have hB_open : IsOpen B := isOpen_lt continuous_const (hh.pow 2)
  have hx0_sq : 0 < h x₀ ^ 2 := sq_pos_iff.mpr hx₀
  have hB_pos : 0 < μ.real B :=
    ENNReal.toReal_pos
      (hB_open.measure_pos μ ⟨x₀, by change δ < h x₀ ^ 2; dsimp [δ]; linarith⟩).ne'
      (MeasureTheory.measure_ne_top μ B)
  have h_cont_int : MeasureTheory.Integrable (fun x => h x ^ 2) μ :=
    integrable_of_continuous_compact μ _ (hh.pow 2)
  have h_ind_int : MeasureTheory.Integrable (Set.indicator B (fun _ => δ)) μ :=
    (MeasureTheory.integrable_const δ).indicator hB_open.measurableSet
  have h_le : ∀ x, Set.indicator B (fun _ => δ) x ≤ h x ^ 2 := by
    intro x
    rw [Set.indicator_apply]
    by_cases hx : x ∈ B
    · rw [if_pos hx]; exact (hx : _ < _).le
    · rw [if_neg hx]; exact sq_nonneg _
  have h_val : ∫ x, Set.indicator B (fun _ => δ) x ∂μ = μ.real B * δ := by
    rw [MeasureTheory.integral_indicator hB_open.measurableSet, MeasureTheory.setIntegral_const]
    simp [smul_eq_mul]
  have h_pos : 0 < ∫ x, h x ^ 2 ∂μ := by
    calc 0 < μ.real B * δ := mul_pos hB_pos hδ
      _ = ∫ x, Set.indicator B (fun _ => δ) x ∂μ := h_val.symm
      _ ≤ ∫ x, h x ^ 2 ∂μ := MeasureTheory.integral_mono h_ind_int h_cont_int h_le
  linarith

structure IsWilsonGroundState (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (Ω : HaarGaugeSpace (latticeHaarMeasure L N))
    (ω : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ) : Prop where
  norm_pos  : 0 < ‖wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd‖
  unit      : ‖Ω‖ = 1
  ω_cont    : Continuous ω
  ω_pos     : ∀ U, 0 < ω U
  ae_eq     : ⇑Ω =ᵐ[latticeHaarMeasure L N] (fun U => (ω U : ℂ))
  eig       : wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd Ω =
                (‖wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd‖ : ℂ) • Ω
  gauge_inv : ∀ g, cubicGaugeRep L N g Ω = Ω
  simple    : ∀ w : HaarGaugeSpace (latticeHaarMeasure L N),
                wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd w =
                  (‖wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd‖ : ℂ) • w →
                ⟪w, Ω⟫_ℂ = 0 → w = 0

/--
**Perron–Frobenius Ground State & Simplicity for `wilsonIntegralOp`**:
for any continuous, symmetric, gauge-invariant, strictly positive kinetic kernel
`K_kin`, `T = wilsonIntegralOp ...` has simple top eigenvalue `‖T‖ > 0`
attained at a strictly positive continuous gauge-invariant eigenfunction `ω`.
-/
theorem wilsonIntegral_ground_state (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_symm : ∀ U U', K_kin U' U = K_kin U U')
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (hK_inv : ∀ g U U', K_kin (gaugeAct g U) (gaugeAct g U') = K_kin U U')
    (c_min : ℝ) (hc_min : 0 < c_min) (hK_lb : ∀ U U', c_min ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (hT_pos : ∀ ψ : HaarGaugeSpace (latticeHaarMeasure L N),
      0 ≤ (⟪ψ, wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ⟫_ℂ).re) :
    ∃ (Ω : HaarGaugeSpace (latticeHaarMeasure L N))
      (ω : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ),
      IsWilsonGroundState L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd Ω ω := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  haveI := instIsOpenPosLatticeHaar L N
  let K_W := wilsonKernel β (cubicPlaquettes L) K_kin
  let T := wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
  have hT_sa : ∀ x y : HaarGaugeSpace μ, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ :=
    wilsonIntegralOp_sa L N β hβ K_kin hK_cont hK_symm hK_nn M_K hM_K hK_bd
  have hT_comp : IsCompactOperator ⇑T :=
    wilsonIntegralOp_compact L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
  let c_W : ℝ := Real.exp (-(2 * β * ((cubicPlaquettes L).length : ℝ))) * c_min
  have hc_W_pos : 0 < c_W := mul_pos (Real.exp_pos _) hc_min
  have hKW_lb : ∀ U U', c_W ≤ K_W U U' := by
    intro U U'
    have h1 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U).2
    have h2 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U').2
    have hexp : Real.exp (-(2 * β * ((cubicPlaquettes L).length : ℝ))) ≤
        Real.exp (-(1 / 2 : ℝ) *
          (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) :=
      Real.exp_le_exp.mpr (by linarith)
    unfold K_W wilsonKernel
    exact mul_le_mul hexp (hK_lb U U') hc_min.le (Real.exp_pos _).le
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  have hT_ne : T ≠ 0 := by
    let oneLp : HaarGaugeSpace μ :=
      MeasureTheory.indicatorConstLp (2 : ENNReal) MeasurableSet.univ
        (MeasureTheory.measure_ne_top μ Set.univ) (1 : ℂ)
    have hone_ae : ⇑oneLp =ᵐ[μ] fun _ => (1 : ℂ) := by
      have h := MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
        (μ := μ) (s := Set.univ) (hs := MeasurableSet.univ)
        (hμs := MeasureTheory.measure_ne_top μ Set.univ) (c := (1 : ℂ))
      filter_upwards [h] with U hU
      simpa [oneLp] using hU
    have h_l2 : MeasureTheory.Integrable (fun U => ⟪oneLp U, (T oneLp) U⟫_ℂ) μ :=
      MeasureTheory.L2.integrable_inner _ _
    have h_re := integral_re h_l2
    have h_in_re : (⟪oneLp, T oneLp⟫_ℂ).re =
        ∫ U, (⟪oneLp U, (T oneLp) U⟫_ℂ).re ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      change RCLike.re (∫ U, ⟪oneLp U, (T oneLp) U⟫_ℂ ∂μ) = _
      rw [← h_re]
      rfl
    have h_ae_ge : ∀ᵐ U ∂μ, c_W ≤ (⟪oneLp U, (T oneLp) U⟫_ℂ).re := by
      filter_upwards [hone_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
        M_K hM_K hK_bd oneLp] with U hU1 hUT
      change c_W ≤ (⟪oneLp U, (T oneLp) U⟫_ℂ).re
      rw [hU1, hUT]
      have hc1 : ⟪(1 : ℂ), wilsonIntegralFn L N β K_kin oneLp U⟫_ℂ =
          wilsonIntegralFn L N β K_kin oneLp U := by
        rw [hcinner, map_one, one_mul]
      rw [hc1]
      dsimp [wilsonIntegralFn]
      have h_int_fn := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd oneLp U
      change c_W ≤ RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * oneLp U' ∂μ)
      rw [← integral_re h_int_fn]
      have h_int_K : MeasureTheory.Integrable (fun U' => K_W U U') μ :=
        integrable_of_continuous_compact μ _ (continuous_cubicWilsonKernel_right L N β K_kin hK_cont U)
      have h_eq_int : ∫ x, RCLike.re (((K_W U x : ℝ) : ℂ) * oneLp x) ∂μ =
          ∫ x, K_W U x ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hone_ae] with x hx
        change (((K_W U x : ℝ) : ℂ) * ⇑oneLp x).re = K_W U x
        rw [hx, mul_one, Complex.ofReal_re]
      rw [h_eq_int]
      calc c_W = ∫ _U', c_W ∂μ := by simp [Measure.real, MeasureTheory.measure_univ]
        _ ≤ ∫ U', K_W U U' ∂μ :=
            MeasureTheory.integral_mono (MeasureTheory.integrable_const c_W) h_int_K (hKW_lb U)
    have h_pos_re : c_W ≤ (⟪oneLp, T oneLp⟫_ℂ).re := by
      rw [h_in_re]
      calc c_W = ∫ _U, c_W ∂μ := by simp [Measure.real, MeasureTheory.measure_univ]
        _ ≤ ∫ U, (⟪oneLp U, (T oneLp) U⟫_ℂ).re ∂μ :=
            MeasureTheory.integral_mono_ae (MeasureTheory.integrable_const c_W) h_l2.re h_ae_ge
    intro h0
    rw [h0, ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re] at h_pos_re
    linarith
  obtain ⟨v₀, hv₀_norm, hv₀_eig⟩ :=
    compact_sa_pos_exists_max_eigenvector T hT_sa hT_pos hT_comp hT_ne
  let lam0 : ℝ := ‖T‖
  have hlam0_pos : 0 < lam0 := lt_of_le_of_ne (norm_nonneg T) (Ne.symm (norm_ne_zero_iff.mpr hT_ne))
  let φ₀ : G_L → ℂ := fun U => ((lam0⁻¹ : ℝ) : ℂ) * wilsonIntegralFn L N β K_kin v₀ U
  have hφ₀_cont : Continuous φ₀ :=
    continuous_const.mul (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd v₀)
  have hv₀_ae : ⇑v₀ =ᵐ[μ] φ₀ := by
    have h_eq : v₀ = ((lam0⁻¹ : ℝ) : ℂ) • T v₀ := by
      rw [hv₀_eig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
        Complex.ofReal_one, one_smul]
    have h1 : ⇑v₀ =ᵐ[μ] ((lam0⁻¹ : ℝ) : ℂ) • ⇑(T v₀) := by
      conv_lhs => rw [h_eq]
      exact MeasureTheory.Lp.coeFn_smul _ _
    filter_upwards [h1, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
      M_K hM_K hK_bd v₀] with U hU1 hU2
    change ⇑v₀ U = φ₀ U
    rw [hU1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hU2]
  let φ_abs : G_L → ℂ := fun U => ((‖φ₀ U‖ : ℝ) : ℂ)
  have hφ_abs_mem : MeasureTheory.MemLp φ_abs 2 μ := by
    refine memLp_two_of_measurable_bound μ φ_abs
      (Complex.continuous_ofReal.measurable.comp hφ₀_cont.norm.measurable)
      (lam0⁻¹ * (M_K * ‖v₀‖)) (by positivity) fun U => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hlam0_pos.le)]
    exact mul_le_mul_of_nonneg_left
      (wilsonIntegralFn_pt_bound L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd v₀ U)
      (inv_nonneg.mpr hlam0_pos.le)
  let Ω : HaarGaugeSpace μ := hφ_abs_mem.toLp φ_abs
  have hΩ_ae : ⇑Ω =ᵐ[μ] φ_abs := hφ_abs_mem.coeFn_toLp
  have hΩ_norm : ‖Ω‖ = 1 := by
    have hsq : ‖Ω‖ ^ 2 = 1 := by
      rw [lp_norm_sq_eq_integral]
      have h1 : (fun U => ‖Ω U‖ ^ 2) =ᵐ[μ] fun U => ‖v₀ U‖ ^ 2 := by
        filter_upwards [hΩ_ae, hv₀_ae] with U hU1 hU2
        change ‖⇑Ω U‖ ^ 2 = ‖⇑v₀ U‖ ^ 2
        rw [hU1, hU2]
        simp [φ_abs]
      rw [MeasureTheory.integral_congr_ae h1, ← lp_norm_sq_eq_integral, hv₀_norm, one_pow]
    have hmul : (‖Ω‖ - 1) * (‖Ω‖ + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg Ω]
  have h_in_Ω_ge : lam0 ≤ (⟪Ω, T Ω⟫_ℂ).re := by
    have hv_in : ⟪v₀, T v₀⟫_ℂ = (lam0 : ℂ) := by
      rw [hv₀_eig, inner_smul_right, inner_self_eq_norm_sq_to_K, hv₀_norm]
      simp [lam0]
    have h_v_int : ⟪v₀, T v₀⟫_ℂ =
        ∫ U, starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hv₀_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
        M_K hM_K hK_bd v₀] with U hU1 hU2
      rw [hU1, hU2, hcinner]
    have h_Ω_int : (⟪Ω, T Ω⟫_ℂ).re =
        ∫ U, ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ ∂μ := by
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪Ω U, (T Ω) U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner _ _
      have h_re := integral_re h_l2
      rw [MeasureTheory.L2.inner_def]
      change RCLike.re (∫ U, ⟪Ω U, (T Ω) U⟫_ℂ ∂μ) = _
      rw [← h_re]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hΩ_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
        M_K hM_K hK_bd Ω] with U hU1 hU2
      change (⟪⇑Ω U, ⇑(T Ω) U⟫_ℂ).re = _
      rw [hU1, hU2, hcinner]
      dsimp [φ_abs, wilsonIntegralFn]
      have h_fn_re : (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ).re =
          ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ := by
        have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω U
        change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ) = _
        rw [← integral_re hi]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hΩ_ae] with U' hU'
        change (((K_W U U' : ℝ) : ℂ) * ⇑Ω U').re = K_W U U' * ‖φ₀ U'‖
        rw [hU']
        simp [φ_abs, Complex.ofReal_re]
      have h_mul_eq : ‖φ₀ U‖ * (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ).re =
          ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ := congrArg (‖φ₀ U‖ * ·) h_fn_re
      simp only [neg_zero, zero_mul, sub_zero]
      exact h_mul_eq
    have h_int_norm1 : MeasureTheory.Integrable
        (fun U => ‖starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U‖) μ := by
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪v₀ U, (T v₀) U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner v₀ (T v₀)
      have h_ae : (fun U => ‖starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U‖) =ᵐ[μ]
          fun U => ‖⟪v₀ U, (T v₀) U⟫_ℂ‖ := by
        filter_upwards [hv₀_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
          M_K hM_K hK_bd v₀] with U hU1 hU2
        rw [← hU1, ← hU2, hcinner]
      exact h_l2.norm.congr h_ae.symm
    have h_int_norm2 : MeasureTheory.Integrable
        (fun U => ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ) μ := by
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪Ω U, (T Ω) U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner Ω (T Ω)
      have h_ae : (fun U => ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ) =ᵐ[μ]
          fun U => (⟪Ω U, (T Ω) U⟫_ℂ).re := by
        filter_upwards [hΩ_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
          M_K hM_K hK_bd Ω] with U hU1 hU2
        change _ = (⟪⇑Ω U, ⇑(T Ω) U⟫_ℂ).re
        rw [hU1, hU2, hcinner]
        dsimp [φ_abs, wilsonIntegralFn]
        have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω U
        simp only [neg_zero, zero_mul, sub_zero]
        congr 1
        change _ = RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ)
        rw [← integral_re hi]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hΩ_ae] with U' hU'
        change _ = (((K_W U U' : ℝ) : ℂ) * ⇑Ω U').re
        rw [hU']
        simp [φ_abs]
      exact h_l2.re.congr h_ae.symm
    have h_pt_le : ∀ U, ‖starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U‖ ≤
        ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ := by
      intro U
      have hconj : ‖starRingEnd ℂ (φ₀ U)‖ = ‖φ₀ U‖ := norm_star _
      rw [norm_mul, hconj]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      dsimp [wilsonIntegralFn]
      calc ‖∫ U', ((K_W U U' : ℝ) : ℂ) * v₀ U' ∂μ‖
          ≤ ∫ U', ‖((K_W U U' : ℝ) : ℂ) * v₀ U'‖ ∂μ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ = ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [hv₀_ae] with U' hU'
            have hb := wilsonKernel_cubic_le L N β hβ K_kin hK_nn M_K hK_bd U U'
            rw [hU', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    have h_abs_le : lam0 ≤ ‖⟪v₀, T v₀⟫_ℂ‖ := by
      rw [hv_in, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0_pos]
    calc lam0 ≤ ‖⟪v₀, T v₀⟫_ℂ‖ := h_abs_le
      _ = ‖∫ U, starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U ∂μ‖ := by rw [h_v_int]
      _ ≤ ∫ U, ‖starRingEnd ℂ (φ₀ U) * wilsonIntegralFn L N β K_kin v₀ U‖ ∂μ :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ U, ‖φ₀ U‖ * ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ ∂μ :=
            MeasureTheory.integral_mono h_int_norm1 h_int_norm2 h_pt_le
      _ = (⟪Ω, T Ω⟫_ℂ).re := h_Ω_int.symm
  have hΩ_eig : T Ω = (lam0 : ℂ) • Ω := by
    have h_in_le : (⟪Ω, T Ω⟫_ℂ).re ≤ lam0 := by
      calc (⟪Ω, T Ω⟫_ℂ).re ≤ ‖⟪Ω, T Ω⟫_ℂ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
        _ ≤ ‖Ω‖ * ‖T Ω‖ := norm_inner_le_norm _ _
        _ ≤ ‖Ω‖ * (‖T‖ * ‖Ω‖) := mul_le_mul_of_nonneg_left (T.le_opNorm Ω) (norm_nonneg _)
        _ = lam0 := by rw [hΩ_norm]; ring
    have h_in_re : (⟪Ω, T Ω⟫_ℂ).re = lam0 := le_antisymm h_in_le h_in_Ω_ge
    have h_in_im : (⟪Ω, T Ω⟫_ℂ).im = 0 := by
      have hconj : starRingEnd ℂ ⟪Ω, T Ω⟫_ℂ = ⟪Ω, T Ω⟫_ℂ := by
        rw [inner_conj_symm, hT_sa]
      exact Complex.conj_eq_iff_im.mp hconj
    have h_in_eq : ⟪Ω, T Ω⟫_ℂ = (lam0 : ℂ) := Complex.ext h_in_re h_in_im
    have h_sq_le : ‖T Ω - (lam0 : ℂ) • Ω‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq (𝕜 := ℂ)]
      have h_re : RCLike.re ⟪T Ω, (lam0 : ℂ) • Ω⟫_ℂ = lam0 ^ 2 := by
        rw [inner_smul_right, hT_sa, h_in_eq]
        simp [pow_two]
      have h_norm_TΩ : ‖T Ω‖ ^ 2 ≤ lam0 ^ 2 := by
        have h1 : ‖T Ω‖ ≤ lam0 := by simpa [hΩ_norm] using T.le_opNorm Ω
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h_norm_lamΩ : ‖(lam0 : ℂ) • Ω‖ ^ 2 = lam0 ^ 2 := by
        rw [norm_smul, hΩ_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0_pos]
      linarith
    have h_zero : ‖T Ω - (lam0 : ℂ) • Ω‖ = 0 :=
      sq_eq_zero_iff.mp (le_antisymm h_sq_le (sq_nonneg _))
    exact sub_eq_zero.mp (norm_eq_zero.mp h_zero)
  let ω : G_L → ℝ := fun U => lam0⁻¹ * (wilsonIntegralFn L N β K_kin Ω U).re
  have hω_cont : Continuous ω :=
    continuous_const.mul
      (Complex.continuous_re.comp
        (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω))
  have hΩ_im_zero : ∀ U, (wilsonIntegralFn L N β K_kin Ω U).im = 0 := by
    intro U
    have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω U
    dsimp [wilsonIntegralFn]
    have h1 : (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ).im =
        RCLike.re (-Complex.I * ∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ) := by
      simp [Complex.mul_re]
    rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (hi.const_mul (-Complex.I))]
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    filter_upwards [hΩ_ae] with U' hU'
    change RCLike.re (-Complex.I * (((K_W U U' : ℝ) : ℂ) * ⇑Ω U')) = 0
    rw [hU']
    simp [φ_abs, Complex.mul_re]
  have hΩ_ae_ω : ⇑Ω =ᵐ[μ] fun U => (ω U : ℂ) := by
    have h_eq : Ω = ((lam0⁻¹ : ℝ) : ℂ) • T Ω := by
      rw [hΩ_eig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
        Complex.ofReal_one, one_smul]
    have h1 : ⇑Ω =ᵐ[μ] ((lam0⁻¹ : ℝ) : ℂ) • ⇑(T Ω) := by
      conv_lhs => rw [h_eq]
      exact MeasureTheory.Lp.coeFn_smul _ _
    filter_upwards [h1, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
      M_K hM_K hK_bd Ω] with U hU1 hU2
    change ⇑Ω U = (ω U : ℂ)
    rw [hU1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hU2]
    have him := hΩ_im_zero U
    have h_fn : wilsonIntegralFn L N β K_kin Ω U =
        ((wilsonIntegralFn L N β K_kin Ω U).re : ℂ) := Complex.ext rfl him
    rw [h_fn]
    dsimp [ω]; push_cast; rfl
  have hω_nonneg : ∀ U, 0 ≤ ω U := by
    intro U
    have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω U
    have h_re_eq : (wilsonIntegralFn L N β K_kin Ω U).re = ∫ U', K_W U U' * ‖φ₀ U'‖ ∂μ := by
      dsimp [wilsonIntegralFn]
      change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ) = _
      rw [← integral_re hi]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hΩ_ae] with U' hU'
      change (((K_W U U' : ℝ) : ℂ) * ⇑Ω U').re = K_W U U' * ‖φ₀ U'‖
      rw [hU']; simp [φ_abs, Complex.ofReal_re]
    dsimp [ω]
    rw [h_re_eq]
    exact mul_nonneg (inv_nonneg.mpr hlam0_pos.le)
      (MeasureTheory.integral_nonneg fun U' =>
        mul_nonneg (hc_W_pos.le.trans (hKW_lb U U')) (norm_nonneg _))
  have hω_pos : ∀ U, 0 < ω U := by
    intro U
    have h_ne0 : ∃ U₀ : G_L, ω U₀ ≠ 0 := by
      by_contra h_all
      push_neg at h_all
      have hΩ_zero : Ω = 0 := by
        apply MeasureTheory.Lp.ext
        filter_upwards [hΩ_ae_ω, MeasureTheory.Lp.coeFn_zero ℂ 2 μ] with W hW1 hW2
        rw [hW1, h_all W, Complex.ofReal_zero, hW2]; rfl
      rw [hΩ_zero, norm_zero] at hΩ_norm
      norm_num at hΩ_norm
    rcases h_ne0 with ⟨U₀, hU₀_ne⟩
    have hU₀_pos : 0 < ω U₀ := lt_of_le_of_ne (hω_nonneg U₀) (Ne.symm hU₀_ne)
    let B : Set G_L := { W | ω U₀ / 2 < ω W }
    have hB_open : IsOpen B := isOpen_lt continuous_const hω_cont
    have hB_ne : B.Nonempty := ⟨U₀, by dsimp [B]; linarith⟩
    have hB_pos : 0 < μ.real B := by
      have hm_pos := hB_open.measure_pos μ hB_ne
      exact ENNReal.toReal_pos hm_pos.ne' (MeasureTheory.measure_ne_top μ B)
    have h_int_pos : 0 < ∫ U', K_W U U' * ω U' ∂μ := by
      let δ_lb : ℝ := c_W * (ω U₀ / 2)
      have hδ_lb_pos : 0 < δ_lb := mul_pos hc_W_pos (by linarith)
      have h_int_Kω : MeasureTheory.Integrable (fun U' => K_W U U' * ω U') μ :=
        integrable_of_continuous_compact μ _
          ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul hω_cont)
      have h_ind_int : MeasureTheory.Integrable (Set.indicator B (fun _ => δ_lb)) μ :=
        (MeasureTheory.integrable_const δ_lb).indicator hB_open.measurableSet
      have h_le_ind : ∀ U', Set.indicator B (fun _ => δ_lb) U' ≤ K_W U U' * ω U' := by
        intro U'
        rw [Set.indicator_apply]
        by_cases hU' : U' ∈ B
        · rw [if_pos hU']
          exact mul_le_mul (hKW_lb U U') (le_of_lt hU') (by linarith)
            (hc_W_pos.le.trans (hKW_lb U U'))
        · rw [if_neg hU']
          exact mul_nonneg (hc_W_pos.le.trans (hKW_lb U U')) (hω_nonneg U')
      have h_int_val : ∫ U', Set.indicator B (fun _ => δ_lb) U' ∂μ = μ.real B * δ_lb := by
        rw [MeasureTheory.integral_indicator hB_open.measurableSet, MeasureTheory.setIntegral_const]
        simp [smul_eq_mul]
      calc 0 < μ.real B * δ_lb := mul_pos hB_pos hδ_lb_pos
        _ = ∫ U', Set.indicator B (fun _ => δ_lb) U' ∂μ := h_int_val.symm
        _ ≤ ∫ U', K_W U U' * ω U' ∂μ := MeasureTheory.integral_mono h_ind_int h_int_Kω h_le_ind
    have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd Ω U
    have h_re_eq : (wilsonIntegralFn L N β K_kin Ω U).re = ∫ U', K_W U U' * ω U' ∂μ := by
      dsimp [wilsonIntegralFn]
      change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * Ω U' ∂μ) = _
      rw [← integral_re hi]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hΩ_ae_ω] with U' hU'
      change (((K_W U U' : ℝ) : ℂ) * ⇑Ω U').re = K_W U U' * ω U'
      rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
    dsimp [ω]
    rw [h_re_eq]
    exact mul_pos (inv_pos.mpr hlam0_pos) h_int_pos
  have h_simple : ∀ w : HaarGaugeSpace μ,
      T w = (lam0 : ℂ) • w → ⟪w, Ω⟫_ℂ = 0 → w = 0 := by
    intro w hw_eig hw_orth
    by_contra hw_ne
    let ψ_c : G_L → ℂ := fun U => ((lam0⁻¹ : ℝ) : ℂ) * wilsonIntegralFn L N β K_kin w U
    have hψ_cont : Continuous ψ_c :=
      continuous_const.mul (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd w)
    have hw_ae : ⇑w =ᵐ[μ] ψ_c := by
      have h_eq : w = ((lam0⁻¹ : ℝ) : ℂ) • T w := by
        rw [hw_eig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
          Complex.ofReal_one, one_smul]
      have h1 : ⇑w =ᵐ[μ] ((lam0⁻¹ : ℝ) : ℂ) • ⇑(T w) := by
        conv_lhs => rw [h_eq]
        exact MeasureTheory.Lp.coeFn_smul _ _
      filter_upwards [h1, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
        M_K hM_K hK_bd w] with U hU1 hU2
      change ⇑w U = ψ_c U
      rw [hU1]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hU2]
    have h_ae_eig : (fun U => wilsonIntegralFn L N β K_kin w U) =ᵐ[μ]
        (fun U => (lam0 : ℂ) * ψ_c U) := by
      have h1 : ⇑(T w) =ᵐ[μ] ⇑((lam0 : ℂ) • w) := by rw [hw_eig]
      have h2 := MeasureTheory.Lp.coeFn_smul (lam0 : ℂ) w
      filter_upwards [wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd w,
        h1, h2, hw_ae] with U hUT hT1 hSm hUψ
      change wilsonIntegralFn L N β K_kin w U = (lam0 : ℂ) * ψ_c U
      rw [← hUT, hT1]
      change ⇑((lam0 : ℂ) • w) U = _
      rw [hSm]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hUψ]
    have h_all_eig : ∀ U, wilsonIntegralFn L N β K_kin w U = (lam0 : ℂ) * ψ_c U :=
      eq_of_ae_continuous μ
        (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd w)
        (continuous_const.mul hψ_cont) h_ae_eig
    let u : G_L → ℝ := fun U => (ψ_c U).re
    let v_im : G_L → ℝ := fun U => (ψ_c U).im
    have hu_cont : Continuous u := Complex.continuous_re.comp hψ_cont
    have hv_cont : Continuous v_im := Complex.continuous_im.comp hψ_cont
    have h_u_eig : ∀ U, ∫ U', K_W U U' * u U' ∂μ = lam0 * u U := by
      intro U
      have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd w U
      have h_eq := congrArg Complex.re (h_all_eig U)
      dsimp [wilsonIntegralFn] at h_eq
      simp only [zero_mul, sub_zero] at h_eq
      change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * w U' ∂μ) = lam0 * u U at h_eq
      rw [← integral_re hi] at h_eq
      have h_lhs : ∫ U', RCLike.re (((K_W U U' : ℝ) : ℂ) * w U') ∂μ =
          ∫ U', K_W U U' * u U' ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hw_ae] with U' hU'
        change (((K_W U U' : ℝ) : ℂ) * ⇑w U').re = K_W U U' * u U'
        rw [hU']
        simp [u, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rwa [h_lhs] at h_eq
    have h_v_eig : ∀ U, ∫ U', K_W U U' * v_im U' ∂μ = lam0 * v_im U := by
      intro U
      have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd w U
      have h_eq := congrArg Complex.im (h_all_eig U)
      dsimp [wilsonIntegralFn] at h_eq
      have him_l : (∫ U', ((K_W U U' : ℝ) : ℂ) * w U' ∂μ).im =
          RCLike.re (-Complex.I * ∫ U', ((K_W U U' : ℝ) : ℂ) * w U' ∂μ) := by
        simp [Complex.mul_re]
      rw [him_l, ← MeasureTheory.integral_const_mul,
        ← integral_re (hi.const_mul (-Complex.I))] at h_eq
      have h_ae : (fun U' => RCLike.re (-Complex.I * (((K_W U U' : ℝ) : ℂ) * w U'))) =ᵐ[μ]
          fun U' => K_W U U' * v_im U' := by
        filter_upwards [hw_ae] with U' hU'
        rw [hU']
        change (-Complex.I * (((K_W U U' : ℝ) : ℂ) * ψ_c U')).re = K_W U U' * v_im U'
        simp [v_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [MeasureTheory.integral_congr_ae h_ae] at h_eq
      simpa [v_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using h_eq
    have h_no_eig_real : ∀ (f : G_L → ℝ), Continuous f →
        (∀ U, ∫ U', K_W U U' * f U' ∂μ = lam0 * f U) →
        (∫ U, f U * ω U ∂μ = 0) → (∀ U, f U = 0) := by
      intro f hf_cont hf_eig hf_orth
      by_contra hf_ne
      push_neg at hf_ne
      rcases hf_ne with ⟨U_star, hU_star⟩
      have h_pos_set : ∃ U₁ : G_L, 0 < f U₁ := by
        by_contra h_le
        push_neg at h_le
        have h_neg_or_zero : ∀ U, f U * ω U ≤ 0 := fun U =>
          mul_nonpos_of_nonpos_of_nonneg (h_le U) (hω_pos U).le
        have hU_lt : f U_star < 0 := lt_of_le_of_ne (h_le U_star) hU_star
        let B_neg : Set G_L := { U | f U * ω U < (f U_star * ω U_star) / 2 }
        have hB_open : IsOpen B_neg := isOpen_lt (hf_cont.mul hω_cont) continuous_const
        have hB_ne : B_neg.Nonempty := ⟨U_star, by
          dsimp [B_neg]
          have hmul : f U_star * ω U_star < 0 := mul_neg_of_neg_of_pos hU_lt (hω_pos U_star)
          linarith⟩
        have hB_pos : 0 < μ.real B_neg :=
          ENNReal.toReal_pos (hB_open.measure_pos μ hB_ne).ne' (MeasureTheory.measure_ne_top μ B_neg)
        have h_cont_int : MeasureTheory.Integrable (fun U => f U * ω U) μ :=
          integrable_of_continuous_compact μ _ (hf_cont.mul hω_cont)
        have h_ind_int : MeasureTheory.Integrable
            (Set.indicator B_neg (fun _ => -(f U_star * ω U_star) / 2)) μ :=
          (MeasureTheory.integrable_const _).indicator hB_open.measurableSet
        have h_le_neg : ∀ U, Set.indicator B_neg (fun _ => -(f U_star * ω U_star) / 2) U ≤
            -(f U * ω U) := by
          intro U
          rw [Set.indicator_apply]
          by_cases hU : U ∈ B_neg
          · rw [if_pos hU]; dsimp [B_neg] at hU; linarith
          · rw [if_neg hU]; linarith [h_neg_or_zero U]
        have h_int_neg : 0 < ∫ U, -(f U * ω U) ∂μ := by
          have hc_pos : 0 < -(f U_star * ω U_star) / 2 := by
            have hmul : f U_star * ω U_star < 0 := mul_neg_of_neg_of_pos hU_lt (hω_pos U_star)
            linarith
          have h_val : ∫ U, Set.indicator B_neg (fun _ => -(f U_star * ω U_star) / 2) U ∂μ =
              μ.real B_neg * (-(f U_star * ω U_star) / 2) := by
            rw [MeasureTheory.integral_indicator hB_open.measurableSet, MeasureTheory.setIntegral_const]
            simp [smul_eq_mul]
          calc 0 < μ.real B_neg * (-(f U_star * ω U_star) / 2) := mul_pos hB_pos hc_pos
            _ = ∫ U, Set.indicator B_neg (fun _ => -(f U_star * ω U_star) / 2) U ∂μ := h_val.symm
            _ ≤ ∫ U, -(f U * ω U) ∂μ := MeasureTheory.integral_mono h_ind_int h_cont_int.neg h_le_neg
        rw [MeasureTheory.integral_neg, hf_orth, neg_zero] at h_int_neg
        exact lt_irrefl 0 h_int_neg
      have h_neg_set : ∃ U₂ : G_L, f U₂ < 0 := by
        by_contra h_ge
        push_neg at h_ge
        rcases h_pos_set with ⟨U₁, hU₁⟩
        let B_pos : Set G_L := { U | (f U₁ * ω U₁) / 2 < f U * ω U }
        have hB_open : IsOpen B_pos := isOpen_lt continuous_const (hf_cont.mul hω_cont)
        have hB_ne : B_pos.Nonempty := ⟨U₁, by
          dsimp [B_pos]
          have hmul : 0 < f U₁ * ω U₁ := mul_pos hU₁ (hω_pos U₁)
          linarith⟩
        have hB_pos : 0 < μ.real B_pos :=
          ENNReal.toReal_pos (hB_open.measure_pos μ hB_ne).ne' (MeasureTheory.measure_ne_top μ B_pos)
        have h_cont_int : MeasureTheory.Integrable (fun U => f U * ω U) μ :=
          integrable_of_continuous_compact μ _ (hf_cont.mul hω_cont)
        have h_ind_int : MeasureTheory.Integrable
            (Set.indicator B_pos (fun _ => (f U₁ * ω U₁) / 2)) μ :=
          (MeasureTheory.integrable_const _).indicator hB_open.measurableSet
        have h_le_pos : ∀ U, Set.indicator B_pos (fun _ => (f U₁ * ω U₁) / 2) U ≤ f U * ω U := by
          intro U
          rw [Set.indicator_apply]
          by_cases hU : U ∈ B_pos
          · rw [if_pos hU]; exact (hU : _ < _).le
          · rw [if_neg hU]; exact mul_nonneg (h_ge U) (hω_pos U).le
        have h_int_pos : 0 < ∫ U, f U * ω U ∂μ := by
          have hc_pos : 0 < (f U₁ * ω U₁) / 2 := mul_pos (mul_pos hU₁ (hω_pos U₁)) (by norm_num)
          have h_val : ∫ U, Set.indicator B_pos (fun _ => (f U₁ * ω U₁) / 2) U ∂μ =
              μ.real B_pos * ((f U₁ * ω U₁) / 2) := by
            rw [MeasureTheory.integral_indicator hB_open.measurableSet, MeasureTheory.setIntegral_const]
            simp [smul_eq_mul]
          calc 0 < μ.real B_pos * ((f U₁ * ω U₁) / 2) := mul_pos hB_pos hc_pos
            _ = ∫ U, Set.indicator B_pos (fun _ => (f U₁ * ω U₁) / 2) U ∂μ := h_val.symm
            _ ≤ ∫ U, f U * ω U ∂μ := MeasureTheory.integral_mono h_ind_int h_cont_int h_le_pos
        rw [hf_orth] at h_int_pos
        exact lt_irrefl 0 h_int_pos
      rcases h_pos_set with ⟨U₁, hU₁⟩
      rcases h_neg_set with ⟨U₂, hU₂⟩
      let f_abs : G_L → ℝ := fun U => |f U|
      have hf_abs_cont : Continuous f_abs := continuous_abs.comp hf_cont
      let f_mem := memLp_of_continuous_compact μ f hf_cont
      let f_abs_mem := memLp_of_continuous_compact μ f_abs hf_abs_cont
      let f_Lp : HaarGaugeSpace μ := f_mem.toLp (fun U => (f U : ℂ))
      let f_abs_Lp : HaarGaugeSpace μ := f_abs_mem.toLp (fun U => (f_abs U : ℂ))
      have hf_ae := f_mem.coeFn_toLp
      have hf_abs_ae := f_abs_mem.coeFn_toLp
      have hf_norm_sq : ‖f_abs_Lp‖ ^ 2 = ∫ U, f U * f U ∂μ := by
        rw [lp_norm_sq_eq_integral]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hf_abs_ae] with U hU
        change ‖⇑f_abs_Lp U‖ ^ 2 = f U * f U
        rw [hU, Complex.norm_real, Real.norm_eq_abs, abs_abs, sq_abs, sq]
      have hf_in_val : (⟪f_Lp, T f_Lp⟫_ℂ).re =
          ∫ U, ∫ U', K_W U U' * (f U * f U') ∂μ ∂μ := by
        have h_l2 : MeasureTheory.Integrable (fun U => ⟪f_Lp U, (T f_Lp) U⟫_ℂ) μ :=
          MeasureTheory.L2.integrable_inner f_Lp (T f_Lp)
        have h_re := integral_re h_l2
        rw [MeasureTheory.L2.inner_def]
        change RCLike.re (∫ U, ⟪f_Lp U, (T f_Lp) U⟫_ℂ ∂μ) = _
        rw [← h_re]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hf_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
          M_K hM_K hK_bd f_Lp] with U hU1 hU2
        change (⟪⇑f_Lp U, ⇑(T f_Lp) U⟫_ℂ).re = _
        rw [hU1, hU2, hcinner]
        have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd f_Lp U
        dsimp [wilsonIntegralFn]
        simp only [neg_zero, zero_mul, sub_zero]
        have h_re_u : (∫ U', ((K_W U U' : ℝ) : ℂ) * f_Lp U' ∂μ).re =
            ∫ U', K_W U U' * f U' ∂μ := by
          change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * f_Lp U' ∂μ) = _
          rw [← integral_re hi]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hf_ae] with U' hU'
          change (((K_W U U' : ℝ) : ℂ) * ⇑f_Lp U').re = K_W U U' * f U'
          rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [h_re_u, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
          dsimp only; ring)
      have hf_abs_in_val : (⟪f_abs_Lp, T f_abs_Lp⟫_ℂ).re =
          ∫ U, ∫ U', K_W U U' * (|f U| * |f U'|) ∂μ ∂μ := by
        have h_l2 : MeasureTheory.Integrable (fun U => ⟪f_abs_Lp U, (T f_abs_Lp) U⟫_ℂ) μ :=
          MeasureTheory.L2.integrable_inner f_abs_Lp (T f_abs_Lp)
        have h_re := integral_re h_l2
        rw [MeasureTheory.L2.inner_def]
        change RCLike.re (∫ U, ⟪f_abs_Lp U, (T f_abs_Lp) U⟫_ℂ ∂μ) = _
        rw [← h_re]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hf_abs_ae, wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn
          M_K hM_K hK_bd f_abs_Lp] with U hU1 hU2
        change (⟪⇑f_abs_Lp U, ⇑(T f_abs_Lp) U⟫_ℂ).re = _
        rw [hU1, hU2, hcinner]
        have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd f_abs_Lp U
        dsimp [wilsonIntegralFn]
        simp only [neg_zero, zero_mul, sub_zero]
        have h_re_u : (∫ U', ((K_W U U' : ℝ) : ℂ) * f_abs_Lp U' ∂μ).re =
            ∫ U', K_W U U' * |f U'| ∂μ := by
          change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * f_abs_Lp U' ∂μ) = _
          rw [← integral_re hi]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hf_abs_ae] with U' hU'
          change (((K_W U U' : ℝ) : ℂ) * ⇑f_abs_Lp U').re = K_W U U' * |f U'|
          rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [h_re_u, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
          dsimp only [f_abs]; ring)
      have hf_in_eq : (⟪f_Lp, T f_Lp⟫_ℂ).re = lam0 * ∫ U, f U * f U ∂μ := by
        rw [hf_in_val]
        have h_row : ∀ U, ∫ U', K_W U U' * (f U * f U') ∂μ = lam0 * (f U * f U) := by
          intro U
          rw [show (fun U' => K_W U U' * (f U * f U')) = fun U' => f U * (K_W U U' * f U') by
            funext U'; ring]
          rw [MeasureTheory.integral_const_mul, hf_eig U]
          ring
        simp_rw [h_row, MeasureTheory.integral_const_mul]
      have hf_abs_in_le : (⟪f_abs_Lp, T f_abs_Lp⟫_ℂ).re ≤ lam0 * ∫ U, f U * f U ∂μ := by
        rw [← hf_norm_sq]
        calc (⟪f_abs_Lp, T f_abs_Lp⟫_ℂ).re ≤ ‖⟪f_abs_Lp, T f_abs_Lp⟫_ℂ‖ :=
              (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ ≤ ‖f_abs_Lp‖ * ‖T f_abs_Lp‖ := norm_inner_le_norm _ _
          _ ≤ ‖f_abs_Lp‖ * (lam0 * ‖f_abs_Lp‖) :=
              mul_le_mul_of_nonneg_left (T.le_opNorm f_abs_Lp) (norm_nonneg _)
          _ = lam0 * ‖f_abs_Lp‖ ^ 2 := by ring
      let Δ_row : G_L → ℝ := fun U => ∫ U', K_W U U' * (|f U| * |f U'| - f U * f U') ∂μ
      have h_row_cont1 : Continuous (fun U => ∫ U', K_W U U' * (|f U| * |f U'|) ∂μ) := by
        have h_eq : (fun U => ∫ U', K_W U U' * (|f U| * |f U'|) ∂μ) =
            fun U => |f U| * (wilsonIntegralFn L N β K_kin f_abs_Lp U).re := by
          funext U
          have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn M_K hK_bd f_abs_Lp U
          have h_re_u : (wilsonIntegralFn L N β K_kin f_abs_Lp U).re =
              ∫ U', K_W U U' * |f U'| ∂μ := by
            dsimp [wilsonIntegralFn]
            change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * f_abs_Lp U' ∂μ) = _
            rw [← integral_re hi]
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [hf_abs_ae] with U' hU'
            change (((K_W U U' : ℝ) : ℂ) * ⇑f_abs_Lp U').re = K_W U U' * |f U'|
            rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
          rw [h_re_u, ← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
            dsimp only; ring)
        rw [h_eq]
        exact hf_abs_cont.mul (Complex.continuous_re.comp
          (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn M_K hK_bd f_abs_Lp))
      have h_row_cont2 : Continuous (fun U => ∫ U', K_W U U' * (f U * f U') ∂μ) := by
        have h_eq : (fun U => ∫ U', K_W U U' * (f U * f U') ∂μ) =
            fun U => f U * (lam0 * f U) := by
          funext U
          rw [show (fun U' => K_W U U' * (f U * f U')) = fun U' => f U * (K_W U U' * f U') by
            funext U'; ring, MeasureTheory.integral_const_mul, hf_eig U]
        rw [h_eq]
        exact hf_cont.mul (continuous_const.mul hf_cont)
      have hΔ_int_eq : ∫ U, Δ_row U ∂μ =
          (⟪f_abs_Lp, T f_abs_Lp⟫_ℂ).re - (⟪f_Lp, T f_Lp⟫_ℂ).re := by
        have h_sub_row : ∀ U, Δ_row U =
            (∫ U', K_W U U' * (|f U| * |f U'|) ∂μ) -
              (∫ U', K_W U U' * (f U * f U') ∂μ) := by
          intro U
          have hi1 : MeasureTheory.Integrable (fun U' => K_W U U' * (|f U| * |f U'|)) μ :=
            integrable_of_continuous_compact μ _
              ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul
                (continuous_const.mul hf_abs_cont))
          have hi2 : MeasureTheory.Integrable (fun U' => K_W U U' * (f U * f U')) μ :=
            integrable_of_continuous_compact μ _
              ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul
                (continuous_const.mul hf_cont))
          dsimp [Δ_row]
          rw [← MeasureTheory.integral_sub hi1 hi2]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
            dsimp only; ring)
        simp_rw [h_sub_row]
        rw [MeasureTheory.integral_sub
          (integrable_of_continuous_compact μ _ h_row_cont1)
          (integrable_of_continuous_compact μ _ h_row_cont2),
          hf_abs_in_val, hf_in_val]
      have hΔ_le_zero : ∫ U, Δ_row U ∂μ ≤ 0 := by linarith
      let B₁ : Set G_L := { U | f U₁ / 2 < f U }
      let B₂ : Set G_L := { U' | (-f U₂) / 2 < -f U' }
      have hB₁_open : IsOpen B₁ := isOpen_lt continuous_const hf_cont
      have hB₂_open : IsOpen B₂ := isOpen_lt continuous_const hf_cont.neg
      have hB₁_pos : 0 < μ.real B₁ :=
        ENNReal.toReal_pos
          (hB₁_open.measure_pos μ ⟨U₁, by change f U₁ / 2 < f U₁; linarith⟩).ne'
          (MeasureTheory.measure_ne_top μ B₁)
      have hB₂_pos : 0 < μ.real B₂ :=
        ENNReal.toReal_pos
          (hB₂_open.measure_pos μ ⟨U₂, by change (-f U₂) / 2 < -f U₂; linarith⟩).ne'
          (MeasureTheory.measure_ne_top μ B₂)
      let δ₀ : ℝ := c_W * (f U₁ * (-f U₂) / 2)
      have hδ₀_pos : 0 < δ₀ := mul_pos hc_W_pos (by nlinarith)
      have hΔ_nonneg : ∀ U, 0 ≤ Δ_row U := fun U =>
        MeasureTheory.integral_nonneg fun U' => by
          have h_le : f U * f U' ≤ |f U| * |f U'| := by rw [← abs_mul]; exact le_abs_self _
          exact mul_nonneg (hc_W_pos.le.trans (hKW_lb U U')) (sub_nonneg.mpr h_le)
      have hΔ_B₁ : ∀ U ∈ B₁, δ₀ * μ.real B₂ ≤ Δ_row U := by
        intro U hU
        have hiΔ : MeasureTheory.Integrable (fun U' => K_W U U' * (|f U| * |f U'| - f U * f U')) μ :=
          integrable_of_continuous_compact μ _
            ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul
              ((continuous_const.mul hf_abs_cont).sub (continuous_const.mul hf_cont)))
        have h_ind_int : MeasureTheory.Integrable (Set.indicator B₂ (fun _ => δ₀)) μ :=
          (MeasureTheory.integrable_const δ₀).indicator hB₂_open.measurableSet
        have h_le_ind : ∀ U', Set.indicator B₂ (fun _ => δ₀) U' ≤
            K_W U U' * (|f U| * |f U'| - f U * f U') := by
          intro U'
          rw [Set.indicator_apply]
          by_cases hU' : U' ∈ B₂
          · rw [if_pos hU']
            have hfu : f U₁ / 2 < f U := hU
            have hfu' : (-f U₂) / 2 < -f U' := hU'
            have hfu_pos : 0 < f U := by linarith
            have hfu'_neg : f U' < 0 := by linarith
            have h_diff_eq : |f U| * |f U'| - f U * f U' = 2 * f U * (-f U') := by
              rw [abs_of_pos hfu_pos, abs_of_neg hfu'_neg]; ring
            have h_diff_ge : f U₁ * (-f U₂) / 2 ≤ |f U| * |f U'| - f U * f U' := by
              rw [h_diff_eq]; nlinarith
            exact mul_le_mul (hKW_lb U U') h_diff_ge (by nlinarith) (hc_W_pos.le.trans (hKW_lb U U'))
          · rw [if_neg hU']
            have h_le : f U * f U' ≤ |f U| * |f U'| := by rw [← abs_mul]; exact le_abs_self _
            exact mul_nonneg (hc_W_pos.le.trans (hKW_lb U U')) (sub_nonneg.mpr h_le)
        have h_val : ∫ U', Set.indicator B₂ (fun _ => δ₀) U' ∂μ = μ.real B₂ * δ₀ := by
          rw [MeasureTheory.integral_indicator hB₂_open.measurableSet, MeasureTheory.setIntegral_const]
          simp [smul_eq_mul]
        calc δ₀ * μ.real B₂ = μ.real B₂ * δ₀ := by ring
          _ = ∫ U', Set.indicator B₂ (fun _ => δ₀) U' ∂μ := h_val.symm
          _ ≤ Δ_row U := MeasureTheory.integral_mono h_ind_int hiΔ h_le_ind
      have hΔ_cont : Continuous Δ_row := by
        have h_eq : Δ_row = fun U =>
            (∫ U', K_W U U' * (|f U| * |f U'|) ∂μ) - (∫ U', K_W U U' * (f U * f U') ∂μ) := by
          funext U
          have hi1 : MeasureTheory.Integrable (fun U' => K_W U U' * (|f U| * |f U'|)) μ :=
            integrable_of_continuous_compact μ _
              ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul
                (continuous_const.mul hf_abs_cont))
          have hi2 : MeasureTheory.Integrable (fun U' => K_W U U' * (f U * f U')) μ :=
            integrable_of_continuous_compact μ _
              ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U).mul
                (continuous_const.mul hf_cont))
          dsimp [Δ_row]
          rw [← MeasureTheory.integral_sub hi1 hi2]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U' => by
            dsimp only; ring)
        rw [h_eq]
        exact h_row_cont1.sub h_row_cont2
      have h_int_pos : 0 < ∫ U, Δ_row U ∂μ := by
        have h_ind_int : MeasureTheory.Integrable (Set.indicator B₁ (fun _ => δ₀ * μ.real B₂)) μ :=
          (MeasureTheory.integrable_const _).indicator hB₁_open.measurableSet
        have h_le_ind : ∀ U, Set.indicator B₁ (fun _ => δ₀ * μ.real B₂) U ≤ Δ_row U := by
          intro U
          rw [Set.indicator_apply]
          by_cases hU : U ∈ B₁
          · rw [if_pos hU]; exact hΔ_B₁ U hU
          · rw [if_neg hU]; exact hΔ_nonneg U
        have h_val : ∫ U, Set.indicator B₁ (fun _ => δ₀ * μ.real B₂) U ∂μ =
            μ.real B₁ * (δ₀ * μ.real B₂) := by
          rw [MeasureTheory.integral_indicator hB₁_open.measurableSet, MeasureTheory.setIntegral_const]
          simp [smul_eq_mul]
        calc 0 < μ.real B₁ * (δ₀ * μ.real B₂) := mul_pos hB₁_pos (mul_pos hδ₀_pos hB₂_pos)
          _ = ∫ U, Set.indicator B₁ (fun _ => δ₀ * μ.real B₂) U ∂μ := h_val.symm
          _ ≤ ∫ U, Δ_row U ∂μ :=
              MeasureTheory.integral_mono h_ind_int (integrable_of_continuous_compact μ _ hΔ_cont) h_le_ind
      linarith
    have hw_orth_u : ∫ U, u U * ω U ∂μ = 0 := by
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪w U, Ω U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner w Ω
      have h_re := integral_re h_l2
      have h0 : (⟪w, Ω⟫_ℂ).re = 0 := by rw [hw_orth, Complex.zero_re]
      rw [MeasureTheory.L2.inner_def] at h0
      change RCLike.re (∫ U, ⟪w U, Ω U⟫_ℂ ∂μ) = 0 at h0
      rw [← h_re] at h0
      have h_ae : (fun U => (⟪w U, Ω U⟫_ℂ).re) =ᵐ[μ] fun U => u U * ω U := by
        filter_upwards [hw_ae, hΩ_ae_ω] with U hU1 hU2
        change (⟪⇑w U, ⇑Ω U⟫_ℂ).re = u U * ω U
        rw [hU1, hU2, hcinner]
        simp [u, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      have h_ae' : (fun U => RCLike.re ⟪w U, Ω U⟫_ℂ) =ᵐ[μ] fun U => u U * ω U := h_ae
      rwa [MeasureTheory.integral_congr_ae h_ae'] at h0
    have hw_orth_v : ∫ U, v_im U * ω U ∂μ = 0 := by
      have h_l2 : MeasureTheory.Integrable (fun U => ⟪w U, Ω U⟫_ℂ) μ :=
        MeasureTheory.L2.integrable_inner w Ω
      have h0 : (⟪w, Ω⟫_ℂ).im = 0 := by rw [hw_orth, Complex.zero_im]
      rw [MeasureTheory.L2.inner_def] at h0
      have h1 : (∫ U, ⟪w U, Ω U⟫_ℂ ∂μ).im =
          RCLike.re (-Complex.I * ∫ U, ⟪w U, Ω U⟫_ℂ ∂μ) := by
        simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (h_l2.const_mul (-Complex.I))] at h0
      have h_ae : (fun U => RCLike.re (-Complex.I * ⟪w U, Ω U⟫_ℂ)) =ᵐ[μ]
          fun U => -(v_im U * ω U) := by
        filter_upwards [hw_ae, hΩ_ae_ω] with U hU1 hU2
        change (-Complex.I * ⟪⇑w U, ⇑Ω U⟫_ℂ).re = -(v_im U * ω U)
        rw [hU1, hU2, hcinner]
        simp [v_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      rw [MeasureTheory.integral_congr_ae h_ae, MeasureTheory.integral_neg] at h0
      linarith
    have hu_zero := h_no_eig_real u hu_cont h_u_eig hw_orth_u
    have hv_zero := h_no_eig_real v_im hv_cont h_v_eig hw_orth_v
    apply hw_ne
    apply MeasureTheory.Lp.ext
    filter_upwards [hw_ae, MeasureTheory.Lp.coeFn_zero ℂ 2 μ] with U hU1 hU2
    change ⇑w U = ⇑(0 : HaarGaugeSpace μ) U
    rw [hU1, hU2]
    exact Complex.ext (hu_zero U) (hv_zero U)
  have hΩ_gauge : ∀ g, cubicGaugeRep L N g Ω = Ω := by
    intro g
    let U_g := cubicGaugeRep L N g
    have h_comm := wilsonIntegralOp_gauge_inv L N β hβ K_kin hK_cont hK_nn hK_inv
      M_K hM_K hK_bd g
    have hUg_eig : T (U_g Ω) = (lam0 : ℂ) • (U_g Ω) := by
      have hcomp := congrArg (fun f : HaarGaugeSpace μ →L[ℂ] HaarGaugeSpace μ => f Ω) h_comm
      change U_g (T Ω) = T (U_g Ω) at hcomp
      rw [← hcomp, hΩ_eig, map_smul]
    let c_g : ℂ := ⟪Ω, U_g Ω⟫_ℂ
    let w_g : HaarGaugeSpace μ := U_g Ω - c_g • Ω
    have hw_orth : ⟪w_g, Ω⟫_ℂ = 0 := by
      have h1 : ⟪Ω, Ω⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ_norm]; norm_num
      simp only [w_g, c_g, inner_sub_left, inner_smul_left, h1, mul_one,
        inner_conj_symm, sub_self]
    have hw_eig : T w_g = (lam0 : ℂ) • w_g := by
      simp only [w_g, map_sub, map_smul, hUg_eig, hΩ_eig, smul_sub]
      rw [smul_comm]
    have hw_zero : w_g = 0 := h_simple w_g hw_eig hw_orth
    have hUg_smul : U_g Ω = c_g • Ω := sub_eq_zero.mp hw_zero
    have hc_norm : ‖c_g‖ = 1 := by
      have hn : ‖c_g • Ω‖ = 1 := by
        rw [← hUg_smul]
        have hsq : ‖U_g Ω‖ ^ 2 = 1 := by
          have hin : (⟪U_g Ω, U_g Ω⟫_ℂ).re = 1 := by
            rw [cubicGaugeRep_unitary, inner_self_eq_norm_sq_to_K, hΩ_norm]
            norm_num
          rw [inner_self_eq_norm_sq_to_K] at hin
          simp [pow_two] at hin
          linarith
        have hmul : (‖U_g Ω‖ - 1) * (‖U_g Ω‖ + 1) = 0 := by linarith
        rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg (U_g Ω)]
      rwa [norm_smul, hΩ_norm, mul_one] at hn
    let eqv := gaugeActEquiv L N (fun x => (g x)⁻¹)
    have hmp : MeasureTheory.MeasurePreserving eqv μ μ :=
      ⟨eqv.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (g x)⁻¹)⟩
    have hΩ_g_ae : ⇑(U_g Ω) =ᵐ[μ] fun U => (ω (eqv U) : ℂ) := by
      have h1 := cubicGaugeRep_apply_ae L N g Ω
      have h2 := ae_comp_measurePreserving hmp hΩ_ae_ω
      filter_upwards [h1, h2] with U hu1 hu2
      change ⇑(U_g Ω) U = (ω (eqv U) : ℂ)
      rw [hu1]
      exact hu2
    have hc_int_ae : (fun U => ⟪Ω U, (U_g Ω) U⟫_ℂ) =ᵐ[μ]
        fun U => ((ω U * ω (eqv U) : ℝ) : ℂ) := by
      filter_upwards [hΩ_ae_ω, hΩ_g_ae] with U hU1 hU2
      change ⟪⇑Ω U, ⇑(U_g Ω) U⟫_ℂ = _
      rw [hU1, hU2, hcinner]
      simp [Complex.conj_ofReal, Complex.ofReal_mul]
    have hc_l2 : MeasureTheory.Integrable (fun U => ⟪Ω U, (U_g Ω) U⟫_ℂ) μ :=
      MeasureTheory.L2.integrable_inner Ω (U_g Ω)
    have hc_re_nn : 0 ≤ c_g.re := by
      dsimp [c_g]
      rw [MeasureTheory.L2.inner_def]
      change 0 ≤ RCLike.re (∫ U, ⟪Ω U, (U_g Ω) U⟫_ℂ ∂μ)
      rw [← integral_re hc_l2]
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [hc_int_ae] with U hU
      change 0 ≤ (⟪⇑Ω U, ⇑(U_g Ω) U⟫_ℂ).re
      rw [hU, Complex.ofReal_re]
      exact mul_nonneg (hω_pos U).le (hω_pos _).le
    have hc_im_zero : c_g.im = 0 := by
      dsimp [c_g]
      rw [MeasureTheory.L2.inner_def]
      have h1 : (∫ U, ⟪Ω U, (U_g Ω) U⟫_ℂ ∂μ).im =
          RCLike.re (-Complex.I * ∫ U, ⟪Ω U, (U_g Ω) U⟫_ℂ ∂μ) := by
        simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (hc_l2.const_mul (-Complex.I))]
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [hc_int_ae] with U hU
      change (-Complex.I * ⟪⇑Ω U, ⇑(U_g Ω) U⟫_ℂ).re = 0
      rw [hU]
      simp [Complex.mul_re]
    have hc_re_one : c_g.re = 1 := by
      have hc_eq : c_g = (c_g.re : ℂ) := Complex.ext rfl hc_im_zero
      rw [hc_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc_re_nn] at hc_norm
      exact hc_norm
    have hc_one : c_g = 1 := Complex.ext hc_re_one hc_im_zero
    rw [hUg_smul, hc_one, one_smul]
  exact ⟨Ω, ω, ⟨hlam0_pos, hΩ_norm, hω_cont, hω_pos, hΩ_ae_ω, hΩ_eig, hΩ_gauge, h_simple⟩⟩

/-- Spectral gap properties of `wilsonExactGap` for any normalized compact positive operator. -/
theorem wilsonExactGap_spec
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (T_norm : V →L[ℂ] V) (Ω : V)
    (hT_sa : ∀ x y : V, ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ)
    (hT_pos : ∀ x : V, 0 ≤ (⟪x, T_norm x⟫_ℂ).re)
    (hT_comp : IsCompactOperator ⇑T_norm)
    (hT_le1 : ‖T_norm‖ ≤ 1)
    (hT_Ω : T_norm Ω = Ω)
    (h_simple : ∀ w : V, T_norm w = (1 : ℂ) • w → ⟪w, Ω⟫_ℂ = 0 → w = 0) :
    0 < wilsonExactGap T_norm Ω hT_sa hT_Ω ∧
    (∀ v : V, ⟪v, Ω⟫_ℂ = 0 →
      (⟪v, T_norm v⟫_ℂ).re ≤ Real.exp (-(wilsonExactGap T_norm Ω hT_sa hT_Ω * 1)) * ‖v‖ ^ 2) ∧
    (wilsonPerpOp T_norm Ω hT_sa hT_Ω ≠ 0 →
      wilsonExactGap T_norm Ω hT_sa hT_Ω =
        -Real.log ‖wilsonPerpOp T_norm Ω hT_sa hT_Ω‖ ∧
      ∃ w : V, ‖w‖ = 1 ∧ ⟪w, Ω⟫_ℂ = 0 ∧
        T_norm w = (Real.exp (-wilsonExactGap T_norm Ω hT_sa hT_Ω) : ℂ) • w) := by
  let K : Submodule ℂ V := wilsonPerpSubmodule Ω
  let T_K : ↥K →L[ℂ] ↥K := wilsonPerpOp T_norm Ω hT_sa hT_Ω
  have hK_closed : IsClosed (K : Set V) := (Submodule.span ℂ {Ω}).isClosed_orthogonal
  haveI : CompleteSpace ↥K := by
    refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    have huV : CauchySeq (fun n => (u n : V)) :=
      Metric.cauchySeq_iff.mpr (by simpa [Subtype.dist_eq] using Metric.cauchySeq_iff.mp hu)
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete huV
    have haK : a ∈ (K : Set V) :=
      hK_closed.mem_of_tendsto ha (Filter.Eventually.of_forall fun n => (u n).2)
    exact ⟨⟨a, haK⟩, tendsto_subtype_rng.mpr ha⟩
  have hTK_sa : ∀ x y : ↥K, ⟪T_K x, y⟫_ℂ = ⟪x, T_K y⟫_ℂ := fun x y => hT_sa x.1 y.1
  have hTK_pos : ∀ x : ↥K, 0 ≤ (⟪x, T_K x⟫_ℂ).re := fun x => hT_pos x.1
  have hTK_comp : IsCompactOperator ⇑T_K := by
    obtain ⟨S, hS_comp, hS_nhds⟩ := hT_comp
    let S_K : Set ↥K := Subtype.val ⁻¹' S
    have hSK_comp : IsCompact S_K := by
      have him : Subtype.val '' S_K = S ∩ (K : Set V) := by
        ext x
        simp only [S_K, Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe,
          Subtype.exists, exists_and_right, exists_eq_right]
        exact ⟨fun ⟨hxK, hxS⟩ => ⟨hxS, hxK⟩, fun ⟨hxS, hxK⟩ => ⟨hxK, hxS⟩⟩
      exact Topology.IsInducing.subtypeVal.isCompact_iff.mpr
        (him ▸ hS_comp.inter_right hK_closed)
    refine ⟨S_K, hSK_comp, ?_⟩
    have h_pre : ⇑T_K ⁻¹' S_K = Subtype.val ⁻¹' (⇑T_norm ⁻¹' S) := by ext x; rfl
    rw [h_pre]
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds hS_nhds
  have hTK_le_one : ‖T_K‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    change ‖T_norm x.1‖ ≤ 1 * ‖x.1‖
    rw [one_mul]
    exact (T_norm.le_opNorm x.1).trans (by
      calc ‖T_norm‖ * ‖x.1‖ ≤ 1 * ‖x.1‖ := mul_le_mul_of_nonneg_right hT_le1 (norm_nonneg _)
        _ = ‖x.1‖ := one_mul _)
  by_cases hTK_zero : T_K = 0
  · have h_norm0 : ‖T_K‖ = 0 := norm_eq_zero.mpr hTK_zero
    have h_gap_eq : wilsonExactGap T_norm Ω hT_sa hT_Ω = 1 := by
      dsimp [wilsonExactGap]
      rw [if_pos h_norm0]
    refine ⟨by rw [h_gap_eq]; exact one_pos, fun v hv => ?_, fun hne => absurd hTK_zero hne⟩
    have hvK : v ∈ K := by
      change v ∈ wilsonPerpSubmodule Ω
      unfold wilsonPerpSubmodule
      rw [Submodule.mem_orthogonal]
      intro z hz
      rw [Submodule.mem_span_singleton] at hz
      rcases hz with ⟨c, rfl⟩
      have hΩv : ⟪Ω, v⟫_ℂ = 0 := by rw [← inner_conj_symm, hv, map_zero]
      rw [inner_smul_left, hΩv, mul_zero]
    have hTv : T_norm v = 0 := congrArg Subtype.val
      (congrArg (fun f : ↥K →L[ℂ] ↥K => f ⟨v, hvK⟩) hTK_zero)
    rw [h_gap_eq, hTv, inner_zero_right, Complex.zero_re]
    positivity
  · have hTK_pos_norm : 0 < ‖T_K‖ :=
      lt_of_le_of_ne (norm_nonneg T_K) (Ne.symm (norm_ne_zero_iff.mpr hTK_zero))
    have h_gap_eq : wilsonExactGap T_norm Ω hT_sa hT_Ω = -Real.log ‖T_K‖ := by
      dsimp [wilsonExactGap]
      rw [if_neg hTK_pos_norm.ne']
    obtain ⟨w_K, hwK_norm, hwK_eig⟩ :=
      compact_sa_pos_exists_max_eigenvector T_K hTK_sa hTK_pos hTK_comp hTK_zero
    have hTK_lt_one : ‖T_K‖ < 1 := by
      refine lt_of_le_of_ne hTK_le_one fun h1 => ?_
      have hw_eig_norm : T_norm w_K.1 = (1 : ℂ) • w_K.1 := by
        have h := congrArg Subtype.val hwK_eig
        change T_norm w_K.1 = (‖T_K‖ : ℂ) • w_K.1 at h
        rwa [h1, Complex.ofReal_one] at h
      have hw_orth : ⟪w_K.1, Ω⟫_ℂ = 0 := by
        have hΩw : ⟪Ω, w_K.1⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal _ _).mp w_K.2 Ω (Submodule.subset_span rfl)
        rw [← inner_conj_symm, hΩw, map_zero]
      have hw0 : w_K.1 = 0 := h_simple w_K.1 hw_eig_norm hw_orth
      have h0 : ‖w_K‖ = 0 := by change ‖w_K.1‖ = 0; rw [hw0, norm_zero]
      linarith [hwK_norm]
    have h_gap_pos : 0 < wilsonExactGap T_norm Ω hT_sa hT_Ω := by
      rw [h_gap_eq]
      exact neg_pos.mpr (Real.log_neg hTK_pos_norm hTK_lt_one)
    refine ⟨h_gap_pos, fun v hv => ?_, fun _ => ⟨h_gap_eq, w_K.1, hwK_norm, ?_, ?_⟩⟩
    · have hvK : v ∈ K := by
        change v ∈ wilsonPerpSubmodule Ω
        unfold wilsonPerpSubmodule
        rw [Submodule.mem_orthogonal]
        intro z hz
        rw [Submodule.mem_span_singleton] at hz
        rcases hz with ⟨c, rfl⟩
        have hΩv : ⟪Ω, v⟫_ℂ = 0 := by rw [← inner_conj_symm, hv, map_zero]
        rw [inner_smul_left, hΩv, mul_zero]
      have hexp : Real.exp (-(wilsonExactGap T_norm Ω hT_sa hT_Ω * 1)) = ‖T_K‖ := by
        rw [h_gap_eq, mul_one, neg_neg, Real.exp_log hTK_pos_norm]
      rw [hexp]
      calc (⟪v, T_norm v⟫_ℂ).re ≤ ‖⟪v, T_norm v⟫_ℂ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
        _ ≤ ‖v‖ * ‖T_norm v‖ := norm_inner_le_norm _ _
        _ = ‖(⟨v, hvK⟩ : ↥K)‖ * ‖T_K ⟨v, hvK⟩‖ := rfl
        _ ≤ ‖(⟨v, hvK⟩ : ↥K)‖ * (‖T_K‖ * ‖(⟨v, hvK⟩ : ↥K)‖) :=
            mul_le_mul_of_nonneg_left (T_K.le_opNorm _) (norm_nonneg _)
        _ = ‖T_K‖ * ‖v‖ ^ 2 := by change ‖v‖ * (‖T_K‖ * ‖v‖) = _; ring
    · have hΩw : ⟪Ω, w_K.1⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).mp w_K.2 Ω (Submodule.subset_span rfl)
      rw [← inner_conj_symm, hΩw, map_zero]
    · have hexp : Real.exp (-wilsonExactGap T_norm Ω hT_sa hT_Ω) = ‖T_K‖ := by
        rw [h_gap_eq, neg_neg, Real.exp_log hTK_pos_norm]
      rw [hexp]
      exact congrArg Subtype.val hwK_eig

/--
**Perron–Frobenius Theorem & Finite-Volume Spectral Gap for `wilsonIntegralOp`**:
combines `wilsonIntegral_ground_state` and `wilsonExactGap_spec`.
-/
theorem wilsonIntegral_perron_frobenius (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (K_kin : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hK_cont : Continuous (Function.uncurry K_kin))
    (hK_symm : ∀ U U', K_kin U' U = K_kin U U')
    (hK_nn : ∀ U U', 0 ≤ K_kin U U')
    (hK_inv : ∀ g U U', K_kin (gaugeAct g U) (gaugeAct g U') = K_kin U U')
    (c_min : ℝ) (hc_min : 0 < c_min) (hK_lb : ∀ U U', c_min ≤ K_kin U U')
    (M_K : ℝ) (hM_K : 0 ≤ M_K) (hK_bd : ∀ U U', K_kin U U' ≤ M_K)
    (hT_pos : ∀ ψ : HaarGaugeSpace (latticeHaarMeasure L N),
      0 ≤ (⟪ψ, wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd ψ⟫_ℂ).re) :
    ∃ (Ω : HaarGaugeSpace (latticeHaarMeasure L N)) (lam0 Δ : ℝ),
      0 < lam0 ∧ 0 < Δ ∧ ‖Ω‖ = 1 ∧
      wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd Ω = (lam0 : ℂ) • Ω ∧
      (∀ g, cubicGaugeRep L N g Ω = Ω) ∧
      (∀ v : HaarGaugeSpace (latticeHaarMeasure L N), ⟪v, Ω⟫_ℂ = 0 →
        (⟪v, (((lam0⁻¹ : ℝ) : ℂ) •
          wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd) v⟫_ℂ).re ≤
          Real.exp (-(Δ * 1)) * ‖v‖ ^ 2) := by
  let T := wilsonIntegralOp L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
  obtain ⟨Ω, _, hgs⟩ :=
    wilsonIntegral_ground_state L N β hβ K_kin hK_cont hK_symm hK_nn hK_inv
      c_min hc_min hK_lb M_K hM_K hK_bd hT_pos
  let lam0 : ℝ := ‖T‖
  have hlam0_pos : 0 < lam0 := hgs.norm_pos
  let T_norm : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) := ((lam0⁻¹ : ℝ) : ℂ) • T
  have hT_sa := wilsonIntegralOp_sa L N β hβ K_kin hK_cont hK_symm hK_nn M_K hM_K hK_bd
  have hT_norm_sa : ∀ x y : HaarGaugeSpace (latticeHaarMeasure L N),
      ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ := by
    intro x y
    change ⟪((lam0⁻¹ : ℝ) : ℂ) • T x, y⟫_ℂ = ⟪x, ((lam0⁻¹ : ℝ) : ℂ) • T y⟫_ℂ
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, hT_sa]
  have hT_norm_pos : ∀ x : HaarGaugeSpace (latticeHaarMeasure L N),
      0 ≤ (⟪x, T_norm x⟫_ℂ).re := by
    intro x
    change 0 ≤ (⟪x, ((lam0⁻¹ : ℝ) : ℂ) • T x⟫_ℂ).re
    rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hlam0_pos.le) (hT_pos x)
  have hT_norm_comp : IsCompactOperator ⇑T_norm := by
    obtain ⟨S, hS_comp, hS_nhds⟩ :=
      wilsonIntegralOp_compact L N β hβ K_kin hK_cont hK_nn M_K hM_K hK_bd
    refine ⟨(((lam0⁻¹ : ℝ) : ℂ) • ·) '' S, hS_comp.image (continuous_const_smul _), ?_⟩
    filter_upwards [hS_nhds] with v hv
    exact ⟨T v, hv, rfl⟩
  have hT_norm_le1 : ‖T_norm‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    calc ‖T_norm x‖ = ‖((lam0⁻¹ : ℝ) : ℂ) • T x‖ := rfl
      _ = lam0⁻¹ * ‖T x‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr hlam0_pos.le)]
      _ ≤ lam0⁻¹ * (lam0 * ‖x‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm x) (inv_nonneg.mpr hlam0_pos.le)
      _ = 1 * ‖x‖ := by rw [← mul_assoc, inv_mul_cancel₀ hlam0_pos.ne', one_mul]
  have hT_norm_Ω : T_norm Ω = Ω := by
    change ((lam0⁻¹ : ℝ) : ℂ) • T Ω = Ω
    rw [hgs.eig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
      Complex.ofReal_one, one_smul]
  have h_simple_norm : ∀ w, T_norm w = (1 : ℂ) • w → ⟪w, Ω⟫_ℂ = 0 → w = 0 := by
    intro w hw hwo
    apply hgs.simple w _ hwo
    have h := congrArg (fun z : HaarGaugeSpace (latticeHaarMeasure L N) => (lam0 : ℂ) • z) hw
    dsimp only [T_norm] at h
    rw [ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hlam0_pos.ne', Complex.ofReal_one, one_smul, one_smul] at h
    exact h
  obtain ⟨hΔ_pos, hgap, _⟩ := wilsonExactGap_spec T_norm Ω hT_norm_sa hT_norm_pos
    hT_norm_comp hT_norm_le1 hT_norm_Ω h_simple_norm
  exact ⟨Ω, lam0, wilsonExactGap T_norm Ω hT_norm_sa hT_norm_Ω, hlam0_pos, hΔ_pos,
    hgs.unit, hgs.eig, hgs.gauge_inv, hgap⟩

noncomputable def fullRankTRaw (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (c_χ : ℝ) (hc_χ : 0 < c_χ) (hχ_lb : ∀ U W, c_χ ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ) :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) :=
  let hχ_nn : ∀ U W, 0 ≤ χ U W := fun U W => hc_χ.le.trans (hχ_lb U W)
  wilsonIntegralOp L N β hβ (wilsonGramKernel L N χ)
    (continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)
    (wilsonGramKernel_nonneg L N χ hχ_nn) (M_χ ^ 2) (sq_nonneg M_χ)
    (wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)

theorem fullRankGS (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_inv : ∀ g U W, χ (gaugeAct g U) (gaugeAct g W) = χ U W)
    (c_χ : ℝ) (hc_χ : 0 < c_χ) (hχ_lb : ∀ U W, c_χ ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ) :
    ∃ (Ω : HaarGaugeSpace (latticeHaarMeasure L N))
      (ω : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ),
      IsWilsonGroundState L N β hβ (wilsonGramKernel L N χ)
        (continuous_wilsonGramKernel L N χ hχ_cont
          (fun U W => hc_χ.le.trans (hχ_lb U W)) M_χ hM_χ hχ_bd)
        (wilsonGramKernel_nonneg L N χ (fun U W => hc_χ.le.trans (hχ_lb U W)))
        (M_χ ^ 2) (sq_nonneg M_χ)
        (wilsonGramKernel_le L N χ hχ_cont
          (fun U W => hc_χ.le.trans (hχ_lb U W)) M_χ hM_χ hχ_bd)
        Ω ω :=
  let hχ_nn : ∀ U W, 0 ≤ χ U W := fun U W => hc_χ.le.trans (hχ_lb U W)
  wilsonIntegral_ground_state L N β hβ (wilsonGramKernel L N χ)
    (continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)
    (wilsonGramKernel_symm L N χ)
    (wilsonGramKernel_nonneg L N χ hχ_nn)
    (wilsonGramKernel_gauge_inv L N χ hχ_inv)
    (c_χ ^ 2) (sq_pos_of_pos hc_χ)
    (wilsonGramKernel_lb L N χ hχ_cont c_χ hc_χ.le hχ_lb)
    (M_χ ^ 2) (sq_nonneg M_χ)
    (wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)
    (wilsonIntegralOp_gram_pos L N β hβ χ hχ_cont hχ_nn M_χ hM_χ hχ_bd)

/--
**Full-rank `LatticeGaugeSetup` on `cubicTorus3 L`** driven by `wilsonIntegralOp`
with Gram-factorized kinetic kernel `wilsonGramKernel L N χ`, exposing the exact
constructive spectral gap `wilsonExactGap T_norm Ω` (`-log ‖T_norm|_{Ωᗮ}‖`).
-/
noncomputable def fullRankCubicLatticeGaugeSetup (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_inv : ∀ g U W, χ (gaugeAct g U) (gaugeAct g W) = χ U W)
    (c_χ : ℝ) (hc_χ : 0 < c_χ) (hχ_lb : ∀ U W, c_χ ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ) :
    LatticeGaugeSetup (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (HaarGaugeSpace (latticeHaarMeasure L N)) :=
  let hχ_nn : ∀ U W, 0 ≤ χ U W := fun U W => hc_χ.le.trans (hχ_lb U W)
  let K_kin := wilsonGramKernel L N χ
  let hK_cont := continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let hK_symm := wilsonGramKernel_symm L N χ
  let hK_nn := wilsonGramKernel_nonneg L N χ hχ_nn
  let hK_inv := wilsonGramKernel_gauge_inv L N χ hχ_inv
  let hK_bd := wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let T_raw := fullRankTRaw L N β hβ χ hχ_cont c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
  let hT_pos := wilsonIntegralOp_gram_pos L N β hβ χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let gs := fullRankGS L N β hβ χ hχ_cont hχ_inv c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
  let Ω := Classical.choose gs
  let hgs_spec := Classical.choose_spec (Classical.choose_spec gs)
  let lam0 : ℝ := ‖T_raw‖
  let hlam0_pos : 0 < lam0 := hgs_spec.norm_pos
  let T_norm : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) :=
    ((lam0⁻¹ : ℝ) : ℂ) • T_raw
  let hT_norm_sa : ∀ x y : HaarGaugeSpace (latticeHaarMeasure L N),
      ⟪T_norm x, y⟫_ℂ = ⟪x, T_norm y⟫_ℂ := fun x y => by
    change ⟪((lam0⁻¹ : ℝ) : ℂ) • T_raw x, y⟫_ℂ = ⟪x, ((lam0⁻¹ : ℝ) : ℂ) • T_raw y⟫_ℂ
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    congr 1
    exact wilsonIntegralOp_sa L N β hβ K_kin hK_cont hK_symm hK_nn
      (M_χ ^ 2) (sq_nonneg M_χ) hK_bd x y
  let hT_norm_pos : ∀ v : HaarGaugeSpace (latticeHaarMeasure L N),
      0 ≤ (⟪v, T_norm v⟫_ℂ).re := fun v => by
    simp only [T_norm, ContinuousLinearMap.smul_apply, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hlam0_pos.le) (hT_pos v)
  let hT_norm_comp : IsCompactOperator ⇑T_norm := by
    obtain ⟨S, hS_comp, hS_nhds⟩ :=
      wilsonIntegralOp_compact L N β hβ K_kin hK_cont hK_nn (M_χ ^ 2) (sq_nonneg M_χ) hK_bd
    exact ⟨(((lam0⁻¹ : ℝ) : ℂ) • ·) '' S, hS_comp.image (continuous_const_smul _), by
      filter_upwards [hS_nhds] with v hv
      exact ⟨T_raw v, hv, rfl⟩⟩
  let hT_norm_le1 : ‖T_norm‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    calc ‖T_norm x‖ = ‖((lam0⁻¹ : ℝ) : ℂ) • T_raw x‖ := rfl
      _ = lam0⁻¹ * ‖T_raw x‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr hlam0_pos.le)]
      _ ≤ lam0⁻¹ * (lam0 * ‖x‖) :=
          mul_le_mul_of_nonneg_left (T_raw.le_opNorm x) (inv_nonneg.mpr hlam0_pos.le)
      _ = 1 * ‖x‖ := by rw [← mul_assoc, inv_mul_cancel₀ hlam0_pos.ne', one_mul]
  let hT_norm_Ω : T_norm Ω = Ω := by
    have heig : T_raw Ω = (lam0 : ℂ) • Ω := hgs_spec.eig
    change ((lam0⁻¹ : ℝ) : ℂ) • T_raw Ω = Ω
    rw [heig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
      Complex.ofReal_one, one_smul]
  let h_simple : ∀ w, T_norm w = (1 : ℂ) • w → ⟪w, Ω⟫_ℂ = 0 → w = 0 := fun w hw hwo => by
    apply hgs_spec.simple w _ hwo
    have h := congrArg (fun z : HaarGaugeSpace (latticeHaarMeasure L N) => (lam0 : ℂ) • z) hw
    dsimp only [T_norm] at h
    rw [ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hlam0_pos.ne', Complex.ofReal_one, one_smul, one_smul] at h
    exact h
  let h_gap := wilsonExactGap_spec T_norm Ω hT_norm_sa hT_norm_pos hT_norm_comp
    hT_norm_le1 hT_norm_Ω h_simple
  { rep := cubicGaugeRep L N
    rep_one := cubicGaugeRep_one L N
    rep_mul := cubicGaugeRep_mul L N
    T := T_norm
    a := 1
    a_pos := one_pos
    T_sa := hT_norm_sa
    T_pos := hT_norm_pos
    T_compact := hT_norm_comp
    T_gauge_inv := fun g => by
      ext1 ψ
      simp only [T_norm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
      congr 1
      exact congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ)
        (wilsonIntegralOp_gauge_inv L N β hβ K_kin hK_cont hK_nn hK_inv
          (M_χ ^ 2) (sq_nonneg M_χ) hK_bd g)
    Ω := Ω
    Ω_unit := hgs_spec.unit
    Ω_vac := hT_norm_Ω
    Ω_gauge_inv := hgs_spec.gauge_inv
    Δ := wilsonExactGap T_norm Ω hT_norm_sa hT_norm_Ω
    Δ_pos := h_gap.1
    gap := h_gap.2.1 }

theorem fullRankCubicLatticeGaugeSetup_exact_gap_of_det_ne
    (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (χ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hχ_cont : Continuous (Function.uncurry χ))
    (hχ_inv : ∀ g U W, χ (gaugeAct g U) (gaugeAct g W) = χ U W)
    (c_χ : ℝ) (hc_χ : 0 < c_χ) (hχ_lb : ∀ U W, c_χ ≤ χ U W)
    (M_χ : ℝ) (hM_χ : 0 ≤ M_χ) (hχ_bd : ∀ U W, χ U W ≤ M_χ)
    (U₁ U₂ : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (h_det : χ U₁ U₁ * χ U₂ U₂ ≠ χ U₂ U₁ * χ U₁ U₂) :
    let S := fullRankCubicLatticeGaugeSetup L N β hβ χ hχ_cont hχ_inv c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
    wilsonPerpOp S.T S.Ω S.T_sa S.Ω_vac ≠ 0 ∧
    S.Δ = -Real.log ‖wilsonPerpOp S.T S.Ω S.T_sa S.Ω_vac‖ ∧
    ∃ w : HaarGaugeSpace (latticeHaarMeasure L N),
      ‖w‖ = 1 ∧ ⟪w, S.Ω⟫_ℂ = 0 ∧
      S.T w = (Real.exp (-S.Δ) : ℂ) • w := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  haveI := instIsOpenPosLatticeHaar L N
  let hχ_nn : ∀ U W, 0 ≤ χ U W := fun U W => hc_χ.le.trans (hχ_lb U W)
  let K_kin := wilsonGramKernel L N χ
  let hK_cont := continuous_wilsonGramKernel L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let hK_symm := wilsonGramKernel_symm L N χ
  let hK_nn := wilsonGramKernel_nonneg L N χ hχ_nn
  let hK_bd := wilsonGramKernel_le L N χ hχ_cont hχ_nn M_χ hM_χ hχ_bd
  let T_raw := fullRankTRaw L N β hβ χ hχ_cont c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
  let gs := fullRankGS L N β hβ χ hχ_cont hχ_inv c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
  let Ω := Classical.choose gs
  let ω := Classical.choose (Classical.choose_spec gs)
  let hgs := Classical.choose_spec (Classical.choose_spec gs)
  let lam0 : ℝ := ‖T_raw‖
  have hlam0_pos : 0 < lam0 := hgs.norm_pos
  let S := fullRankCubicLatticeGaugeSetup L N β hβ χ hχ_cont hχ_inv c_χ hc_χ hχ_lb M_χ hM_χ hχ_bd
  have hS_T_eq : S.T = ((lam0⁻¹ : ℝ) : ℂ) • T_raw := rfl
  have hS_Ω_eq : S.Ω = Ω := rfl
  have hS_Δ_eq : S.Δ = wilsonExactGap S.T S.Ω S.T_sa S.Ω_vac := rfl
  have hT_norm_le1 : ‖S.T‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    calc ‖S.T x‖ = ‖((lam0⁻¹ : ℝ) : ℂ) • T_raw x‖ := by rw [hS_T_eq]; rfl
      _ = lam0⁻¹ * ‖T_raw x‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr hlam0_pos.le)]
      _ ≤ lam0⁻¹ * (lam0 * ‖x‖) :=
          mul_le_mul_of_nonneg_left (T_raw.le_opNorm x) (inv_nonneg.mpr hlam0_pos.le)
      _ = 1 * ‖x‖ := by rw [← mul_assoc, inv_mul_cancel₀ hlam0_pos.ne', one_mul]
  have h_simple_norm : ∀ w, S.T w = (1 : ℂ) • w → ⟪w, S.Ω⟫_ℂ = 0 → w = 0 := by
    intro w hw hwo
    have hwo' : ⟪w, Ω⟫_ℂ = 0 := hS_Ω_eq ▸ hwo
    apply hgs.simple w _ hwo'
    have h := congrArg (fun z : HaarGaugeSpace μ => (lam0 : ℂ) • z) hw
    dsimp only at h
    rw [hS_T_eq, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hlam0_pos.ne', Complex.ofReal_one, one_smul, one_smul] at h
    exact h
  have h_perp_ne : wilsonPerpOp S.T S.Ω S.T_sa S.Ω_vac ≠ 0 := by
    intro h_zero
    let K_W := wilsonKernel β (cubicPlaquettes L) K_kin
    have h_rank1 : ∀ ψ : HaarGaugeSpace μ, T_raw ψ = ((lam0 : ℂ) * ⟪Ω, ψ⟫_ℂ) • Ω := by
      intro ψ
      let c : ℂ := ⟪Ω, ψ⟫_ℂ
      let v : HaarGaugeSpace μ := ψ - c • Ω
      have hΩ_self : ⟪Ω, Ω⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hgs.unit]; norm_num
      have hv_orth : ⟪v, Ω⟫_ℂ = 0 := by
        simp only [v, c, inner_sub_left, inner_smul_left, hΩ_self, mul_one,
          inner_conj_symm, sub_self]
      have hvK : v ∈ wilsonPerpSubmodule S.Ω := by
        unfold wilsonPerpSubmodule
        rw [Submodule.mem_orthogonal]
        intro z hz
        rw [Submodule.mem_span_singleton] at hz
        rcases hz with ⟨r, rfl⟩
        have hΩv : ⟪S.Ω, v⟫_ℂ = 0 := by
          rw [hS_Ω_eq, ← inner_conj_symm, hv_orth, map_zero]
        rw [inner_smul_left, hΩv, mul_zero]
      have hTv : S.T v = 0 := congrArg Subtype.val
        (congrArg (fun f : ↥(wilsonPerpSubmodule S.Ω) →L[ℂ] _ => f ⟨v, hvK⟩) h_zero)
      have hSTψ : S.T ψ = c • Ω := by
        have hψ : ψ = c • Ω + v := by dsimp [v]; abel
        conv_lhs => rw [hψ]
        rw [map_add, map_smul, hTv, add_zero, ← hS_Ω_eq, S.Ω_vac, hS_Ω_eq]
      have hTψ := congrArg (fun z : HaarGaugeSpace μ => (lam0 : ℂ) • z) hSTψ
      dsimp only at hTψ
      rw [hS_T_eq, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hlam0_pos.ne', Complex.ofReal_one, one_smul] at hTψ
      rw [hTψ, smul_smul]
    let h : G_L → ℝ := fun U' => ω U₂ * K_W U₁ U' - ω U₁ * K_W U₂ U'
    have hh_cont : Continuous h :=
      (continuous_const.mul (continuous_cubicWilsonKernel_right L N β K_kin hK_cont U₁)).sub
        (continuous_const.mul (continuous_cubicWilsonKernel_right L N β K_kin hK_cont U₂))
    let h_mem := memLp_of_continuous_compact μ h hh_cont
    let h_Lp : HaarGaugeSpace μ := h_mem.toLp (fun U => (h U : ℂ))
    have hh_ae : ⇑h_Lp =ᵐ[μ] fun U => (h U : ℂ) := h_mem.coeFn_toLp
    let c_h : ℂ := (lam0 : ℂ) * ⟪Ω, h_Lp⟫_ℂ
    have hT_ae1 : ⇑(T_raw h_Lp) =ᵐ[μ] wilsonIntegralFn L N β K_kin h_Lp :=
      wilsonIntegralOp_apply_ae L N β hβ K_kin hK_cont hK_nn (M_χ ^ 2) (sq_nonneg M_χ) hK_bd h_Lp
    have hT_ae2 : ⇑(T_raw h_Lp) =ᵐ[μ] fun U => c_h * (ω U : ℂ) := by
      have h1 : ⇑(T_raw h_Lp) =ᵐ[μ] ⇑(c_h • Ω) := by rw [h_rank1 h_Lp]
      have h2 := MeasureTheory.Lp.coeFn_smul c_h Ω
      filter_upwards [h1, h2, hgs.ae_eq] with U hu1 hu2 hu3
      rw [hu1, hu2]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hu3]
    have h_all_eq : ∀ U, wilsonIntegralFn L N β K_kin h_Lp U = c_h * (ω U : ℂ) :=
      eq_of_ae_continuous μ
        (wilsonIntegralFn_continuous L N β hβ K_kin hK_cont hK_nn (M_χ ^ 2) hK_bd h_Lp)
        (continuous_const.mul (Complex.continuous_ofReal.comp hgs.ω_cont))
        (hT_ae1.symm.trans hT_ae2)
    have h_int_re : ∀ U, ∫ U', K_W U U' * h U' ∂μ = c_h.re * ω U := by
      intro U
      have hi := wilsonKernel_mul_integrable L N β hβ K_kin hK_cont hK_nn
        (M_χ ^ 2) hK_bd h_Lp U
      have h_eq := congrArg Complex.re (h_all_eq U)
      dsimp [wilsonIntegralFn] at h_eq
      change RCLike.re (∫ U', ((K_W U U' : ℝ) : ℂ) * h_Lp U' ∂μ) = (c_h * (ω U : ℂ)).re at h_eq
      rw [← integral_re hi] at h_eq
      have h_lhs : ∫ U', RCLike.re (((K_W U U' : ℝ) : ℂ) * h_Lp U') ∂μ =
          ∫ U', K_W U U' * h U' ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hh_ae] with U' hU'
        change (((K_W U U' : ℝ) : ℂ) * ⇑h_Lp U').re = K_W U U' * h U'
        rw [hU', ← Complex.ofReal_mul, Complex.ofReal_re]
      have h_rhs : (c_h * (ω U : ℂ)).re = c_h.re * ω U := by
        simp [Complex.mul_re]
      rw [h_lhs, h_rhs] at h_eq
      exact h_eq
    have hi1 : MeasureTheory.Integrable (fun U' => K_W U₁ U' * h U') μ :=
      integrable_of_continuous_compact μ _
        ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U₁).mul hh_cont)
    have hi2 : MeasureTheory.Integrable (fun U' => K_W U₂ U' * h U') μ :=
      integrable_of_continuous_compact μ _
        ((continuous_cubicWilsonKernel_right L N β K_kin hK_cont U₂).mul hh_cont)
    have h_sq_zero : ∫ U', h U' ^ 2 ∂μ = 0 := by
      have h_eq : (fun U' => h U' ^ 2) = fun U' => ω U₂ * (K_W U₁ U' * h U') - ω U₁ * (K_W U₂ U' * h U') := by
        funext U'; dsimp [h]; ring
      rw [h_eq, MeasureTheory.integral_sub (hi1.const_mul _) (hi2.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        h_int_re U₁, h_int_re U₂]
      ring
    have hh_zero : ∀ U', h U' = 0 := eq_zero_of_continuous_sq_integral_zero μ h hh_cont h_sq_zero
    let C : ℝ := (ω U₁ * cubicWilsonWeight L N β U₂) / (ω U₂ * cubicWilsonWeight L N β U₁)
    have hω2_pos : 0 < ω U₂ := hgs.ω_pos U₂
    have hw1_pos : 0 < cubicWilsonWeight L N β U₁ := by
      unfold cubicWilsonWeight; exact Real.exp_pos _
    have h_Kkin_eq : ∀ U', K_kin U₁ U' = C * K_kin U₂ U' := by
      intro U'
      have hw_pos : 0 < cubicWilsonWeight L N β U' := by
        unfold cubicWilsonWeight; exact Real.exp_pos _
      have h0 := sub_eq_zero.mp (hh_zero U')
      have hKW1 : K_W U₁ U' = cubicWilsonWeight L N β U₁ * cubicWilsonWeight L N β U' * K_kin U₁ U' := by
        dsimp [K_W, wilsonKernel, cubicWilsonWeight]
        rw [← Real.exp_add]
        congr 2; ring
      have hKW2 : K_W U₂ U' = cubicWilsonWeight L N β U₂ * cubicWilsonWeight L N β U' * K_kin U₂ U' := by
        dsimp [K_W, wilsonKernel, cubicWilsonWeight]
        rw [← Real.exp_add]
        congr 2; ring
      rw [hKW1, hKW2] at h0
      have hden : ω U₂ * cubicWilsonWeight L N β U₁ ≠ 0 := (mul_pos hω2_pos hw1_pos).ne'
      have h_cancel : (ω U₂ * cubicWilsonWeight L N β U₁) * K_kin U₁ U' =
          (ω U₁ * cubicWilsonWeight L N β U₂) * K_kin U₂ U' := by
        apply mul_right_cancel₀ hw_pos.ne'
        calc ((ω U₂ * cubicWilsonWeight L N β U₁) * K_kin U₁ U') * cubicWilsonWeight L N β U'
            = ω U₂ * (cubicWilsonWeight L N β U₁ * cubicWilsonWeight L N β U' * K_kin U₁ U') := by ring
          _ = ω U₁ * (cubicWilsonWeight L N β U₂ * cubicWilsonWeight L N β U' * K_kin U₂ U') := h0
          _ = ((ω U₁ * cubicWilsonWeight L N β U₂) * K_kin U₂ U') * cubicWilsonWeight L N β U' := by ring
      dsimp [C]
      rw [div_mul_eq_mul_div, eq_div_iff hden, mul_comm (K_kin U₁ U')]
      exact h_cancel
    have h_diff_cont : Continuous (fun W : G_L => χ U₁ W - C * χ U₂ W) :=
      (hχ_cont.comp (continuous_const.prodMk continuous_id)).sub
        (continuous_const.mul (hχ_cont.comp (continuous_const.prodMk continuous_id)))
    have h_diff_int : ∫ W, (χ U₁ W - C * χ U₂ W) ^ 2 ∂μ = 0 := by
      have hi11 : MeasureTheory.Integrable (fun W => χ U₁ W * χ U₁ W) μ :=
        integrable_of_continuous_compact μ _
          ((hχ_cont.comp (continuous_const.prodMk continuous_id)).mul
            (hχ_cont.comp (continuous_const.prodMk continuous_id)))
      have hi12 : MeasureTheory.Integrable (fun W => χ U₁ W * χ U₂ W) μ :=
        integrable_of_continuous_compact μ _
          ((hχ_cont.comp (continuous_const.prodMk continuous_id)).mul
            (hχ_cont.comp (continuous_const.prodMk continuous_id)))
      have hi22 : MeasureTheory.Integrable (fun W => χ U₂ W * χ U₂ W) μ :=
        integrable_of_continuous_compact μ _
          ((hχ_cont.comp (continuous_const.prodMk continuous_id)).mul
            (hχ_cont.comp (continuous_const.prodMk continuous_id)))
      have hi12c : MeasureTheory.Integrable (fun W => (2 * C) * (χ U₁ W * χ U₂ W)) μ :=
        hi12.const_mul (2 * C)
      have hi22c : MeasureTheory.Integrable (fun W => (C ^ 2) * (χ U₂ W * χ U₂ W)) μ :=
        hi22.const_mul (C ^ 2)
      have h_sub_int : MeasureTheory.Integrable
          (fun W => χ U₁ W * χ U₁ W - (2 * C) * (χ U₁ W * χ U₂ W)) μ :=
        hi11.sub hi12c
      have h_eq1 : ∫ W, (χ U₁ W - C * χ U₂ W) ^ 2 ∂μ =
          ∫ W, (χ U₁ W * χ U₁ W - (2 * C) * (χ U₁ W * χ U₂ W)) ∂μ +
            ∫ W, (C ^ 2) * (χ U₂ W * χ U₂ W) ∂μ := by
        rw [← MeasureTheory.integral_add h_sub_int hi22c]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
        dsimp only; ring
      rw [h_eq1, MeasureTheory.integral_sub hi11 hi12c,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      change K_kin U₁ U₁ - (2 * C) * K_kin U₁ U₂ + (C ^ 2) * K_kin U₂ U₂ = 0
      rw [h_Kkin_eq U₁, h_Kkin_eq U₂,
        show K_kin U₂ U₁ = K_kin U₁ U₂ from hK_symm U₁ U₂, h_Kkin_eq U₂]
      ring
    have h_chi_eq : ∀ W, χ U₁ W = C * χ U₂ W := fun W =>
      sub_eq_zero.mp (eq_zero_of_continuous_sq_integral_zero μ _ h_diff_cont h_diff_int W)
    have h_eq1 := h_chi_eq U₁
    have h_eq2 := h_chi_eq U₂
    have h_chi11_pos : 0 < χ U₁ U₁ := hc_χ.trans_le (hχ_lb U₁ U₁)
    have hC_ne : C ≠ 0 := by
      intro hC0
      rw [hC0, zero_mul] at h_eq1
      linarith
    apply h_det
    apply mul_left_cancel₀ hC_ne
    calc C * (χ U₁ U₁ * χ U₂ U₂)
        = χ U₁ U₁ * (C * χ U₂ U₂) := by ring
      _ = (C * χ U₂ U₁) * χ U₁ U₂ := by rw [← h_eq1, ← h_eq2]
      _ = C * (χ U₂ U₁ * χ U₁ U₂) := by ring
  have h_spec := (wilsonExactGap_spec S.T S.Ω S.T_sa
    S.T_pos S.T_compact hT_norm_le1 S.Ω_vac h_simple_norm).2.2 h_perp_ne
  exact ⟨h_perp_ne, hS_Δ_eq.trans h_spec.1, h_spec.2⟩

/-- Rank-2 Boltzmann kinetic kernel (kept for reference). -/
noncomputable def cubicActionKineticKernel (L N : ℕ) [NeZero L] (β : ℝ)
    (U W : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  1 + cubicWilsonWeight L N β U * cubicWilsonWeight L N β W

/--
**Link-coupled gauge-invariant Wilson kinetic kernel** on `cubicTorus3 L`:
`χ_link(U, W) = ∏_{e} exp((β / (2N)) Re Tr(U_e W_e⁻¹))`.
-/
noncomputable def cubicLinkKineticKernel (L N : ℕ) [NeZero L] (β : ℝ)
    (U W : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  ∏ e : (cubicTorus3 L).Link,
    Real.exp ((β / (2 * (N : ℝ))) *
      (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ))).re)

theorem su_trace_conj' {N : ℕ}
    (A B : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix.trace ((A * B * A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) =
      Matrix.trace (B : Matrix (Fin N) (Fin N) ℂ) := by
  have hmul : ∀ X Y : Matrix.specialUnitaryGroup (Fin N) ℂ,
      ((X * Y : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
        (X : Matrix (Fin N) (Fin N) ℂ) * (Y : Matrix (Fin N) (Fin N) ℂ) :=
    fun _ _ => rfl
  have hone : ((1 : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) = 1 := rfl
  have hinv : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← hmul A⁻¹ A, inv_mul_cancel, hone]
  rw [hmul (A * B) A⁻¹, hmul A B,
    Matrix.trace_mul_comm ((A : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ))
      ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ),
    ← mul_assoc, hinv, one_mul]

theorem continuous_cubicLinkKineticKernel (L N : ℕ) [NeZero L] (β : ℝ) :
    Continuous (Function.uncurry (cubicLinkKineticKernel L N β)) := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  change Continuous (fun p : G_L × G_L =>
    ∏ e : (cubicTorus3 L).Link,
      Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((p.1 e * (p.2 e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re))
  refine continuous_finset_prod Finset.univ fun e _ => ?_
  have h1 : Continuous (fun p : G_L × G_L => p.1 e) :=
    (continuous_apply e).comp continuous_fst
  have h2 : Continuous (fun p : G_L × G_L => (p.2 e)⁻¹) :=
    continuous_inv.comp ((continuous_apply e).comp continuous_snd)
  exact Real.continuous_exp.comp (continuous_const.mul (h_tr.comp (h1.mul h2)))

theorem cubicLinkKineticKernel_gauge_inv (L N : ℕ) [NeZero L] (β : ℝ)
    (g : GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U W : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubicLinkKineticKernel L N β (gaugeAct g U) (gaugeAct g W) =
      cubicLinkKineticKernel L N β U W := by
  dsimp only [cubicLinkKineticKernel]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hconj : gaugeAct g U e * (gaugeAct g W e)⁻¹ =
      g ((cubicTorus3 L).src e) * (U e * (W e)⁻¹) * (g ((cubicTorus3 L).src e))⁻¹ := by
    simp only [gaugeAct, mul_inv_rev, inv_inv]
    group
  rw [hconj, su_trace_conj']

theorem cubicLinkKineticKernel_bounds (L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    (U W : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (Real.exp (-(β / 2))) ^ (Fintype.card (cubicTorus3 L).Link) ≤
        cubicLinkKineticKernel L N β U W ∧
      cubicLinkKineticKernel L N β U W ≤
        (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h_fac_lb : ∀ e : (cubicTorus3 L).Link,
      Real.exp (-(β / 2)) ≤
        Real.exp ((β / (2 * (N : ℝ))) *
          (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ))).re) := by
    intro e
    have htr := (abs_le.mp (abs_re_trace_su_le (U e * (W e)⁻¹))).1
    have hmul : -(β / 2) ≤ (β / (2 * (N : ℝ))) *
        (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re := by
      have heq : -(β / 2) = (β / (2 * (N : ℝ))) * (-(N : ℝ)) := by
        field_simp [hN_pos.ne']
      rw [heq]
      exact mul_le_mul_of_nonneg_left htr (by positivity)
    exact Real.exp_le_exp.mpr hmul
  have h_fac_ub : ∀ e : (cubicTorus3 L).Link,
      Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) ≤
        Real.exp (β / 2) := by
    intro e
    have htr := (abs_le.mp (abs_re_trace_su_le (U e * (W e)⁻¹))).2
    have hmul : (β / (2 * (N : ℝ))) *
        (Matrix.trace (((U e * (W e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re ≤ β / 2 := by
      have heq : β / 2 = (β / (2 * (N : ℝ))) * (N : ℝ) := by
        field_simp [hN_pos.ne']
      rw [heq]
      exact mul_le_mul_of_nonneg_left htr (by positivity)
    exact Real.exp_le_exp.mpr hmul
  dsimp only [cubicLinkKineticKernel]
  constructor
  · calc (Real.exp (-(β / 2))) ^ (Fintype.card (cubicTorus3 L).Link)
        = ∏ _e : (cubicTorus3 L).Link, Real.exp (-(β / 2)) := by
            simp [Finset.prod_const, Finset.card_univ]
      _ ≤ ∏ e : (cubicTorus3 L).Link, _ :=
            Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) (fun e _ => h_fac_lb e)
  · calc ∏ e : (cubicTorus3 L).Link, _
        ≤ ∏ _e : (cubicTorus3 L).Link, Real.exp (β / 2) :=
            Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) (fun e _ => h_fac_ub e)
      _ = (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) := by
            simp [Finset.prod_const, Finset.card_univ]

theorem suFlip2_inv_eq (N : ℕ) (hN : 2 ≤ N) :
    (suFlip2 N hN)⁻¹ = suFlip2 N hN := by
  have h_mul : ((suFlip2 N hN : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) *
      ((suFlip2 N hN : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [suFlip2, Matrix.mul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rw [Finset.sum_eq_single i]
      · by_cases hi : (i : ℕ) < 2 <;> simp [hi]
      · intro k _ hki
        simp [Matrix.diagonal_apply_ne _ hki.symm, Matrix.diagonal_apply_ne _ hki]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · simp only [suFlip2, Matrix.mul_apply, Matrix.one_apply_ne hij]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hki : k = i
      · subst hki; simp [Matrix.diagonal_apply, hij]
      · simp [Matrix.diagonal_apply, Ne.symm hki]
  exact inv_eq_of_mul_eq_one_left (Subtype.ext h_mul)

theorem suFlip2_trace_re (N : ℕ) (hN : 2 ≤ N) :
    (Matrix.trace ((suFlip2 N hN : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re = (N : ℝ) - 4 := by
  simp only [suFlip2, Matrix.trace, Matrix.diag, Matrix.diagonal_apply_eq, Complex.re_sum]
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h; have := congrArg Fin.val h; norm_num [i0, i1] at this
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)]
  have hi1_mem : i1 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩
  rw [← Finset.add_sum_erase (Finset.univ.erase i0) _ hi1_mem]
  have h0 : ((if (i0 : ℕ) < 2 then (-1 : ℂ) else 1)).re = -1 := by simp [i0]
  have h1 : ((if (i1 : ℕ) < 2 then (-1 : ℂ) else 1)).re = -1 := by simp [i1]
  have h_rest : ∑ x ∈ (Finset.univ.erase i0).erase i1,
      ((if (x : ℕ) < 2 then (-1 : ℂ) else 1)).re = (N : ℝ) - 2 := by
    have h_eq : ∑ x ∈ (Finset.univ.erase i0).erase i1,
        ((if (x : ℕ) < 2 then (-1 : ℂ) else 1)).re =
        ∑ _x ∈ (Finset.univ.erase i0).erase i1, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx1 : x ≠ i1 := (Finset.mem_erase.mp hx).1
      have hx0 : x ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hge2 : ¬ (x : ℕ) < 2 := by
        intro hlt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h_0 | h_1
        · exact hx0 (Fin.ext (Nat.lt_one_iff.mp h_0))
        · exact hx1 (Fin.ext h_1)
      simp [hge2]
    rw [h_eq, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc1 : ((Finset.univ.erase i0).erase i1).card = N - 2 := by
      rw [Finset.card_erase_of_mem hi1_mem, Finset.card_erase_of_mem (Finset.mem_univ i0),
        Finset.card_univ, Fintype.card_fin]
      omega
    rw [hc1, Nat.cast_sub hN]
    norm_num
  rw [h0, h1, h_rest]
  ring

theorem su_one_trace_re (N : ℕ) :
    (Matrix.trace ((1 : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re = (N : ℝ) := by
  change (Matrix.trace (1 : Matrix (Fin N) (Fin N) ℂ)).re = (N : ℝ)
  simp

noncomputable def linkChiLb (L : ℕ) [NeZero L] (β : ℝ) : ℝ :=
  (Real.exp (-(β / 2))) ^ (Fintype.card (cubicTorus3 L).Link)

noncomputable def linkChiUb (L : ℕ) [NeZero L] (β : ℝ) : ℝ :=
  (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link)

theorem linkChiLb_pos (L : ℕ) [NeZero L] (β : ℝ) : 0 < linkChiLb L β :=
  pow_pos (Real.exp_pos _) _

theorem linkChiUb_nonneg (L : ℕ) [NeZero L] (β : ℝ) : 0 ≤ linkChiUb L β :=
  pow_nonneg (Real.exp_pos _).le _

theorem linkChi_nn (L N : ℕ) [NeZero L] (hN : 2 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    (U W : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ cubicLinkKineticKernel L N β U W :=
  (linkChiLb_pos L β).le.trans (cubicLinkKineticKernel_bounds L N (by omega) β hβ U W).1

/--
**Full-rank `NonAbelianWilsonSetup` on `cubicTorus3 L`** with `L²(SU(N)^{3L³}, dμ_Haar)`,
the link-coupled kinetic kernel `cubicLinkKineticKernel`, and `wilsonIntegralOp`.
-/
noncomputable def fullRankCubicNonAbelianWilsonSetup (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
    (β : ℝ) (hβ : 0 < β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    NonAbelianWilsonSetup (cubicTorus3 L) N hN :=
  let χ := cubicLinkKineticKernel L N β
  let setup := fullRankCubicLatticeGaugeSetup L N β hβ.le χ
    (continuous_cubicLinkKineticKernel L N β)
    (cubicLinkKineticKernel_gauge_inv L N β)
    (linkChiLb L β) (linkChiLb_pos L β)
    (fun U W => (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U W).1)
    (linkChiUb L β) (linkChiUb_nonneg L β)
    (fun U W => (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U W).2)
  { μ := latticeHaarMeasure L N
    μ_prob := latticeHaarMeasure_prob L N
    μ_inv := latticeHaarMeasure_gauge_inv L N
    β := β
    β_pos := hβ
    plaquettes := cubicPlaquettes L
    K_kin := wilsonGramKernel L N χ
    K_symm := wilsonGramKernel_symm L N χ
    K_nonneg := wilsonGramKernel_nonneg L N χ (linkChi_nn L N hN β hβ.le)
    K_inv := wilsonGramKernel_gauge_inv L N χ (cubicLinkKineticKernel_gauge_inv L N β)
    gaugeSetup := setup
    SymmIdx := GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
    symmOp := cubicGaugeRep L N
    symm_comm := fun g => by
      unfold lieBracketCLM
      change (setup.rep g).comp setup.T - setup.T.comp (setup.rep g) = 0
      rw [setup.T_gauge_inv g, sub_self] }

/--
**Non-degeneracy and exact spectral gap** of `fullRankCubicNonAbelianWilsonSetup`:
for every $L \ge 1$, $N \ge 2$, $\beta > 0$, the link-coupled transfer operator
is non-degenerate on $\Omega^\perp$ (`wilsonPerpOp ≠ 0`), its spectral gap equals
`setup.Δ = -Real.log ‖wilsonPerpOp‖ = log(λ₀ / λ₁)`, and `setup.T` attains
`exp(-setup.Δ)` at a unit excited eigenstate `w ∈ Ωᗮ`.
-/
theorem fullRankCubicNonAbelianWilsonSetup_exact_gap
    (L N : ℕ) [NeZero L] (hN : 2 ≤ N) (β : ℝ) (hβ : 0 < β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    let S := (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup
    wilsonPerpOp S.T S.Ω S.T_sa S.Ω_vac ≠ 0 ∧
    S.Δ = -Real.log ‖wilsonPerpOp S.T S.Ω S.T_sa S.Ω_vac‖ ∧
    ∃ w : HaarGaugeSpace (latticeHaarMeasure L N),
      ‖w‖ = 1 ∧ ⟪w, S.Ω⟫_ℂ = 0 ∧
      S.T w = (Real.exp (-S.Δ) : ℂ) • w := by
  let G_L := GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let χ := cubicLinkKineticKernel L N β
  let U₁ : G_L := fun _ => 1
  let e₀ : (cubicTorus3 L).Link := ((0, 0, 0), 0)
  let U₂ : G_L := fun e => if e = e₀ then suFlip2 N hN else 1
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have h_11 : χ U₁ U₁ = (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) := by
    dsimp only [χ, cubicLinkKineticKernel]
    have h_each : ∀ e : (cubicTorus3 L).Link,
        Real.exp ((β / (2 * (N : ℝ))) *
          (Matrix.trace (((U₁ e * (U₁ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ))).re) = Real.exp (β / 2) := by
      intro e
      simp only [U₁, mul_inv_cancel, su_one_trace_re]
      congr 1; field_simp [hN_pos.ne']
    simp_rw [h_each, Finset.prod_const, Finset.card_univ]
  have h_22 : χ U₂ U₂ = (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) := by
    dsimp only [χ, cubicLinkKineticKernel]
    have h_each : ∀ e : (cubicTorus3 L).Link,
        Real.exp ((β / (2 * (N : ℝ))) *
          (Matrix.trace (((U₂ e * (U₂ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ))).re) = Real.exp (β / 2) := by
      intro e
      simp only [mul_inv_cancel, su_one_trace_re]
      congr 1; field_simp [hN_pos.ne']
    simp_rw [h_each, Finset.prod_const, Finset.card_univ]
  have h_lt_fac : Real.exp ((β / (2 * (N : ℝ))) * ((N : ℝ) - 4)) < Real.exp (β / 2) := by
    have h_arg : (β / (2 * (N : ℝ))) * ((N : ℝ) - 4) < β / 2 := by
      have heq : β / 2 = (β / (2 * (N : ℝ))) * (N : ℝ) := by field_simp [hN_pos.ne']
      rw [heq]
      exact mul_lt_mul_of_pos_left (by linarith) (by positivity)
    exact Real.exp_lt_exp.mpr h_arg
  have h_21_lt : χ U₂ U₁ < χ U₁ U₁ := by
    rw [h_11]
    dsimp only [χ, cubicLinkKineticKernel]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e₀)]
    have h_e₀ : Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U₂ e₀ * (U₁ e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) =
        Real.exp ((β / (2 * (N : ℝ))) * ((N : ℝ) - 4)) := by
      simp only [U₂, U₁, ↓reduceIte, inv_one, mul_one, suFlip2_trace_re]
    have h_rest : ∏ e ∈ Finset.univ.erase e₀, Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U₂ e * (U₁ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) =
        (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link - 1) := by
      have h_each : ∀ e ∈ Finset.univ.erase e₀,
          Real.exp ((β / (2 * (N : ℝ))) *
            (Matrix.trace (((U₂ e * (U₁ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ))).re) = Real.exp (β / 2) := by
        intro e he
        have hne : e ≠ e₀ := (Finset.mem_erase.mp he).1
        simp only [U₂, U₁, if_neg hne, inv_one, mul_one, su_one_trace_re]
        congr 1; field_simp [hN_pos.ne']
      rw [Finset.prod_congr rfl h_each, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ e₀), Finset.card_univ]
    rw [h_e₀, h_rest]
    have hcard_pos : 1 ≤ Fintype.card (cubicTorus3 L).Link :=
      Fintype.card_pos_iff.mpr ⟨e₀⟩
    have h_pow : (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) =
        Real.exp (β / 2) * (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hcard_pos]
    rw [h_pow]
    exact mul_lt_mul_of_pos_right h_lt_fac (pow_pos (Real.exp_pos _) _)
  have h_12_lt : χ U₁ U₂ < χ U₂ U₂ := by
    rw [h_22]
    dsimp only [χ, cubicLinkKineticKernel]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e₀)]
    have h_e₀ : Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U₁ e₀ * (U₂ e₀)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) =
        Real.exp ((β / (2 * (N : ℝ))) * ((N : ℝ) - 4)) := by
      simp only [U₁, U₂, ↓reduceIte, one_mul, suFlip2_inv_eq, suFlip2_trace_re]
    have h_rest : ∏ e ∈ Finset.univ.erase e₀, Real.exp ((β / (2 * (N : ℝ))) *
        (Matrix.trace (((U₁ e * (U₂ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) =
        (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link - 1) := by
      have h_each : ∀ e ∈ Finset.univ.erase e₀,
          Real.exp ((β / (2 * (N : ℝ))) *
            (Matrix.trace (((U₁ e * (U₂ e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ))).re) = Real.exp (β / 2) := by
        intro e he
        have hne : e ≠ e₀ := (Finset.mem_erase.mp he).1
        simp only [U₁, U₂, if_neg hne, one_mul, inv_one, su_one_trace_re]
        congr 1; field_simp [hN_pos.ne']
      rw [Finset.prod_congr rfl h_each, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ e₀), Finset.card_univ]
    rw [h_e₀, h_rest]
    have hcard_pos : 1 ≤ Fintype.card (cubicTorus3 L).Link :=
      Fintype.card_pos_iff.mpr ⟨e₀⟩
    have h_pow : (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link) =
        Real.exp (β / 2) * (Real.exp (β / 2)) ^ (Fintype.card (cubicTorus3 L).Link - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hcard_pos]
    rw [h_pow]
    exact mul_lt_mul_of_pos_right h_lt_fac (pow_pos (Real.exp_pos _) _)
  have h_chi21_pos : 0 < χ U₂ U₁ :=
    (linkChiLb_pos L β).trans_le (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U₂ U₁).1
  have h_chi12_pos : 0 < χ U₁ U₂ :=
    (linkChiLb_pos L β).trans_le (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U₁ U₂).1
  have h_det : χ U₁ U₁ * χ U₂ U₂ ≠ χ U₂ U₁ * χ U₁ U₂ :=
    ne_of_gt (mul_lt_mul'' h_21_lt h_12_lt h_chi21_pos.le h_chi12_pos.le)
  exact fullRankCubicLatticeGaugeSetup_exact_gap_of_det_ne L N β hβ.le χ
    (continuous_cubicLinkKineticKernel L N β)
    (cubicLinkKineticKernel_gauge_inv L N β)
    (linkChiLb L β) (linkChiLb_pos L β)
    (fun U W => (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U W).1)
    (linkChiUb L β) (linkChiUb_nonneg L β)
    (fun U W => (cubicLinkKineticKernel_bounds L N (by omega) β hβ.le U W).2)
    U₁ U₂ h_det

theorem fullRankCubic_clustering (L N : ℕ) [NeZero L] (hN : 2 ≤ N) (β : ℝ) (hβ : 0 < β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A B : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N))
    (hA : ⟪A (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω,
        (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω⟫_ℂ = 0)
    (hB : ⟪B (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω,
        (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω⟫_ℂ = 0)
    (k : ℕ) :
    ‖⟪(fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω,
        A (((fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.T ^ k)
          (B (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Ω))⟫_ℂ‖ ≤
      ‖A‖ * ‖B‖ * Real.exp
        (-((fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.Δ *
          (k * (fullRankCubicNonAbelianWilsonSetup L N hN β hβ).gaugeSetup.a))) :=
  nonAbelianWilson_clustering (fullRankCubicNonAbelianWilsonSetup L N hN β hβ) A B hA hB k

end FullRankWilsonSpectralGap

/-! ## §36.  4D Wilson Schwinger reflection positivity, time-reflection, translation & hypercubic symmetries -/

section CubicSpacetime4DOSAndSymmetries

theorem su_inv_val_eq_star {N : ℕ} (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      star (A : Matrix (Fin N) (Fin N) ℂ) := by
  have hU : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    (Unitary.mem_iff.mp A.2.1).1
  have hinv : (A : Matrix (Fin N) (Fin N) ℂ) *
      ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    have h1 : ((A * A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
      rw [mul_inv_cancel]; rfl
    exact h1
  calc ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
      = 1 * ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := (one_mul _).symm
    _ = (star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ)) *
          ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by rw [hU]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) *
          ((A : Matrix (Fin N) (Fin N) ℂ) *
            ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) := by rw [mul_assoc]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) * 1 := by rw [hinv]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) := mul_one _

theorem su_trace_inv_re {N : ℕ} (A : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (Matrix.trace ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)).re =
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re := by
  rw [su_inv_val_eq_star]
  simp only [Matrix.trace, Matrix.diag, Matrix.star_apply, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.conj_re _

theorem su_trace_conj_4d {N : ℕ}
    (A B : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Matrix.trace ((A * B * A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ) =
      Matrix.trace (B : Matrix (Fin N) (Fin N) ℂ) := by
  have hmul : ∀ X Y : Matrix.specialUnitaryGroup (Fin N) ℂ,
      ((X * Y : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
        (X : Matrix (Fin N) (Fin N) ℂ) * (Y : Matrix (Fin N) (Fin N) ℂ) := fun _ _ => rfl
  have hone : ((1 : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := rfl
  have hinv : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      (A : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← hmul A⁻¹ A, inv_mul_cancel, hone]
  rw [hmul (A * B) A⁻¹, hmul A B,
    Matrix.trace_mul_comm ((A : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ))
      ((A⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ),
    ← mul_assoc, hinv, one_mul]

theorem sum_map_flatMap {α β : Type*} (l : List α) (g : α → List β) (f : β → ℝ) :
    ((l.flatMap g).map f).sum = (l.map (fun x => ((g x).map f).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change (((g a ++ l.flatMap g)).map f).sum = _
    rw [List.map_append, List.sum_append, ih]
    rfl

theorem sum_map_univ_toList {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) :
    ((Finset.univ : Finset α).toList.map f).sum = ∑ x : α, f x := by
  rw [← List.sum_toFinset f (Finset.nodup_toList Finset.univ)]
  congr 1
  ext x
  simp [Finset.mem_toList]

noncomputable def sitePlaqSum4 (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (cubicTorus4 Ls Lt).Site) : ℝ :=
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U +
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
  wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U

theorem wilsonAction_cubic4_eq_sum (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes Ls Lt) U =
      β * ∑ x : (cubicTorus4 Ls Lt).Site, sitePlaqSum4 Ls Lt N U x := by
  unfold wilsonAction cubic4Plaquettes
  rw [sum_map_flatMap, sum_map_univ_toList]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  dsimp [sitePlaqSum4]
  ring

theorem fin_neg_add_one {n : ℕ} [NeZero n] (t : Fin n) : -(t + 1) = -t - 1 := by
  abel

theorem fin_neg_sub_one_add_one {n : ℕ} [NeZero n] (t : Fin n) : (-t - 1) + 1 = -t := by
  abel

theorem fin_neg_sub_one_invol {n : ℕ} [NeZero n] (t : Fin n) : -(-t - 1) - 1 = t := by
  abel

theorem wilsonPlaquetteTerm_spatial_timeReflect
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (cubicTorus4 Ls Lt).Site) (d₁ d₂ : Fin 4) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    wilsonPlaquetteTerm
        ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩
        (cubic4TimeReflect Ls Lt N U) =
      wilsonPlaquetteTerm
        ⟨(-x.1, x.2.1, x.2.2.1, x.2.2.2),
          cubic4Plaquette (-x.1, x.2.1, x.2.2.1, x.2.2.2) d₁ d₂,
          cubic4Plaquette_isPath (-x.1, x.2.1, x.2.2.1, x.2.2.2) d₁ d₂⟩
        U := by
  have hsh : ∀ (d : Fin 4), d ≠ 0 → ∀ y : (cubicTorus4 Ls Lt).Site,
      cubicShift4 Ls Lt d (-y.1, y.2.1, y.2.2.1, y.2.2.2) =
        (-(cubicShift4 Ls Lt d y).1, (cubicShift4 Ls Lt d y).2.1,
          (cubicShift4 Ls Lt d y).2.2.1, (cubicShift4 Ls Lt d y).2.2.2) := by
    intro d hd ⟨t, a, b, c⟩
    fin_cases d
    · exact absurd rfl hd
    · rfl
    · rfl
    · rfl
  unfold wilsonPlaquetteTerm
  simp only [cubic4Plaquette, pathHolonomy, cubic4TimeReflect, hd₁, hd₂, ↓reduceIte,
    hsh d₁ hd₁ x, hsh d₂ hd₂ x]

theorem wilsonPlaquetteTerm_temporal_timeReflect
    (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (cubicTorus4 Ls Lt).Site) (d : Fin 4) (hd : d ≠ 0) :
    wilsonPlaquetteTerm
        ⟨x, cubic4Plaquette x 0 d, cubic4Plaquette_isPath x 0 d⟩
        (cubic4TimeReflect Ls Lt N U) =
      wilsonPlaquetteTerm
        ⟨(-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2),
          cubic4Plaquette (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2) 0 d,
          cubic4Plaquette_isPath (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2) 0 d⟩
        U := by
  let x' : (cubicTorus4 Ls Lt).Site := (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
  have h_s0 : (-((cubicShift4 Ls Lt 0 x).1), (cubicShift4 Ls Lt 0 x).2.1,
      (cubicShift4 Ls Lt 0 x).2.2.1, (cubicShift4 Ls Lt 0 x).2.2.2) = x' := by
    rcases x with ⟨t, a, b, c⟩
    dsimp [cubicShift4, x']
    congr 1
    exact fin_neg_add_one t
  have h_sd : (-((cubicShift4 Ls Lt d x).1) - 1, (cubicShift4 Ls Lt d x).2.1,
      (cubicShift4 Ls Lt d x).2.2.1, (cubicShift4 Ls Lt d x).2.2.2) =
      cubicShift4 Ls Lt d x' := by
    rcases x with ⟨t, a, b, c⟩
    fin_cases d
    · exact absurd rfl hd
    · rfl
    · rfl
    · rfl
  have h_s0' : cubicShift4 Ls Lt 0 x' = (-x.1, x.2.1, x.2.2.1, x.2.2.2) := by
    rcases x with ⟨t, a, b, c⟩
    dsimp [cubicShift4, x']
    congr 1
    exact fin_neg_sub_one_add_one t
  let A := U (x', 0)
  let B := U (x', d)
  let C := U (cubicShift4 Ls Lt d x', 0)
  let D := U (cubicShift4 Ls Lt 0 x', d)
  have hH : pathHolonomy (cubic4TimeReflect Ls Lt N U) (cubic4Plaquette x 0 d) =
      A⁻¹ * B * C * D⁻¹ := by
    simp only [cubic4Plaquette, pathHolonomy, cubic4TimeReflect, ↓reduceIte, hd, inv_inv,
      h_s0, h_sd, ← h_s0']
    dsimp only [A, B, C, D, x']
    group
  have hH' : pathHolonomy U (cubic4Plaquette x' 0 d) = A * D * C⁻¹ * B⁻¹ := by
    simp only [cubic4Plaquette, pathHolonomy]
    dsimp only [A, B, C, D]
    group
  have h_conj : pathHolonomy (cubic4TimeReflect Ls Lt N U) (cubic4Plaquette x 0 d) =
      A⁻¹ * (pathHolonomy U (cubic4Plaquette x' 0 d))⁻¹ * (A⁻¹)⁻¹ := by
    rw [hH, hH', mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, inv_inv]
    group
  unfold wilsonPlaquetteTerm
  rw [h_conj, su_trace_conj_4d, su_trace_inv_re]

/-- Exact invariance of the 4D Wilson action under Euclidean time reflection `cubic4TimeReflect`. -/
theorem cubic4WilsonAction_timeReflect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes Ls Lt) (cubic4TimeReflect Ls Lt N U) =
      wilsonAction β (cubic4Plaquettes Ls Lt) U := by
  rw [wilsonAction_cubic4_eq_sum, wilsonAction_cubic4_eq_sum]
  congr 1
  let e_sp : (cubicTorus4 Ls Lt).Site ≃ (cubicTorus4 Ls Lt).Site :=
    { toFun := fun x => (-x.1, x.2.1, x.2.2.1, x.2.2.2)
      invFun := fun x => (-x.1, x.2.1, x.2.2.1, x.2.2.2)
      left_inv := fun ⟨t, a, b, c⟩ => by simp
      right_inv := fun ⟨t, a, b, c⟩ => by simp }
  let e_tm : (cubicTorus4 Ls Lt).Site ≃ (cubicTorus4 Ls Lt).Site :=
    { toFun := fun x => (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
      invFun := fun x => (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
      left_inv := fun ⟨t, a, b, c⟩ => by simp only [Prod.mk.injEq, fin_neg_sub_one_invol, true_and]
      right_inv := fun ⟨t, a, b, c⟩ => by simp only [Prod.mk.injEq, fin_neg_sub_one_invol, true_and] }
  have hsplit : ∀ V : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ),
      ∑ x : (cubicTorus4 Ls Lt).Site, sitePlaqSum4 Ls Lt N V x =
        (∑ x : (cubicTorus4 Ls Lt).Site,
          (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ V +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ V +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ V)) +
        (∑ x : (cubicTorus4 Ls Lt).Site,
          (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ V +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ V +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ V)) := by
    intro V
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp [sitePlaqSum4]
    ring
  rw [hsplit (cubic4TimeReflect Ls Lt N U), hsplit U]
  have h_tm :
      ∑ x : (cubicTorus4 Ls Lt).Site,
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩
            (cubic4TimeReflect Ls Lt N U) +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩
            (cubic4TimeReflect Ls Lt N U) +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩
            (cubic4TimeReflect Ls Lt N U)) =
      ∑ x : (cubicTorus4 Ls Lt).Site,
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U) := by
    refine Fintype.sum_equiv e_tm _ _ fun x => ?_
    rw [wilsonPlaquetteTerm_temporal_timeReflect Ls Lt N U x 1 (by decide),
      wilsonPlaquetteTerm_temporal_timeReflect Ls Lt N U x 2 (by decide),
      wilsonPlaquetteTerm_temporal_timeReflect Ls Lt N U x 3 (by decide)]
    rfl
  have h_sp :
      ∑ x : (cubicTorus4 Ls Lt).Site,
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩
            (cubic4TimeReflect Ls Lt N U) +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩
            (cubic4TimeReflect Ls Lt N U) +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩
            (cubic4TimeReflect Ls Lt N U)) =
      ∑ x : (cubicTorus4 Ls Lt).Site,
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U) := by
    refine Fintype.sum_equiv e_sp _ _ fun x => ?_
    rw [wilsonPlaquetteTerm_spatial_timeReflect Ls Lt N U x 1 2 (by decide) (by decide),
      wilsonPlaquetteTerm_spatial_timeReflect Ls Lt N U x 1 3 (by decide) (by decide),
      wilsonPlaquetteTerm_spatial_timeReflect Ls Lt N U x 2 3 (by decide) (by decide)]
    rfl
  rw [h_tm, h_sp]

theorem cubic4WilsonWeight_timeReflect (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    cubic4WilsonWeight Ls Lt N β (cubic4TimeReflect Ls Lt N U) =
      cubic4WilsonWeight Ls Lt N β U := by
  unfold cubic4WilsonWeight
  rw [cubic4WilsonAction_timeReflect]

/-- `cubic4TimeReflect` as a `MeasurePreserving` measurable equivalence on 4D gauge fields. -/
def cubic4TimeReflectEquiv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) where
  toFun := cubic4TimeReflect Ls Lt N
  invFun := cubic4TimeReflect Ls Lt N
  left_inv := cubic4TimeReflect_involutive Ls Lt N
  right_inv := cubic4TimeReflect_involutive Ls Lt N
  measurable_toFun := by
    change Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => cubic4TimeReflect Ls Lt N U)
    refine measurable_pi_iff.mpr fun ⟨⟨t, a, b, c⟩, d⟩ => ?_
    by_cases hd : d = 0
    · subst hd
      simp only [cubic4TimeReflect, ↓reduceIte]
      exact (continuous_inv (G := Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable.comp
        (measurable_pi_apply ((-t - 1, a, b, c), 0))
    · simp only [cubic4TimeReflect, hd, ↓reduceIte]
      exact measurable_pi_apply ((-t, a, b, c), d)
  measurable_invFun := by
    change Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => cubic4TimeReflect Ls Lt N U)
    refine measurable_pi_iff.mpr fun ⟨⟨t, a, b, c⟩, d⟩ => ?_
    by_cases hd : d = 0
    · subst hd
      simp only [cubic4TimeReflect, ↓reduceIte]
      exact (continuous_inv (G := Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable.comp
        (measurable_pi_apply ((-t - 1, a, b, c), 0))
    · simp only [cubic4TimeReflect, hd, ↓reduceIte]
      exact measurable_pi_apply ((-t, a, b, c), d)

theorem cubic4TimeReflectEquiv_mp (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.MeasurePreserving (cubic4TimeReflectEquiv Ls Lt N)
      (spacetimeHaarMeasure Ls Lt N) (spacetimeHaarMeasure Ls Lt N) :=
  ⟨(cubic4TimeReflectEquiv Ls Lt N).measurable, spacetimeHaarMeasure_timeReflect Ls Lt N⟩

/-- Exact Euclidean time-reflection invariance of the 4D lattice Schwinger functions. -/
theorem cubic4Schwinger_timeReflect_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)) :
    cubic4Schwinger Ls Lt N β n (fun i U => obs i (cubic4TimeReflect Ls Lt N U)) =
      cubic4Schwinger Ls Lt N β n obs := by
  unfold cubic4Schwinger
  congr 1
  calc ∫ U, (∏ i : Fin n, obs i (cubic4TimeReflect Ls Lt N U)) *
          ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N)
      = ∫ U, (∏ i : Fin n, obs i ((cubic4TimeReflectEquiv Ls Lt N) U)) *
          ((cubic4WilsonWeight Ls Lt N β ((cubic4TimeReflectEquiv Ls Lt N) U) : ℝ) : ℂ)
          ∂(spacetimeHaarMeasure Ls Lt N) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            change (∏ i : Fin n, obs i (cubic4TimeReflect Ls Lt N U)) *
                ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) =
              (∏ i : Fin n, obs i (cubic4TimeReflect Ls Lt N U)) *
                ((cubic4WilsonWeight Ls Lt N β (cubic4TimeReflect Ls Lt N U) : ℝ) : ℂ)
            rw [cubic4WilsonWeight_timeReflect]
    _ = ∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)
          ∂(spacetimeHaarMeasure Ls Lt N) :=
        (cubic4TimeReflectEquiv_mp Ls Lt N).integral_comp'
          (fun U => (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ))

/-- Boundary-slice links (`t = 0` or `t = M`, spatial directions `d ≠ 0`) on `cubicTorus4 Ls (2 * M)`. -/
def isBdryTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) : Prop :=
  e.2 ≠ 0 ∧ (e.1.1.val = 0 ∨ e.1.1.val = M)

/-- Positive-time links on `cubicTorus4 Ls (2 * M)`. -/
def isPosTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) : Prop :=
  if e.2 = 0 then e.1.1.val < M else (0 < e.1.1.val ∧ e.1.1.val < M)

/-- Negative-time links on `cubicTorus4 Ls (2 * M)`. -/
def isNegTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) : Prop :=
  if e.2 = 0 then M ≤ e.1.1.val else M < e.1.1.val

instance instDecidableBdryTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M] :
    DecidablePred (isBdryTimeLink Ls M) := fun e => by
  unfold isBdryTimeLink; infer_instance

instance instDecidablePosTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M] :
    DecidablePred (isPosTimeLink Ls M) := fun e => by
  unfold isPosTimeLink; infer_instance

instance instDecidableNegTimeLink (Ls M : ℕ) [NeZero Ls] [NeZero M] :
    DecidablePred (isNegTimeLink Ls M) := fun e => by
  unfold isNegTimeLink; infer_instance

/-- Observable supported solely on positive-time and boundary-slice links (`¬ isNegTimeLink`). -/
def SupportedOnPosTime (Ls M N : ℕ) [NeZero Ls] [NeZero M]
    (f : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) : Prop :=
  ∀ U V, (∀ e, ¬ isNegTimeLink Ls M e → U e = V e) → f U = f V

theorem fin_2M_neg_val (M : ℕ) [NeZero M] (t : Fin (2 * M)) :
    (-t).val = if t.val = 0 then 0 else 2 * M - t.val := by
  by_cases ht : t.val = 0
  · have ht0 : t = 0 := Fin.ext ht
    subst ht0
    simp
  · rw [if_neg ht]
    have hlt : 2 * M - t.val < 2 * M := by omega
    let r : Fin (2 * M) := ⟨2 * M - t.val, hlt⟩
    have hadd : t + r = 0 := by
      apply Fin.ext
      rw [Fin.val_add]
      change (t.val + (2 * M - t.val)) % (2 * M) = 0
      rw [Nat.add_sub_of_le (le_of_lt t.isLt), Nat.mod_self]
    have hr : -t = r := neg_eq_of_add_eq_zero_right hadd
    rw [hr]

theorem fin_2M_neg_sub_one_val (M : ℕ) [NeZero M] (t : Fin (2 * M)) :
    (-t - 1).val = 2 * M - 1 - t.val := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hlt : 2 * M - 1 - t.val < 2 * M := by omega
  let r : Fin (2 * M) := ⟨2 * M - 1 - t.val, hlt⟩
  have hadd : t + r = -1 := by
    have hadd1 : t + r + 1 = 0 := by
      apply Fin.ext
      have h1val : (1 : Fin (2 * M)).val = 1 := by
        change 1 % (2 * M) = 1
        exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_add, h1val, Fin.val_zero, Nat.mod_add_mod]
      have heq : t.val + r.val + 1 = 2 * M := by dsimp [r]; omega
      rw [heq, Nat.mod_self]
    exact eq_neg_of_add_eq_zero_left hadd1
  have hr : -t - 1 = r := by
    have h := neg_eq_of_add_eq_zero_right (show (t + 1) + r = 0 by
      rw [add_right_comm, hadd, neg_add_cancel])
    calc -t - 1 = -(t + 1) := (fin_neg_add_one t).symm
      _ = r := h
  rw [hr]

theorem link_partition_trichotomy (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) :
    (¬ isBdryTimeLink Ls M e ∧ ¬ isPosTimeLink Ls M e ↔ isNegTimeLink Ls M e) ∧
    (isBdryTimeLink Ls M e → ¬ isPosTimeLink Ls M e ∧ ¬ isNegTimeLink Ls M e) := by
  rcases e with ⟨⟨t, a, b, c⟩, d⟩
  have hlt : t.val < 2 * M := t.isLt
  by_cases hd : d = 0
  · simp only [isBdryTimeLink, isPosTimeLink, isNegTimeLink, hd, ne_eq, not_true_eq_false,
      false_and, not_false_eq_true, ↓reduceIte, true_and, false_implies, and_true]
    omega
  · simp only [isBdryTimeLink, isPosTimeLink, isNegTimeLink, hd, ne_eq, not_false_eq_true,
      true_and, ↓reduceIte]
    omega

theorem cubic4TimeReflectLink_zero (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (t : Fin Lt) (a b c : Fin Ls) :
    cubic4TimeReflectLink Ls Lt ((t, a, b, c), 0) = ((-t - 1, a, b, c), 0) := by
  simp [cubic4TimeReflectLink]

theorem cubic4TimeReflectLink_succ (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (t : Fin Lt) (a b c : Fin Ls) (d : Fin 4) (hd : d ≠ 0) :
    cubic4TimeReflectLink Ls Lt ((t, a, b, c), d) = ((-t, a, b, c), d) := by
  simp [cubic4TimeReflectLink, hd]

theorem isPosTimeLink_zero (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (t : Fin (2 * M)) (a b c : Fin Ls) :
    isPosTimeLink Ls M ((t, a, b, c), 0) ↔ t.val < M := by
  simp [isPosTimeLink]

theorem isPosTimeLink_ne_zero (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (t : Fin (2 * M)) (a b c : Fin Ls) {d : Fin 4} (hd : d ≠ 0) :
    isPosTimeLink Ls M ((t, a, b, c), d) ↔ (0 < t.val ∧ t.val < M) := by
  simp [isPosTimeLink, hd]

theorem isNegTimeLink_zero (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (t : Fin (2 * M)) (a b c : Fin Ls) :
    isNegTimeLink Ls M ((t, a, b, c), 0) ↔ M ≤ t.val := by
  simp [isNegTimeLink]

theorem isNegTimeLink_ne_zero (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (t : Fin (2 * M)) (a b c : Fin Ls) {d : Fin 4} (hd : d ≠ 0) :
    isNegTimeLink Ls M ((t, a, b, c), d) ↔ M < t.val := by
  simp [isNegTimeLink, hd]

theorem isBdryTimeLink_iff (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (t : Fin (2 * M)) (a b c : Fin Ls) (d : Fin 4) :
    isBdryTimeLink Ls M ((t, a, b, c), d) ↔ d ≠ 0 ∧ (t.val = 0 ∨ t.val = M) :=
  Iff.rfl

theorem cubic4TimeReflectLink_bdry_iff (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) :
    isBdryTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) ↔ isBdryTimeLink Ls M e := by
  have hM : 0 < M := NeZero.pos M
  rcases e with ⟨⟨t, a, b, c⟩, d⟩
  have hlt : t.val < 2 * M := t.isLt
  by_cases hd : d = 0
  · subst hd
    rw [cubic4TimeReflectLink_zero, isBdryTimeLink_iff, isBdryTimeLink_iff]
    simp
  · rw [cubic4TimeReflectLink_succ Ls (2 * M) t a b c d hd,
      isBdryTimeLink_iff, isBdryTimeLink_iff, fin_2M_neg_val M t]
    simp only [hd, ne_eq, not_false_eq_true, true_and]
    split_ifs <;> omega

theorem cubic4TimeReflect_bdry_fix (Ls M N : ℕ) [NeZero Ls] [NeZero M]
    (U : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    {e : (cubicTorus4 Ls (2 * M)).Link} (he : isBdryTimeLink Ls M e) :
    cubic4TimeReflect Ls (2 * M) N U e = U e := by
  rcases e with ⟨⟨t, a, b, c⟩, d⟩
  rw [isBdryTimeLink_iff] at he
  rcases he with ⟨hd, ht0 | htM⟩
  · have ht : t = 0 := Fin.ext ht0
    subst ht
    simp [cubic4TimeReflect, hd]
  · have hM_neg : -t = t := by
      apply Fin.ext
      rw [fin_2M_neg_val]
      have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
      rw [if_neg (by omega), htM]
      omega
    simp [cubic4TimeReflect, hd, hM_neg]

theorem cubic4TimeReflectLink_pos_iff_neg (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) :
    isPosTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) ↔ isNegTimeLink Ls M e := by
  have hM : 0 < M := NeZero.pos M
  rcases e with ⟨⟨t, a, b, c⟩, d⟩
  have hlt : t.val < 2 * M := t.isLt
  by_cases hd : d = 0
  · subst hd
    rw [cubic4TimeReflectLink_zero, isPosTimeLink_zero, isNegTimeLink_zero,
      fin_2M_neg_sub_one_val]
    omega
  · rw [cubic4TimeReflectLink_succ Ls (2 * M) t a b c d hd,
      isPosTimeLink_ne_zero Ls M (-t) a b c hd,
      isNegTimeLink_ne_zero Ls M t a b c hd,
      fin_2M_neg_val]
    split_ifs <;> omega
theorem cubic4TimeReflectLink_neg_iff_pos (Ls M : ℕ) [NeZero Ls] [NeZero M]
    (e : (cubicTorus4 Ls (2 * M)).Link) :
    isNegTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) ↔ isPosTimeLink Ls M e := by
  have h := cubic4TimeReflectLink_pos_iff_neg Ls M (cubic4TimeReflectLink Ls (2 * M) e)
  have hinv : cubic4TimeReflectLink Ls (2 * M) (cubic4TimeReflectLink Ls (2 * M) e) = e :=
    (cubic4TimeReflectLink Ls (2 * M)).left_inv e
  rw [hinv] at h
  exact h.symm

noncomputable def wilsonActionBdry (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  β * ∑ x : (cubicTorus4 Ls (2 * M)).Site,
    if (x.1.val = 0 ∨ x.1.val = M) then
      (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
       wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
       wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
    else 0

noncomputable def wilsonActionPos (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  β * ∑ x : (cubicTorus4 Ls (2 * M)).Site,
    ((if (0 < x.1.val ∧ x.1.val < M) then
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
      else 0) +
     (if x.1.val < M then
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U)
      else 0))

theorem wilsonAction_split_pos_neg (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ)
    (U : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes Ls (2 * M)) U =
      wilsonActionBdry Ls M N β U +
      wilsonActionPos Ls M N β U +
      wilsonActionPos Ls M N β (cubic4TimeReflect Ls (2 * M) N U) := by
  let S_neg : ℝ := β * ∑ x : (cubicTorus4 Ls (2 * M)).Site,
    ((if M < x.1.val then
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
      else 0) +
     (if M ≤ x.1.val then
        (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
         wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U)
      else 0))
  have h_sum_eq : wilsonAction β (cubic4Plaquettes Ls (2 * M)) U =
      wilsonActionBdry Ls M N β U + wilsonActionPos Ls M N β U + S_neg := by
    rw [wilsonAction_cubic4_eq_sum]
    dsimp [wilsonActionBdry, wilsonActionPos, S_neg]
    rw [← mul_add, ← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp [sitePlaqSum4]
    have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    by_cases ht0 : x.1.val = 0
    · have h1 : ¬ (0 < x.1.val ∧ x.1.val < M) := by omega
      have h2 : ¬ (M < x.1.val) := by omega
      have h3 : ¬ (M ≤ x.1.val) := by omega
      rw [if_pos (Or.inl ht0), if_neg h1, if_pos (by omega : x.1.val < M),
        if_neg h2, if_neg h3]
      ring
    · by_cases htM : x.1.val = M
      · have h1 : ¬ (0 < x.1.val ∧ x.1.val < M) := by omega
        have h2 : ¬ (x.1.val < M) := by omega
        have h3 : ¬ (M < x.1.val) := by omega
        rw [if_pos (Or.inr htM), if_neg h1, if_neg h2, if_neg h3,
          if_pos (by omega : M ≤ x.1.val)]
        ring
      · by_cases hltM : x.1.val < M
        · have h1 : ¬ (x.1.val = 0 ∨ x.1.val = M) := by omega
          have h2 : 0 < x.1.val ∧ x.1.val < M := by omega
          have h3 : ¬ (M < x.1.val) := by omega
          have h4 : ¬ (M ≤ x.1.val) := by omega
          rw [if_neg h1, if_pos h2, if_pos hltM, if_neg h3, if_neg h4]
          ring
        · have h1 : ¬ (x.1.val = 0 ∨ x.1.val = M) := by omega
          have h2 : ¬ (0 < x.1.val ∧ x.1.val < M) := by omega
          have h3 : M < x.1.val := by omega
          have h4 : M ≤ x.1.val := by omega
          rw [if_neg h1, if_neg h2, if_neg hltM, if_pos h3, if_pos h4]
          ring
  have h_neg_eq : S_neg = wilsonActionPos Ls M N β (cubic4TimeReflect Ls (2 * M) N U) := by
    dsimp [S_neg, wilsonActionPos]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    · let e_sp : (cubicTorus4 Ls (2 * M)).Site ≃ (cubicTorus4 Ls (2 * M)).Site :=
        { toFun := fun x => (-x.1, x.2.1, x.2.2.1, x.2.2.2)
          invFun := fun x => (-x.1, x.2.1, x.2.2.1, x.2.2.2)
          left_inv := fun ⟨t, a, b, c⟩ => by simp
          right_inv := fun ⟨t, a, b, c⟩ => by simp }
      refine Fintype.sum_equiv e_sp _ _ fun x => ?_
      have h_cond : (M < x.1.val) ↔ (0 < (-x.1).val ∧ (-x.1).val < M) := by
        have hlt := x.1.isLt
        rw [fin_2M_neg_val]
        by_cases ht0 : x.1.val = 0
        · rw [if_pos ht0]; omega
        · rw [if_neg ht0]; omega
      change (if M < x.1.val then _ else 0) =
        (if (0 < (-x.1).val ∧ (-x.1).val < M) then _ else 0)
      by_cases hx : M < x.1.val
      · rw [if_pos hx, if_pos (h_cond.mp hx)]
        dsimp only [e_sp, Equiv.coe_fn_mk]
        rw [wilsonPlaquetteTerm_spatial_timeReflect Ls (2 * M) N U
              (-x.1, x.2.1, x.2.2.1, x.2.2.2) 1 2 (by decide) (by decide),
            wilsonPlaquetteTerm_spatial_timeReflect Ls (2 * M) N U
              (-x.1, x.2.1, x.2.2.1, x.2.2.2) 1 3 (by decide) (by decide),
            wilsonPlaquetteTerm_spatial_timeReflect Ls (2 * M) N U
              (-x.1, x.2.1, x.2.2.1, x.2.2.2) 2 3 (by decide) (by decide)]
        simp [neg_neg]
      · rw [if_neg hx, if_neg (mt h_cond.mpr hx)]
    · let e_tm : (cubicTorus4 Ls (2 * M)).Site ≃ (cubicTorus4 Ls (2 * M)).Site :=
        { toFun := fun x => (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
          invFun := fun x => (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
          left_inv := fun ⟨t, a, b, c⟩ => by simp only [Prod.mk.injEq, fin_neg_sub_one_invol, true_and]
          right_inv := fun ⟨t, a, b, c⟩ => by simp only [Prod.mk.injEq, fin_neg_sub_one_invol, true_and] }
      refine Fintype.sum_equiv e_tm _ _ fun x => ?_
      have h_cond : (M ≤ x.1.val) ↔ (-x.1 - 1).val < M := by
        have hlt := x.1.isLt
        rw [fin_2M_neg_sub_one_val]
        omega
      change (if M ≤ x.1.val then _ else 0) = (if (-x.1 - 1).val < M then _ else 0)
      by_cases hx : M ≤ x.1.val
      · rw [if_pos hx, if_pos (h_cond.mp hx)]
        dsimp only [e_tm, Equiv.coe_fn_mk]
        rw [wilsonPlaquetteTerm_temporal_timeReflect Ls (2 * M) N U
              (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2) 1 (by decide),
            wilsonPlaquetteTerm_temporal_timeReflect Ls (2 * M) N U
              (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2) 2 (by decide),
            wilsonPlaquetteTerm_temporal_timeReflect Ls (2 * M) N U
              (-x.1 - 1, x.2.1, x.2.2.1, x.2.2.2) 3 (by decide)]
        simp only [fin_neg_sub_one_invol]
        rfl
      · rw [if_neg hx, if_neg (mt h_cond.mpr hx)]
  rw [h_sum_eq, h_neg_eq]

theorem wilsonPlaquetteTerm_depends_on_links
    {L : SpatialLattice} {N : ℕ} (p : LatticePlaquette L)
    (U V : GaugeField L (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hUV : ∀ (e : L.Link) (b : Bool), (e, b) ∈ p.loop → U e = V e) :
    wilsonPlaquetteTerm p U = wilsonPlaquetteTerm p V := by
  have hhol : ∀ (γ : List (L.Link × Bool)),
      (∀ (e : L.Link) (b : Bool), (e, b) ∈ γ → U e = V e) →
      pathHolonomy U γ = pathHolonomy V γ := by
    intro γ hγ
    induction γ with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨e, b⟩
      have he : U e = V e := hγ e b (by simp)
      have htl : pathHolonomy U tl = pathHolonomy V tl :=
        ih (fun e' b' hm => hγ e' b' (by simp [hm]))
      cases b <;> simp [pathHolonomy, he, htl]
  unfold wilsonPlaquetteTerm
  rw [hhol p.loop hUV]

theorem wilsonActionBdry_depends_only (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ)
    (U V : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hUV : ∀ e, isBdryTimeLink Ls M e → U e = V e) :
    wilsonActionBdry Ls M N β U = wilsonActionBdry Ls M N β V := by
  dsimp [wilsonActionBdry]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · have hsp : ∀ (d₁ d₂ : Fin 4), d₁ ≠ 0 → d₂ ≠ 0 →
        wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩ U =
        wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩ V := by
      intro d₁ d₂ hd₁ hd₂
      refine wilsonPlaquetteTerm_depends_on_links _ U V fun e b hm => ?_
      apply hUV
      have he_mem : e = (x, d₁) ∨ e = (cubicShift4 Ls (2 * M) d₁ x, d₂) ∨
          e = (cubicShift4 Ls (2 * M) d₂ x, d₁) ∨ e = (x, d₂) := by
        simp [cubic4Plaquette] at hm
        rcases hm with h | h | h | h <;> simp [h]
      have hsh_t : ∀ (d : Fin 4), d ≠ 0 → (cubicShift4 Ls (2 * M) d x).1 = x.1 := by
        intro d hd; rcases x with ⟨t, a, b', c⟩; fin_cases d <;> first | exact absurd rfl hd | rfl
      rcases he_mem with rfl | rfl | rfl | rfl
      · exact ⟨hd₁, hx⟩
      · exact ⟨hd₂, by rw [hsh_t d₁ hd₁]; exact hx⟩
      · exact ⟨hd₁, by rw [hsh_t d₂ hd₂]; exact hx⟩
      · exact ⟨hd₂, hx⟩
    rw [hsp 1 2 (by decide) (by decide), hsp 1 3 (by decide) (by decide),
      hsp 2 3 (by decide) (by decide)]
  · rfl

theorem not_isNeg_of_lt {Ls M : ℕ} [NeZero Ls] [NeZero M]
    (y : (cubicTorus4 Ls (2 * M)).Site) (d : Fin 4)
    (h0 : d = 0 → y.1.val < M) (hd : d ≠ 0 → y.1.val ≤ M) :
    ¬ isNegTimeLink Ls M (y, d) := by
  by_cases h : d = 0
  · simp only [isNegTimeLink, if_pos h]
    exact not_le_of_gt (h0 h)
  · simp only [isNegTimeLink, if_neg h]
    exact not_lt_of_ge (hd h)

theorem wilsonActionPos_supported_on_pos (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ)
    (U V : GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hUV : ∀ e, ¬ isNegTimeLink Ls M e → U e = V e) :
    wilsonActionPos Ls M N β U = wilsonActionPos Ls M N β V := by
  dsimp [wilsonActionPos]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases x with ⟨t, a, b', c⟩
  have hsh_t : ∀ (d : Fin 4), d ≠ 0 → ∀ y : (cubicTorus4 Ls (2 * M)).Site,
      (cubicShift4 Ls (2 * M) d y).1 = y.1 := by
    intro d hd ⟨t', a', b'', c'⟩; fin_cases d <;> first | exact absurd rfl hd | rfl
  have h1 : (if (0 < t.val ∧ t.val < M) then
        (wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 1 2,
            cubic4Plaquette_isPath (t, a, b', c) 1 2⟩ U +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 1 3,
            cubic4Plaquette_isPath (t, a, b', c) 1 3⟩ U +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 2 3,
            cubic4Plaquette_isPath (t, a, b', c) 2 3⟩ U)
      else 0) =
      (if (0 < t.val ∧ t.val < M) then
        (wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 1 2,
            cubic4Plaquette_isPath (t, a, b', c) 1 2⟩ V +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 1 3,
            cubic4Plaquette_isPath (t, a, b', c) 1 3⟩ V +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 2 3,
            cubic4Plaquette_isPath (t, a, b', c) 2 3⟩ V)
      else 0) := by
    split_ifs with hx
    · have hsp : ∀ (d₁ d₂ : Fin 4), d₁ ≠ 0 → d₂ ≠ 0 →
          wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) d₁ d₂,
              cubic4Plaquette_isPath (t, a, b', c) d₁ d₂⟩ U =
          wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) d₁ d₂,
              cubic4Plaquette_isPath (t, a, b', c) d₁ d₂⟩ V := by
        intro d₁ d₂ hd₁ hd₂
        refine wilsonPlaquetteTerm_depends_on_links _ U V fun e b hm => ?_
        apply hUV
        have he_mem : e = ((t, a, b', c), d₁) ∨
            e = (cubicShift4 Ls (2 * M) d₁ (t, a, b', c), d₂) ∨
            e = (cubicShift4 Ls (2 * M) d₂ (t, a, b', c), d₁) ∨
            e = ((t, a, b', c), d₂) := by
          simp [cubic4Plaquette] at hm
          rcases hm with h | h | h | h <;> simp [h]
        rcases he_mem with rfl | rfl | rfl | rfl
        · exact not_isNeg_of_lt (t, a, b', c) d₁ (fun h => absurd h hd₁) (fun _ => hx.2.le)
        · exact not_isNeg_of_lt _ d₂ (fun h => absurd h hd₂)
            (fun _ => by rw [hsh_t d₁ hd₁]; exact hx.2.le)
        · exact not_isNeg_of_lt _ d₁ (fun h => absurd h hd₁)
            (fun _ => by rw [hsh_t d₂ hd₂]; exact hx.2.le)
        · exact not_isNeg_of_lt (t, a, b', c) d₂ (fun h => absurd h hd₂) (fun _ => hx.2.le)
      rw [hsp 1 2 (by decide) (by decide), hsp 1 3 (by decide) (by decide),
        hsp 2 3 (by decide) (by decide)]
    · rfl
  have h2 : (if t.val < M then
        (wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 1,
            cubic4Plaquette_isPath (t, a, b', c) 0 1⟩ U +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 2,
            cubic4Plaquette_isPath (t, a, b', c) 0 2⟩ U +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 3,
            cubic4Plaquette_isPath (t, a, b', c) 0 3⟩ U)
      else 0) =
      (if t.val < M then
        (wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 1,
            cubic4Plaquette_isPath (t, a, b', c) 0 1⟩ V +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 2,
            cubic4Plaquette_isPath (t, a, b', c) 0 2⟩ V +
         wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 3,
            cubic4Plaquette_isPath (t, a, b', c) 0 3⟩ V)
      else 0) := by
    split_ifs with hx
    · have htm : ∀ (d : Fin 4), d ≠ 0 →
          wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 d,
              cubic4Plaquette_isPath (t, a, b', c) 0 d⟩ U =
          wilsonPlaquetteTerm ⟨(t, a, b', c), cubic4Plaquette (t, a, b', c) 0 d,
              cubic4Plaquette_isPath (t, a, b', c) 0 d⟩ V := by
        intro d hd
        refine wilsonPlaquetteTerm_depends_on_links _ U V fun e b hm => ?_
        apply hUV
        have he_mem : e = ((t, a, b', c), 0) ∨
            e = (cubicShift4 Ls (2 * M) 0 (t, a, b', c), d) ∨
            e = (cubicShift4 Ls (2 * M) d (t, a, b', c), 0) ∨
            e = ((t, a, b', c), d) := by
          simp [cubic4Plaquette] at hm
          rcases hm with h | h | h | h <;> simp [h]
        have hx1_le : (t + 1).val ≤ M := by
          have h1lt : 1 < 2 * M := by have := NeZero.pos M; omega
          have h1val : (1 : Fin (2 * M)).val = 1 := by
            change 1 % (2 * M) = 1
            exact Nat.mod_eq_of_lt h1lt
          rw [Fin.val_add, h1val, Nat.mod_eq_of_lt (by omega : t.val + 1 < 2 * M)]
          omega
        rcases he_mem with rfl | rfl | rfl | rfl
        · exact not_isNeg_of_lt (t, a, b', c) 0 (fun _ => hx) (fun h => absurd rfl h)
        · exact not_isNeg_of_lt _ d (fun h => absurd h hd) (fun _ => hx1_le)
        · exact not_isNeg_of_lt _ 0 (fun _ => by rw [hsh_t d hd]; exact hx)
            (fun h => absurd rfl h)
        · exact not_isNeg_of_lt (t, a, b', c) d (fun h => absurd h hd) (fun _ => hx.le)
      rw [htm 1 (by decide), htm 2 (by decide), htm 3 (by decide)]
    · rfl
  exact congrArg₂ (· + ·) h1 h2

theorem measurable_cubic4_plaquette_term (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (p : LatticePlaquette (cubicTorus4 Ls Lt)) :
    Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      wilsonPlaquetteTerm p U) := by
  have hev : ∀ e : (cubicTorus4 Ls Lt).Link,
      Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) => U e) := by
    intro e
    change Measurable (fun U : (cubicTorus4 Ls Lt).Link → _ => U e)
    exact measurable_pi_apply e
  have hhol : ∀ γ : List ((cubicTorus4 Ls Lt).Link × Bool),
      Measurable (fun U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        pathHolonomy U γ) := by
    intro γ
    induction γ with
    | nil => simpa [pathHolonomy] using measurable_const
    | cons hd tl ih =>
      rcases hd with ⟨e, b⟩
      cases b
      · simpa [pathHolonomy] using
          ((continuous_inv (G := Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable.comp (hev e)).mul ih
      · simpa [pathHolonomy] using (hev e).mul ih
  unfold wilsonPlaquetteTerm
  have h_ent : ∀ i : Fin N, Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (A : Matrix (Fin N) (Fin N) ℂ) i i) := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  exact measurable_const.sub (measurable_const.mul (h_tr.measurable.comp (hhol p.loop)))

theorem integrable_of_measurable_bound {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (f : α → ℂ) (hf : Measurable f) (C : ℝ) (hbd : ∀ x, ‖f x‖ ≤ C) :
    MeasureTheory.Integrable f μ := by
  refine (MeasureTheory.integrable_const C).mono' hf.stronglyMeasurable.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall hbd

theorem measurable_finset_sum_real {ι α : Type*} [MeasurableSpace α]
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => ∑ i ∈ s, f i a) :=
  Finset.measurable_sum s hf

theorem measurable_finset_sum_complex {ι α : Type*} [MeasurableSpace α]
    (s : Finset ι) (f : ι → α → ℂ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => ∑ i ∈ s, f i a) :=
  Finset.measurable_sum s hf

/--
**4D Wilson Lattice $n$-Point Osterwalder–Schrader Reflection Positivity** directly for
`cubic4Schwinger Ls (2 * M) N β`: for any finite family of measurable bounded
positive-time gauge-field observables `obs i k` (`SupportedOnPosTime`),
`0 ≤ Re ∑_{i,j} c_i · c̄_j · S^{(n_i+n_j)}((obs_i ∘ Θ)* ‖ obs_j)`.
-/
theorem cubic4Schwinger_refl_pos_n (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (m : ℕ) (n_pts : Fin m → ℕ) (c : Fin m → ℂ)
    (obs : ∀ i : Fin m, Fin (n_pts i) →
      (GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (h_meas : ∀ i k, Measurable (obs i k))
    (C_bd : ℝ) (hC_bd : 0 ≤ C_bd) (h_bd : ∀ i k U, ‖obs i k U‖ ≤ C_bd)
    (h_pos_supp : ∀ i k, SupportedOnPosTime Ls M N (obs i k)) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        cubic4Schwinger Ls (2 * M) N β (n_pts i + n_pts j)
          (Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
            (obs j))).re := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let G_4 := GaugeField (cubicTorus4 Ls (2 * M)) G
  let μ := spacetimeHaarMeasure Ls (2 * M) N
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob Ls (2 * M) N
  let Z := cubic4PartitionFn Ls (2 * M) N β
  have hZ_pos : 0 < Z := cubic4PartitionFn_pos Ls (2 * M) N β hβ
  let w_bdry : G_4 → ℝ := fun U => Real.exp (-wilsonActionBdry Ls M N β U)
  let w_pos : G_4 → ℝ := fun U => Real.exp (-wilsonActionPos Ls M N β U)
  have hw_bdry_meas : Measurable w_bdry := by
    have h_sum_meas : Measurable (fun U : G_4 => ∑ x : (cubicTorus4 Ls (2 * M)).Site,
        if (x.1.val = 0 ∨ x.1.val = M) then
          (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
           wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
        else (0 : ℝ)) := by
      refine Finset.measurable_sum Finset.univ fun x _ => ?_
      by_cases hx : x.1.val = 0 ∨ x.1.val = M
      · simp_rw [if_pos hx]
        exact ((measurable_cubic4_plaquette_term Ls (2 * M) N _).add
          (measurable_cubic4_plaquette_term Ls (2 * M) N _)).add
          (measurable_cubic4_plaquette_term Ls (2 * M) N _)
      · simp_rw [if_neg hx]
        exact measurable_const
    exact Real.continuous_exp.measurable.comp (Measurable.neg (measurable_const.mul h_sum_meas))
  have hw_pos_meas : Measurable w_pos := by
    have h_term : ∀ x : (cubicTorus4 Ls (2 * M)).Site, Measurable (fun U : G_4 =>
        (if (0 < x.1.val ∧ x.1.val < M) then
            (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
          else (0 : ℝ)) +
         (if x.1.val < M then
            (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U)
          else (0 : ℝ))) := by
      intro x
      refine Measurable.add ?_ ?_
      · by_cases hx : 0 < x.1.val ∧ x.1.val < M
        · simp_rw [if_pos hx]
          exact ((measurable_cubic4_plaquette_term Ls (2 * M) N _).add
            (measurable_cubic4_plaquette_term Ls (2 * M) N _)).add
            (measurable_cubic4_plaquette_term Ls (2 * M) N _)
        · simp_rw [if_neg hx]
          exact measurable_const
      · by_cases hx : x.1.val < M
        · simp_rw [if_pos hx]
          exact ((measurable_cubic4_plaquette_term Ls (2 * M) N _).add
            (measurable_cubic4_plaquette_term Ls (2 * M) N _)).add
            (measurable_cubic4_plaquette_term Ls (2 * M) N _)
        · simp_rw [if_neg hx]
          exact measurable_const
    have h_sum_meas : Measurable (fun U : G_4 => ∑ x : (cubicTorus4 Ls (2 * M)).Site,
        ((if (0 < x.1.val ∧ x.1.val < M) then
            (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 2, cubic4Plaquette_isPath x 1 2⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 1 3, cubic4Plaquette_isPath x 1 3⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 2 3, cubic4Plaquette_isPath x 2 3⟩ U)
          else (0 : ℝ)) +
         (if x.1.val < M then
            (wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 1, cubic4Plaquette_isPath x 0 1⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 2, cubic4Plaquette_isPath x 0 2⟩ U +
             wilsonPlaquetteTerm ⟨x, cubic4Plaquette x 0 3, cubic4Plaquette_isPath x 0 3⟩ U)
          else (0 : ℝ)))) :=
      measurable_finset_sum_real Finset.univ _ (fun x _ => h_term x)
    have h_act_meas : Measurable (fun U : G_4 => wilsonActionPos Ls M N β U) :=
      measurable_const.mul h_sum_meas
    exact Real.continuous_exp.measurable.comp h_act_meas.neg
  have hw_bdry_bounds : ∀ U, 0 ≤ w_bdry U ∧ w_bdry U ≤ 1 := fun U => by
    have hact : 0 ≤ wilsonActionBdry Ls M N β U := by
      dsimp [wilsonActionBdry]
      refine mul_nonneg hβ (Finset.sum_nonneg fun x _ => ?_)
      split_ifs
      · exact add_nonneg (add_nonneg (wilsonPlaquetteTerm_bounds _ U).1
          (wilsonPlaquetteTerm_bounds _ U).1) (wilsonPlaquetteTerm_bounds _ U).1
      · exact le_rfl
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  have hw_pos_bounds : ∀ U, 0 ≤ w_pos U ∧ w_pos U ≤ 1 := fun U => by
    have hact : 0 ≤ wilsonActionPos Ls M N β U := by
      dsimp [wilsonActionPos]
      refine mul_nonneg hβ (Finset.sum_nonneg fun x _ => add_nonneg ?_ ?_)
      · split_ifs
        · exact add_nonneg (add_nonneg (wilsonPlaquetteTerm_bounds _ U).1
            (wilsonPlaquetteTerm_bounds _ U).1) (wilsonPlaquetteTerm_bounds _ U).1
        · exact le_rfl
      · split_ifs
        · exact add_nonneg (add_nonneg (wilsonPlaquetteTerm_bounds _ U).1
            (wilsonPlaquetteTerm_bounds _ U).1) (wilsonPlaquetteTerm_bounds _ U).1
        · exact le_rfl
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  have hw_fact : ∀ U, cubic4WilsonWeight Ls (2 * M) N β U =
      w_bdry U * w_pos U * w_pos (cubic4TimeReflect Ls (2 * M) N U) := by
    intro U
    unfold cubic4WilsonWeight
    rw [wilsonAction_split_pos_neg Ls M N β U]
    dsimp [w_bdry, w_pos]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  let F_sum : G_4 → ℂ := fun U =>
    (∑ j : Fin m, starRingEnd ℂ (c j) * ∏ k : Fin (n_pts j), obs j k U) * ((w_pos U : ℝ) : ℂ)
  have hF_meas : Measurable F_sum := by
    have hF_sum_meas : Measurable (fun U : G_4 =>
        (∑ j : Fin m, starRingEnd ℂ (c j) * ∏ k : Fin (n_pts j), obs j k U : ℂ)) :=
      Finset.measurable_sum (Finset.univ : Finset (Fin m)) fun j _ =>
        measurable_const.mul (Finset.measurable_prod Finset.univ fun k _ => h_meas j k)
    exact hF_sum_meas.mul (Complex.continuous_ofReal.measurable.comp hw_pos_meas)
  let C_sum : ℝ := ∑ j : Fin m, ‖c j‖ * C_bd ^ (n_pts j)
  have hF_bd : ∀ U, ‖F_sum U‖ ≤ C_sum := fun U => by
    dsimp [F_sum, C_sum]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_pos_bounds U).1]
    let f_term : Fin m → ℂ := fun j => starRingEnd ℂ (c j) * ∏ k : Fin (n_pts j), obs j k U
    change ‖∑ j : Fin m, f_term j‖ * w_pos U ≤ ∑ j : Fin m, ‖c j‖ * C_bd ^ (n_pts j)
    calc ‖(∑ j : Fin m, f_term j : ℂ)‖ * w_pos U
        ≤ ‖(∑ j : Fin m, f_term j : ℂ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hw_pos_bounds U).2 (norm_nonneg _)
      _ = ‖(∑ j : Fin m, f_term j : ℂ)‖ := mul_one _
      _ ≤ (∑ j : Fin m, ‖f_term j‖ : ℝ) :=
          norm_sum_le (Finset.univ : Finset (Fin m)) f_term
      _ ≤ (∑ j : Fin m, ‖c j‖ * C_bd ^ (n_pts j) : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          dsimp [f_term]
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left
            (norm_prod_fin_le (fun k => obs j k U) C_bd hC_bd (fun k => h_bd j k U))
            (norm_nonneg _)
  have hF_supp : SupportedOnPosTime Ls M N F_sum := by
    intro U V hUV
    dsimp [F_sum, w_pos]
    rw [wilsonActionPos_supported_on_pos Ls M N β U V hUV]
    refine congrArg (· * _) ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine congrArg (starRingEnd ℂ (c j) * ·) ?_
    exact Finset.prod_congr rfl fun k _ => h_pos_supp j k U V hUV
  let θ_F : G_4 → ℂ := fun U =>
    starRingEnd ℂ (F_sum (cubic4TimeReflect Ls (2 * M) N U)) * F_sum U * ((w_bdry U : ℝ) : ℂ)
  have hθ_F_meas : Measurable θ_F :=
    ((continuous_star.measurable.comp
      (hF_meas.comp (cubic4TimeReflectEquiv Ls (2 * M) N).measurable)).mul hF_meas).mul
      (Complex.continuous_ofReal.measurable.comp hw_bdry_meas)
  have h_int_ij : ∀ i j : Fin m, MeasureTheory.Integrable (fun U =>
      c i * starRingEnd ℂ (c j) *
        ((∏ x : Fin (n_pts i + n_pts j),
            Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
              (obs j) x U) *
          ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ))) μ := by
    intro i j
    have hm : Measurable (fun U =>
        c i * starRingEnd ℂ (c j) *
          ((∏ x : Fin (n_pts i + n_pts j),
              Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
                (obs j) x U) *
            ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ))) := by
      refine measurable_const.mul ((Finset.measurable_prod Finset.univ fun x _ => ?_).mul
        (Complex.continuous_ofReal.measurable.comp (measurable_cubic4WilsonWeight Ls (2 * M) N β)))
      induction x using Fin.addCases with
      | left k =>
        simp only [Fin.append_left]
        exact continuous_star.measurable.comp
          ((h_meas i k).comp (cubic4TimeReflectEquiv Ls (2 * M) N).measurable)
      | right k =>
        simp only [Fin.append_right]
        exact h_meas j k
    refine integrable_of_measurable_bound μ _ hm
      (‖c i‖ * ‖c j‖ * C_bd ^ (n_pts i + n_pts j)) fun U => ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    have hwb := cubic4WilsonWeight_bounds Ls (2 * M) N β hβ U
    have hwnn : 0 ≤ cubic4WilsonWeight Ls (2 * M) N β U := by
      unfold cubic4WilsonWeight; exact (Real.exp_pos _).le
    rw [abs_of_nonneg hwnn]
    have hpb : ‖∏ x : Fin (n_pts i + n_pts j),
        Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
          (obs j) x U‖ ≤ C_bd ^ (n_pts i + n_pts j) := by
      refine norm_prod_fin_le _ C_bd hC_bd fun x => ?_
      induction x using Fin.addCases with
      | left k =>
        simp only [Fin.append_left, Complex.norm_conj]
        exact h_bd i k _
      | right k =>
        simp only [Fin.append_right]
        exact h_bd j k U
    calc ‖c i‖ * ‖c j‖ * (‖∏ x : Fin (n_pts i + n_pts j), _‖ * cubic4WilsonWeight Ls (2 * M) N β U)
        ≤ ‖c i‖ * ‖c j‖ * (C_bd ^ (n_pts i + n_pts j) * 1) := by
            gcongr; exact hwb.2
      _ = ‖c i‖ * ‖c j‖ * C_bd ^ (n_pts i + n_pts j) := by ring
  have h_sum_eq :
      (∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) *
          cubic4Schwinger Ls (2 * M) N β (n_pts i + n_pts j)
            (Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
              (obs j))) =
      ((Z : ℂ)⁻¹) * ∫ U, θ_F U ∂μ := by
    unfold cubic4Schwinger
    have h_pull : ∀ i j : Fin m,
        c i * starRingEnd ℂ (c j) * (((Z : ℂ)⁻¹) *
          ∫ U, (∏ x : Fin (n_pts i + n_pts j),
              Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
                (obs j) x U) *
            ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ) ∂μ) =
        ((Z : ℂ)⁻¹) * ∫ U, c i * starRingEnd ℂ (c j) *
          ((∏ x : Fin (n_pts i + n_pts j),
              Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
                (obs j) x U) *
            ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ)) ∂μ := by
      intro i j
      rw [MeasureTheory.integral_const_mul]
      ring
    change (∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) * (((Z : ℂ)⁻¹) * ∫ U, _ ∂μ)) =
      ((Z : ℂ)⁻¹) * ∫ U, θ_F U ∂μ
    simp_rw [h_pull, ← Finset.mul_sum]
    congr 1
    have h_in : ∀ i : Fin m,
        (∑ j : Fin m, ∫ U, c i * starRingEnd ℂ (c j) *
          ((∏ x : Fin (n_pts i + n_pts j),
              Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
                (obs j) x U) *
            ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ)) ∂μ) =
        ∫ U, ∑ j : Fin m, c i * starRingEnd ℂ (c j) *
          ((∏ x : Fin (n_pts i + n_pts j),
              Fin.append (fun k U => starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U)))
                (obs j) x U) *
            ((cubic4WilsonWeight Ls (2 * M) N β U : ℝ) : ℂ)) ∂μ :=
      fun i => (MeasureTheory.integral_finset_sum _ (fun j _ => h_int_ij i j)).symm
    simp_rw [h_in]
    rw [← MeasureTheory.integral_finset_sum _ (fun i _ =>
      MeasureTheory.integrable_finset_sum _ (fun j _ => h_int_ij i j))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    dsimp [θ_F, F_sum]
    simp_rw [Fin.prod_univ_add, Fin.append_left, Fin.append_right, hw_fact U]
    simp only [map_mul, map_sum, map_prod, Complex.conj_conj, Complex.conj_ofReal,
      Complex.ofReal_mul]
    let L : Fin m → ℂ := fun i => c i * ∏ k : Fin (n_pts i),
      starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U))
    let R : Fin m → ℂ := fun j => starRingEnd ℂ (c j) * ∏ k : Fin (n_pts j), obs j k U
    calc ∑ i : Fin m, ∑ j : Fin m, c i * starRingEnd ℂ (c j) *
          ((∏ k : Fin (n_pts i), starRingEnd ℂ (obs i k (cubic4TimeReflect Ls (2 * M) N U))) *
           (∏ k : Fin (n_pts j), obs j k U) *
           ((w_bdry U : ℂ) * (w_pos U : ℂ) * (w_pos (cubic4TimeReflect Ls (2 * M) N U) : ℂ)))
        = ∑ i : Fin m, ∑ j : Fin m, L i * (R j *
            ((w_bdry U : ℂ) * (w_pos U : ℂ) * (w_pos (cubic4TimeReflect Ls (2 * M) N U) : ℂ))) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            dsimp only [L, R]; ring
      _ = ∑ i : Fin m, L i * ((∑ j : Fin m, R j) *
            ((w_bdry U : ℂ) * (w_pos U : ℂ) * (w_pos (cubic4TimeReflect Ls (2 * M) N U) : ℂ))) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = (∑ i : Fin m, L i) * ((∑ j : Fin m, R j) *
            ((w_bdry U : ℂ) * (w_pos U : ℂ) * (w_pos (cubic4TimeReflect Ls (2 * M) N U) : ℂ))) := by
            rw [← Finset.sum_mul]
      _ = ((∑ i : Fin m, L i) * (w_pos (cubic4TimeReflect Ls (2 * M) N U) : ℂ)) *
            ((∑ j : Fin m, R j) * (w_pos U : ℂ)) * (w_bdry U : ℂ) := by ring
  rw [h_sum_eq, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  refine mul_nonneg (inv_nonneg.mpr hZ_pos.le) ?_
  let p_b := isBdryTimeLink Ls M
  let E_b := { e : (cubicTorus4 Ls (2 * M)).Link // p_b e }
  let E_nb := { e : (cubicTorus4 Ls (2 * M)).Link // ¬ p_b e }
  let p_p : E_nb → Prop := fun e => isPosTimeLink Ls M e.1
  let E_p := { e : E_nb // p_p e }
  let E_n := { e : E_nb // ¬ p_p e }
  let e₁ : G_4 ≃ᵐ (E_b → G) × (E_nb → G) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : (cubicTorus4 Ls (2 * M)).Link => G) p_b
  let e₂ : (E_nb → G) ≃ᵐ (E_p → G) × (E_n → G) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : E_nb => G) p_p
  let μ_b : MeasureTheory.Measure (E_b → G) := MeasureTheory.Measure.pi (fun _ => suHaar N)
  let μ_nb : MeasureTheory.Measure (E_nb → G) := MeasureTheory.Measure.pi (fun _ => suHaar N)
  let μ_p : MeasureTheory.Measure (E_p → G) := MeasureTheory.Measure.pi (fun _ => suHaar N)
  let μ_n : MeasureTheory.Measure (E_n → G) := MeasureTheory.Measure.pi (fun _ => suHaar N)
  haveI : MeasureTheory.IsProbabilityMeasure μ_b := by dsimp [μ_b]; infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μ_nb := by dsimp [μ_nb]; infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μ_p := by dsimp [μ_p]; infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μ_n := by dsimp [μ_n]; infer_instance
  have mp₁ : MeasureTheory.MeasurePreserving e₁ μ (μ_b.prod μ_nb) :=
    MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (fun _ : (cubicTorus4 Ls (2 * M)).Link => suHaar N) p_b
  have mp₂ : MeasureTheory.MeasurePreserving e₂ μ_nb (μ_p.prod μ_n) :=
    MeasureTheory.measurePreserving_piEquivPiSubtypeProd (fun _ : E_nb => suHaar N) p_p
  let reflIdx : E_p ≃ E_n :=
    { toFun := fun ⟨⟨e, hnb⟩, hp⟩ =>
        ⟨⟨cubic4TimeReflectLink Ls (2 * M) e,
            fun hb => hnb ((cubic4TimeReflectLink_bdry_iff Ls M e).mp hb)⟩,
          fun hp' => ((link_partition_trichotomy Ls M _).1.mpr
            ((cubic4TimeReflectLink_neg_iff_pos Ls M e).mpr hp)).2 hp'⟩
      invFun := fun ⟨⟨e, hnb⟩, hnp⟩ =>
        ⟨⟨cubic4TimeReflectLink Ls (2 * M) e,
            fun hb => hnb ((cubic4TimeReflectLink_bdry_iff Ls M e).mp hb)⟩,
          (cubic4TimeReflectLink_pos_iff_neg Ls M e).mpr
            ((link_partition_trichotomy Ls M e).1.mp ⟨hnb, hnp⟩)⟩
      left_inv := fun ⟨⟨e, _⟩, _⟩ => by
        apply Subtype.ext; apply Subtype.ext; exact (cubic4TimeReflectLink Ls (2 * M)).left_inv e
      right_inv := fun ⟨⟨e, _⟩, _⟩ => by
        apply Subtype.ext; apply Subtype.ext; exact (cubic4TimeReflectLink Ls (2 * M)).right_inv e }
  let e_refl : (E_p → G) ≃ᵐ (E_n → G) :=
    { toFun := fun U_p e_n =>
        if e_n.1.1.2 = 0 then (U_p (reflIdx.symm e_n))⁻¹ else U_p (reflIdx.symm e_n)
      invFun := fun U_n e_p =>
        if e_p.1.1.2 = 0 then (U_n (reflIdx e_p))⁻¹ else U_n (reflIdx e_p)
      left_inv := fun U_p => by
        funext ⟨⟨e, hnb⟩, hp⟩
        have hd_eq : (reflIdx ⟨⟨e, hnb⟩, hp⟩).1.1.2 = e.2 := by
          dsimp [reflIdx, cubic4TimeReflectLink]
          split_ifs <;> rfl
        dsimp only
        by_cases hd : e.2 = 0
        · rw [hd_eq, if_pos hd, if_pos hd, reflIdx.symm_apply_apply, inv_inv]
        · rw [hd_eq, if_neg hd, if_neg hd, reflIdx.symm_apply_apply]
      right_inv := fun U_n => by
        funext ⟨⟨e, hnb⟩, hnp⟩
        have hd_eq : (reflIdx.symm ⟨⟨e, hnb⟩, hnp⟩).1.1.2 = e.2 := by
          dsimp [reflIdx, cubic4TimeReflectLink]
          split_ifs <;> rfl
        dsimp only
        by_cases hd : e.2 = 0
        · rw [hd_eq, if_pos hd, if_pos hd, reflIdx.apply_symm_apply, inv_inv]
        · rw [hd_eq, if_neg hd, if_neg hd, reflIdx.apply_symm_apply]
      measurable_toFun := by
        refine measurable_pi_iff.mpr fun e_n => ?_
        change Measurable (fun U_p : E_p → G =>
          if e_n.1.1.2 = 0 then (U_p (reflIdx.symm e_n))⁻¹ else U_p (reflIdx.symm e_n))
        split_ifs
        · exact (continuous_inv (G := G)).measurable.comp (measurable_pi_apply (reflIdx.symm e_n))
        · exact measurable_pi_apply (reflIdx.symm e_n)
      measurable_invFun := by
        refine measurable_pi_iff.mpr fun e_p => ?_
        change Measurable (fun U_n : E_n → G =>
          if e_p.1.1.2 = 0 then (U_n (reflIdx e_p))⁻¹ else U_n (reflIdx e_p))
        split_ifs
        · exact (continuous_inv (G := G)).measurable.comp (measurable_pi_apply (reflIdx e_p))
        · exact measurable_pi_apply (reflIdx e_p) }
  have he_refl_app : ∀ (U_p : E_p → G) (e_n : E_n),
      e_refl U_p e_n =
        if e_n.1.1.2 = 0 then (U_p (reflIdx.symm e_n))⁻¹ else U_p (reflIdx.symm e_n) :=
    fun _ _ => rfl
  have mp_refl : MeasureTheory.MeasurePreserving e_refl μ_p μ_n := by
    refine ⟨e_refl.measurable, ?_⟩
    symm
    refine MeasureTheory.Measure.pi_eq fun s hs => ?_
    rw [MeasureTheory.Measure.map_apply e_refl.measurable (MeasurableSet.univ_pi hs)]
    let φ : E_p → G → G := fun e_p u => if e_p.1.1.2 = 0 then u⁻¹ else u
    have hpre : e_refl ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ (fun e_p => φ e_p ⁻¹' s (reflIdx e_p)) := by
      ext U_p
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, e_refl, φ]
      constructor
      · intro h e_p
        have hd_eq : (reflIdx e_p).1.1.2 = e_p.1.1.2 := by
          rcases e_p with ⟨⟨e, hnb⟩, hp⟩
          dsimp [reflIdx, cubic4TimeReflectLink]
          split_ifs <;> rfl
        have he := h (reflIdx e_p)
        rw [he_refl_app, hd_eq, reflIdx.symm_apply_apply] at he
        exact he
      · intro h e_n
        have hd_eq : (reflIdx.symm e_n).1.1.2 = e_n.1.1.2 := by
          rcases e_n with ⟨⟨e, hnb⟩, hnp⟩
          dsimp [reflIdx, cubic4TimeReflectLink]
          split_ifs <;> rfl
        have he := h (reflIdx.symm e_n)
        rw [reflIdx.apply_symm_apply] at he
        rw [he_refl_app, ← hd_eq]
        exact he
    rw [hpre]
    have hpi : μ_p (Set.pi Set.univ (fun e_p => φ e_p ⁻¹' s (reflIdx e_p))) =
        ∏ e_p : E_p, suHaar N (φ e_p ⁻¹' s (reflIdx e_p)) :=
      MeasureTheory.Measure.pi_pi (fun _ => suHaar N) _
    rw [hpi]
    have h_each : ∀ e_p : E_p, suHaar N (φ e_p ⁻¹' s (reflIdx e_p)) = suHaar N (s (reflIdx e_p)) := by
      intro e_p
      by_cases hd : e_p.1.1.2 = 0
      · simp only [φ, hd, ↓reduceIte]
        rw [← MeasureTheory.Measure.map_apply (continuous_inv (G := G)).measurable
          (hs (reflIdx e_p)), suHaar_map_inv N]
      · simp only [φ, hd, ↓reduceIte]; rfl
    rw [Finset.prod_congr rfl fun e_p _ => h_each e_p]
    exact Fintype.prod_equiv reflIdx (fun e_p => suHaar N (s (reflIdx e_p)))
      (fun e_n => suHaar N (s e_n)) (fun _ => rfl)
  let combine : (E_b → G) → (E_p → G) → (E_p → G) → G_4 :=
    fun U_b U_p U_p' => e₁.symm (U_b, e₂.symm (U_p, e_refl U_p'))
  have h_comb_bdry : ∀ U_b U_p U_p' (e : (cubicTorus4 Ls (2 * M)).Link) (hb : p_b e),
      combine U_b U_p U_p' e = U_b ⟨e, hb⟩ := fun U_b U_p U_p' e hb =>
    congrArg (fun q => q.1 ⟨e, hb⟩) (e₁.apply_symm_apply (U_b, e₂.symm (U_p, e_refl U_p')))
  have h_comb_pos : ∀ U_b U_p U_p' (e : (cubicTorus4 Ls (2 * M)).Link)
      (hnb : ¬ p_b e) (hp : p_p ⟨e, hnb⟩),
      combine U_b U_p U_p' e = U_p ⟨⟨e, hnb⟩, hp⟩ := fun U_b U_p U_p' e hnb hp =>
    (congrArg (fun q => q.2 ⟨e, hnb⟩)
      (e₁.apply_symm_apply (U_b, e₂.symm (U_p, e_refl U_p')))).trans
      (congrArg (fun q => q.1 ⟨⟨e, hnb⟩, hp⟩) (e₂.apply_symm_apply (U_p, e_refl U_p')))
  have h_comb_neg : ∀ U_b U_p U_p' (e : (cubicTorus4 Ls (2 * M)).Link)
      (hnb : ¬ p_b e) (hnp : ¬ p_p ⟨e, hnb⟩),
      combine U_b U_p U_p' e = e_refl U_p' ⟨⟨e, hnb⟩, hnp⟩ := fun U_b U_p U_p' e hnb hnp =>
    (congrArg (fun q => q.2 ⟨e, hnb⟩)
      (e₁.apply_symm_apply (U_b, e₂.symm (U_p, e_refl U_p')))).trans
      (congrArg (fun q => q.2 ⟨⟨e, hnb⟩, hnp⟩) (e₂.apply_symm_apply (U_p, e_refl U_p')))
  have h_combine_reflect : ∀ U_b U_p U_p',
      cubic4TimeReflect Ls (2 * M) N (combine U_b U_p U_p') = combine U_b U_p' U_p := by
    intro U_b U_p U_p'
    funext e
    by_cases hb : isBdryTimeLink Ls M e
    · rw [cubic4TimeReflect_bdry_fix Ls M N _ hb, h_comb_bdry _ _ _ e hb, h_comb_bdry _ _ _ e hb]
    · have hc_e := cubic4TimeReflectLink_bdry_iff Ls M e
      have hb_refl : ¬ isBdryTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) :=
        fun h => hb (hc_e.mp h)
      have h_lhs_val : cubic4TimeReflect Ls (2 * M) N (combine U_b U_p U_p') e =
          if e.2 = 0 then (combine U_b U_p U_p' (cubic4TimeReflectLink Ls (2 * M) e))⁻¹
          else combine U_b U_p U_p' (cubic4TimeReflectLink Ls (2 * M) e) := by
        rcases e with ⟨⟨t, a, b', c⟩, d⟩
        by_cases hd : d = 0 <;> simp [cubic4TimeReflect, cubic4TimeReflectLink, hd]
      rw [h_lhs_val]
      by_cases hp : isPosTimeLink Ls M e
      · have hn_refl : isNegTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) :=
          (cubic4TimeReflectLink_neg_iff_pos Ls M e).mpr hp
        have hnp_refl : ¬ isPosTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) :=
          ((link_partition_trichotomy Ls M _).1.mpr hn_refl).2
        rw [h_comb_neg U_b U_p U_p' _ hb_refl hnp_refl, h_comb_pos U_b U_p' U_p e hb hp,
          he_refl_app]
        have hd_eq : (⟨⟨cubic4TimeReflectLink Ls (2 * M) e, hb_refl⟩, hnp_refl⟩ : E_n).1.1.2 = e.2 := by
          rcases e with ⟨⟨t, a, b', c⟩, d⟩
          dsimp [cubic4TimeReflectLink]
          split_ifs <;> rfl
        have hrefl_eq : reflIdx.symm ⟨⟨cubic4TimeReflectLink Ls (2 * M) e, hb_refl⟩, hnp_refl⟩ =
            ⟨⟨e, hb⟩, hp⟩ := by
          apply Subtype.ext; apply Subtype.ext
          exact (cubic4TimeReflectLink Ls (2 * M)).left_inv e
        rw [hd_eq, hrefl_eq]
        by_cases hd : e.2 = 0
        · simp only [hd, ↓reduceIte]
          exact inv_inv _
        · simp only [hd, ↓reduceIte]
      · have hn : isNegTimeLink Ls M e := (link_partition_trichotomy Ls M e).1.mp ⟨hb, hp⟩
        have hp_refl : isPosTimeLink Ls M (cubic4TimeReflectLink Ls (2 * M) e) :=
          (cubic4TimeReflectLink_pos_iff_neg Ls M e).mpr hn
        rw [h_comb_pos U_b U_p U_p' _ hb_refl hp_refl, h_comb_neg U_b U_p' U_p e hb hp,
          he_refl_app]
        have hrefl_eq : reflIdx.symm ⟨⟨e, hb⟩, hp⟩ =
            ⟨⟨cubic4TimeReflectLink Ls (2 * M) e, hb_refl⟩, hp_refl⟩ := rfl
        rw [hrefl_eq]
  have h_bdry_const : ∀ U_b U_p U_p',
      w_bdry (combine U_b U_p U_p') = w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) := by
    intro U_b U_p U_p'
    dsimp [w_bdry]
    congr 2
    refine wilsonActionBdry_depends_only Ls M N β _ _ fun e he => ?_
    rw [h_comb_bdry _ _ _ e he, h_comb_bdry _ _ _ e he]
  let g_val : (E_b → G) → (E_p → G) → ℂ :=
    fun U_b U_p => F_sum (combine U_b U_p (fun _ => 1))
  have h_F_indep : ∀ U_b U_p U_p', F_sum (combine U_b U_p U_p') = g_val U_b U_p := by
    intro U_b U_p U_p'
    refine hF_supp _ _ fun e hne => ?_
    by_cases hb : isBdryTimeLink Ls M e
    · rw [h_comb_bdry _ _ _ e hb, h_comb_bdry _ _ _ e hb]
    · have hp : isPosTimeLink Ls M e := by
        by_contra hnp
        exact hne ((link_partition_trichotomy Ls M e).1.mp ⟨hb, hnp⟩)
      rw [h_comb_pos _ _ _ e hb hp, h_comb_pos _ _ _ e hb hp]
  have hm_comb2 : Measurable (fun z : (E_b → G) × ((E_p → G) × (E_p → G)) =>
      combine z.1 z.2.1 z.2.2) := by
    have hm1 : Measurable (fun q : (E_p → G) × (E_p → G) => e₂.symm (q.1, e_refl q.2)) :=
      e₂.symm.measurable.comp (measurable_fst.prodMk (e_refl.measurable.comp measurable_snd))
    exact e₁.symm.measurable.comp (measurable_fst.prodMk (hm1.comp measurable_snd))
  have h_int_rewrite :
      ∫ U, θ_F U ∂μ =
        ∫ U_b, ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) : ℝ) : ℂ) *
          (∫ U_p, (∫ U_p', starRingEnd ℂ (g_val U_b U_p') * g_val U_b U_p ∂μ_p) ∂μ_p) ∂μ_b := by
    have hmp1_sym := MeasureTheory.MeasurePreserving.symm e₁ mp₁
    have hmp2_sym := MeasureTheory.MeasurePreserving.symm e₂ mp₂
    rw [← hmp1_sym.integral_comp' θ_F]
    have h_int1 : MeasureTheory.Integrable (fun p => θ_F (e₁.symm p)) (μ_b.prod μ_nb) :=
      integrable_of_measurable_bound (μ_b.prod μ_nb) _ (hθ_F_meas.comp e₁.symm.measurable)
        (C_sum ^ 2) fun p => by
          dsimp [θ_F]
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw_bdry_bounds _).1]
          calc ‖F_sum _‖ * ‖F_sum _‖ * w_bdry _
              ≤ C_sum * C_sum * 1 := by
                gcongr
                · exact hF_bd _
                · exact hF_bd _
                · exact (hw_bdry_bounds _).2
            _ = C_sum ^ 2 := by ring
    rw [MeasureTheory.integral_prod _ h_int1]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_b => ?_)
    dsimp only
    rw [← hmp2_sym.integral_comp' (fun U_nb => θ_F (e₁.symm (U_b, U_nb)))]
    have h_int2 : MeasureTheory.Integrable (fun q => θ_F (e₁.symm (U_b, e₂.symm q)))
        (μ_p.prod μ_n) :=
      integrable_of_measurable_bound (μ_p.prod μ_n) _
        (hθ_F_meas.comp (e₁.symm.measurable.comp (measurable_const.prodMk e₂.symm.measurable)))
        (C_sum ^ 2) fun q => by
          dsimp [θ_F]
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw_bdry_bounds _).1]
          calc ‖F_sum _‖ * ‖F_sum _‖ * w_bdry _
              ≤ C_sum * C_sum * 1 := by
                gcongr
                · exact hF_bd _
                · exact hF_bd _
                · exact (hw_bdry_bounds _).2
            _ = C_sum ^ 2 := by ring
    rw [MeasureTheory.integral_prod _ h_int2, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_p => ?_)
    dsimp only
    rw [← mp_refl.integral_comp' (fun U_n => θ_F (e₁.symm (U_b, e₂.symm (U_p, U_n)))),
      ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_p' => ?_)
    change θ_F (combine U_b U_p U_p') =
      ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) : ℝ) : ℂ) *
        (starRingEnd ℂ (g_val U_b U_p') * g_val U_b U_p)
    dsimp [θ_F]
    rw [h_combine_reflect, h_F_indep U_b U_p' U_p, h_F_indep U_b U_p U_p', h_bdry_const]
    ring
  have h_factor_pos : ∀ U_b : E_b → G,
      (∫ U_p, (∫ U_p', starRingEnd ℂ (g_val U_b U_p') * g_val U_b U_p ∂μ_p) ∂μ_p) =
        (((‖∫ U_p, g_val U_b U_p ∂μ_p‖ ^ 2 : ℝ) : ℂ)) := by
    intro U_b
    let I_b : ℂ := ∫ U_p, g_val U_b U_p ∂μ_p
    have h_inner_p : ∀ U_p,
        (∫ U_p', starRingEnd ℂ (g_val U_b U_p') * g_val U_b U_p ∂μ_p) =
          starRingEnd ℂ I_b * g_val U_b U_p := by
      intro U_p
      rw [MeasureTheory.integral_mul_const, integral_conj]
    simp_rw [h_inner_p, MeasureTheory.integral_const_mul]
    change starRingEnd ℂ I_b * I_b = _
    rw [Complex.conj_mul', Complex.ofReal_pow]
  have h_final_eq :
      ∫ U, θ_F U ∂μ =
        ∫ U_b, ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) *
          ‖∫ U_p, g_val U_b U_p ∂μ_p‖ ^ 2 : ℝ) : ℂ) ∂μ_b := by
    rw [h_int_rewrite]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_b => ?_)
    dsimp only
    rw [h_factor_pos U_b, ← Complex.ofReal_mul]
  rw [h_final_eq]
  have h_int_comb : MeasureTheory.Integrable
      (fun z : (E_b → G) × ((E_p → G) × (E_p → G)) => θ_F (combine z.1 z.2.1 z.2.2))
      (μ_b.prod (μ_p.prod μ_p)) :=
    integrable_of_measurable_bound (μ_b.prod (μ_p.prod μ_p)) _ (hθ_F_meas.comp hm_comb2)
      (C_sum ^ 2) fun z => by
        dsimp [θ_F]
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw_bdry_bounds _).1]
        calc ‖F_sum _‖ * ‖F_sum _‖ * w_bdry _
            ≤ C_sum * C_sum * 1 := by
              gcongr; exact hF_bd _; exact hF_bd _; exact (hw_bdry_bounds _).2
          _ = C_sum ^ 2 := by ring
  have h_real_int : MeasureTheory.Integrable
      (fun U_b => ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) *
        ‖∫ U_p, g_val U_b U_p ∂μ_p‖ ^ 2 : ℝ) : ℂ)) μ_b := by
    refine h_int_comb.integral_prod_left.congr (Filter.Eventually.of_forall fun U_b => ?_)
    have h_int_ub : MeasureTheory.Integrable
        (fun q : (E_p → G) × (E_p → G) => θ_F (combine U_b q.1 q.2)) (μ_p.prod μ_p) :=
      integrable_of_measurable_bound (μ_p.prod μ_p) _
        (hθ_F_meas.comp (hm_comb2.comp (measurable_const.prodMk measurable_id)))
        (C_sum ^ 2) fun q => by
          dsimp [θ_F]
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw_bdry_bounds _).1]
          calc ‖F_sum _‖ * ‖F_sum _‖ * w_bdry _
              ≤ C_sum * C_sum * 1 := by
                gcongr; exact hF_bd _; exact hF_bd _; exact (hw_bdry_bounds _).2
            _ = C_sum ^ 2 := by ring
    dsimp only
    rw [MeasureTheory.integral_prod _ h_int_ub]
    have h_inner_eq :
        (∫ U_p, ∫ U_p', θ_F (combine U_b U_p U_p') ∂μ_p ∂μ_p) =
          ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) : ℝ) : ℂ) *
            ∫ U_p, ∫ U_p', starRingEnd ℂ (g_val U_b U_p') * g_val U_b U_p ∂μ_p ∂μ_p := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_p => ?_)
      dsimp only
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U_p' => ?_)
      dsimp only [θ_F]
      rw [h_combine_reflect, h_F_indep U_b U_p' U_p, h_F_indep U_b U_p U_p', h_bdry_const]
      ring
    rw [h_inner_eq, h_factor_pos U_b, ← Complex.ofReal_mul]
  change 0 ≤ RCLike.re (∫ U_b, ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) *
    ‖∫ U_p, g_val U_b U_p ∂μ_p‖ ^ 2 : ℝ) : ℂ) ∂μ_b)
  rw [← integral_re h_real_int]
  refine MeasureTheory.integral_nonneg fun U_b => ?_
  change 0 ≤ ((w_bdry (combine U_b (fun _ => 1) (fun _ => 1)) *
    ‖∫ U_p, g_val U_b U_p ∂μ_p‖ ^ 2 : ℝ) : ℂ).re
  rw [Complex.ofReal_re]
  exact mul_nonneg (hw_bdry_bounds _).1 (sq_nonneg _)

/-- 2-point specialization of `cubic4Schwinger_refl_pos_n`. -/
theorem cubic4Schwinger_refl_pos_2 (Ls M N : ℕ) [NeZero Ls] [NeZero M] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (m : ℕ) (c : Fin m → ℂ)
    (obs : Fin m →
      (GaugeField (cubicTorus4 Ls (2 * M)) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ))
    (h_meas : ∀ i, Measurable (obs i))
    (C_bd : ℝ) (hC_bd : 0 ≤ C_bd) (h_bd : ∀ i U, ‖obs i U‖ ≤ C_bd)
    (h_pos_supp : ∀ i, SupportedOnPosTime Ls M N (obs i)) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        cubic4Schwinger Ls (2 * M) N β 2
          ![fun U => starRingEnd ℂ (obs i (cubic4TimeReflect Ls (2 * M) N U)), obs j]).re := by
  have h := cubic4Schwinger_refl_pos_n Ls M N β hβ m (fun _ => 1) c (fun i _ => obs i)
    (fun i _ => h_meas i) C_bd hC_bd (fun i _ U => h_bd i U) (fun i _ => h_pos_supp i)
  have heq :
      (∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) *
          cubic4Schwinger Ls (2 * M) N β (1 + 1)
            (Fin.append
              (fun (_ : Fin 1) U => starRingEnd ℂ (obs i (cubic4TimeReflect Ls (2 * M) N U)))
              (fun (_ : Fin 1) => obs j))) =
      ∑ i : Fin m, ∑ j : Fin m,
        c i * starRingEnd ℂ (c j) *
          cubic4Schwinger Ls (2 * M) N β 2
            ![fun U => starRingEnd ℂ (obs i (cubic4TimeReflect Ls (2 * M) N U)), obs j] := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have happ :
        Fin.append
            (fun (_ : Fin 1) U => starRingEnd ℂ (obs i (cubic4TimeReflect Ls (2 * M) N U)))
            (fun (_ : Fin 1) => obs j) =
          ![fun U => starRingEnd ℂ (obs i (cubic4TimeReflect Ls (2 * M) N U)), obs j] := by
      funext k; fin_cases k <;> rfl
    rw [happ]
  rwa [← heq]

/-- 4D spacetime lattice translation on sites. -/
def siteShiftVec4 (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (a x : (cubicTorus4 Ls Lt).Site) : (cubicTorus4 Ls Lt).Site :=
  (x.1 + a.1, x.2.1 + a.2.1, x.2.2.1 + a.2.2.1, x.2.2.2 + a.2.2.2)

/-- Link bijection for 4D spacetime translation by `a`. -/
def cubic4TransLink (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (a : (cubicTorus4 Ls Lt).Site) :
    (cubicTorus4 Ls Lt).Link ≃ (cubicTorus4 Ls Lt).Link where
  toFun e := (siteShiftVec4 Ls Lt a e.1, e.2)
  invFun e := (siteShiftVec4 Ls Lt (-a.1, -a.2.1, -a.2.2.1, -a.2.2.2) e.1, e.2)
  left_inv := fun ⟨⟨t, x, y, z⟩, d⟩ => by simp [siteShiftVec4]
  right_inv := fun ⟨⟨t, x, y, z⟩, d⟩ => by simp [siteShiftVec4]

/-- 4D spacetime lattice translation of a gauge field `U`. -/
def cubic4Translate (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (a : (cubicTorus4 Ls Lt).Site)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e => U (cubic4TransLink Ls Lt a e)

theorem spacetimeHaarMeasure_translate (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : (cubicTorus4 Ls Lt).Site) :
    MeasureTheory.Measure.map (cubic4Translate Ls Lt N a) (spacetimeHaarMeasure Ls Lt N) =
      spacetimeHaarMeasure Ls Lt N := by
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  let σ := cubic4TransLink Ls Lt a
  let F : ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) →
      ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun U e => U (σ e)
  have hF_meas : Measurable F := measurable_pi_iff.mpr fun e => measurable_pi_apply (σ e)
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus4 Ls Lt).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  change MeasureTheory.Measure.map F μ_pi = μ_pi
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hF_meas (MeasurableSet.univ_pi hs)]
  have hpre : F ⁻¹' Set.pi Set.univ s = Set.pi Set.univ (fun e' => s (σ.symm e')) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, F]
    constructor
    · intro h e'; simpa using h (σ.symm e')
    · intro h e; simpa using h (σ e)
  rw [hpre, MeasureTheory.Measure.pi_pi (fun _ => suHaar N)]
  exact Fintype.prod_equiv σ.symm (fun e' => suHaar N (s (σ.symm e')))
    (fun e => suHaar N (s e)) (fun _ => rfl)

theorem cubic4WilsonAction_translate (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (a : (cubicTorus4 Ls Lt).Site)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes Ls Lt) (cubic4Translate Ls Lt N a U) =
      wilsonAction β (cubic4Plaquettes Ls Lt) U := by
  rw [wilsonAction_cubic4_eq_sum, wilsonAction_cubic4_eq_sum]
  congr 1
  let e_site : (cubicTorus4 Ls Lt).Site ≃ (cubicTorus4 Ls Lt).Site :=
    { toFun := siteShiftVec4 Ls Lt a
      invFun := siteShiftVec4 Ls Lt (-a.1, -a.2.1, -a.2.2.1, -a.2.2.2)
      left_inv := fun ⟨t, x, y, z⟩ => by simp [siteShiftVec4]
      right_inv := fun ⟨t, x, y, z⟩ => by simp [siteShiftVec4] }
  have hsh : ∀ (d : Fin 4) (x : (cubicTorus4 Ls Lt).Site),
      siteShiftVec4 Ls Lt a (cubicShift4 Ls Lt d x) =
        cubicShift4 Ls Lt d (siteShiftVec4 Ls Lt a x) := by
    intro d ⟨t, x₁, x₂, x₃⟩
    fin_cases d <;> simp [siteShiftVec4, cubicShift4, add_right_comm]
  have hpt : ∀ x d₁ d₂,
      wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩
          (cubic4Translate Ls Lt N a U) =
        wilsonPlaquetteTerm ⟨siteShiftVec4 Ls Lt a x,
          cubic4Plaquette (siteShiftVec4 Ls Lt a x) d₁ d₂,
          cubic4Plaquette_isPath (siteShiftVec4 Ls Lt a x) d₁ d₂⟩ U := by
    intro x d₁ d₂
    unfold wilsonPlaquetteTerm
    simp only [cubic4Plaquette, pathHolonomy, cubic4Translate, cubic4TransLink,
      Equiv.coe_fn_mk, hsh]
  refine Fintype.sum_equiv e_site _ _ fun x => ?_
  dsimp [sitePlaqSum4, e_site]
  rw [hpt x 0 1, hpt x 0 2, hpt x 0 3, hpt x 1 2, hpt x 1 3, hpt x 2 3]

/-- **Exact 4D spacetime lattice translation invariance of `cubic4Schwinger`**. -/
theorem cubic4Schwinger_trans_inv (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : (cubicTorus4 Ls Lt).Site) (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)) :
    cubic4Schwinger Ls Lt N β n (fun i U => obs i (cubic4Translate Ls Lt N a U)) =
      cubic4Schwinger Ls Lt N β n obs := by
  let eqv : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    { toFun := cubic4Translate Ls Lt N a
      invFun := cubic4Translate Ls Lt N (-a.1, -a.2.1, -a.2.2.1, -a.2.2.2)
      left_inv := fun U => by funext ⟨x, d⟩; simp [cubic4Translate, cubic4TransLink, siteShiftVec4]
      right_inv := fun U => by funext ⟨x, d⟩; simp [cubic4Translate, cubic4TransLink, siteShiftVec4]
      measurable_toFun := measurable_pi_iff.mpr fun e =>
        measurable_pi_apply (cubic4TransLink Ls Lt a e)
      measurable_invFun := measurable_pi_iff.mpr fun e =>
        measurable_pi_apply (cubic4TransLink Ls Lt (-a.1, -a.2.1, -a.2.2.1, -a.2.2.2) e) }
  have hmp : MeasureTheory.MeasurePreserving eqv
      (spacetimeHaarMeasure Ls Lt N) (spacetimeHaarMeasure Ls Lt N) :=
    ⟨eqv.measurable, spacetimeHaarMeasure_translate Ls Lt N a⟩
  unfold cubic4Schwinger
  congr 1
  calc ∫ U, (∏ i : Fin n, obs i (cubic4Translate Ls Lt N a U)) *
          ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N)
      = ∫ U, (∏ i : Fin n, obs i (eqv U)) *
          ((cubic4WilsonWeight Ls Lt N β (eqv U) : ℝ) : ℂ) ∂(spacetimeHaarMeasure Ls Lt N) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            change (∏ i : Fin n, obs i (cubic4Translate Ls Lt N a U)) *
                ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ) =
              (∏ i : Fin n, obs i (cubic4Translate Ls Lt N a U)) *
                ((cubic4WilsonWeight Ls Lt N β (cubic4Translate Ls Lt N a U) : ℝ) : ℂ)
            unfold cubic4WilsonWeight
            rw [cubic4WilsonAction_translate]
    _ = ∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)
          ∂(spacetimeHaarMeasure Ls Lt N) :=
        hmp.integral_comp'
          (fun U => (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ))

def siteCoord4 (L : ℕ) [NeZero L] (x : (cubicTorus4 L L).Site) : Fin 4 → Fin L
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | 3 => x.2.2.2

def ofSiteCoord4 (L : ℕ) [NeZero L] (f : Fin 4 → Fin L) : (cubicTorus4 L L).Site :=
  (f 0, f 1, f 2, f 3)

theorem siteCoord4_ofSiteCoord4 (L : ℕ) [NeZero L] (f : Fin 4 → Fin L) :
    siteCoord4 L (ofSiteCoord4 L f) = f := by
  funext d; fin_cases d <;> rfl

theorem ofSiteCoord4_siteCoord4 (L : ℕ) [NeZero L] (x : (cubicTorus4 L L).Site) :
    ofSiteCoord4 L (siteCoord4 L x) = x := by
  rcases x with ⟨t, a, b, c⟩; rfl

/-- Site permutation induced by `σ : Equiv.Perm (Fin 4)` on the isotropic 4D torus `cubicTorus4 L L`. -/
def sitePerm4 (L : ℕ) [NeZero L] (σ : Equiv.Perm (Fin 4))
    (x : (cubicTorus4 L L).Site) : (cubicTorus4 L L).Site :=
  ofSiteCoord4 L (fun d => siteCoord4 L x (σ.symm d))

/-- Link permutation induced by `σ : Equiv.Perm (Fin 4)` on `cubicTorus4 L L`. -/
def cubic4AxisPermLink (L : ℕ) [NeZero L] (σ : Equiv.Perm (Fin 4)) :
    (cubicTorus4 L L).Link ≃ (cubicTorus4 L L).Link where
  toFun e := (sitePerm4 L σ e.1, σ e.2)
  invFun e := (sitePerm4 L σ.symm e.1, σ.symm e.2)
  left_inv := fun ⟨x, d⟩ => by
    simp only [sitePerm4, siteCoord4_ofSiteCoord4, Equiv.symm_symm,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply, ofSiteCoord4_siteCoord4]
  right_inv := fun ⟨x, d⟩ => by
    simp only [sitePerm4, siteCoord4_ofSiteCoord4, Equiv.symm_symm,
      Equiv.apply_symm_apply, ofSiteCoord4_siteCoord4]

/-- 4D hypercubic axis-permutation action on gauge fields over `cubicTorus4 L L`. -/
def cubic4AxisPermField (L N : ℕ) [NeZero L] (σ : Equiv.Perm (Fin 4))
    (U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun e => U (cubic4AxisPermLink L σ e)

theorem spacetimeHaarMeasure_axisPerm (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (σ : Equiv.Perm (Fin 4)) :
    MeasureTheory.Measure.map (cubic4AxisPermField L N σ) (spacetimeHaarMeasure L L N) =
      spacetimeHaarMeasure L L N := by
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob L L N
  let e_lk := cubic4AxisPermLink L σ
  let F : ((cubicTorus4 L L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) →
      ((cubicTorus4 L L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun U e => U (e_lk e)
  have hF_meas : Measurable F := measurable_pi_iff.mpr fun e => measurable_pi_apply (e_lk e)
  let μ_pi : MeasureTheory.Measure
      ((cubicTorus4 L L).Link → Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    MeasureTheory.Measure.pi (fun _ => suHaar N)
  change MeasureTheory.Measure.map F μ_pi = μ_pi
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hF_meas (MeasurableSet.univ_pi hs)]
  have hpre : F ⁻¹' Set.pi Set.univ s = Set.pi Set.univ (fun e' => s (e_lk.symm e')) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, F]
    constructor
    · intro h e'; simpa using h (e_lk.symm e')
    · intro h e; simpa using h (e_lk e)
  rw [hpre, MeasureTheory.Measure.pi_pi (fun _ => suHaar N)]
  exact Fintype.prod_equiv e_lk.symm (fun e' => suHaar N (s (e_lk.symm e')))
    (fun e => suHaar N (s e)) (fun _ => rfl)

theorem sitePerm4_cubicShift4 (L : ℕ) [NeZero L] (σ : Equiv.Perm (Fin 4))
    (d : Fin 4) (x : (cubicTorus4 L L).Site) :
    sitePerm4 L σ (cubicShift4 L L d x) = cubicShift4 L L (σ d) (sitePerm4 L σ x) := by
  dsimp [sitePerm4]
  have hcoord : ∀ (y : (cubicTorus4 L L).Site) (d' : Fin 4),
      siteCoord4 L (cubicShift4 L L d' y) =
        fun k => siteCoord4 L y k + if k = d' then (1 : Fin L) else 0 := by
    intro ⟨t, a, b, c⟩ d'
    funext k
    fin_cases d' <;> fin_cases k <;> simp [cubicShift4, siteCoord4]
  have h_eq : (fun k => siteCoord4 L (cubicShift4 L L d x) (σ.symm k)) =
      siteCoord4 L (cubicShift4 L L (σ d) (ofSiteCoord4 L (fun k => siteCoord4 L x (σ.symm k)))) := by
    rw [hcoord, hcoord]
    funext k
    rw [siteCoord4_ofSiteCoord4]
    have heq : (σ.symm k = d) ↔ (k = σ d) := Equiv.symm_apply_eq σ
    simp [heq]
  rw [h_eq, ofSiteCoord4_siteCoord4]

theorem wilsonPlaquetteTerm_swap_axes (L N : ℕ) [NeZero L]
    (U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (cubicTorus4 L L).Site) (d₁ d₂ : Fin 4) :
    wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩ U =
      wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₂ d₁, cubic4Plaquette_isPath x d₂ d₁⟩ U := by
  unfold wilsonPlaquetteTerm
  have hinv : pathHolonomy U (cubic4Plaquette x d₁ d₂) =
      (pathHolonomy U (cubic4Plaquette x d₂ d₁))⁻¹ := by
    simp only [cubic4Plaquette, pathHolonomy, mul_inv_rev, inv_inv]
    group
  rw [hinv, su_trace_inv_re]

theorem cubic4WilsonAction_axisPerm (L N : ℕ) [NeZero L] (β : ℝ)
    (σ : Equiv.Perm (Fin 4))
    (U : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilsonAction β (cubic4Plaquettes L L) (cubic4AxisPermField L N σ U) =
      wilsonAction β (cubic4Plaquettes L L) U := by
  let T_all : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) →
      (cubicTorus4 L L).Site → ℝ := fun V x =>
    ∑ d₁ : Fin 4, ∑ d₂ : Fin 4,
      if d₁ = d₂ then 0
      else wilsonPlaquetteTerm ⟨x, cubic4Plaquette x d₁ d₂, cubic4Plaquette_isPath x d₁ d₂⟩ V
  have h_site_eq : ∀ V x, sitePlaqSum4 L L N V x = (1 / 2 : ℝ) * T_all V x := by
    intro V x
    dsimp [T_all, sitePlaqSum4]
    rw [Fin.sum_univ_four]
    simp only [Fin.sum_univ_four, Fin.reduceEq, ↓reduceIte]
    rw [wilsonPlaquetteTerm_swap_axes L N V x 1 0,
      wilsonPlaquetteTerm_swap_axes L N V x 2 0,
      wilsonPlaquetteTerm_swap_axes L N V x 3 0,
      wilsonPlaquetteTerm_swap_axes L N V x 2 1,
      wilsonPlaquetteTerm_swap_axes L N V x 3 1,
      wilsonPlaquetteTerm_swap_axes L N V x 3 2]
    ring
  rw [wilsonAction_cubic4_eq_sum, wilsonAction_cubic4_eq_sum]
  simp_rw [h_site_eq, ← Finset.mul_sum]
  congr 2
  let e_site : (cubicTorus4 L L).Site ≃ (cubicTorus4 L L).Site :=
    { toFun := sitePerm4 L σ
      invFun := sitePerm4 L σ.symm
      left_inv := fun x => by
        simp only [sitePerm4, siteCoord4_ofSiteCoord4, Equiv.symm_symm,
          Equiv.symm_apply_apply, ofSiteCoord4_siteCoord4]
      right_inv := fun x => by
        simp only [sitePerm4, siteCoord4_ofSiteCoord4, Equiv.symm_symm,
          Equiv.apply_symm_apply, ofSiteCoord4_siteCoord4] }
  refine Fintype.sum_equiv e_site _ _ fun x => ?_
  dsimp [T_all, e_site]
  refine Fintype.sum_equiv σ _ _ fun d₁ => Fintype.sum_equiv σ _ _ fun d₂ => ?_
  by_cases h12 : d₁ = d₂
  · subst h12; simp
  · have h12' : σ d₁ ≠ σ d₂ := fun h => h12 (σ.injective h)
    simp only [h12, h12', ↓reduceIte]
    unfold wilsonPlaquetteTerm
    simp only [cubic4Plaquette, pathHolonomy, cubic4AxisPermField, cubic4AxisPermLink,
      Equiv.coe_fn_mk, sitePerm4_cubicShift4]

/-- **Exact 4D hypercubic $S_4$ axis-permutation symmetry of `cubic4Schwinger` on `cubicTorus4 L L`**. -/
theorem cubic4Schwinger_axis_perm_inv (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (σ : Equiv.Perm (Fin 4)) (n : ℕ)
    (obs : Fin n →
      (GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)) :
    cubic4Schwinger L L N β n (fun i U => obs i (cubic4AxisPermField L N σ U)) =
      cubic4Schwinger L L N β n obs := by
  let eqv : GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      GaugeField (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    { toFun := cubic4AxisPermField L N σ
      invFun := cubic4AxisPermField L N σ.symm
      left_inv := fun U => by
        funext ⟨x, d⟩
        simp only [cubic4AxisPermField, cubic4AxisPermLink, Equiv.coe_fn_mk, sitePerm4,
          siteCoord4_ofSiteCoord4, Equiv.symm_symm, Equiv.apply_symm_apply,
          Equiv.symm_apply_apply, ofSiteCoord4_siteCoord4]
      right_inv := fun U => by
        funext ⟨x, d⟩
        simp only [cubic4AxisPermField, cubic4AxisPermLink, Equiv.coe_fn_mk, sitePerm4,
          siteCoord4_ofSiteCoord4, Equiv.symm_symm, Equiv.apply_symm_apply,
          Equiv.symm_apply_apply, ofSiteCoord4_siteCoord4]
      measurable_toFun := measurable_pi_iff.mpr fun e =>
        measurable_pi_apply (cubic4AxisPermLink L σ e)
      measurable_invFun := measurable_pi_iff.mpr fun e =>
        measurable_pi_apply (cubic4AxisPermLink L σ.symm e) }
  have hmp : MeasureTheory.MeasurePreserving eqv
      (spacetimeHaarMeasure L L N) (spacetimeHaarMeasure L L N) :=
    ⟨eqv.measurable, spacetimeHaarMeasure_axisPerm L N σ⟩
  unfold cubic4Schwinger
  congr 1
  calc ∫ U, (∏ i : Fin n, obs i (cubic4AxisPermField L N σ U)) *
          ((cubic4WilsonWeight L L N β U : ℝ) : ℂ) ∂(spacetimeHaarMeasure L L N)
      = ∫ U, (∏ i : Fin n, obs i (eqv U)) *
          ((cubic4WilsonWeight L L N β (eqv U) : ℝ) : ℂ) ∂(spacetimeHaarMeasure L L N) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
            change (∏ i : Fin n, obs i (cubic4AxisPermField L N σ U)) *
                ((cubic4WilsonWeight L L N β U : ℝ) : ℂ) =
              (∏ i : Fin n, obs i (cubic4AxisPermField L N σ U)) *
                ((cubic4WilsonWeight L L N β (cubic4AxisPermField L N σ U) : ℝ) : ℂ)
            unfold cubic4WilsonWeight
            rw [cubic4WilsonAction_axisPerm]
    _ = ∫ U, (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight L L N β U : ℝ) : ℂ)
          ∂(spacetimeHaarMeasure L L N) :=
        hmp.integral_comp'
          (fun U => (∏ i : Fin n, obs i U) * ((cubic4WilsonWeight L L N β U : ℝ) : ℂ))

end CubicSpacetime4DOSAndSymmetries


end YangMills
