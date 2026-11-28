import Imscribing.YangMills.CanonicalWilsonHaar4D
import Imscribing.YangMills.CantorBanachAlaogluSchwartz

/-!
# Canonical 4D SU(N) Haar Expectation, Bounds, Gauge Invariance, & Continuum Subsequence

Discharges all abstract measure, probability, measurability, and invariance
hypotheses across `WilsonHaarCompactness4D`, `LatticeRiemannSchwartzBound4D`,
`CantorBanachAlaogluSchwartz`, and `SchwingerCovarianceAndSymmetry` using
`wilsonHaarLinkMeasure N L` (`0 sorry`).
-/

namespace Imscribing.YangMills.CanonicalWilsonBridge

open scoped Topology
open MeasureTheory
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D
open Imscribing.YangMills.WilsonMeasure4D
open Imscribing.YangMills.WilsonFrobenius4D
open Imscribing.YangMills.LatticeRiemannBound4D
open Imscribing.YangMills.CantorSchwartzLimit
open Imscribing.YangMills.SchwingerSymmetry
open Imscribing.YangMills.CanonicalHaar4D

/-- Matrix entry projections on `GaugeGroup N` are measurable with respect to `borel (GaugeGroup N)`. -/
theorem canonicalGaugeEntryMeasurable (N : ℕ) (i j : Fin N) :
    letI := borel (GaugeGroup N)
    Measurable (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ) i j) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  have hcont : Continuous (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact hcont.measurable

/-- `wilsonAction N L β` is measurable with respect to the product Borel σ-algebra on `LinkConfig N L`. -/
theorem canonicalWilsonActionMeasurable (N L : ℕ) [NeZero N] [NeZero L] (β : ℝ) :
    letI := borel (GaugeGroup N)
    Measurable (fun U : LinkConfig N L => wilsonAction N L β U) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) := by unfold Matrix; infer_instance
  haveI : SecondCountableTopology (GaugeGroup N) := by
    have h_ind : Topology.IsInducing (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ)) := ⟨rfl⟩
    exact h_ind.secondCountableTopology
  haveI : MeasurableMul₂ (GaugeGroup N) := ContinuousMul.measurableMul₂
  haveI : ContinuousInv (GaugeGroup N) := by
    refine ⟨?_⟩
    have h_ind : Topology.IsInducing (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ)) := ⟨rfl⟩
    rw [h_ind.continuous_iff]
    change Continuous (fun A : GaugeGroup N => ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ))
    have h_eq : (fun A : GaugeGroup N => ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)) =
        (fun A : GaugeGroup N => star (A : Matrix (Fin N) (Fin N) ℂ)) := by
      funext A
      first | rfl | rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
    rw [h_eq]
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val))
  haveI : MeasurableInv (GaugeGroup N) := ContinuousInv.measurableInv
  unfold wilsonAction
  refine measurable_const.mul (Finset.measurable_sum _ fun x _ =>
    Finset.measurable_sum _ fun μ _ => Finset.measurable_sum _ fun ν _ => ?_)
  refine measurable_const.sub ((Complex.continuous_re.measurable.comp ?_).div_const _)
  unfold plaquetteHolonomy
  have h_link : ∀ (y : Lat4 L) (ν : Fin 4), Measurable (fun U : LinkConfig N L => U y ν) :=
    fun y ν => (measurable_pi_apply ν).comp (measurable_pi_apply y : Measurable fun U : LinkConfig N L => U y)
  have ml1 := h_link x μ
  have ml2 := h_link (x + stepDir L μ) ν
  have ml3 := (h_link (x + stepDir L ν) μ).inv
  have ml4 := (h_link x ν).inv
  have mprod := ((ml1.mul ml2).mul ml3).mul ml4
  change Measurable (fun U : LinkConfig N L =>
    Matrix.trace ((plaquetteHolonomy U x μ ν : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ))
  exact Finset.measurable_sum _ fun k _ => (canonicalGaugeEntryMeasurable N k k).comp mprod

/-- Product of `localPlaqDensity` over `Fin n` is measurable on `LinkConfig N L`. -/
theorem canonicalLocalPlaqProdMeasurable (N L n : ℕ) [NeZero N] [NeZero L] (xs : Fin n → Lat4 L) :
    letI := borel (GaugeGroup N)
    Measurable (fun U : LinkConfig N L => (∏ k : Fin n, localPlaqDensity N L U (xs k) : ℂ)) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) := by unfold Matrix; infer_instance
  haveI : SecondCountableTopology (GaugeGroup N) := by
    have h_ind : Topology.IsInducing (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ)) := ⟨rfl⟩
    exact h_ind.secondCountableTopology
  haveI : MeasurableMul₂ (GaugeGroup N) := ContinuousMul.measurableMul₂
  haveI : ContinuousInv (GaugeGroup N) := by
    refine ⟨?_⟩
    have h_ind : Topology.IsInducing (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ)) := ⟨rfl⟩
    rw [h_ind.continuous_iff]
    change Continuous (fun A : GaugeGroup N => ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ))
    have h_eq : (fun A : GaugeGroup N => ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)) =
        (fun A : GaugeGroup N => star (A : Matrix (Fin N) (Fin N) ℂ)) := by
      funext A
      first | rfl | rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
    rw [h_eq]
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val))
  haveI : MeasurableInv (GaugeGroup N) := ContinuousInv.measurableInv
  refine Finset.measurable_prod _ fun k _ => Complex.continuous_ofReal.measurable.comp ?_
  unfold localPlaqDensity
  refine Finset.measurable_sum _ fun μ _ => Finset.measurable_sum _ fun ν _ => ?_
  refine measurable_const.sub ((Complex.continuous_re.measurable.comp ?_).div_const _)
  unfold plaquetteHolonomy
  have h_link : ∀ (y : Lat4 L) (ν : Fin 4), Measurable (fun U : LinkConfig N L => U y ν) :=
    fun y ν => (measurable_pi_apply ν).comp (measurable_pi_apply y : Measurable fun U : LinkConfig N L => U y)
  have ml1 := h_link (xs k) μ
  have ml2 := h_link (xs k + stepDir L μ) ν
  have ml3 := (h_link (xs k + stepDir L ν) μ).inv
  have ml4 := (h_link (xs k) ν).inv
  have mprod := ((ml1.mul ml2).mul ml3).mul ml4
  change Measurable (fun U : LinkConfig N L =>
    Matrix.trace ((plaquetteHolonomy U (xs k) μ ν : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ))
  exact Finset.measurable_sum _ fun i _ => (canonicalGaugeEntryMeasurable N i i).comp mprod

/-- Canonical 4D SU(N) Wilson partition function on `wilsonHaarLinkMeasure N L`. -/
noncomputable def canonicalWilsonPartitionFn (N L : ℕ) [NeZero N] [NeZero L] (β : ℝ) : ℝ :=
  letI := borel (GaugeGroup N)
  wilsonPartitionFn N L β (wilsonHaarLinkMeasure N L)

/-- Canonical normalized 4D SU(N) Wilson expectation on `wilsonHaarLinkMeasure N L`. -/
noncomputable def canonicalWilsonExpectation (N L : ℕ) [NeZero N] [NeZero L] (β : ℝ)
    (F : LinkConfig N L → ℂ) : ℂ :=
  letI := borel (GaugeGroup N)
  wilsonExpectation N L β (wilsonHaarLinkMeasure N L) F

/-- Canonical smeared `n`-point Wilson plaquette Schwinger functional. -/
noncomputable def canonicalSmearedPlaqSchwinger (N L n : ℕ) [NeZero N] [NeZero L]
    (a β Z_ren : ℝ) : EuclideanSchwartz n →ₗ[ℂ] ℂ :=
  letI := borel (GaugeGroup N)
  smearedPlaqSchwinger N L n a β Z_ren (wilsonHaarLinkMeasure N L)

/-- Unconditional partition-function bounds `0 < exp(-32 β |L⁴|) ≤ Z_{N, L}(β) ≤ 1`. -/
theorem canonicalWilsonPartitionFn_bounds (N L : ℕ) [NeZero N] [NeZero L] {β : ℝ} (hβ : 0 ≤ β) :
    0 < Real.exp (-(32 * β * ((Fintype.card (Lat4 L) : ℕ) : ℝ))) ∧
    Real.exp (-(32 * β * ((Fintype.card (Lat4 L) : ℕ) : ℝ))) ≤
      canonicalWilsonPartitionFn N L β ∧
    canonicalWilsonPartitionFn N L β ≤ 1 := by
  letI := borel (GaugeGroup N)
  haveI := wilsonHaarLinkMeasure_isProbability N L
  exact wilsonPartitionFn_bounds hβ (wilsonHaarLinkMeasure N L)
    (canonicalWilsonActionMeasurable N L β)

/-- Unconditional gauge invariance of closed Wilson loops under `canonicalWilsonExpectation`. -/
theorem canonicalWilsonExpectation_loop_gaugeInvariant
    (N L k : ℕ) [NeZero N] [NeZero L] (hk : 0 < k) {β : ℝ} (hβ : 0 ≤ β)
    (g : GaugeTransform N L) (γ : Fin k → Lat4 L × Fin 4)
    (hcontig : IsContiguousPath γ)
    (hclosed : (γ ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).1 +
        stepDir L (γ ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).2 = (γ ⟨0, hk⟩).1) :
    canonicalWilsonExpectation N L β
        (fun U => (realTrace (pathHolonomy (applyGauge g U) γ) : ℂ)) =
      canonicalWilsonExpectation N L β
        (fun U => (realTrace (pathHolonomy U γ) : ℂ)) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) := by unfold Matrix; infer_instance
  haveI : SecondCountableTopology (GaugeGroup N) := by
    have h_ind : Topology.IsInducing (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ)) := ⟨rfl⟩
    exact h_ind.secondCountableTopology
  haveI : MeasurableMul₂ (GaugeGroup N) := ContinuousMul.measurableMul₂
  haveI : ContinuousInv (GaugeGroup N) := by
    refine ⟨?_⟩
    have h_ind : Topology.IsInducing (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ)) := ⟨rfl⟩
    rw [h_ind.continuous_iff]
    change Continuous (fun A : GaugeGroup N => ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ))
    have h_eq : (fun A : GaugeGroup N => ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)) =
        (fun A : GaugeGroup N => star (A : Matrix (Fin N) (Fin N) ℂ)) := by
      funext A
      first | rfl | rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
    rw [h_eq]
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val))
  haveI : MeasurableInv (GaugeGroup N) := ContinuousInv.measurableInv
  haveI := wilsonHaarLinkMeasure_isProbability N L
  have h_loop_meas : Measurable (fun U : LinkConfig N L =>
      (realTrace (pathHolonomy U γ) : ℂ) * (Real.exp (-wilsonAction N L β U) : ℂ)) := by
    have h_path : Measurable (fun U : LinkConfig N L => pathHolonomy U γ) := by
      clear hcontig hclosed
      induction k with
      | zero => exact absurd hk (lt_irrefl 0)
      | succ m ih =>
          cases m with
          | zero =>
              simpa [pathHolonomy] using
                (measurable_pi_apply (γ 0).2).comp (measurable_pi_apply (γ 0).1)
          | succ m' =>
              have h1 : Measurable (fun U : LinkConfig N L => U (γ 0).1 (γ 0).2) :=
                (measurable_pi_apply (γ 0).2).comp (measurable_pi_apply (γ 0).1)
              have h2 : Measurable (fun U : LinkConfig N L =>
                  pathHolonomy U (fun i : Fin (m' + 1) => γ i.succ)) :=
                ih (Nat.succ_pos m') (fun i => γ i.succ)
              simpa [pathHolonomy] using h1.mul h2
    have h_tr : Measurable (fun U : LinkConfig N L => (realTrace (pathHolonomy U γ) : ℂ)) := by
      apply Complex.continuous_ofReal.measurable.comp
      unfold realTrace
      refine Complex.continuous_re.measurable.comp ?_
      change Measurable (fun U =>
        Matrix.trace ((pathHolonomy U γ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ))
      exact Finset.measurable_sum _ fun i _ => (canonicalGaugeEntryMeasurable N i i).comp h_path
    exact h_tr.mul (Complex.continuous_ofReal.measurable.comp
      (Real.continuous_exp.measurable.comp (canonicalWilsonActionMeasurable N L β).neg))
  have h_int : Integrable (fun U : LinkConfig N L =>
      (realTrace (pathHolonomy U γ) : ℂ) * (Real.exp (-wilsonAction N L β U) : ℂ))
      (wilsonHaarLinkMeasure N L) := by
    refine Integrable.of_bound h_loop_meas.aestronglyMeasurable (N : ℝ)
      (Filter.Eventually.of_forall fun U => ?_)
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : |realTrace (pathHolonomy U γ)| ≤ (N : ℝ) := realTrace_abs_le _
    have h2 : Real.exp (-wilsonAction N L β U) ≤ 1 := (gibbsWeight_pos_le_one hβ U).2
    simpa using mul_le_mul h1 h2 (Real.exp_pos _).le (Nat.cast_nonneg N)
  have hg_meas : Measurable (applyGauge g) := by
    refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun μ => ?_
    have hU : Measurable (fun U : LinkConfig N L => U x μ) :=
      (measurable_pi_apply μ).comp (measurable_pi_apply x : Measurable fun U : LinkConfig N L => U x)
    exact (measurable_const.mul hU).mul measurable_const
  exact wilsonExpectation_gaugeInvariant hk β (wilsonHaarLinkMeasure N L) g
    (wilsonHaar_gaugeInvariant N L g) hg_meas γ hcontig hclosed h_int

/-- **Unconditional Uniform Schwartz Bound on `canonicalSmearedPlaqSchwinger`.** -/
theorem canonicalWilsonSchwinger_uniform_schwartz_bound (N L n : ℕ) [NeZero N] [NeZero L]
    {a β : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hβ : 0 ≤ β) (Z_ren : ℝ)
    (f : EuclideanSchwartz n) :
    ‖canonicalSmearedPlaqSchwinger N L n a β Z_ren f‖ ≤
      (|Z_ren| * 8192) ^ n *
        ∑ j ∈ Finset.range (8 * n + 1),
          ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 f := by
  letI := borel (GaugeGroup N)
  haveI := wilsonHaarLinkMeasure_isProbability N L
  exact smearedPlaqSchwinger_uniform_schwartz_bound N L n ha0 ha1 hβ Z_ren
    (wilsonHaarLinkMeasure N L) (canonicalWilsonActionMeasurable N L β)
    (canonicalLocalPlaqProdMeasurable N L n) f

/-- **Unconditional Continuum Subsequential Extraction on Canonical 4D SU(N) Haar Measures:**
    Extracts a continuum Schwartz distribution `S_lim` with uniform E0 continuity bound
    and exact E3 permutation symmetry directly from `wilsonHaarLinkMeasure N (L m)`. -/
theorem canonicalWilsonSchwinger_subsequential_limit
    (N n : ℕ) [NeZero N]
    (L : ℕ → ℕ) [∀ m, NeZero (L m)]
    (a β Z_ren : ℕ → ℝ) (Z_max : ℝ) (hZ_max : 0 ≤ Z_max)
    (ha : ∀ m, 0 < a m ∧ a m ≤ 1) (hβ : ∀ m, 0 ≤ β m)
    (hZ : ∀ m, |Z_ren m| ≤ Z_max)
    (D : ℕ → EuclideanSchwartz n)
    (h_dense : ∀ f : EuclideanSchwartz n, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ,
        ((Z_max * 8192) ^ n * ∑ j ∈ Finset.range (8 * n + 1),
          ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 (f - D k)) < ε) :
    let p : EuclideanSchwartz n → ℝ := fun f =>
      (Z_max * 8192) ^ n * ∑ j ∈ Finset.range (8 * n + 1),
        ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 f
    ∃ (φ : ℕ → ℕ) (S_lim : EuclideanSchwartz n →ₗ[ℂ] ℂ),
      StrictMono φ ∧
      (∀ f : EuclideanSchwartz n,
        Filter.Tendsto (fun m =>
          canonicalSmearedPlaqSchwinger N (L (φ m)) n (a (φ m)) (β (φ m)) (Z_ren (φ m)) f)
          Filter.atTop (𝓝 (S_lim f))) ∧
      (∀ f : EuclideanSchwartz n, ‖S_lim f‖ ≤ p f) ∧
      (∀ (π : Equiv.Perm (Fin n)) (f f_π : EuclideanSchwartz n),
        (∀ y : Fin n → ContinuumInterfaces.Spacetime4, f_π y = f (fun k => y (π k))) →
        S_lim f_π = S_lim f) := by
  letI := borel (GaugeGroup N)
  intro p
  obtain ⟨φ, S_lim, hφ, h_lim, h_bd⟩ := wilson_lattice_subsequential_schwinger_limit N n L a β
    Z_ren Z_max hZ_max ha hβ hZ (fun _ => inferInstance)
    (fun m => wilsonHaarLinkMeasure N (L m))
    (fun m => wilsonHaarLinkMeasure_isProbability N (L m))
    (fun m => canonicalWilsonActionMeasurable N (L m) (β m))
    (fun m xs => canonicalLocalPlaqProdMeasurable N (L m) n xs)
    D h_dense
  refine ⟨φ, S_lim, hφ, h_lim, h_bd, fun π f f_π hf => ?_⟩
  exact continuum_schwinger_perm_symm N n (fun m => L (φ m)) (fun m => a (φ m))
    (fun m => β (φ m)) (fun m => Z_ren (φ m))
    (fun _ => inferInstance) (fun m => wilsonHaarLinkMeasure N (L (φ m)))
    S_lim h_lim π f f_π hf

end Imscribing.YangMills.CanonicalWilsonBridge