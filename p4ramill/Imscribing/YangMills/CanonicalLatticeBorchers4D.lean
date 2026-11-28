import Imscribing.YangMills.CanonicalWilsonHalfMeasureRP4D
import Imscribing.YangMills.LatticeExteriorCutoff4D
import Imscribing.YangMills.ConcreteMinimalClayReduction

/-!
# Canonical Lattice Magnetic Schwinger Functional & Unconditional Finite-Volume RP
-/

namespace Imscribing.YangMills.CanonicalLatticeBorchers

open MeasureTheory
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D
open Imscribing.YangMills.WilsonMeasure4D
open Imscribing.YangMills.LatticeRP4D
open Imscribing.YangMills.LatticeOSRP4D
open Imscribing.YangMills.LatticeSchwingerRP4D
open Imscribing.YangMills.CenteredTranslation4D
open Imscribing.YangMills.CanonicalHaar4D
open Imscribing.YangMills.CanonicalWilsonBridge
open Imscribing.YangMills.CanonicalHalfRP4D

private lemma clb_gaugeGroup_coe_inv_star {N : ℕ} (A : GaugeGroup N) :
    ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = star (A : Matrix (Fin N) (Fin N) ℂ) := by
  have h1 : (A : Matrix (Fin N) (Fin N) ℂ) * ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    congrArg Subtype.val (mul_inv_cancel A)
  have h2 : star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp A.2.1
  calc ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)
      = (star (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ)) *
          ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) := by rw [h2, Matrix.one_mul]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) *
          ((A : Matrix (Fin N) (Fin N) ℂ) * ((A⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ)) := by
          rw [Matrix.mul_assoc]
    _ = star (A : Matrix (Fin N) (Fin N) ℂ) := by rw [h1, Matrix.mul_one]

private lemma canonicalPlaqHolonomyMeasurable (N L : ℕ) [NeZero N] (x : Lat4 L) (μ ν : Fin 4) :
    letI := borel (GaugeGroup N)
    Measurable (fun U : LinkConfig N L => plaquetteHolonomy U x μ ν) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  haveI : SecondCountableTopology (GaugeGroup N) :=
    Topology.IsInducing.secondCountableTopology
      (⟨rfl⟩ : Topology.IsInducing (Subtype.val : GaugeGroup N → Matrix (Fin N) (Fin N) ℂ))
  haveI : ContinuousInv (GaugeGroup N) :=
    ⟨continuous_induced_rng.mpr (by
      simpa only [Function.comp_def, clb_gaugeGroup_coe_inv_star] using
        continuous_star.comp continuous_subtype_val)⟩
  haveI : MeasurableMul₂ (GaugeGroup N) := ContinuousMul.measurableMul₂
  haveI : MeasurableInv (GaugeGroup N) := ContinuousInv.measurableInv
  unfold plaquetteHolonomy
  have m1 : Measurable (fun U : LinkConfig N L => U x μ) :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  have m2 : Measurable (fun U : LinkConfig N L => U (x + stepDir L μ) ν) :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  have m3' : Measurable (fun U : LinkConfig N L => U (x + stepDir L ν) μ) :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  have m3 : Measurable (fun U : LinkConfig N L => (U (x + stepDir L ν) μ)⁻¹) := m3'.inv
  have m4' : Measurable (fun U : LinkConfig N L => U x ν) :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  have m4 : Measurable (fun U : LinkConfig N L => (U x ν)⁻¹) := m4'.inv
  exact ((m1.mul m2).mul m3).mul m4

private lemma canonicalSpatialPlaqMeasurable (N L : ℕ) [NeZero N] (x : Lat4 L) :
    letI := borel (GaugeGroup N)
    Measurable (fun U : LinkConfig N L => spatialPlaqDensity N L U x) := by
  letI := borel (GaugeGroup N)
  have hEntry := canonicalGaugeEntryMeasurable N
  unfold spatialPlaqDensity realTrace
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  refine measurable_const.sub ((Complex.continuous_re.measurable.comp ?_).div_const _)
  change Measurable (fun U : LinkConfig N L =>
    Matrix.trace ((plaquetteHolonomy U x i.succ j.succ : GaugeGroup N) :
      Matrix (Fin N) (Fin N) ℂ))
  exact Finset.measurable_sum _ fun k _ =>
    (hEntry k k).comp (canonicalPlaqHolonomyMeasurable N L x i.succ j.succ)

private lemma canonicalWilsonActionMeasurable (N L : ℕ) [NeZero N] [NeZero L] (β : ℝ) :
    letI := borel (GaugeGroup N)
    Measurable (fun U : LinkConfig N L => wilsonAction N L β U) := by
  letI := borel (GaugeGroup N)
  have hEntry := canonicalGaugeEntryMeasurable N
  unfold wilsonAction realTrace
  refine measurable_const.mul (Finset.measurable_sum _ fun x _ =>
    Finset.measurable_sum _ fun μ _ => Finset.measurable_sum _ fun ν _ => ?_)
  refine measurable_const.sub ((Complex.continuous_re.measurable.comp ?_).div_const _)
  change Measurable (fun U : LinkConfig N L =>
    Matrix.trace ((plaquetteHolonomy U x μ ν : GaugeGroup N) :
      Matrix (Fin N) (Fin N) ℂ))
  exact Finset.measurable_sum _ fun k _ =>
    (hEntry k k).comp (canonicalPlaqHolonomyMeasurable N L x μ ν)

/-- Measurability of the `n`-point product of `spatialPlaqDensity` on `LinkConfig N L`. -/
theorem canonicalSpatialPlaqProdMeasurable (N L n : ℕ) [NeZero N] (xs : Fin n → Lat4 L) :
    letI := borel (GaugeGroup N)
    Measurable (fun U : LinkConfig N L => (∏ k : Fin n, spatialPlaqDensity N L U (xs k) : ℂ)) := by
  letI := borel (GaugeGroup N)
  exact Finset.measurable_prod Finset.univ fun k _ =>
    Complex.continuous_ofReal.measurable.comp (canonicalSpatialPlaqMeasurable N L (xs k))

/-- Centered smeared `n`-point 4D SU(N) magnetic plaquette Schwinger functional. -/
noncomputable def canonicalMagneticSchwinger (N L n : ℕ) [NeZero N] [NeZero L]
    (a β Z_ren : ℝ) : EuclideanSchwartz n →ₗ[ℂ] ℂ where
  toFun f :=
    letI := borel (GaugeGroup N)
    (Z_ren ^ n * a ^ (4 * n) : ℂ) *
      ∑ xs : Fin n → Lat4 L,
        f (fun k => centeredLatSite L a (xs k)) *
          wilsonExpectation N L β (wilsonHaarLinkMeasure N L)
            (fun U => (∏ k : Fin n, spatialPlaqDensity N L U (xs k) : ℂ))
  map_add' f g := by
    simp only [SchwartzMap.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    ring

/-- **Unconditional Vacuum Normalization:** `canonicalMagneticSchwinger N L 0 a β Z_ren 1 = 1`. -/
theorem canonicalMagneticSchwinger_zero (N L : ℕ) [NeZero N] [NeZero L]
    (a : ℝ) {β : ℝ} (hβ : 0 ≤ β) (Z_ren : ℝ) :
    canonicalMagneticSchwinger N L 0 a β Z_ren 1 = 1 := by
  letI := borel (GaugeGroup N)
  haveI := wilsonHaarLinkMeasure_isProbability N L
  have h_act_meas := canonicalWilsonActionMeasurable N L β
  obtain ⟨hpos_lb, hZ_lb, _⟩ := wilsonPartitionFn_bounds hβ (wilsonHaarLinkMeasure N L) h_act_meas
  have hZ_pos : 0 < wilsonPartitionFn N L β (wilsonHaarLinkMeasure N L) :=
    lt_of_lt_of_le hpos_lb hZ_lb
  dsimp [canonicalMagneticSchwinger]
  simp only [pow_zero, mul_zero, mul_one, one_mul, Finset.univ_unique, Finset.sum_singleton,
    Finset.univ_eq_empty, Finset.prod_empty, Complex.ofReal_one]
  unfold wilsonExpectation
  simp only [one_mul]
  have h_int : (∫ (U : LinkConfig N L), (Real.exp (-wilsonAction N L β U) : ℂ) ∂wilsonHaarLinkMeasure N L) =
      (wilsonPartitionFn N L β (wilsonHaarLinkMeasure N L) : ℂ) := by
    unfold wilsonPartitionFn
    exact (integral_ofReal : (∫ U : LinkConfig N L, ((Real.exp (-wilsonAction N L β U) : ℝ) : ℂ) ∂wilsonHaarLinkMeasure N L) = _)
  rw [h_int]
  exact_mod_cast inv_mul_cancel₀ hZ_pos.ne'

/-- **Uniform Schwartz Bound on Centered Magnetic Schwinger Functionals.** -/
theorem canonicalMagneticSchwinger_uniform_schwartz_bound
    (N L n : ℕ) [NeZero N] [NeZero L]
    {a β : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hβ : 0 ≤ β) (Z_ren : ℝ)
    (f : EuclideanSchwartz n) :
    ‖canonicalMagneticSchwinger N L n a β Z_ren f‖ ≤
      (|Z_ren| * 73728) ^ n *
        ∑ j ∈ Finset.range (8 * n + 1),
          ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 f := by
  letI := borel (GaugeGroup N)
  haveI := wilsonHaarLinkMeasure_isProbability N L
  have h_act_meas := canonicalWilsonActionMeasurable N L β
  have h_exp_bd : ∀ xs : Fin n → Lat4 L,
      ‖wilsonExpectation N L β (wilsonHaarLinkMeasure N L)
        (fun U => (∏ k : Fin n, spatialPlaqDensity N L U (xs k) : ℂ))‖ ≤ (18 : ℝ) ^ n := by
    intro xs
    refine wilsonExpectation_norm_le hβ _ h_act_meas _
      (canonicalSpatialPlaqProdMeasurable N L n xs) ((18 : ℝ) ^ n) (by positivity) fun U => ?_
    rw [← Complex.ofReal_prod, Complex.norm_real, Real.norm_of_nonneg (Finset.prod_nonneg fun k _ =>
      (spatialPlaqDensity_bounds N L U (xs k)).1)]
    calc (∏ k : Fin n, spatialPlaqDensity N L U (xs k))
        ≤ ∏ _k : Fin n, (18 : ℝ) :=
          Finset.prod_le_prod (fun k _ => (spatialPlaqDensity_bounds N L U (xs k)).1)
            fun k _ => (spatialPlaqDensity_bounds N L U (xs k)).2
      _ = (18 : ℝ) ^ n := by simp [Finset.prod_const]
  have h_1d := centered_1d_riemann_le_eight L ha0 ha1
  have h_4d : ∑ x : Lat4 L, ∏ μ : Fin 4, (a / (1 + a * |(centeredCoord L (x μ) : ℝ)|) ^ 2) ≤ 4096 := by
    have h_prod_sum :
        (∑ x : Lat4 L, ∏ μ : Fin 4, (a / (1 + a * |(centeredCoord L (x μ) : ℝ)|) ^ 2)) =
        ∏ _μ : Fin 4, ∑ v : ZMod L, a / (1 + a * |(centeredCoord L v : ℝ)|) ^ 2 :=
      (Fintype.prod_sum (fun (_ : Fin 4) (v : ZMod L) =>
        a / (1 + a * |(centeredCoord L v : ℝ)|) ^ 2)).symm
    rw [h_prod_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h_nn : 0 ≤ ∑ v : ZMod L, a / (1 + a * |(centeredCoord L v : ℝ)|) ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    calc (∑ v : ZMod L, a / (1 + a * |(centeredCoord L v : ℝ)|) ^ 2) ^ 4 ≤ 8 ^ 4 :=
          pow_le_pow_left₀ h_nn h_1d 4
      _ = 4096 := by norm_num
  have h_nd :
      (∑ xs : Fin n → Lat4 L, ∏ k : Fin n, ∏ μ : Fin 4,
          (a / (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2)) ≤ (4096 : ℝ) ^ n := by
    have h_prod_sum :
        (∑ xs : Fin n → Lat4 L, ∏ k : Fin n, ∏ μ : Fin 4,
          (a / (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2)) =
        ∏ _k : Fin n, ∑ x : Lat4 L, ∏ μ : Fin 4,
          (a / (1 + a * |(centeredCoord L (x μ) : ℝ)|) ^ 2) :=
      (Fintype.prod_sum (fun (_ : Fin n) (x : Lat4 L) =>
        ∏ μ : Fin 4, (a / (1 + a * |(centeredCoord L (x μ) : ℝ)|) ^ 2))).symm
    rw [h_prod_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h_nn : 0 ≤ ∑ x : Lat4 L, ∏ μ : Fin 4,
        (a / (1 + a * |(centeredCoord L (x μ) : ℝ)|) ^ 2) :=
      Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity
    exact pow_le_pow_left₀ h_nn h_4d n
  let S_semi : ℝ := ∑ j ∈ Finset.range (8 * n + 1),
    ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 f
  have hS_nn : 0 ≤ S_semi := Finset.sum_nonneg fun j _ =>
    mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  have h_pt : ∀ xs : Fin n → Lat4 L,
      a ^ (4 * n) * ‖f (fun k => centeredLatSite L a (xs k))‖ ≤
        S_semi * (∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2)) := by
    intro xs
    let x_phys := fun k : Fin n => centeredLatSite L a (xs k)
    have h_coord_le : ∀ k : Fin n, ∀ μ : Fin 4,
        1 + a * |(centeredCoord L (xs k μ) : ℝ)| ≤ 1 + ‖x_phys‖ := by
      intro k μ
      have h1 : a * |(centeredCoord L (xs k μ) : ℝ)| = ‖(x_phys k) μ‖ := by
        dsimp [x_phys, centeredLatSite]
        rw [abs_mul, abs_of_pos ha0]
      have h2 : ‖(x_phys k) μ‖ ≤ ‖x_phys k‖ := PiLp.norm_apply_le (x_phys k) μ
      have h3 : ‖x_phys k‖ ≤ ‖x_phys‖ := norm_le_pi_norm x_phys k
      linarith
    have h_prod_den :
        (∏ k : Fin n, ∏ μ : Fin 4, (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2) ≤
          (1 + ‖x_phys‖) ^ (8 * n) := by
      calc (∏ k : Fin n, ∏ μ : Fin 4, (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2)
          ≤ ∏ _k : Fin n, ∏ _μ : Fin 4, (1 + ‖x_phys‖) ^ 2 := by
            refine Finset.prod_le_prod (fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
              fun k _ => Finset.prod_le_prod (fun _ _ => by positivity) fun μ _ =>
                pow_le_pow_left₀ (by positivity) (h_coord_le k μ) 2
        _ = (1 + ‖x_phys‖) ^ (8 * n) := by
            simp [Finset.prod_const, ← pow_mul]
    have h_f_bound : (1 + ‖x_phys‖) ^ (8 * n) * ‖f x_phys‖ ≤ S_semi := by
      rw [add_comm, add_pow, Finset.sum_mul]
      dsimp [S_semi]
      refine Finset.sum_le_sum fun j _ => ?_
      have h_le_s : ‖x_phys‖ ^ j * ‖f x_phys‖ ≤ SchwartzMap.seminorm ℂ j 0 f := by
        simpa [norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℂ j 0 f x_phys
      calc ‖x_phys‖ ^ j * 1 ^ (8 * n - j) * ((8 * n).choose j : ℝ) * ‖f x_phys‖
          = ((8 * n).choose j : ℝ) * (‖x_phys‖ ^ j * ‖f x_phys‖) := by ring
        _ ≤ ((8 * n).choose j : ℝ) * SchwartzMap.seminorm ℂ j 0 f :=
            mul_le_mul_of_nonneg_left h_le_s (Nat.cast_nonneg _)
    have h_a_eq : a ^ (4 * n) =
        (∏ k : Fin n, ∏ μ : Fin 4, (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2) *
        (∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2)) := by
      have ha4 : a ^ (4 * n) = ∏ _k : Fin n, ∏ _μ : Fin 4, a := by
        simp [Finset.prod_const, ← pow_mul, mul_comm]
      rw [ha4, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun μ _ => ?_
      have hne : (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2 ≠ 0 := by positivity
      field_simp [hne]
    rw [h_a_eq, mul_assoc]
    calc (∏ k : Fin n, ∏ μ : Fin 4, (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2) *
          ((∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2)) * ‖f x_phys‖)
        = ((∏ k : Fin n, ∏ μ : Fin 4, (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2) * ‖f x_phys‖) *
          (∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2)) := by ring
      _ ≤ S_semi * (∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2)) :=
          mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_right h_prod_den (norm_nonneg _)) h_f_bound)
            (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
  dsimp [canonicalMagneticSchwinger]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha0]
  calc (|Z_ren| ^ n * a ^ (4 * n)) *
        ‖∑ xs : Fin n → Lat4 L, f (fun k => centeredLatSite L a (xs k)) *
          wilsonExpectation N L β (wilsonHaarLinkMeasure N L)
            (fun U => (∏ k : Fin n, spatialPlaqDensity N L U (xs k) : ℂ))‖
      ≤ |Z_ren| ^ n * (a ^ (4 * n) * ∑ xs : Fin n → Lat4 L,
          ‖f (fun k => centeredLatSite L a (xs k))‖ * (18 : ℝ) ^ n) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun xs _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (h_exp_bd xs) (norm_nonneg _)
    _ = |Z_ren| ^ n * (18 : ℝ) ^ n *
          ∑ xs : Fin n → Lat4 L, a ^ (4 * n) * ‖f (fun k => centeredLatSite L a (xs k))‖ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun xs _ => ?_
        ring
    _ ≤ |Z_ren| ^ n * (18 : ℝ) ^ n *
          ∑ xs : Fin n → Lat4 L, S_semi *
            (∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun xs _ => h_pt xs) (by positivity)
    _ = |Z_ren| ^ n * (18 : ℝ) ^ n * (S_semi * ∑ xs : Fin n → Lat4 L,
          ∏ k : Fin n, ∏ μ : Fin 4, (a / (1 + a * |(centeredCoord L (xs k μ) : ℝ)|) ^ 2)) := by
        simp only [Finset.mul_sum]
    _ ≤ |Z_ren| ^ n * (18 : ℝ) ^ n * (S_semi * (4096 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_nd hS_nn) (by positivity)
    _ = (|Z_ren| * 73728) ^ n * S_semi := by
        have h73 : (73728 : ℝ) = 18 * 4096 := by norm_num
        rw [h73, mul_pow, mul_pow]
        ring

/-- **OS Axiom E3 Permutation Symmetry on `canonicalMagneticSchwinger`.** -/
theorem canonicalMagneticSchwinger_perm_symm (N L n : ℕ) [NeZero N] [NeZero L]
    (a β Z_ren : ℝ) (π : Equiv.Perm (Fin n)) (f f_π : EuclideanSchwartz n)
    (hf : ∀ y, f_π y = f (fun k => y (π k))) :
    canonicalMagneticSchwinger N L n a β Z_ren f_π =
      canonicalMagneticSchwinger N L n a β Z_ren f := by
  dsimp [canonicalMagneticSchwinger]
  congr 1
  let e : (Fin n → Lat4 L) ≃ (Fin n → Lat4 L) :=
    { toFun := fun xs k => xs (π k)
      invFun := fun xs k => xs (π.symm k)
      left_inv := fun xs => by funext k; simp
      right_inv := fun xs => by funext k; simp }
  refine Fintype.sum_equiv e _ _ fun xs => ?_
  have hf_eq : f_π (fun k => centeredLatSite L a (xs k)) =
      f (fun k => centeredLatSite L a (e xs k)) := by
    rw [hf]; rfl
  have hprod_eq : (fun U : LinkConfig N L => (∏ k : Fin n, spatialPlaqDensity N L U (xs k) : ℂ)) =
      (fun U : LinkConfig N L => (∏ k : Fin n, spatialPlaqDensity N L U (e xs k) : ℂ)) := by
    funext U
    exact (Fintype.prod_equiv π _ _ fun k => by simp [e]).symm
  rw [hf_eq, hprod_eq]

/-- **Unconditional Finite-Volume Osterwalder–Seiler Reflection Positivity.** -/
theorem canonical_magnetic_half_torus_rp
    (N M : ℕ) [NeZero N] [NeZero M] {β : ℝ} (hβ : 0 ≤ β)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (n : ι → ℕ)
    (xs : ∀ α : ι, Fin (n α) → Lat4 (2 * M))
    (hpos : ∀ α ∈ s, ∀ k : Fin (n α), ((xs α k) 0).val < M) :
    letI := borel (GaugeGroup N)
    let μ := halfVarHaarMeasure N M
    let F : LinkConfig N (2 * M) → ℂ := fun U =>
      ∑ α ∈ s, c α * ∏ k : Fin (n α), (spatialPlaqDensity N (2 * M) U (xs α k) : ℂ)
    0 ≤ (∫ p, ∫ q, star (F (linkReflect (glueConfig p q))) * F (glueConfig p q) *
      (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ ∂μ).re :=
  canonical_smeared_magnetic_rp_nonneg N M hβ s c n xs hpos

end Imscribing.YangMills.CanonicalLatticeBorchers