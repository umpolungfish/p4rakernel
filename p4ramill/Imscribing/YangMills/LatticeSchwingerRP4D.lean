import Imscribing.YangMills.LatticeOSReflectionPositivity4D
import Imscribing.YangMills.WilsonFrobeniusAndSmeared4D

/-!
# Reflection Positivity for Smeared Positive-Time 4D SU(N) Magnetic Observables
-/

namespace Imscribing.YangMills.LatticeSchwingerRP4D

open MeasureTheory
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D
open Imscribing.YangMills.LatticeRP4D
open Imscribing.YangMills.LatticeCutSplit4D
open Imscribing.YangMills.LatticeOSRP4D

/-- Gauge-invariant spatial (magnetic) plaquette energy density at site `x`. -/
noncomputable def spatialPlaqDensity (N L : ℕ) [NeZero N] (U : LinkConfig N L) (x : Lat4 L) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (1 - realTrace (plaquetteHolonomy U x i.succ j.succ) / (N : ℝ))

theorem spatialPlaqDensity_gaugeInvariant (N L : ℕ) [NeZero N]
    (g : GaugeTransform N L) (U : LinkConfig N L) (x : Lat4 L) :
    spatialPlaqDensity N L (applyGauge g U) x = spatialPlaqDensity N L U x := by
  unfold spatialPlaqDensity
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [plaquetteHolonomy_applyGauge, realTrace_conj]

theorem spatialPlaqDensity_bounds (N L : ℕ) [NeZero N] (U : LinkConfig N L) (x : Lat4 L) :
    0 ≤ spatialPlaqDensity N L U x ∧ spatialPlaqDensity N L U x ≤ 18 := by
  unfold spatialPlaqDensity
  refine ⟨Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    (plaquette_density_bounds _).1, ?_⟩
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, (1 - realTrace (plaquetteHolonomy U x i.succ j.succ) / (N : ℝ)))
        ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (2 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (plaquette_density_bounds _).2
    _ = 18 := by simp [Finset.sum_const]; norm_num

private lemma glueConfig_pos_spatial_eq {N M : ℕ} (p q : HalfVar N M)
    {x : Lat4 (2 * M)} (hx : (x 0).val < M) (i : Fin 3) :
    glueConfig p q x i.succ = p.1 x i.succ := by
  classical
  have hpos : IsPosLink M x i.succ := ⟨hx, fun h => absurd h (Fin.succ_ne_zero i)⟩
  simp [glueConfig, hpos]

private lemma linkReflect_glueConfig_pos_spatial_eq {N M : ℕ} [NeZero M] (p q : HalfVar N M)
    {x : Lat4 (2 * M)} (hx : (x 0).val < M) (i : Fin 3) :
    linkReflect (glueConfig p q) x i.succ = q.1 x i.succ := by
  classical
  haveI : NeZero (2 * M) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne M)⟩
  have hM : 0 < M := NeZero.pos M
  have hx_lt : (x 0).val < 2 * M := ZMod.val_lt (x 0)
  have h_refl_val : ((reflectSite (2 * M) x) 0).val = 2 * M - 1 - (x 0).val := by
    simp only [reflectSite, ↓reduceIte]
    have heq : -(x 0 + 1) = (((2 * M - 1 - (x 0).val : ℕ) : ZMod (2 * M))) := by
      have hsub : ((x 0).val + (2 * M - 1 - (x 0).val) + 1 : ℕ) = 2 * M := by omega
      have hz : (((x 0).val + (2 * M - 1 - (x 0).val) + 1 : ℕ) : ZMod (2 * M)) = 0 := by
        rw [hsub]; exact ZMod.natCast_self (2 * M)
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at hz
      linear_combination -hz
    rw [heq, ZMod.val_natCast_of_lt (by omega)]
  have h_neg : IsNegLink M (reflectSite (2 * M) x) i.succ :=
    ⟨by omega, fun h => absurd h (Fin.succ_ne_zero i)⟩
  have h_np : ¬ IsPosLink M (reflectSite (2 * M) x) i.succ := by
    rintro ⟨a, _⟩; exact absurd a (not_lt.mpr h_neg.1)
  have h_ncm : ¬ IsCutLinkMid M (reflectSite (2 * M) x) i.succ := by
    rintro ⟨h, _⟩; exact Fin.succ_ne_zero i h
  have h_nct : ¬ IsCutLinkTop M (reflectSite (2 * M) x) i.succ := by
    rintro ⟨h, _⟩; exact Fin.succ_ne_zero i h
  simp only [linkReflect, Fin.succ_ne_zero, ↓reduceIte, glueConfig, h_np, h_ncm, h_nct]
  exact congrFun (congrFun (linkReflect_involutive q.1) x) i.succ

private lemma spatial_shift_zero_val (M : ℕ) (x : Lat4 (2 * M)) (i : Fin 3) :
    ((x + stepDir (2 * M) i.succ) 0).val = (x 0).val := by
  simp [stepDir, (Fin.succ_ne_zero i).symm]

/-- At any positive-time site `(x 0).val < M`, `spatialPlaqDensity` on `glueConfig p q`
    depends only on the positive-half configuration `p.1`. -/
theorem spatialPlaqDensity_glue_pos {N M : ℕ} [NeZero N] (p q : HalfVar N M)
    {x : Lat4 (2 * M)} (hx : (x 0).val < M) :
    spatialPlaqDensity N (2 * M) (glueConfig p q) x = spatialPlaqDensity N (2 * M) p.1 x := by
  unfold spatialPlaqDensity
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 := glueConfig_pos_spatial_eq p q hx i
  have h2 := glueConfig_pos_spatial_eq p q (by rw [spatial_shift_zero_val M x i]; exact hx) j
  have h3 := glueConfig_pos_spatial_eq p q (by rw [spatial_shift_zero_val M x j]; exact hx) i
  have h4 := glueConfig_pos_spatial_eq p q hx j
  simp only [plaquetteHolonomy, h1, h2, h3, h4]

/-- At any positive-time site `(x 0).val < M`, `spatialPlaqDensity` on `linkReflect (glueConfig p q)`
    depends only on the negative-half configuration `q.1`. -/
theorem spatialPlaqDensity_reflect_glue_pos {N M : ℕ} [NeZero N] [NeZero M] (p q : HalfVar N M)
    {x : Lat4 (2 * M)} (hx : (x 0).val < M) :
    spatialPlaqDensity N (2 * M) (linkReflect (glueConfig p q)) x =
      spatialPlaqDensity N (2 * M) q.1 x := by
  unfold spatialPlaqDensity
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 := linkReflect_glueConfig_pos_spatial_eq p q hx i
  have h2 := linkReflect_glueConfig_pos_spatial_eq p q (by rw [spatial_shift_zero_val M x i]; exact hx) j
  have h3 := linkReflect_glueConfig_pos_spatial_eq p q (by rw [spatial_shift_zero_val M x j]; exact hx) i
  have h4 := linkReflect_glueConfig_pos_spatial_eq p q hx j
  simp only [plaquetteHolonomy, h1, h2, h3, h4]

/-- **Finite-Volume Reflection Positivity for Smeared Positive-Time Magnetic Observables.** -/
theorem smeared_magnetic_wilson_rp_nonneg
    {N M : ℕ} [NeZero N] [NeZero M] {β : ℝ} (hβ : 0 ≤ β)
    [MeasurableSpace (GaugeGroup N)] [MeasurableMul₂ (GaugeGroup N)] [MeasurableInv (GaugeGroup N)]
    (hEntry : ∀ i j : Fin N, Measurable (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ) i j))
    (μ : Measure (HalfVar N M)) [IsFiniteMeasure μ]
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (n : ι → ℕ)
    (xs : ∀ α : ι, Fin (n α) → Lat4 (2 * M))
    (hpos : ∀ α ∈ s, ∀ k : Fin (n α), ((xs α k) 0).val < M) :
    let F : LinkConfig N (2 * M) → ℂ := fun U =>
      ∑ α ∈ s, c α * ∏ k : Fin (n α), (spatialPlaqDensity N (2 * M) U (xs α k) : ℂ)
    0 ≤ (∫ p, ∫ q, star (F (linkReflect (glueConfig p q))) * F (glueConfig p q) *
      (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ ∂μ).re := by
  intro F
  let F_half : HalfVar N M → ℂ := fun p => F p.1
  have h_meas_site : ∀ x : Lat4 (2 * M),
      Measurable (fun p : HalfVar N M => (spatialPlaqDensity N (2 * M) p.1 x : ℂ)) := by
    intro x
    apply Complex.continuous_ofReal.measurable.comp
    unfold spatialPlaqDensity realTrace
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    refine measurable_const.sub ((Complex.continuous_re.measurable.comp ?_).div_const _)
    unfold plaquetteHolonomy
    have ml1 : Measurable (fun p : HalfVar N M => p.1 x i.succ) :=
      ((measurable_pi_apply i.succ).comp
        (measurable_pi_apply x : Measurable fun U : LinkConfig N (2 * M) => U x)).comp measurable_fst
    have ml2 : Measurable (fun p : HalfVar N M => p.1 (x + stepDir (2 * M) i.succ) j.succ) :=
      ((measurable_pi_apply j.succ).comp
        (measurable_pi_apply (x + stepDir (2 * M) i.succ) :
          Measurable fun U : LinkConfig N (2 * M) => U (x + stepDir (2 * M) i.succ))).comp measurable_fst
    have ml3 : Measurable (fun p : HalfVar N M => (p.1 (x + stepDir (2 * M) j.succ) i.succ)⁻¹) :=
      (((measurable_pi_apply i.succ).comp
        (measurable_pi_apply (x + stepDir (2 * M) j.succ) :
          Measurable fun U : LinkConfig N (2 * M) => U (x + stepDir (2 * M) j.succ))).comp measurable_fst).inv
    have ml4 : Measurable (fun p : HalfVar N M => (p.1 x j.succ)⁻¹) :=
      (((measurable_pi_apply j.succ).comp
        (measurable_pi_apply x : Measurable fun U : LinkConfig N (2 * M) => U x)).comp measurable_fst).inv
    have mprod := ((ml1.mul ml2).mul ml3).mul ml4
    change Measurable (fun p : HalfVar N M =>
      Matrix.trace ((plaquetteHolonomy p.1 x i.succ j.succ : GaugeGroup N) :
        Matrix (Fin N) (Fin N) ℂ))
    simp only [Matrix.trace, Matrix.diag_apply]
    exact Finset.measurable_sum _ fun k _ => (hEntry k k).comp mprod
  have hF_meas : Measurable F_half := by
    dsimp [F_half, F]
    refine Finset.measurable_sum _ fun α _ => measurable_const.mul ?_
    exact Finset.measurable_prod _ fun k _ => h_meas_site (xs α k)
  let BF : ℝ := ∑ α ∈ s, ‖c α‖ * (18 : ℝ) ^ (n α)
  have hBF_nn : 0 ≤ BF := Finset.sum_nonneg fun α _ => by positivity
  have hF_bound : ∀ p : HalfVar N M, ‖F_half p‖ ≤ BF := by
    intro p
    dsimp [F_half, F, BF]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun α _ => ?_)
    rw [norm_mul, norm_prod]
    have h_prod_le : (∏ k : Fin (n α), ‖(spatialPlaqDensity N (2 * M) p.1 (xs α k) : ℂ)‖) ≤
        (18 : ℝ) ^ (n α) := by
      calc
        (∏ k : Fin (n α), ‖(spatialPlaqDensity N (2 * M) p.1 (xs α k) : ℂ)‖)
            ≤ ∏ _k : Fin (n α), (18 : ℝ) := by
                refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => ?_
                rw [Complex.norm_real, Real.norm_of_nonneg (spatialPlaqDensity_bounds N (2 * M) p.1 _).1]
                exact (spatialPlaqDensity_bounds N (2 * M) p.1 _).2
        _ = (18 : ℝ) ^ (n α) := by simp [Finset.prod_const]
    exact mul_le_mul_of_nonneg_left h_prod_le (norm_nonneg _)
  have h_rp := wilson4D_reflection_positivity hβ hEntry μ F_half hF_meas BF hBF_nn hF_bound
  have h_eq : ∀ p q : HalfVar N M,
      star (F (linkReflect (glueConfig p q))) * F (glueConfig p q) =
        star (F_half q) * F_half p := by
    intro p q
    have hp : F (glueConfig p q) = F_half p := by
      dsimp [F, F_half]
      refine Finset.sum_congr rfl fun α hα => congrArg (c α * ·) ?_
      refine Finset.prod_congr rfl fun k _ => ?_
      exact congrArg Complex.ofReal (spatialPlaqDensity_glue_pos p q (hpos α hα k))
    have hq : F (linkReflect (glueConfig p q)) = F_half q := by
      dsimp [F, F_half]
      refine Finset.sum_congr rfl fun α hα => congrArg (c α * ·) ?_
      refine Finset.prod_congr rfl fun k _ => ?_
      exact congrArg Complex.ofReal (spatialPlaqDensity_reflect_glue_pos p q (hpos α hα k))
    rw [hp, hq]
  have h_conj_eq :
      (∫ p, ∫ q, star (F (linkReflect (glueConfig p q))) * F (glueConfig p q) *
        (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ ∂μ) =
      star (∫ p, ∫ q, star (F_half p) * F_half q *
        (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ ∂μ) := by
    change _ = starRingEnd ℂ (∫ p, ∫ q, star (F_half p) * F_half q *
      (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ ∂μ)
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    change star (F (linkReflect (glueConfig p q))) * F (glueConfig p q) *
        (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) =
      star (star (F_half p) * F_half q *
        (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ))
    rw [h_eq p q, star_mul, star_mul, star_star, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [h_conj_eq]
  change (starRingEnd ℂ _).re ≥ 0
  rw [Complex.conj_re]
  exact h_rp

end Imscribing.YangMills.LatticeSchwingerRP4D