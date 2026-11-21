import Mathlib
import Imscribing.YangMills.OSCompletion

set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 50000
set_option maxRecDepth 20000

open scoped InnerProductSpace
open Complex Finset Real MeasureTheory Set

namespace YangMills

/-! ## §39.  Exact 4D Wilson temporal-gauge transfer kernel & operator on `cubicTorus3` -/

section ExactWilson4DTransferOperator

/-- Spatial gauge group `𝒢_L = Site → SU(N)` over `cubicTorus3 L`. -/
abbrev GaugeGrp3 (L N : ℕ) [NeZero L] :=
  (cubicTorus3 L).Site → Matrix.specialUnitaryGroup (Fin N) ℂ

@[reducible] instance instMeasurableSpaceGaugeGrp3 (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasurableSpace (GaugeGrp3 L N) :=
  MeasurableSpace.pi

/-- Normalized Haar probability measure on `GaugeGrp3 L N = ∏_x SU(N)`. -/
noncomputable def gaugeGrpHaarMeasure (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure (GaugeGrp3 L N) :=
  MeasureTheory.Measure.pi (fun _ => suHaar N)

theorem gaugeGrpHaarMeasure_prob (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.IsProbabilityMeasure (gaugeGrpHaarMeasure L N) := by
  haveI := suHaar_prob N
  change MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.Measure.pi fun _ : (cubicTorus3 L).Site => suHaar N)
  infer_instance

theorem gaugeGrpHaarMeasure_inv (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    MeasureTheory.Measure.map (fun g : GaugeGrp3 L N => fun x => (g x)⁻¹)
      (gaugeGrpHaarMeasure L N) = gaugeGrpHaarMeasure L N := by
  haveI := suHaar_prob N
  haveI := gaugeGrpHaarMeasure_prob L N
  let F : GaugeGrp3 L N → GaugeGrp3 L N := fun g x => (g x)⁻¹
  have hF_meas : Measurable F := measurable_pi_iff.mpr fun x =>
    (continuous_inv (G := Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable.comp
      (measurable_pi_apply x)
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hF_meas (MeasurableSet.univ_pi hs)]
  have hpre : F ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun x => (fun u : Matrix.specialUnitaryGroup (Fin N) ℂ => u⁻¹) ⁻¹' s x) := by
    ext g; simp [F]
  rw [hpre]
  change (MeasureTheory.Measure.pi (fun _ : (cubicTorus3 L).Site => suHaar N))
      (Set.pi Set.univ fun x => (fun u : Matrix.specialUnitaryGroup (Fin N) ℂ => u⁻¹) ⁻¹' s x) =
    ∏ x : (cubicTorus3 L).Site, suHaar N (s x)
  rw [MeasureTheory.Measure.pi_pi]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [← MeasureTheory.Measure.map_apply
    (continuous_inv (G := Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable (hs x),
    suHaar_map_inv N]

theorem gaugeGrpHaarMeasure_mul_left_right (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (h₁ h₂ : GaugeGrp3 L N) :
    MeasureTheory.Measure.map (fun g : GaugeGrp3 L N => fun x => h₁ x * g x * h₂ x)
      (gaugeGrpHaarMeasure L N) = gaugeGrpHaarMeasure L N := by
  haveI := suHaar_prob N
  haveI := gaugeGrpHaarMeasure_prob L N
  let φ : (cubicTorus3 L).Site →
      Matrix.specialUnitaryGroup (Fin N) ℂ → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    fun x u => h₁ x * u * h₂ x
  let F : GaugeGrp3 L N → GaugeGrp3 L N := fun g x => φ x (g x)
  have hφ_meas : ∀ x, Measurable (φ x) := fun x =>
    ((continuous_mul_right (h₂ x)).comp (continuous_mul_left (h₁ x))).measurable
  have hF_meas : Measurable F := measurable_pi_iff.mpr fun x =>
    (hφ_meas x).comp (measurable_pi_apply x)
  symm
  refine MeasureTheory.Measure.pi_eq fun s hs => ?_
  rw [MeasureTheory.Measure.map_apply hF_meas (MeasurableSet.univ_pi hs)]
  have hpre : F ⁻¹' Set.pi Set.univ s = Set.pi Set.univ (fun x => φ x ⁻¹' s x) := by
    ext g; simp [F]
  rw [hpre]
  change (MeasureTheory.Measure.pi (fun _ : (cubicTorus3 L).Site => suHaar N))
      (Set.pi Set.univ fun x => φ x ⁻¹' s x) =
    ∏ x : (cubicTorus3 L).Site, suHaar N (s x)
  rw [MeasureTheory.Measure.pi_pi]
  refine Finset.prod_congr rfl fun x _ => ?_
  have hcomp : φ x = (fun u => u * h₂ x) ∘ (fun u => h₁ x * u) := rfl
  have hmap : MeasureTheory.Measure.map (φ x) (suHaar N) = suHaar N := by
    rw [hcomp, ← MeasureTheory.Measure.map_map (continuous_mul_right _).measurable
        (continuous_mul_left _).measurable, suHaar_map_mul_left, suHaar_map_mul_right]
  rw [← MeasureTheory.Measure.map_apply (hφ_meas x) (hs x), hmap]

/-- Single temporal plaquette Boltzmann factor between spatial slices `U` and `U'` under temporal links `g`. -/
noncomputable def temporalPlaqFactor {L N : ℕ} [NeZero L] (β : ℝ)
    (e : (cubicTorus3 L).Link)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (g : GaugeGrp3 L N) : ℝ :=
  Real.exp (-(β * (1 - (1 / (N : ℝ)) *
    (Matrix.trace (((U e * (gaugeAct g U' e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ))).re)))

/-- Exact 4D Wilson temporal-link-integrated kinetic kernel `K_4D(U, U')`. -/
noncomputable def wilson4DKernel (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  ∫ g, (∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g) ∂(gaugeGrpHaarMeasure L N)

theorem temporalPlaqFactor_bounds {L N : ℕ} [NeZero L] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β) (e : (cubicTorus3 L).Link)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (g : GaugeGrp3 L N) :
    Real.exp (-(2 * β)) ≤ temporalPlaqFactor β e U U' g ∧
      temporalPlaqFactor β e U U' g ≤ 1 := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have htr := abs_le.mp (abs_re_trace_su_le (U e * (gaugeAct g U' e)⁻¹))
  have h_le1 : (1 / (N : ℝ)) *
      (Matrix.trace (((U e * (gaugeAct g U' e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ))).re ≤ 1 := by
    rw [one_div, inv_mul_le_iff₀ hN_pos, mul_one]; exact htr.2
  have h_ge_neg1 : -1 ≤ (1 / (N : ℝ)) *
      (Matrix.trace (((U e * (gaugeAct g U' e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ))).re := by
    rw [one_div, le_inv_mul_iff₀ hN_pos, mul_neg, mul_one]; exact htr.1
  unfold temporalPlaqFactor
  exact ⟨Real.exp_le_exp.mpr (by nlinarith), Real.exp_le_one_iff.mpr (by nlinarith)⟩

theorem continuous_temporalPlaqProd (L N : ℕ) [NeZero L] (β : ℝ) :
    Continuous (fun q :
        (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
         GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        GaugeGrp3 L N =>
      ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e q.1.1 q.1.2 q.2) := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  have h_ent : ∀ i : Fin N, Continuous (fun A : G => (A : Matrix (Fin N) (Fin N) ℂ) i i) :=
    fun i => (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : G => (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  refine continuous_finset_prod Finset.univ fun e _ => ?_
  have hU : Continuous (fun q :
      (GaugeField (cubicTorus3 L) G × GaugeField (cubicTorus3 L) G) × GaugeGrp3 L N => q.1.1 e) :=
    (continuous_apply e).comp (continuous_fst.comp continuous_fst)
  have hg1 : Continuous (fun q :
      (GaugeField (cubicTorus3 L) G × GaugeField (cubicTorus3 L) G) × GaugeGrp3 L N =>
        q.2 ((cubicTorus3 L).src e)) :=
    (continuous_apply ((cubicTorus3 L).src e)).comp continuous_snd
  have hU' : Continuous (fun q :
      (GaugeField (cubicTorus3 L) G × GaugeField (cubicTorus3 L) G) × GaugeGrp3 L N => q.1.2 e) :=
    (continuous_apply e).comp (continuous_snd.comp continuous_fst)
  have hg2 : Continuous (fun q :
      (GaugeField (cubicTorus3 L) G × GaugeField (cubicTorus3 L) G) × GaugeGrp3 L N =>
        (q.2 ((cubicTorus3 L).dst e))⁻¹) :=
    continuous_inv.comp ((continuous_apply ((cubicTorus3 L).dst e)).comp continuous_snd)
  have h_act_inv : Continuous (fun q :
      (GaugeField (cubicTorus3 L) G × GaugeField (cubicTorus3 L) G) × GaugeGrp3 L N =>
        (gaugeAct q.2 q.1.2 e)⁻¹) :=
    continuous_inv.comp ((hg1.mul hU').mul hg2)
  exact Real.continuous_exp.comp
    ((continuous_const.mul (continuous_const.sub (continuous_const.mul
      (h_tr.comp (hU.mul h_act_inv))))).neg)

private theorem continuous_temporalPlaqProd_fixed (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (g : GaugeGrp3 L N) :
    Continuous (fun p :
        (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
         GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) =>
      ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e p.1 p.2 g) := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  have h_ent : ∀ i : Fin N, Continuous (fun A : G => (A : Matrix (Fin N) (Fin N) ℂ) i i) :=
    fun i => (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : G => (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  refine continuous_finset_prod Finset.univ fun e _ => ?_
  have hU : Continuous (fun p :
      (GaugeField (cubicTorus3 L) G × GaugeField (cubicTorus3 L) G) => p.1 e) :=
    (continuous_apply e).comp continuous_fst
  have hU' : Continuous (fun p :
      (GaugeField (cubicTorus3 L) G × GaugeField (cubicTorus3 L) G) => p.2 e) :=
    (continuous_apply e).comp continuous_snd
  have h_act_inv : Continuous (fun p :
      (GaugeField (cubicTorus3 L) G × GaugeField (cubicTorus3 L) G) =>
        (gaugeAct g p.2 e)⁻¹) := by
    have hsrc : Continuous (fun _p : GaugeField (cubicTorus3 L) G × GaugeField (cubicTorus3 L) G =>
        g ((cubicTorus3 L).src e)) := continuous_const
    have hdst : Continuous (fun _p : GaugeField (cubicTorus3 L) G × GaugeField (cubicTorus3 L) G =>
        (g ((cubicTorus3 L).dst e))⁻¹) := continuous_const
    exact continuous_inv.comp ((hsrc.mul hU').mul hdst)
  exact Real.continuous_exp.comp
    ((continuous_const.mul (continuous_const.sub (continuous_const.mul
      (h_tr.comp (hU.mul h_act_inv))))).neg)

private theorem continuous_temporalPlaqProd_in_g (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Continuous (fun g : GaugeGrp3 L N =>
      ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g) := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  have h_ent : ∀ i : Fin N, Continuous (fun A : G => (A : Matrix (Fin N) (Fin N) ℂ) i i) :=
    fun i => (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  have h_tr : Continuous (fun A : G => (Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re) := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact continuous_finset_sum Finset.univ fun i _ => Complex.continuous_re.comp (h_ent i)
  refine continuous_finset_prod Finset.univ fun e _ => ?_
  have hU : Continuous (fun _g : GaugeGrp3 L N => U e) := continuous_const
  have hU' : Continuous (fun _g : GaugeGrp3 L N => U' e) := continuous_const
  have hg1 : Continuous (fun g : GaugeGrp3 L N => g ((cubicTorus3 L).src e)) :=
    continuous_apply ((cubicTorus3 L).src e)
  have hg2 : Continuous (fun g : GaugeGrp3 L N => (g ((cubicTorus3 L).dst e))⁻¹) :=
    continuous_inv.comp (continuous_apply ((cubicTorus3 L).dst e))
  have h_act_inv : Continuous (fun g : GaugeGrp3 L N => (gaugeAct g U' e)⁻¹) :=
    continuous_inv.comp ((hg1.mul hU').mul hg2)
  exact Real.continuous_exp.comp
    ((continuous_const.mul (continuous_const.sub (continuous_const.mul
      (h_tr.comp (hU.mul h_act_inv))))).neg)

theorem continuous_wilson4DKernel (L N : ℕ) [NeZero L] (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    Continuous (Function.uncurry (wilson4DKernel L N β)) := by
  let μ_g := gaugeGrpHaarMeasure L N
  haveI := gaugeGrpHaarMeasure_prob L N
  have hc_prod := continuous_temporalPlaqProd L N β
  refine MeasureTheory.continuous_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_
    (MeasureTheory.integrable_const (1 : ℝ)) ?_
  · intro p
    exact (hc_prod.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable.aestronglyMeasurable
  · intro p
    refine Filter.Eventually.of_forall fun g => ?_
    have hnn : 0 ≤ ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e p.1 p.2 g :=
      Finset.prod_nonneg fun e _ => (temporalPlaqFactor_bounds hN β hβ e p.1 p.2 g).1.trans'
        (Real.exp_pos _).le
    have hle : ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e p.1 p.2 g ≤ 1 := by
      calc ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e p.1 p.2 g
          ≤ ∏ _e : (cubicTorus3 L).Link, (1 : ℝ) :=
            Finset.prod_le_prod
              (fun e _ => (Real.exp_pos _).le)
              (fun e _ => (temporalPlaqFactor_bounds hN β hβ e p.1 p.2 g).2)
        _ = 1 := by simp
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hle
  · refine Filter.Eventually.of_forall fun g : GaugeGrp3 L N => ?_
    exact continuous_temporalPlaqProd_fixed L N β g

theorem wilson4DKernel_bounds (L N : ℕ) [NeZero L] (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Real.exp (-(2 * β * (Fintype.card (cubicTorus3 L).Link : ℝ))) ≤
        wilson4DKernel L N β U U' ∧
      wilson4DKernel L N β U U' ≤ 1 := by
  let μ_g := gaugeGrpHaarMeasure L N
  haveI := gaugeGrpHaarMeasure_prob L N
  have hc_g : Continuous (fun g : GaugeGrp3 L N =>
      ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g) :=
    continuous_temporalPlaqProd_in_g L N β U U'
  have h_int : MeasureTheory.Integrable
      (fun g => ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g) μ_g :=
    (MeasureTheory.integrable_const (1 : ℝ)).mono' hc_g.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        have hnn : 0 ≤ ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g :=
          Finset.prod_nonneg fun e _ => (Real.exp_pos _).le
        have hle : ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g ≤ 1 := by
          calc ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g
              ≤ ∏ _e : (cubicTorus3 L).Link, (1 : ℝ) :=
                Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
                  (fun e _ => (temporalPlaqFactor_bounds hN β hβ e U U' g).2)
            _ = 1 := by simp
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        exact hle)
  have h_pt_lb : ∀ g, Real.exp (-(2 * β * (Fintype.card (cubicTorus3 L).Link : ℝ))) ≤
      ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g := by
    intro g
    have hpow : (Real.exp (-(2 * β))) ^ (Fintype.card (cubicTorus3 L).Link) =
        Real.exp (-(2 * β * (Fintype.card (cubicTorus3 L).Link : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1; ring
    rw [← hpow]
    calc (Real.exp (-(2 * β))) ^ (Fintype.card (cubicTorus3 L).Link)
        = ∏ _e : (cubicTorus3 L).Link, Real.exp (-(2 * β)) := by
            simp [Finset.prod_const, Finset.card_univ]
      _ ≤ ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g :=
            Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
              (fun e _ => (temporalPlaqFactor_bounds hN β hβ e U U' g).1)
  have h_pt_ub : ∀ g, ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g ≤ 1 := by
    intro g
    calc ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g
        ≤ ∏ _e : (cubicTorus3 L).Link, (1 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
            (fun e _ => (temporalPlaqFactor_bounds hN β hβ e U U' g).2)
      _ = 1 := by simp
  constructor
  · calc Real.exp (-(2 * β * (Fintype.card (cubicTorus3 L).Link : ℝ)))
        = ∫ _g, Real.exp (-(2 * β * (Fintype.card (cubicTorus3 L).Link : ℝ))) ∂μ_g := by
            simp [Measure.real, MeasureTheory.measure_univ]
      _ ≤ wilson4DKernel L N β U U' :=
            MeasureTheory.integral_mono (MeasureTheory.integrable_const _) h_int h_pt_lb
  · calc wilson4DKernel L N β U U'
        ≤ ∫ _g, (1 : ℝ) ∂μ_g :=
            MeasureTheory.integral_mono h_int (MeasureTheory.integrable_const _) h_pt_ub
      _ = 1 := by simp [Measure.real, MeasureTheory.measure_univ]

/-- Exact symmetry `wilson4DKernel L N β U' U = wilson4DKernel L N β U U'`. -/
theorem wilson4DKernel_symm (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilson4DKernel L N β U' U = wilson4DKernel L N β U U' := by
  let invEquiv : GaugeGrp3 L N ≃ᵐ GaugeGrp3 L N :=
    { toFun := fun g x => (g x)⁻¹
      invFun := fun g x => (g x)⁻¹
      left_inv := fun g => by funext x; simp
      right_inv := fun g => by funext x; simp
      measurable_toFun := measurable_pi_iff.mpr fun x =>
        (continuous_inv (G := Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable.comp
          (measurable_pi_apply x)
      measurable_invFun := measurable_pi_iff.mpr fun x =>
        (continuous_inv (G := Matrix.specialUnitaryGroup (Fin N) ℂ)).measurable.comp
          (measurable_pi_apply x) }
  have hmp : MeasureTheory.MeasurePreserving invEquiv
      (gaugeGrpHaarMeasure L N) (gaugeGrpHaarMeasure L N) :=
    ⟨invEquiv.measurable, gaugeGrpHaarMeasure_inv L N⟩
  unfold wilson4DKernel
  rw [← hmp.integral_comp' (fun g => ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U' U g)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  refine Finset.prod_congr rfl fun e _ => ?_
  have h_conj : U' e * (gaugeAct (fun x => (g x)⁻¹) U e)⁻¹ =
      (g ((cubicTorus3 L).src e))⁻¹ *
        (U e * (gaugeAct g U' e)⁻¹)⁻¹ *
        ((g ((cubicTorus3 L).src e))⁻¹)⁻¹ := by
    simp only [gaugeAct, mul_inv_rev, inv_inv]
    group
  have h_tr :
      (Matrix.trace (((U' e * (gaugeAct (invEquiv g) U e)⁻¹ :
          Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))).re =
        (Matrix.trace (((U e * (gaugeAct g U' e)⁻¹ :
          Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))).re := by
    change (Matrix.trace (((U' e * (gaugeAct (fun x => (g x)⁻¹) U e)⁻¹ :
        Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))).re = _
    rw [h_conj, su_trace_conj', su_trace_inv_re]
  unfold temporalPlaqFactor
  rw [h_tr]

/-- Exact two-sided local gauge invariance of the 4D Wilson temporal kernel. -/
theorem wilson4DKernel_gauge_inv_two_sided (L N : ℕ) [NeZero L] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (h₁ h₂ : GaugeGrp3 L N)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    wilson4DKernel L N β (gaugeAct h₁ U) (gaugeAct h₂ U') =
      wilson4DKernel L N β U U' := by
  let shiftEquiv : GaugeGrp3 L N ≃ᵐ GaugeGrp3 L N :=
    { toFun := fun g x => (h₁ x)⁻¹ * g x * h₂ x
      invFun := fun g x => h₁ x * g x * (h₂ x)⁻¹
      left_inv := fun g => by funext x; group
      right_inv := fun g => by funext x; group
      measurable_toFun := measurable_pi_iff.mpr fun x =>
        ((continuous_mul_right _).comp (continuous_mul_left _)).measurable.comp
          (measurable_pi_apply x)
      measurable_invFun := measurable_pi_iff.mpr fun x =>
        ((continuous_mul_right _).comp (continuous_mul_left _)).measurable.comp
          (measurable_pi_apply x) }
  have hmp : MeasureTheory.MeasurePreserving shiftEquiv
      (gaugeGrpHaarMeasure L N) (gaugeGrpHaarMeasure L N) :=
    ⟨shiftEquiv.measurable, gaugeGrpHaarMeasure_mul_left_right L N (fun x => (h₁ x)⁻¹) h₂⟩
  unfold wilson4DKernel
  rw [← hmp.integral_comp'
    (fun g => ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  refine Finset.prod_congr rfl fun e _ => ?_
  have h_conj : gaugeAct h₁ U e * (gaugeAct g (gaugeAct h₂ U') e)⁻¹ =
      h₁ ((cubicTorus3 L).src e) *
        (U e * (gaugeAct (fun x => (h₁ x)⁻¹ * g x * h₂ x) U' e)⁻¹) *
        (h₁ ((cubicTorus3 L).src e))⁻¹ := by
    simp only [gaugeAct, mul_inv_rev, inv_inv]
    group
  have h_tr :
      (Matrix.trace (((gaugeAct h₁ U e * (gaugeAct g (gaugeAct h₂ U') e)⁻¹ :
          Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))).re =
        (Matrix.trace (((U e * (gaugeAct (shiftEquiv g) U' e)⁻¹ :
          Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))).re := by
    change _ = (Matrix.trace (((U e * (gaugeAct (fun x => (h₁ x)⁻¹ * g x * h₂ x) U' e)⁻¹ :
        Matrix.specialUnitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))).re
    rw [h_conj, su_trace_conj']
  unfold temporalPlaqFactor
  rw [h_tr]

/-- Genuine 4D Wilson transfer operator on `L²(SU(N)^{3L³}, dμ_Haar)` using `wilson4DKernel`. -/
noncomputable def wilson4DTransferOp (L N : ℕ) [NeZero L] (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] HaarGaugeSpace (latticeHaarMeasure L N) :=
  wilsonIntegralOp L N β hβ (wilson4DKernel L N β)
    (continuous_wilson4DKernel L N hN β hβ)
    (fun U U' => (Real.exp_pos _).le.trans (wilson4DKernel_bounds L N hN β hβ U U').1)
    1 zero_le_one
    (fun U U' => (wilson4DKernel_bounds L N hN β hβ U U').2)

theorem wilson4DTransferOp_sa (L N : ℕ) [NeZero L] (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ₁ ψ₂ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    ⟪wilson4DTransferOp L N hN β hβ ψ₁, ψ₂⟫_ℂ =
      ⟪ψ₁, wilson4DTransferOp L N hN β hβ ψ₂⟫_ℂ :=
  wilsonIntegralOp_sa L N β hβ (wilson4DKernel L N β)
    (continuous_wilson4DKernel L N hN β hβ)
    (wilson4DKernel_symm L N β)
    (fun U U' => (Real.exp_pos _).le.trans (wilson4DKernel_bounds L N hN β hβ U U').1)
    1 zero_le_one
    (fun U U' => (wilson4DKernel_bounds L N hN β hβ U U').2)
    ψ₁ ψ₂

theorem wilson4DTransferOp_compact (L N : ℕ) [NeZero L] (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    IsCompactOperator ⇑(wilson4DTransferOp L N hN β hβ) :=
  wilsonIntegralOp_compact L N β hβ (wilson4DKernel L N β)
    (continuous_wilson4DKernel L N hN β hβ)
    (fun U U' => (Real.exp_pos _).le.trans (wilson4DKernel_bounds L N hN β hβ U U').1)
    1 zero_le_one
    (fun U U' => (wilson4DKernel_bounds L N hN β hβ U U').2)

/-- `wilson4DTransferOp` projects strictly onto the physical Gauss-law gauge-invariant subspace. -/
theorem wilson4DTransferOp_gauge_proj (L N : ℕ) [NeZero L] (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (h : GaugeGrp3 L N) (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    cubicGaugeRep L N h (wilson4DTransferOp L N hN β hβ ψ) =
      wilson4DTransferOp L N hN β hβ ψ := by
  apply MeasureTheory.Lp.ext
  let μ := latticeHaarMeasure L N
  let eqv := gaugeActEquiv L N (fun x => (h x)⁻¹)
  let hmp : MeasureTheory.MeasurePreserving eqv μ μ :=
    ⟨eqv.measurable, latticeHaarMeasure_gauge_inv L N (fun x => (h x)⁻¹)⟩
  let K4 := wilson4DKernel L N β
  have hK_cont := continuous_wilson4DKernel L N hN β hβ
  have hK_nn : ∀ U U', 0 ≤ K4 U U' := fun U U' =>
    (Real.exp_pos _).le.trans (wilson4DKernel_bounds L N hN β hβ U U').1
  have hK_bd : ∀ U U', K4 U U' ≤ 1 := fun U U' =>
    (wilson4DKernel_bounds L N hN β hβ U U').2
  have hL1 := cubicGaugeRep_apply_ae L N h (wilson4DTransferOp L N hN β hβ ψ)
  have hL2 : (fun U => (wilson4DTransferOp L N hN β hβ ψ) (eqv U)) =ᵐ[μ]
      fun U => wilsonIntegralFn L N β K4 ψ (eqv U) :=
    ae_comp_measurePreserving hmp
      (wilsonIntegralOp_apply_ae L N β hβ K4 hK_cont hK_nn 1 zero_le_one hK_bd ψ)
  have hR := wilsonIntegralOp_apply_ae L N β hβ K4 hK_cont hK_nn 1 zero_le_one hK_bd ψ
  filter_upwards [hL1, hL2, hR] with U hl1 hl2 hr
  rw [hl1]
  have hl2' : (wilson4DTransferOp L N hN β hβ ψ) (gaugeAct (fun x => (h x)⁻¹) U) =
      wilsonIntegralFn L N β K4 ψ (gaugeAct (fun x => (h x)⁻¹) U) := by
    simpa [eqv] using hl2
  rw [hl2']
  dsimp only [wilson4DTransferOp]
  rw [hr]
  -- The 4D kernel is invariant in each argument separately, so the SAME ψ appears
  -- on both sides: no change of variables is needed, only first-argument invariance.
  dsimp [wilsonIntegralFn]
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall fun U' => ?_
  apply congrArg (fun z : ℂ => z * ψ U')
  apply congrArg (fun r : ℝ => (r : ℂ))
  dsimp [eqv]
  unfold wilsonKernel
  rw [wilsonAction_gauge_inv]
  have hk4 : K4 (gaugeAct (fun x => (h x)⁻¹) U) U' = K4 U U' := by
    simpa [K4, gaugeAct_one] using
      (wilson4DKernel_gauge_inv_two_sided L N β (fun x => (h x)⁻¹) (fun _ => 1) U U')
  rw [hk4]

end ExactWilson4DTransferOperator

/-! ## §40.  Positivity, Perron–Frobenius gap, and non-degeneracy of `wilson4DTransferOp` -/

section Wilson4DPositivityAndGap

theorem bernoulli_one_sub {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∀ n : ℕ, 1 - (n : ℝ) * u ≤ (1 - u) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1u : 0 ≤ 1 - u := by linarith
    have h_step : 1 - ((n : ℝ) + 1) * u ≤ (1 - (n : ℝ) * u) * (1 - u) := by
      have hnn : 0 ≤ (n : ℝ) * u ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg u)
      nlinarith
    simpa [Nat.cast_add, Nat.cast_one] using (calc
      1 - ((n : ℝ) + 1) * u
          ≤ (1 - (n : ℝ) * u) * (1 - u) := h_step
      _ ≤ (1 - u) ^ n * (1 - u) := mul_le_mul_of_nonneg_right ih h1u
      _ = (1 - u) ^ (n + 1) := (pow_succ (1 - u) n).symm)

theorem one_add_pow_le_two {u : ℝ} (hu0 : 0 ≤ u) (n : ℕ) (hnu : (n : ℝ) * u ≤ 1 / 2) :
    (1 + u) ^ n ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hn_ge1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hu_le1 : u ≤ 1 := by
      have hn2_pos : 0 < 2 * (n : ℝ) := by positivity
      have h1 : u ≤ 1 / (2 * (n : ℝ)) := by
        rw [le_div_iff₀ hn2_pos]
        nlinarith
      have h2 : 1 / (2 * (n : ℝ)) ≤ 1 := by
        rw [div_le_one hn2_pos]
        linarith
      exact h1.trans h2
    have h_bern : (1 / 2 : ℝ) ≤ (1 - u) ^ n := by
      have hb := bernoulli_one_sub hu0 hu_le1 n
      linarith
    have h_prod_le : ((1 + u) * (1 - u)) ^ n ≤ 1 := by
      have h1 : 0 ≤ (1 + u) * (1 - u) := mul_nonneg (by linarith) (by linarith)
      have h2 : (1 + u) * (1 - u) ≤ 1 := by nlinarith [sq_nonneg u]
      exact pow_le_one₀ h1 h2
    rw [mul_pow] at h_prod_le
    have h_half : (1 + u) ^ n * (1 / 2 : ℝ) ≤ (1 + u) ^ n * (1 - u) ^ n :=
      mul_le_mul_of_nonneg_left h_bern (pow_nonneg (by linarith) n)
    linarith

theorem pow_sub_pow_eq (n : ℕ) (a b : ℝ) :
    a ^ n - b ^ n = (a - b) * ∑ k ∈ Finset.range n, a ^ k * b ^ (n - 1 - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h_shift : ∑ k ∈ Finset.range n, a ^ k * b ^ (n + 1 - 1 - k) =
        (∑ k ∈ Finset.range n, a ^ k * b ^ (n - 1 - k)) * b := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_lt : k < n := Finset.mem_range.mp hk
      have heq : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
      rw [heq, pow_succ]
      ring
    rw [h_shift]
    have h_last : n + 1 - 1 - n = 0 := by omega
    rw [h_last, pow_zero, mul_one, ← mul_assoc, ← ih]
    ring

theorem exp_approx_one_add_div {B y : ℝ} (hB : 0 ≤ B) (hy0 : 0 ≤ y) (hyB : y ≤ B)
    (n : ℕ) (hn1 : 1 ≤ (n : ℝ)) (hnB : B ≤ n) (hnB2 : 2 * B ^ 2 ≤ n) :
    |Real.exp y - (1 + y / (n : ℝ)) ^ n| ≤ 2 * B ^ 2 * Real.exp B / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by linarith
  let z : ℝ := y / (n : ℝ)
  let u : ℝ := z ^ 2
  have hz0 : 0 ≤ z := div_nonneg hy0 hn_pos.le
  have hz1 : z ≤ 1 := by rw [div_le_one hn_pos]; exact hyB.trans hnB
  have h_diff_z : |Real.exp z - (1 + z)| ≤ u := by
    have h1 := Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hz0]; exact hz1 : |z| ≤ 1)
    simpa [sub_sub, add_comm, u] using h1
  have ha_ge1 : 1 ≤ Real.exp z := Real.exp_le_exp.mpr hz0 |>.trans' (by simp)
  have hb_le_exp_u : 1 + z ≤ Real.exp z * (1 + u) := by
    have h1 : 1 + z ≤ Real.exp z + u := by linarith [(abs_le.mp h_diff_z).1]
    calc 1 + z ≤ Real.exp z + u := h1
      _ ≤ Real.exp z + Real.exp z * u := by
          gcongr; exact le_mul_of_one_le_left (sq_nonneg z) ha_ge1
      _ = Real.exp z * (1 + u) := by ring
  have hnu : (n : ℝ) * u ≤ 1 / 2 := by
    have hz_le : z ≤ B / (n : ℝ) := div_le_div_of_nonneg_right hyB hn_pos.le
    have hu_le : u ≤ B ^ 2 / (n : ℝ) ^ 2 := by
      dsimp [u]
      calc z ^ 2 ≤ (B / (n : ℝ)) ^ 2 := pow_le_pow_left₀ hz0 hz_le 2
        _ = B ^ 2 / (n : ℝ) ^ 2 := by ring
    calc (n : ℝ) * u ≤ (n : ℝ) * (B ^ 2 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hu_le hn_pos.le
      _ = B ^ 2 / (n : ℝ) := by field_simp [hn_pos.ne']
      _ ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 2)]
          linarith
  have h_one_add_u_pow : (1 + u) ^ n ≤ 2 := one_add_pow_le_two (sq_nonneg z) n hnu
  have hexp_y_eq : Real.exp y = (Real.exp z) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [z]
    field_simp [hn_pos.ne']
  have hb0 : 0 ≤ 1 + z := by linarith
  have h_sum_le : ∑ k ∈ Finset.range n, (Real.exp z) ^ k * (1 + z) ^ (n - 1 - k) ≤
      (n : ℝ) * (2 * Real.exp B) := by
    calc ∑ k ∈ Finset.range n, (Real.exp z) ^ k * (1 + z) ^ (n - 1 - k)
        ≤ ∑ _k ∈ Finset.range n, (2 * Real.exp B) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk_lt : k < n := Finset.mem_range.mp hk
            have hk_sum : k + (n - 1 - k) = n - 1 := by omega
            have hb_pow : (1 + z) ^ (n - 1 - k) ≤
                (Real.exp z) ^ (n - 1 - k) * (1 + u) ^ (n - 1 - k) := by
              rw [← mul_pow]
              exact pow_le_pow_left₀ hb0 hb_le_exp_u _
            have h_exp_n : (Real.exp z) ^ (n - 1) ≤ (Real.exp z) ^ n := by
              have hn_sub : n - 1 ≤ n := Nat.sub_le n 1
              exact pow_le_pow_right₀ ha_ge1 hn_sub
            have h_u_pow : (1 + u) ^ (n - 1 - k) ≤ (1 + u) ^ n := by
              exact pow_le_pow_right₀ (by linarith [sq_nonneg z]) (Nat.sub_le (n - 1) k |>.trans (Nat.sub_le n 1))
            calc (Real.exp z) ^ k * (1 + z) ^ (n - 1 - k)
                ≤ (Real.exp z) ^ k * ((Real.exp z) ^ (n - 1 - k) * (1 + u) ^ (n - 1 - k)) :=
                    mul_le_mul_of_nonneg_left hb_pow (pow_nonneg (Real.exp_pos _).le _)
              _ = (Real.exp z) ^ (k + (n - 1 - k)) * (1 + u) ^ (n - 1 - k) := by
                    rw [pow_add, mul_assoc]
              _ = (Real.exp z) ^ (n - 1) * (1 + u) ^ (n - 1 - k) := by rw [hk_sum]
              _ ≤ (Real.exp z) ^ n * (1 + u) ^ n :=
                    mul_le_mul h_exp_n h_u_pow (pow_nonneg (by linarith [sq_nonneg z]) _)
                      (pow_nonneg (Real.exp_pos _).le _)
              _ = Real.exp y * (1 + u) ^ n := by rw [hexp_y_eq]
              _ ≤ Real.exp B * 2 :=
                    mul_le_mul (Real.exp_le_exp.mpr hyB) h_one_add_u_pow
                      (pow_nonneg (by linarith [sq_nonneg z]) _) (Real.exp_pos _).le
              _ = 2 * Real.exp B := by ring
      _ = (n : ℝ) * (2 * Real.exp B) := by simp [Finset.sum_const, nsmul_eq_mul]
  have h_sum_nn : 0 ≤ ∑ k ∈ Finset.range n, (Real.exp z) ^ k * (1 + z) ^ (n - 1 - k) :=
    Finset.sum_nonneg fun _ _ =>
      mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (pow_nonneg hb0 _)
  have hu_le_B : u ≤ B ^ 2 / (n : ℝ) ^ 2 := by
    dsimp [u]
    calc z ^ 2 ≤ (B / (n : ℝ)) ^ 2 := pow_le_pow_left₀ hz0 (div_le_div_of_nonneg_right hyB hn_pos.le) 2
      _ = B ^ 2 / (n : ℝ) ^ 2 := by ring
  rw [hexp_y_eq, pow_sub_pow_eq n (Real.exp z) (1 + z), abs_mul, abs_of_nonneg h_sum_nn]
  calc |Real.exp z - (1 + z)| * ∑ k ∈ Finset.range n, (Real.exp z) ^ k * (1 + z) ^ (n - 1 - k)
      ≤ (B ^ 2 / (n : ℝ) ^ 2) * ((n : ℝ) * (2 * Real.exp B)) :=
          mul_le_mul (h_diff_z.trans hu_le_B) h_sum_le h_sum_nn (by positivity)
    _ = 2 * B ^ 2 * Real.exp B / (n : ℝ) := by field_simp [hn_pos.ne']

/-- Finite non-negative separable kernel representation on a topological space `X`. -/
def evalSepList {X : Type*} (l : List (ℝ × (X → ℝ))) (x y : X) : ℝ :=
  (l.map fun p => p.1 * p.2 x * p.2 y).sum

def ValidSepList {X : Type*} [TopologicalSpace X] (l : List (ℝ × (X → ℝ))) : Prop :=
  ∀ p ∈ l, 0 ≤ p.1 ∧ Continuous p.2

theorem evalSepList_nonneg {X : Type*} [TopologicalSpace X]
    {l : List (ℝ × (X → ℝ))} (hl : ValidSepList l) (x : X) :
    0 ≤ evalSepList l x x := by
  induction l with
  | nil => simp [evalSepList]
  | cons p l ih =>
    have hp := hl p (by simp)
    have hl' : ValidSepList l := fun q hq => hl q (by simp [hq])
    simp only [evalSepList, List.map_cons, List.sum_cons]
    have hp_nn : 0 ≤ p.1 * p.2 x * p.2 x := by
      rw [mul_assoc]; exact mul_nonneg hp.1 (mul_self_nonneg _)
    exact add_nonneg hp_nn (ih hl')

theorem continuous_evalSepList {X : Type*} [TopologicalSpace X]
    {l : List (ℝ × (X → ℝ))} (hl : ValidSepList l) :
    Continuous (fun q : X × X => evalSepList l q.1 q.2) := by
  induction l with
  | nil => simp [evalSepList, continuous_const]
  | cons p l ih =>
    have hp := hl p (by simp)
    have hl' : ValidSepList l := fun q hq => hl q (by simp [hq])
    simp only [evalSepList, List.map_cons, List.sum_cons]
    exact ((continuous_const.mul (hp.2.comp continuous_fst)).mul
      (hp.2.comp continuous_snd)).add (ih hl')

theorem evalSepList_append {X : Type*} (l₁ l₂ : List (ℝ × (X → ℝ))) (x y : X) :
    evalSepList (l₁ ++ l₂) x y = evalSepList l₁ x y + evalSepList l₂ x y := by
  simp [evalSepList, List.map_append, List.sum_append]

theorem validSepList_append {X : Type*} [TopologicalSpace X]
    {l₁ l₂ : List (ℝ × (X → ℝ))} (h₁ : ValidSepList l₁) (h₂ : ValidSepList l₂) :
    ValidSepList (l₁ ++ l₂) := by
  intro p hp
  rcases List.mem_append.mp hp with hp1 | hp2
  · exact h₁ p hp1
  · exact h₂ p hp2

def mulSepList {X : Type*} (l₁ l₂ : List (ℝ × (X → ℝ))) : List (ℝ × (X → ℝ)) :=
  l₁.flatMap fun p => l₂.map fun q => (p.1 * q.1, fun x => p.2 x * q.2 x)

theorem evalSepList_mul_singleton {X : Type*}
    (p : ℝ × (X → ℝ)) (l₂ : List (ℝ × (X → ℝ))) (x y : X) :
    evalSepList (l₂.map fun q => (p.1 * q.1, fun z => p.2 z * q.2 z)) x y =
      (p.1 * p.2 x * p.2 y) * evalSepList l₂ x y := by
  induction l₂ with
  | nil => simp [evalSepList]
  | cons q l₂ ih =>
    simp only [evalSepList, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

theorem evalSepList_mul {X : Type*} (l₁ l₂ : List (ℝ × (X → ℝ))) (x y : X) :
    evalSepList (mulSepList l₁ l₂) x y = evalSepList l₁ x y * evalSepList l₂ x y := by
  induction l₁ with
  | nil => simp [mulSepList, evalSepList]
  | cons p l₁ ih =>
    have h_flat : mulSepList (p :: l₁) l₂ =
        (l₂.map fun q => (p.1 * q.1, fun z => p.2 z * q.2 z)) ++ mulSepList l₁ l₂ := rfl
    rw [h_flat, evalSepList_append, evalSepList_mul_singleton, ih]
    simp only [evalSepList, List.map_cons, List.sum_cons]
    ring

theorem validSepList_mul {X : Type*} [TopologicalSpace X]
    {l₁ l₂ : List (ℝ × (X → ℝ))} (h₁ : ValidSepList l₁) (h₂ : ValidSepList l₂) :
    ValidSepList (mulSepList l₁ l₂) := by
  intro r hr
  dsimp [mulSepList] at hr
  rw [List.mem_flatMap] at hr
  rcases hr with ⟨p, hp, hr'⟩
  rw [List.mem_map] at hr'
  rcases hr' with ⟨q, hq, rfl⟩
  have hpv := h₁ p hp
  have hqv := h₂ q hq
  exact ⟨mul_nonneg hpv.1 hqv.1, hpv.2.mul hqv.2⟩

def scaleSepList {X : Type*} (c : ℝ) (l : List (ℝ × (X → ℝ))) : List (ℝ × (X → ℝ)) :=
  l.map fun p => (c * p.1, p.2)

theorem evalSepList_scale {X : Type*} (c : ℝ) (l : List (ℝ × (X → ℝ))) (x y : X) :
    evalSepList (scaleSepList c l) x y = c * evalSepList l x y := by
  induction l with
  | nil => simp [scaleSepList, evalSepList]
  | cons p l ih =>
    simp only [scaleSepList, evalSepList, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

theorem validSepList_scale {X : Type*} [TopologicalSpace X]
    {c : ℝ} (hc : 0 ≤ c) {l : List (ℝ × (X → ℝ))} (hl : ValidSepList l) :
    ValidSepList (scaleSepList c l) := by
  intro r hr
  rw [scaleSepList, List.mem_map] at hr
  rcases hr with ⟨p, hp, rfl⟩
  exact ⟨mul_nonneg hc (hl p hp).1, (hl p hp).2⟩

def powSepList {X : Type*} (l : List (ℝ × (X → ℝ))) : ℕ → List (ℝ × (X → ℝ))
  | 0 => [(1, fun _ => 1)]
  | k + 1 => mulSepList l (powSepList l k)

theorem evalSepList_pow {X : Type*} (l : List (ℝ × (X → ℝ))) (k : ℕ) (x y : X) :
    evalSepList (powSepList l k) x y = (evalSepList l x y) ^ k := by
  induction k with
  | zero => simp [powSepList, evalSepList]
  | succ k ih =>
    rw [powSepList, evalSepList_mul, ih, pow_succ']

theorem validSepList_pow {X : Type*} [TopologicalSpace X]
    {l : List (ℝ × (X → ℝ))} (hl : ValidSepList l) (k : ℕ) :
    ValidSepList (powSepList l k) := by
  induction k with
  | zero =>
    intro p hp
    simp only [powSepList, List.mem_singleton] at hp
    subst hp
    exact ⟨zero_le_one, continuous_const⟩
  | succ k ih => exact validSepList_mul hl ih

def prodSepList {X : Type*} : List (List (ℝ × (X → ℝ))) → List (ℝ × (X → ℝ))
  | [] => [(1, fun _ => 1)]
  | l :: ls => mulSepList l (prodSepList ls)

theorem evalSepList_prod {X : Type*} (ls : List (List (ℝ × (X → ℝ)))) (x y : X) :
    evalSepList (prodSepList ls) x y = (ls.map fun l => evalSepList l x y).prod := by
  induction ls with
  | nil => simp [prodSepList, evalSepList]
  | cons l ls ih =>
    simp only [prodSepList, List.map_cons, List.prod_cons, evalSepList_mul, ih]

theorem validSepList_prod {X : Type*} [TopologicalSpace X]
    {ls : List (List (ℝ × (X → ℝ)))} (hls : ∀ l ∈ ls, ValidSepList l) :
    ValidSepList (prodSepList ls) := by
  induction ls with
  | nil =>
    intro p hp
    simp only [prodSepList, List.mem_singleton] at hp
    subst hp
    exact ⟨zero_le_one, continuous_const⟩
  | cons l ls ih =>
    exact validSepList_mul (hls l (by simp)) (ih fun l' hl' => hls l' (by simp [hl']))

/--
Gauge-averaged `SepKernelList` over `gaugeGrpHaarMeasure L N`:
for any left-gauge-invariant `l`, the gauge-averaged kernel `∫ g, evalSepList l U (gaugeAct g U')`
equals `evalSepList (gaugeAvgSepList L N l) U U'`.
-/
noncomputable def gaugeAvgSepList (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (l : List (ℝ × (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ))) :
    List (ℝ × (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)) :=
  l.map fun p => (p.1, fun U => ∫ h, p.2 (gaugeAct h U) ∂(gaugeGrpHaarMeasure L N))

theorem validSepList_gaugeAvg (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {l : List (ℝ × (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ))}
    (hl : ValidSepList l) :
    ValidSepList (gaugeAvgSepList L N l) := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let G_L := GaugeField (cubicTorus3 L) G
  let μ_g := gaugeGrpHaarMeasure L N
  haveI := gaugeGrpHaarMeasure_prob L N
  intro r hr
  rw [gaugeAvgSepList, List.mem_map] at hr
  rcases hr with ⟨p, hp, rfl⟩
  have hpc := hl p hp
  refine ⟨hpc.1, ?_⟩
  obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_abs.comp hpc.2)).bddAbove
  let C : ℝ := max M 0
  have h_act_cont : Continuous (fun q : G_L × GaugeGrp3 L N => gaugeAct q.2 q.1) := by
    change Continuous (fun q : G_L × GaugeGrp3 L N => fun e =>
      q.2 ((cubicTorus3 L).src e) * q.1 e * (q.2 ((cubicTorus3 L).dst e))⁻¹)
    rw [continuous_pi_iff]
    intro e
    have h1 : Continuous (fun q : G_L × GaugeGrp3 L N => q.2 ((cubicTorus3 L).src e)) :=
      (continuous_apply ((cubicTorus3 L).src e)).comp continuous_snd
    have h2 : Continuous (fun q : G_L × GaugeGrp3 L N => q.1 e) :=
      (continuous_apply e).comp continuous_fst
    have h3 : Continuous (fun q : G_L × GaugeGrp3 L N => (q.2 ((cubicTorus3 L).dst e))⁻¹) :=
      continuous_inv.comp ((continuous_apply ((cubicTorus3 L).dst e)).comp continuous_snd)
    exact (h1.mul h2).mul h3
  refine MeasureTheory.continuous_of_dominated (bound := fun _ : GaugeGrp3 L N => C) ?_ ?_
    (MeasureTheory.integrable_const C) ?_
  · intro U
    exact (hpc.2.comp (h_act_cont.comp (continuous_const.prodMk continuous_id))).stronglyMeasurable.aestronglyMeasurable
  · intro U
    refine Filter.Eventually.of_forall fun h => ?_
    rw [Real.norm_eq_abs]
    exact le_max_of_le_left (hM ⟨gaugeAct h U, Set.mem_univ _, rfl⟩)
  · refine Filter.Eventually.of_forall fun h => ?_
    have h_map : Continuous (fun U : G_L => (U, h)) := continuous_id.prodMk continuous_const
    have h_act : Continuous (fun U : G_L => gaugeAct h U) := by
      simpa using h_act_cont.comp h_map
    exact hpc.2.comp h_act

theorem evalSepList_gaugeAvg (L N : ℕ) [NeZero L]
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {l : List (ℝ × (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ))}
    (hl : ValidSepList l)
    (h_inv : ∀ h U U', evalSepList l (gaugeAct h U) (gaugeAct h U') = evalSepList l U U')
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    evalSepList (gaugeAvgSepList L N l) U U' =
      ∫ g, evalSepList l U (gaugeAct g U') ∂(gaugeGrpHaarMeasure L N) := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let G_L := GaugeField (cubicTorus3 L) G
  let μ_g := gaugeGrpHaarMeasure L N
  haveI := gaugeGrpHaarMeasure_prob L N
  have h_act_cont : Continuous (fun q : G_L × GaugeGrp3 L N => gaugeAct q.2 q.1) := by
    change Continuous (fun q : G_L × GaugeGrp3 L N => fun e =>
      q.2 ((cubicTorus3 L).src e) * q.1 e * (q.2 ((cubicTorus3 L).dst e))⁻¹)
    rw [continuous_pi_iff]
    intro e
    exact (((continuous_apply ((cubicTorus3 L).src e)).comp continuous_snd).mul
      ((continuous_apply e).comp continuous_fst)).mul
      (continuous_inv.comp ((continuous_apply ((cubicTorus3 L).dst e)).comp continuous_snd))
  have h_lhs_prod : ∀ l' : List (ℝ × (G_L → ℝ)),
      (∀ p ∈ l', 0 ≤ p.1 ∧ Continuous p.2) →
      evalSepList (gaugeAvgSepList L N l') U U' =
        ∫ h₁ : GaugeGrp3 L N, ∫ h₂ : GaugeGrp3 L N,
          evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U') ∂μ_g ∂μ_g := by
    intro l' hl'
    induction l' with
    | nil => simp [gaugeAvgSepList, evalSepList]
    | cons p l' ih =>
      have hp := hl' p (by simp)
      have hl'' : ∀ q ∈ l', 0 ≤ q.1 ∧ Continuous q.2 := fun q hq => hl' q (by simp [hq])
      have hi_p : MeasureTheory.Integrable (fun h : GaugeGrp3 L N => p.2 (gaugeAct h U)) μ_g := by
        obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_abs.comp hp.2)).bddAbove
        refine (MeasureTheory.integrable_const (max M 0)).mono'
          (hp.2.comp (h_act_cont.comp (continuous_const.prodMk continuous_id))).stronglyMeasurable.aestronglyMeasurable
          (Filter.Eventually.of_forall fun h => by
            rw [Real.norm_eq_abs]; exact le_max_of_le_left (hM ⟨gaugeAct h U, Set.mem_univ _, rfl⟩))
      have hi_p' : MeasureTheory.Integrable (fun h : GaugeGrp3 L N => p.2 (gaugeAct h U')) μ_g := by
        obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_abs.comp hp.2)).bddAbove
        refine (MeasureTheory.integrable_const (max M 0)).mono'
          (hp.2.comp (h_act_cont.comp (continuous_const.prodMk continuous_id))).stronglyMeasurable.aestronglyMeasurable
          (Filter.Eventually.of_forall fun h => by
            rw [Real.norm_eq_abs]; exact le_max_of_le_left (hM ⟨gaugeAct h U', Set.mem_univ _, rfl⟩))
      have h_int_l'_inner : ∀ h₁ : GaugeGrp3 L N, MeasureTheory.Integrable
          (fun h₂ : GaugeGrp3 L N => evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U')) μ_g := by
        intro h₁
        have hc : Continuous (fun h₂ : GaugeGrp3 L N =>
            evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U')) :=
          (continuous_evalSepList hl'').comp
            (continuous_const.prodMk (h_act_cont.comp (continuous_const.prodMk continuous_id)))
        obtain ⟨M, hM⟩ := (isCompact_univ.image
          (continuous_abs.comp (continuous_evalSepList hl''))).bddAbove
        refine (MeasureTheory.integrable_const (max M 0)).mono' hc.stronglyMeasurable.aestronglyMeasurable
          (Filter.Eventually.of_forall fun h₂ => by
            rw [Real.norm_eq_abs]
            exact le_max_of_le_left (hM ⟨(gaugeAct h₁ U, gaugeAct h₂ U'), Set.mem_univ _, rfl⟩))
      have h_int_l'_outer : MeasureTheory.Integrable
          (fun h₁ : GaugeGrp3 L N =>
            ∫ h₂ : GaugeGrp3 L N, evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U') ∂μ_g) μ_g := by
        obtain ⟨M, hM⟩ := (isCompact_univ.image
          (continuous_abs.comp (continuous_evalSepList hl''))).bddAbove
        have hc_out : Continuous (fun h₁ : GaugeGrp3 L N =>
            ∫ h₂ : GaugeGrp3 L N, evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U') ∂μ_g) := by
          refine MeasureTheory.continuous_of_dominated (bound := fun _ => max M 0) ?_ ?_
            (MeasureTheory.integrable_const _) ?_
          · intro h₁
            exact ((continuous_evalSepList hl'').comp
              (continuous_const.prodMk (h_act_cont.comp (continuous_const.prodMk continuous_id)))).stronglyMeasurable.aestronglyMeasurable
          · intro h₁
            refine Filter.Eventually.of_forall fun h₂ => ?_
            rw [Real.norm_eq_abs]
            exact le_max_of_le_left (hM ⟨(gaugeAct h₁ U, gaugeAct h₂ U'), Set.mem_univ _, rfl⟩)
          · refine Filter.Eventually.of_forall fun h₂ => ?_
            exact (continuous_evalSepList hl'').comp
              ((h_act_cont.comp (continuous_const.prodMk continuous_id)).prodMk continuous_const)
        refine (MeasureTheory.integrable_const (max M 0)).mono' hc_out.stronglyMeasurable.aestronglyMeasurable
          (Filter.Eventually.of_forall fun h₁ => ?_)
        rw [Real.norm_eq_abs]
        calc |∫ h₂, evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U') ∂μ_g|
            ≤ ∫ h₂, |evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U')| ∂μ_g :=
                MeasureTheory.abs_integral_le_integral_abs
          _ ≤ ∫ _h₂, max M 0 ∂μ_g :=
                MeasureTheory.integral_mono (h_int_l'_inner h₁).abs (MeasureTheory.integrable_const _)
                  (fun h₂ => le_max_of_le_left
                    (hM ⟨(gaugeAct h₁ U, gaugeAct h₂ U'), Set.mem_univ _, rfl⟩))
          _ = max M 0 := by simp [Measure.real, MeasureTheory.measure_univ]
      have h_in_p : ∀ h₁ : GaugeGrp3 L N,
          ∫ h₂ : GaugeGrp3 L N, p.1 * p.2 (gaugeAct h₁ U) * p.2 (gaugeAct h₂ U') ∂μ_g =
            (p.1 * p.2 (gaugeAct h₁ U)) * ∫ h₂ : GaugeGrp3 L N, p.2 (gaugeAct h₂ U') ∂μ_g :=
        fun h₁ => MeasureTheory.integral_const_mul (p.1 * p.2 (gaugeAct h₁ U))
          (fun h₂ => p.2 (gaugeAct h₂ U'))
      have h_term :
          p.1 * (∫ h₁ : GaugeGrp3 L N, p.2 (gaugeAct h₁ U) ∂μ_g) *
              (∫ h₂ : GaugeGrp3 L N, p.2 (gaugeAct h₂ U') ∂μ_g) =
            ∫ h₁ : GaugeGrp3 L N, ∫ h₂ : GaugeGrp3 L N,
              p.1 * p.2 (gaugeAct h₁ U) * p.2 (gaugeAct h₂ U') ∂μ_g ∂μ_g := by
        symm
        simp_rw [h_in_p]
        rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
      have h_int_p_inner : ∀ h₁ : GaugeGrp3 L N, MeasureTheory.Integrable
          (fun h₂ : GaugeGrp3 L N => p.1 * p.2 (gaugeAct h₁ U) * p.2 (gaugeAct h₂ U')) μ_g :=
        fun h₁ => hi_p'.const_mul (p.1 * p.2 (gaugeAct h₁ U))
      have h_int_p_outer : MeasureTheory.Integrable
          (fun h₁ : GaugeGrp3 L N =>
            ∫ h₂ : GaugeGrp3 L N, p.1 * p.2 (gaugeAct h₁ U) * p.2 (gaugeAct h₂ U') ∂μ_g) μ_g := by
        simp_rw [h_in_p]
        exact (hi_p.const_mul p.1).mul_const _
      change p.1 * (∫ h₁, p.2 (gaugeAct h₁ U) ∂μ_g) * (∫ h₂, p.2 (gaugeAct h₂ U') ∂μ_g) +
          evalSepList (gaugeAvgSepList L N l') U U' =
        ∫ h₁ : GaugeGrp3 L N, ∫ h₂ : GaugeGrp3 L N,
          p.1 * p.2 (gaugeAct h₁ U) * p.2 (gaugeAct h₂ U') +
            evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U') ∂μ_g ∂μ_g
      rw [h_term, ih hl'']
      calc (∫ h₁ : GaugeGrp3 L N, ∫ h₂ : GaugeGrp3 L N,
              p.1 * p.2 (gaugeAct h₁ U) * p.2 (gaugeAct h₂ U') ∂μ_g ∂μ_g) +
            (∫ h₁ : GaugeGrp3 L N, ∫ h₂ : GaugeGrp3 L N,
              evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U') ∂μ_g ∂μ_g)
          = ∫ h₁ : GaugeGrp3 L N,
              ((∫ h₂ : GaugeGrp3 L N, p.1 * p.2 (gaugeAct h₁ U) * p.2 (gaugeAct h₂ U') ∂μ_g) +
               (∫ h₂ : GaugeGrp3 L N, evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U') ∂μ_g)) ∂μ_g :=
              (MeasureTheory.integral_add h_int_p_outer h_int_l'_outer).symm
        _ = ∫ h₁ : GaugeGrp3 L N, ∫ h₂ : GaugeGrp3 L N,
              p.1 * p.2 (gaugeAct h₁ U) * p.2 (gaugeAct h₂ U') +
                evalSepList l' (gaugeAct h₁ U) (gaugeAct h₂ U') ∂μ_g ∂μ_g := by
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h₁ => ?_)
              exact (MeasureTheory.integral_add (h_int_p_inner h₁) (h_int_l'_inner h₁)).symm
  rw [h_lhs_prod l hl]
  have h_const_h₁ : ∀ h₁ : GaugeGrp3 L N,
      (∫ h₂ : GaugeGrp3 L N, evalSepList l (gaugeAct h₁ U) (gaugeAct h₂ U') ∂μ_g) =
        ∫ g : GaugeGrp3 L N, evalSepList l U (gaugeAct g U') ∂μ_g := by
    intro h₁
    let eqv : GaugeGrp3 L N ≃ᵐ GaugeGrp3 L N :=
      { toFun := fun h₂ x => (h₁ x)⁻¹ * h₂ x
        invFun := fun g x => h₁ x * g x
        left_inv := fun h₂ => by funext x; group
        right_inv := fun g => by funext x; group
        measurable_toFun := measurable_pi_iff.mpr fun x =>
          (continuous_mul_left _).measurable.comp (measurable_pi_apply x)
        measurable_invFun := measurable_pi_iff.mpr fun x =>
          (continuous_mul_left _).measurable.comp (measurable_pi_apply x) }
    have hmp : MeasureTheory.MeasurePreserving eqv μ_g μ_g := by
      refine ⟨eqv.measurable, ?_⟩
      simpa [eqv] using gaugeGrpHaarMeasure_mul_left_right L N (fun x => (h₁ x)⁻¹) (fun _ => 1)
    rw [← hmp.integral_comp' (fun g => evalSepList l U (gaugeAct g U'))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h₂ => ?_)
    have h_act_eq : gaugeAct h₂ U' = gaugeAct h₁ (gaugeAct (eqv h₂) U') := by
      funext e
      simp only [gaugeAct]
      change h₂ ((cubicTorus3 L).src e) * U' e * (h₂ ((cubicTorus3 L).dst e))⁻¹ =
        h₁ ((cubicTorus3 L).src e) *
          (((h₁ ((cubicTorus3 L).src e))⁻¹ * h₂ ((cubicTorus3 L).src e)) * U' e *
            (((h₁ ((cubicTorus3 L).dst e))⁻¹ * h₂ ((cubicTorus3 L).dst e))⁻¹)) *
          (h₁ ((cubicTorus3 L).dst e))⁻¹
      group
    dsimp only
    rw [h_act_eq, h_inv h₁ U (gaugeAct (eqv h₂) U')]
  simp_rw [h_const_h₁]
  simp [Measure.real, MeasureTheory.measure_univ]
  rfl

theorem sepList_wilson_inner_nonneg (L N : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (l : List (ℝ × (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)))
    (hl : ValidSepList l)
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (∫ U, starRingEnd ℂ (ψ U) *
      (∫ U', ((wilsonKernel β (cubicPlaquettes L) (evalSepList l) U U' : ℝ) : ℂ) * ψ U'
        ∂(latticeHaarMeasure L N)) ∂(latticeHaarMeasure L N)).re := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let G_L := GaugeField (cubicTorus3 L) G
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  let w : G_L → ℝ := cubicWilsonWeight L N β
  have hw_cont : Continuous w :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_cubicWilsonAction L N β))
  let l' := l.map fun p => (p.1, fun U => w U * p.2 U)
  have hl' : ValidSepList l' := by
    intro q hq
    rw [List.mem_map] at hq
    rcases hq with ⟨p, hp, rfl⟩
    exact ⟨(hl p hp).1, hw_cont.mul (hl p hp).2⟩
  have hK_eq : ∀ U U', wilsonKernel β (cubicPlaquettes L) (evalSepList l) U U' =
      evalSepList l' U U' := by
    intro U U'
    have hw_mul : Real.exp (-(1 / 2 : ℝ) *
        (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U')) =
        w U * w U' := by
      dsimp [w, cubicWilsonWeight]
      rw [← Real.exp_add]
      congr 1; ring
    unfold wilsonKernel
    rw [hw_mul, mul_comm (w U * w U')]
    clear hw_mul
    induction l with
    | nil => simp [l', evalSepList]
    | cons p l ih =>
      have hp := hl p (by simp)
      have hlp : ValidSepList l := fun q hq => hl q (by simp [hq])
      have hlpm : ValidSepList (l.map fun p => (p.1, fun U => w U * p.2 U)) := by
        intro q hq
        rw [List.mem_map] at hq
        rcases hq with ⟨p, hp', rfl⟩
        exact ⟨(hlp p hp').1, hw_cont.mul (hlp p hp').2⟩
      specialize ih hlp hlpm
      simp only [l', List.map_cons, evalSepList, List.sum_cons] at ih ⊢
      rw [← ih]
      ring
  simp_rw [hK_eq]
  have h_pos_list : ∀ (ls : List (ℝ × (G_L → ℝ))), ValidSepList ls →
      0 ≤ (∫ U, starRingEnd ℂ (ψ U) *
        (∫ U', ((evalSepList ls U U' : ℝ) : ℂ) * ψ U' ∂μ) ∂μ).re := by
    intro ls hls
    induction ls with
    | nil => simp [evalSepList]
    | cons p ls ih =>
      have hp := hls p (by simp)
      have hls' : ValidSepList ls := fun q hq => hls q (by simp [hq])
      obtain ⟨M_p, hM_p⟩ := (isCompact_univ.image (continuous_abs.comp hp.2)).bddAbove
      let C_p : ℝ := max M_p 0
      have h_int_p : MeasureTheory.Integrable (fun U' => ((p.2 U' : ℝ) : ℂ) * ψ U') μ := by
        refine (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul C_p).mono' ?_ ?_
        · exact (Complex.continuous_ofReal.comp hp.2).stronglyMeasurable.aestronglyMeasurable.mul
            (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun U' => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (le_max_of_le_left (hM_p ⟨U', Set.mem_univ _, rfl⟩))
            (norm_nonneg _)
      obtain ⟨M_s, hM_s⟩ := (isCompact_univ.image
        (continuous_abs.comp (continuous_evalSepList hls'))).bddAbove
      let C_s : ℝ := max M_s 0
      have h_int_s : ∀ U, MeasureTheory.Integrable
          (fun U' => ((evalSepList ls U U' : ℝ) : ℂ) * ψ U') μ := by
        intro U
        refine (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul C_s).mono' ?_ ?_
        · exact (Complex.continuous_ofReal.comp ((continuous_evalSepList hls').comp
            (continuous_const.prodMk continuous_id))).stronglyMeasurable.aestronglyMeasurable.mul
            (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun U' => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (le_max_of_le_left (hM_s ⟨(U, U'), Set.mem_univ _, rfl⟩))
            (norm_nonneg _)
      let I_p : ℂ := ∫ U', ((p.2 U' : ℝ) : ℂ) * ψ U' ∂μ
      have h_split_inner : ∀ U,
          (∫ U', ((evalSepList (p :: ls) U U' : ℝ) : ℂ) * ψ U' ∂μ) =
            ((p.1 : ℂ) * ((p.2 U : ℝ) : ℂ) * I_p) +
              (∫ U', ((evalSepList ls U U' : ℝ) : ℂ) * ψ U' ∂μ) := by
        intro U
        have h_eq : (fun U' => ((evalSepList (p :: ls) U U' : ℝ) : ℂ) * ψ U') =
            fun U' => ((p.1 : ℂ) * ((p.2 U : ℝ) : ℂ)) * (((p.2 U' : ℝ) : ℂ) * ψ U') +
              ((evalSepList ls U U' : ℝ) : ℂ) * ψ U' := by
          funext U'
          simp only [evalSepList, List.map_cons, List.sum_cons, Complex.ofReal_add,
            Complex.ofReal_mul]
          ring
        rw [h_eq, MeasureTheory.integral_add (h_int_p.const_mul _) (h_int_s U),
          MeasureTheory.integral_const_mul]
      have h_outer_p : MeasureTheory.Integrable
          (fun U => starRingEnd ℂ (ψ U) * ((p.1 : ℂ) * ((p.2 U : ℝ) : ℂ) * I_p)) μ := by
        have h_eq : (fun U => starRingEnd ℂ (ψ U) * ((p.1 : ℂ) * ((p.2 U : ℝ) : ℂ) * I_p)) =
            fun U => ((p.1 : ℂ) * I_p) * starRingEnd ℂ (((p.2 U : ℝ) : ℂ) * ψ U) := by
          funext U; rw [map_mul, Complex.conj_ofReal]; ring
        rw [h_eq]
        have h_int_p_conj : MeasureTheory.Integrable
            (fun U => starRingEnd ℂ (((p.2 U : ℝ) : ℂ) * ψ U)) μ := by
          refine ⟨?_, ?_⟩
          · exact continuous_star.comp_aestronglyMeasurable h_int_p.1
          · exact h_int_p.2.congr' (Filter.Eventually.of_forall fun u => by simp)
        exact h_int_p_conj.const_mul ((p.1 : ℂ) * I_p)
      have h_outer_s : MeasureTheory.Integrable
          (fun U => starRingEnd ℂ (ψ U) *
            ∫ U', ((evalSepList ls U U' : ℝ) : ℂ) * ψ U' ∂μ) μ := by
        have h_cont_s : Continuous
            (fun U => ∫ U', ((evalSepList ls U U' : ℝ) : ℂ) * ψ U' ∂μ) := by
          refine MeasureTheory.continuous_of_dominated
            (bound := fun U' => C_s * ‖ψ U'‖) ?_ ?_
            (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul C_s) ?_
          · intro U; exact (h_int_s U).aestronglyMeasurable
          · intro U
            refine Filter.Eventually.of_forall fun U' => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right
              (le_max_of_le_left (hM_s ⟨(U, U'), Set.mem_univ _, rfl⟩)) (norm_nonneg _)
          · refine Filter.Eventually.of_forall fun U' => ?_
            exact (Complex.continuous_ofReal.comp ((continuous_evalSepList hls').comp
              (continuous_id.prodMk continuous_const))).mul continuous_const
        have h_bd_s : ∀ U, ‖∫ U', ((evalSepList ls U U' : ℝ) : ℂ) * ψ U' ∂μ‖ ≤ C_s * ‖ψ‖ := by
          intro U
          calc ‖∫ U', ((evalSepList ls U U' : ℝ) : ℂ) * ψ U' ∂μ‖
              ≤ ∫ U', ‖((evalSepList ls U U' : ℝ) : ℂ) * ψ U'‖ ∂μ :=
                  MeasureTheory.norm_integral_le_integral_norm _
            _ ≤ ∫ U', C_s * ‖ψ U'‖ ∂μ := by
                  refine MeasureTheory.integral_mono (h_int_s U).norm
                    (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul C_s)
                    fun U' => ?_
                  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                  exact mul_le_mul_of_nonneg_right
                    (le_max_of_le_left (hM_s ⟨(U, U'), Set.mem_univ _, rfl⟩)) (norm_nonneg _)
            _ = C_s * ∫ U', ‖ψ U'‖ ∂μ := MeasureTheory.integral_const_mul C_s _
            _ ≤ C_s * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) (le_max_right M_s 0)
        refine (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul
          (C_s * ‖ψ‖)).mono' ?_ ?_
        · exact (continuous_star.comp_aestronglyMeasurable
            (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable).mul
            h_cont_s.stronglyMeasurable.aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun U => ?_
          rw [norm_mul, Complex.norm_conj]
          exact (mul_le_mul_of_nonneg_left (h_bd_s U) (norm_nonneg _)).trans_eq
            (mul_comm _ (C_s * ‖ψ‖))
      have h_term1 : (∫ U, starRingEnd ℂ (ψ U) * ((p.1 : ℂ) * ((p.2 U : ℝ) : ℂ) * I_p) ∂μ).re =
          p.1 * ‖I_p‖ ^ 2 := by
        have h_eq : (fun U => starRingEnd ℂ (ψ U) * ((p.1 : ℂ) * ((p.2 U : ℝ) : ℂ) * I_p)) =
            fun U => ((p.1 : ℂ) * I_p) * starRingEnd ℂ (((p.2 U : ℝ) : ℂ) * ψ U) := by
          funext U; rw [map_mul, Complex.conj_ofReal]; ring
        rw [h_eq, MeasureTheory.integral_const_mul, integral_conj]
        change (((p.1 : ℂ) * I_p) * starRingEnd ℂ I_p).re = p.1 * ‖I_p‖ ^ 2
        have hmul : ((p.1 : ℂ) * I_p) * starRingEnd ℂ I_p =
            (((p.1 * ‖I_p‖ ^ 2 : ℝ) : ℂ)) := by
          rw [mul_assoc, mul_comm I_p, Complex.conj_mul', ← Complex.ofReal_pow,
            ← Complex.ofReal_mul]
        rw [hmul, Complex.ofReal_re]
      simp_rw [h_split_inner, mul_add]
      rw [MeasureTheory.integral_add h_outer_p h_outer_s, Complex.add_re, h_term1]
      exact add_nonneg (mul_nonneg hp.1 (sq_nonneg _)) (ih hls')
  exact h_pos_list l' hl'

noncomputable def suEntrySepList (L N : ℕ) [NeZero L]
    (e : (cubicTorus3 L).Link) (β : ℝ) :
    List (ℝ × (GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)) :=
  [(β, fun _ => 1)] ++
  ((Finset.univ : Finset (Fin N × Fin N)).toList.flatMap fun ij =>
    [ (β / (N : ℝ), fun U => ((U e : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2).re),
      (β / (N : ℝ), fun U => ((U e : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2).im) ])

theorem validSepList_suEntry (L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (e : (cubicTorus3 L).Link) (β : ℝ) (hβ : 0 ≤ β) :
    ValidSepList (suEntrySepList L N e β) := by
  intro p hp
  rw [suEntrySepList, List.mem_append] at hp
  rcases hp with hp | hp
  · simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨hβ, continuous_const⟩
  · rw [List.mem_flatMap] at hp
    rcases hp with ⟨ij, _, hp'⟩
    have h_eval : Continuous (fun V : GaugeField (cubicTorus3 L)
        (Matrix.specialUnitaryGroup (Fin N) ℂ) => V e) := continuous_cubicField_eval L N e
    have h_val : Continuous (fun A : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (A : Matrix (Fin N) (Fin N) ℂ)) := continuous_subtype_val
    have h_row : Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => A ij.1) := continuous_apply ij.1
    have h_entry : Continuous (fun v : Fin N → ℂ => v ij.2) := continuous_apply ij.2
    have h_ent : Continuous (fun U : GaugeField (cubicTorus3 L)
        (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        ((U e : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)) :=
      h_entry.comp (h_row.comp (h_val.comp h_eval))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact ⟨by positivity, Complex.continuous_re.comp h_ent⟩
    · exact ⟨by positivity, Complex.continuous_im.comp h_ent⟩

theorem evalSepList_suEntry (L N : ℕ) [NeZero L]
    (e : (cubicTorus3 L).Link) (β : ℝ)
    (U U' : GaugeField (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    evalSepList (suEntrySepList L N e β) U U' =
      β * (1 + (1 / (N : ℝ)) *
        (Matrix.trace (((U e * (U' e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re) := by
  let A := (U e : Matrix (Fin N) (Fin N) ℂ)
  let B := (U' e : Matrix (Fin N) (Fin N) ℂ)
  have htr_eq : (Matrix.trace (((U e * (U' e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ))).re =
      ∑ ij : Fin N × Fin N, ((A ij.1 ij.2).re * (B ij.1 ij.2).re +
        (A ij.1 ij.2).im * (B ij.1 ij.2).im) := by
    have hinv : ((U' e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) = star (U' e : _) := rfl
    change (Matrix.trace (A * ((U' e)⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).re = _
    rw [su_inv_val_eq_star (U' e)]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
      Complex.re_sum, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      mul_neg, sub_neg_eq_add]
    rw [Fintype.sum_prod_type]
  have h_flat : evalSepList ((Finset.univ : Finset (Fin N × Fin N)).toList.flatMap fun ij =>
      [ (β / (N : ℝ), fun V => ((V e : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2).re),
        (β / (N : ℝ), fun V => ((V e : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2).im) ]) U U' =
      (β / (N : ℝ)) * ∑ ij : Fin N × Fin N,
        ((A ij.1 ij.2).re * (B ij.1 ij.2).re + (A ij.1 ij.2).im * (B ij.1 ij.2).im) := by
    have h_gen : ∀ (l_ij : List (Fin N × Fin N)),
        evalSepList (l_ij.flatMap fun ij =>
          [ (β / (N : ℝ), fun V => ((V e : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2).re),
            (β / (N : ℝ), fun V => ((V e : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2).im) ]) U U' =
        (β / (N : ℝ)) * (l_ij.map fun ij =>
          (A ij.1 ij.2).re * (B ij.1 ij.2).re + (A ij.1 ij.2).im * (B ij.1 ij.2).im).sum := by
      intro l_ij
      induction l_ij with
      | nil => simp [evalSepList]
      | cons ij tl ih =>
        rw [List.flatMap_cons, evalSepList_append, ih, List.map_cons, List.sum_cons]
        simp only [evalSepList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
        dsimp [A, B]
        ring
    rw [h_gen, sum_map_univ_toList]
  rw [suEntrySepList, evalSepList_append, h_flat, htr_eq]
  have h_const : evalSepList [(β, fun _ => 1)] U U' = β := by simp [evalSepList]
  rw [h_const]
  ring

/--
**Exact positivity of `wilson4DTransferOp`**:
proved via uniform Bernoulli–Taylor `evalSepList` approximation of `temporalPlaqFactor`,
Fubini/Haar gauge averaging (`evalSepList_gaugeAvg`), and `sepList_wilson_inner_nonneg`.
-/
theorem wilson4DTransferOp_pos (L N : ℕ) [NeZero L] (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (ψ : HaarGaugeSpace (latticeHaarMeasure L N)) :
    0 ≤ (⟪ψ, wilson4DTransferOp L N hN β hβ ψ⟫_ℂ).re := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let G_L := GaugeField (cubicTorus3 L) G
  let μ := latticeHaarMeasure L N
  haveI := latticeHaarMeasure_prob L N
  haveI := gaugeGrpHaarMeasure_prob L N
  let E_card := Fintype.card (cubicTorus3 L).Link
  let S_e : (cubicTorus3 L).Link → G_L → G_L → ℝ := fun e U U' =>
    β * (1 + (1 / (N : ℝ)) *
      (Matrix.trace (((U e * (U' e)⁻¹ : G) : Matrix (Fin N) (Fin N) ℂ))).re)
  have hS_bounds : ∀ e U U', 0 ≤ S_e e U U' ∧ S_e e U U' ≤ 2 * β := by
    intro e U U'
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have htr := abs_le.mp (abs_re_trace_su_le (U e * (U' e)⁻¹))
    have h1 : -1 ≤ (1 / (N : ℝ)) *
        (Matrix.trace (((U e * (U' e)⁻¹ : G) : Matrix (Fin N) (Fin N) ℂ))).re := by
      rw [one_div, le_inv_mul_iff₀ hN_pos, mul_neg, mul_one]; exact htr.1
    have h2 : (1 / (N : ℝ)) *
        (Matrix.trace (((U e * (U' e)⁻¹ : G) : Matrix (Fin N) (Fin N) ℂ))).re ≤ 1 := by
      rw [one_div, inv_mul_le_iff₀ hN_pos, mul_one]; exact htr.2
    exact ⟨mul_nonneg hβ (by linarith), by nlinarith⟩
  have hS_factor : ∀ e U U',
      Real.exp (-(2 * β)) * Real.exp (S_e e U U') = temporalPlaqFactor β e U U' (fun _ => 1) := by
    intro e U U'
    rw [← Real.exp_add]
    unfold temporalPlaqFactor S_e
    rw [gaugeAct_one]
    congr 1; ring
  let B : ℝ := 2 * β
  have hB : 0 ≤ B := by positivity
  let n₀ : ℕ := Nat.ceil (max 1 (max B (2 * B ^ 2))) + 1
  have hn_ok : ∀ n ≥ n₀, 1 ≤ (n : ℝ) ∧ B ≤ (n : ℝ) ∧ 2 * B ^ 2 ≤ (n : ℝ) := by
    intro n hn
    have hle : max 1 (max B (2 * B ^ 2)) ≤ (n : ℝ) := by
      have h1 : max 1 (max B (2 * B ^ 2)) ≤ (Nat.ceil (max 1 (max B (2 * B ^ 2))) : ℝ) :=
        Nat.le_ceil _
      have h2 : (Nat.ceil (max 1 (max B (2 * B ^ 2))) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (by omega : Nat.ceil (max 1 (max B (2 * B ^ 2))) ≤ n)
      exact h1.trans h2
    exact ⟨(le_max_left 1 _).trans hle,
      ((le_max_left B _).trans (le_max_right 1 _)).trans hle,
      ((le_max_right B _).trans (le_max_right 1 _)).trans hle⟩
  let links := (Finset.univ : Finset (cubicTorus3 L).Link).toList
  have h_links_nodup : links.Nodup := Finset.nodup_toList _
  let K_n : ℕ → G_L → G_L → ℝ := fun n U U' =>
    Real.exp (-(2 * β * (links.length : ℝ))) *
      (links.map fun e => (1 + S_e e U U' / (n : ℝ)) ^ n).prod
  have hK_n_sep : ∀ n ≥ 1, ∃ l_n, ValidSepList l_n ∧
      (∀ U U', evalSepList l_n U U' = K_n n U U') ∧
      (∀ h U U', evalSepList l_n (gaugeAct h U) (gaugeAct h U') = evalSepList l_n U U') := by
    intro n hn
    let l_fac : (cubicTorus3 L).Link → List (ℝ × (G_L → ℝ)) := fun e =>
      powSepList ([(1, fun _ => 1)] ++ scaleSepList ((n : ℝ)⁻¹) (suEntrySepList L N e β)) n
    have hl_fac_valid : ∀ e, ValidSepList (l_fac e) := fun e =>
      validSepList_pow
        (validSepList_append (fun p hp => by simp at hp; subst hp; exact ⟨zero_le_one, continuous_const⟩)
          (validSepList_scale (inv_nonneg.mpr (Nat.cast_nonneg n))
            (validSepList_suEntry L N hN e β hβ))) n
    have hl_fac_eval : ∀ e U U',
        evalSepList (l_fac e) U U' = (1 + S_e e U U' / (n : ℝ)) ^ n := by
      intro e U U'
      rw [evalSepList_pow, evalSepList_append, evalSepList_scale, evalSepList_suEntry]
      have h1 : evalSepList ([(1, fun _ => 1)] : List (ℝ × (G_L → ℝ))) U U' = 1 := by
        simp [evalSepList]
      rw [h1]
      congr 1
      dsimp [S_e]
      rw [div_eq_mul_inv]
      ring
    let l_n := scaleSepList (Real.exp (-(2 * β * (links.length : ℝ))))
      (prodSepList (links.map l_fac))
    refine ⟨l_n, validSepList_scale (Real.exp_pos _).le
        (validSepList_prod fun l hl => by
          rw [List.mem_map] at hl; rcases hl with ⟨e, _, rfl⟩; exact hl_fac_valid e),
      fun U U' => ?_, fun h U U' => ?_⟩
    · dsimp [l_n, K_n]
      rw [evalSepList_scale, evalSepList_prod, List.map_map]
      congr 2
      refine List.map_congr_left fun e _ => hl_fac_eval e U U'
    · have h_e : ∀ e U U', S_e e (gaugeAct h U) (gaugeAct h U') = S_e e U U' := by
        intro e U U'
        have h_conj : gaugeAct h U e * (gaugeAct h U' e)⁻¹ =
            h ((cubicTorus3 L).src e) * (U e * (U' e)⁻¹) * (h ((cubicTorus3 L).src e))⁻¹ := by
          simp only [gaugeAct, mul_inv_rev, inv_inv, mul_assoc]
          simp
        change β * (1 + (1 / (N : ℝ)) *
            (Matrix.trace (((gaugeAct h U e * (gaugeAct h U' e)⁻¹ : G) :
              Matrix (Fin N) (Fin N) ℂ))).re) =
          β * (1 + (1 / (N : ℝ)) *
            (Matrix.trace (((U e * (U' e)⁻¹ : G) : Matrix (Fin N) (Fin N) ℂ))).re)
        rw [h_conj, su_trace_conj']
      have h_eq : ∀ V₁ V₂, evalSepList l_n V₁ V₂ = K_n n V₁ V₂ := fun V₁ V₂ => by
        dsimp [l_n, K_n]
        rw [evalSepList_scale, evalSepList_prod, List.map_map]
        congr 2
        exact List.map_congr_left fun e _ => hl_fac_eval e V₁ V₂
      rw [h_eq, h_eq]
      dsimp [K_n]
      congr 2
      exact List.map_congr_left fun e _ => by rw [h_e e U U']
  let δ : ℕ → ℝ := fun n => 2 * B ^ 2 * Real.exp B / (n : ℝ)
  have h_err : ∀ n ≥ n₀, ∀ U U',
      |∫ g, K_n n U (gaugeAct g U') ∂(gaugeGrpHaarMeasure L N) - wilson4DKernel L N β U U'| ≤
        (2 : ℝ) ^ links.length * (links.length : ℝ) * (δ n / 2) := by
    intro n hn U U'
    obtain ⟨hn1, hnB, hnB2⟩ := hn_ok n hn
    have h_pt : ∀ g : GaugeGrp3 L N,
        |K_n n U (gaugeAct g U') - ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g| ≤
          (2 : ℝ) ^ links.length * (links.length : ℝ) * (δ n / 2) := by
      intro g
      let V := gaugeAct g U'
      have hK_prod : K_n n U V =
          ∏ e : (cubicTorus3 L).Link, Real.exp (-(2 * β)) * (1 + S_e e U V / (n : ℝ)) ^ n := by
        have h_list_eq : (links.map fun e => Real.exp (-(2 * β)) * (1 + S_e e U V / (n : ℝ)) ^ n).prod =
            ∏ e : (cubicTorus3 L).Link, Real.exp (-(2 * β)) * (1 + S_e e U V / (n : ℝ)) ^ n := by
          rw [← List.prod_toFinset _ h_links_nodup]
          congr 1
          ext e; simp [links, Finset.mem_toList]
        have h_scale_prod :
            (links.map fun e => Real.exp (-(2 * β)) * (1 + S_e e U V / (n : ℝ)) ^ n).prod =
              (Real.exp (-(2 * β))) ^ links.length *
                (links.map fun e => (1 + S_e e U V / (n : ℝ)) ^ n).prod := by
          clear h_list_eq
          induction links with
          | nil => simp
          | cons e tl ih =>
            simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
            rw [ih, pow_succ']
            ring
        have h_exp_pow : (Real.exp (-(2 * β))) ^ links.length =
            Real.exp (-(2 * β * (links.length : ℝ))) := by
          rw [← Real.exp_nat_mul]; ring_nf
        rw [← h_list_eq, h_scale_prod, h_exp_pow]
      have hfac_g : ∀ e : (cubicTorus3 L).Link,
          temporalPlaqFactor β e U U' g = temporalPlaqFactor β e U V (fun _ => 1) := by
        intro e
        unfold temporalPlaqFactor
        rw [gaugeAct_one]
      have h_rhs_prod :
          (∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g) =
            ∏ e : (cubicTorus3 L).Link, Real.exp (-(2 * β)) * Real.exp (S_e e U V) := by
        refine Finset.prod_congr rfl fun e _ => ?_
        rw [hfac_g e]
        exact (hS_factor e U V).symm
      rw [hK_prod, h_rhs_prod]
      have h_a_bd : ∀ e ∈ (Finset.univ : Finset (cubicTorus3 L).Link),
          |Real.exp (-(2 * β)) * (1 + S_e e U V / (n : ℝ)) ^ n| ≤ 2 := by
        intro e _
        have hs := hS_bounds e U V
        have h_app := exp_approx_one_add_div hB hs.1 hs.2 n hn1 hnB hnB2
        have h_pow_nn : 0 ≤ (1 + S_e e U V / (n : ℝ)) ^ n :=
          pow_nonneg (add_nonneg zero_le_one (div_nonneg hs.1 (Nat.cast_nonneg n))) n
        have h_one_u_le : (1 + S_e e U V / (n : ℝ)) ^ n ≤ 2 * Real.exp (S_e e U V) := by
          have hz : 0 ≤ S_e e U V / (n : ℝ) := div_nonneg hs.1 (Nat.cast_nonneg n)
          have hnu : (n : ℝ) * (S_e e U V / (n : ℝ)) ^ 2 ≤ 1 / 2 := by
            have hn_pos : (0 : ℝ) < n := by linarith
            calc (n : ℝ) * (S_e e U V / (n : ℝ)) ^ 2
                = S_e e U V ^ 2 / (n : ℝ) := by field_simp [hn_pos.ne']
              _ ≤ B ^ 2 / (n : ℝ) := div_le_div_of_nonneg_right (pow_le_pow_left₀ hs.1 hs.2 2) hn_pos.le
              _ ≤ 1 / 2 := by rw [div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 2)]; linarith
          have h_exp_u : 1 + S_e e U V / (n : ℝ) ≤
              Real.exp (S_e e U V / (n : ℝ)) * (1 + (S_e e U V / (n : ℝ)) ^ 2) := by
            have h_diff := Real.abs_exp_sub_one_sub_id_le (by
              rw [abs_of_nonneg hz, div_le_one (by linarith)]; exact hs.2.trans hnB)
            have h1 : 1 + S_e e U V / (n : ℝ) ≤
                Real.exp (S_e e U V / (n : ℝ)) + (S_e e U V / (n : ℝ)) ^ 2 := by
              linarith [(abs_le.mp h_diff).1]
            have h_ge1 : 1 ≤ Real.exp (S_e e U V / (n : ℝ)) :=
              (by simp : (1 : ℝ) ≤ Real.exp 0).trans (Real.exp_le_exp.mpr hz)
            calc 1 + S_e e U V / (n : ℝ)
                ≤ Real.exp (S_e e U V / (n : ℝ)) + (S_e e U V / (n : ℝ)) ^ 2 := h1
              _ ≤ Real.exp (S_e e U V / (n : ℝ)) +
                    Real.exp (S_e e U V / (n : ℝ)) * (S_e e U V / (n : ℝ)) ^ 2 := by
                  gcongr; exact le_mul_of_one_le_left (sq_nonneg _) h_ge1
              _ = Real.exp (S_e e U V / (n : ℝ)) * (1 + (S_e e U V / (n : ℝ)) ^ 2) := by ring
          calc (1 + S_e e U V / (n : ℝ)) ^ n
              ≤ (Real.exp (S_e e U V / (n : ℝ)) * (1 + (S_e e U V / (n : ℝ)) ^ 2)) ^ n :=
                  pow_le_pow_left₀ (by linarith) h_exp_u n
            _ = (Real.exp (S_e e U V / (n : ℝ))) ^ n * (1 + (S_e e U V / (n : ℝ)) ^ 2) ^ n := by
                  rw [mul_pow]
            _ = Real.exp (S_e e U V) * (1 + (S_e e U V / (n : ℝ)) ^ 2) ^ n := by
                  rw [← Real.exp_nat_mul]
                  congr 2; field_simp [(by linarith : (n : ℝ) ≠ 0)]
            _ ≤ Real.exp (S_e e U V) * 2 :=
                  mul_le_mul_of_nonneg_left (one_add_pow_le_two (sq_nonneg _) n hnu) (Real.exp_pos _).le
            _ = 2 * Real.exp (S_e e U V) := by ring
        rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h_pow_nn)]
        calc Real.exp (-(2 * β)) * (1 + S_e e U V / (n : ℝ)) ^ n
            ≤ Real.exp (-(2 * β)) * (2 * Real.exp (S_e e U V)) :=
                mul_le_mul_of_nonneg_left h_one_u_le (Real.exp_pos _).le
          _ = 2 * (Real.exp (-(2 * β)) * Real.exp (S_e e U V)) := by ring
          _ ≤ 2 * (Real.exp (-(2 * β)) * Real.exp (2 * β)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs.2) (Real.exp_pos _).le)
                  (by norm_num : (0 : ℝ) ≤ 2)
          _ = 2 := by rw [← Real.exp_add]; simp
      have h_b_bd : ∀ e ∈ (Finset.univ : Finset (cubicTorus3 L).Link),
          |Real.exp (-(2 * β)) * Real.exp (S_e e U V)| ≤ 2 := by
        intro e _
        rw [abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
        rw [hS_factor e U V, ← hfac_g e]
        exact (temporalPlaqFactor_bounds hN β hβ e U U' g).2.trans (by norm_num)
      have h_ab_bd : ∀ e ∈ (Finset.univ : Finset (cubicTorus3 L).Link),
          |Real.exp (-(2 * β)) * (1 + S_e e U V / (n : ℝ)) ^ n -
            Real.exp (-(2 * β)) * Real.exp (S_e e U V)| ≤ 2 * (δ n / 2) := by
        intro e _
        have hs := hS_bounds e U V
        have h_app := exp_approx_one_add_div hB hs.1 hs.2 n hn1 hnB hnB2
        have h_eq : Real.exp (-(2 * β)) * (1 + S_e e U V / (n : ℝ)) ^ n -
            Real.exp (-(2 * β)) * Real.exp (S_e e U V) =
            -(Real.exp (-(2 * β)) * (Real.exp (S_e e U V) - (1 + S_e e U V / (n : ℝ)) ^ n)) := by
          ring
        rw [h_eq, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hexp_le1 : Real.exp (-(2 * β)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        calc Real.exp (-(2 * β)) * |Real.exp (S_e e U V) - (1 + S_e e U V / (n : ℝ)) ^ n|
            ≤ 1 * δ n := mul_le_mul hexp_le1 h_app (abs_nonneg _) zero_le_one
          _ = 2 * (δ n / 2) := by ring
      have h_prod_bd := prod_sub_prod_bound Finset.univ
        (fun e => Real.exp (-(2 * β)) * (1 + S_e e U V / (n : ℝ)) ^ n)
        (fun e => Real.exp (-(2 * β)) * Real.exp (S_e e U V))
        (δ n / 2) (by dsimp [δ]; positivity) h_a_bd h_b_bd h_ab_bd
      simpa [links, Finset.length_toList] using h_prod_bd
    have h_int1 : MeasureTheory.Integrable (fun g => K_n n U (gaugeAct g U'))
        (gaugeGrpHaarMeasure L N) := by
      obtain ⟨l_n, hl_n, hl_eval, _⟩ := hK_n_sep n (by omega)
      have hc : Continuous (fun g : GaugeGrp3 L N => K_n n U (gaugeAct g U')) := by
        have hc_act : Continuous (fun g : GaugeGrp3 L N => gaugeAct g U') := by
          change Continuous (fun g : GaugeGrp3 L N => fun e =>
            g ((cubicTorus3 L).src e) * U' e * (g ((cubicTorus3 L).dst e))⁻¹)
          rw [continuous_pi_iff]
          intro e
          exact (((continuous_apply ((cubicTorus3 L).src e)).mul continuous_const).mul
            (continuous_inv.comp (continuous_apply ((cubicTorus3 L).dst e))))
        simp_rw [← hl_eval]
        exact (continuous_evalSepList hl_n).comp (continuous_const.prodMk hc_act)
      obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_abs.comp hc)).bddAbove
      refine (MeasureTheory.integrable_const (max M 0)).mono' hc.stronglyMeasurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun g => by
          rw [Real.norm_eq_abs]; exact le_max_of_le_left (hM ⟨g, Set.mem_univ _, rfl⟩))
    have h_int2 : MeasureTheory.Integrable
        (fun g => ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g)
        (gaugeGrpHaarMeasure L N) := by
      have hc : Continuous (fun g : GaugeGrp3 L N =>
          ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g) :=
        continuous_temporalPlaqProd_in_g L N β U U'
      refine (MeasureTheory.integrable_const (1 : ℝ)).mono' hc.stronglyMeasurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun g => by
          have hnn : 0 ≤ ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g :=
            Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
          rw [Real.norm_eq_abs, abs_of_nonneg hnn]
          calc ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g
              ≤ ∏ _e : (cubicTorus3 L).Link, (1 : ℝ) :=
                Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
                  (fun e _ => (temporalPlaqFactor_bounds hN β hβ e U U' g).2)
            _ = 1 := by simp)
    unfold wilson4DKernel
    change |(∫ g : GaugeGrp3 L N, K_n n U (gaugeAct g U') ∂(gaugeGrpHaarMeasure L N)) -
        (∫ g : GaugeGrp3 L N, ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g ∂(gaugeGrpHaarMeasure L N))| ≤ _
    have h_sub : (∫ g : GaugeGrp3 L N, K_n n U (gaugeAct g U') ∂(gaugeGrpHaarMeasure L N)) -
        (∫ g : GaugeGrp3 L N, ∏ e : (cubicTorus3 L).Link,
          temporalPlaqFactor β e U U' g ∂(gaugeGrpHaarMeasure L N)) =
        ∫ g : GaugeGrp3 L N, (K_n n U (gaugeAct g U') -
          ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g)
          ∂(gaugeGrpHaarMeasure L N) :=
      (MeasureTheory.integral_sub h_int1 h_int2).symm
    rw [h_sub]
    calc |∫ g, (K_n n U (gaugeAct g U') -
            ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g)
          ∂(gaugeGrpHaarMeasure L N)|
        ≤ ∫ g, |K_n n U (gaugeAct g U') -
            ∏ e : (cubicTorus3 L).Link, temporalPlaqFactor β e U U' g|
          ∂(gaugeGrpHaarMeasure L N) := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ _g, (2 : ℝ) ^ links.length * (links.length : ℝ) * (δ n / 2)
          ∂(gaugeGrpHaarMeasure L N) :=
            MeasureTheory.integral_mono (h_int1.sub h_int2).abs
              (MeasureTheory.integrable_const _) h_pt
      _ = (2 : ℝ) ^ links.length * (links.length : ℝ) * (δ n / 2) := by
            simp [Measure.real, MeasureTheory.measure_univ]
  have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
    intro a b
    have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K]; norm_num
    calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
      _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
            rw [inner_smul_left, inner_smul_right]
      _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
  have hT_inner : (⟪ψ, wilson4DTransferOp L N hN β hβ ψ⟫_ℂ).re =
      (∫ U, starRingEnd ℂ (ψ U) *
        wilsonIntegralFn L N β (wilson4DKernel L N β) ψ U ∂μ).re := by
    rw [MeasureTheory.L2.inner_def]
    congr 1
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [wilsonIntegralOp_apply_ae L N β hβ (wilson4DKernel L N β)
      (continuous_wilson4DKernel L N hN β hβ)
      (fun U U' => (Real.exp_pos _).le.trans (wilson4DKernel_bounds L N hN β hβ U U').1)
      1 zero_le_one
      (fun U U' => (wilson4DKernel_bounds L N hN β hβ U U').2) ψ] with U hU
    have hU' : (wilson4DTransferOp L N hN β hβ ψ) U =
        wilsonIntegralFn L N β (wilson4DKernel L N β) ψ U := by
      simpa [wilson4DTransferOp] using hU
    rw [hU', hcinner]
  rw [hT_inner]
  apply le_of_forall_pos_le_add
  intro ε hε
  let C_glob : ℝ := (2 : ℝ) ^ links.length * (links.length : ℝ) * (B ^ 2 * Real.exp B)
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (C_glob * (‖ψ‖ ^ 2 + 1) / ε)
  let n := max n₀ (n₁ + 1)
  obtain ⟨l_n, hl_n, hl_eval, hl_inv⟩ := hK_n_sep n (by omega)
  let l_av := gaugeAvgSepList L N l_n
  have hl_av_valid : ValidSepList l_av := validSepList_gaugeAvg L N hl_n
  have hl_av_eval : ∀ U U', evalSepList l_av U U' =
      ∫ g, K_n n U (gaugeAct g U') ∂(gaugeGrpHaarMeasure L N) := by
    intro U U'
    rw [evalSepList_gaugeAvg L N hl_n hl_inv U U']
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => hl_eval U (gaugeAct g U'))
  have h_sep_nn := sepList_wilson_inner_nonneg L N β hβ l_av hl_av_valid ψ
  let η : ℝ := (2 : ℝ) ^ links.length * (links.length : ℝ) * (δ n / 2)
  have hη_le : η * ‖ψ‖ ^ 2 ≤ ε := by
    have hn_pos : (0 : ℝ) < n := by
      have : 1 ≤ n := le_trans (by omega : 1 ≤ n₁ + 1) (le_max_right _ _)
      exact_mod_cast this
    have hη_eq : η = C_glob / (n : ℝ) := by
      dsimp [η, δ, C_glob]; ring
    have h1 : C_glob * (‖ψ‖ ^ 2 + 1) / ε < (n : ℝ) := by
      have hn1_le : (n₁ : ℝ) < (n : ℝ) := by
        exact_mod_cast (by omega : n₁ < n)
      exact hn₁.trans hn1_le
    have h2 : C_glob * (‖ψ‖ ^ 2 + 1) < (n : ℝ) * ε := (div_lt_iff₀ hε).mp h1
    have hC_nn : 0 ≤ C_glob := by dsimp [C_glob]; positivity
    have h3 : C_glob * ‖ψ‖ ^ 2 ≤ (n : ℝ) * ε := by
      nlinarith [sq_nonneg ‖ψ‖]
    rw [hη_eq, div_mul_eq_mul_div, div_le_iff₀ hn_pos]
    linarith
  have h_diff_le :
      (∫ U, starRingEnd ℂ (ψ U) *
        (∫ U', ((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U' ∂μ) ∂μ).re -
      (∫ U, starRingEnd ℂ (ψ U) *
        wilsonIntegralFn L N β (wilson4DKernel L N β) ψ U ∂μ).re ≤ η * ‖ψ‖ ^ 2 := by
    let F_diff : G_L → ℂ := fun U =>
      starRingEnd ℂ (ψ U) *
        ((∫ U', ((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U' ∂μ) -
          wilsonIntegralFn L N β (wilson4DKernel L N β) ψ U)
    have h_int_1 : MeasureTheory.Integrable (fun U => starRingEnd ℂ (ψ U) *
        (∫ U', ((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U' ∂μ)) μ := by
      have hK_cont : Continuous (Function.uncurry (evalSepList l_av)) := continuous_evalSepList hl_av_valid
      obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_abs.comp hK_cont)).bddAbove
      let C_av := max M 0
      have h_inner_int : ∀ U, MeasureTheory.Integrable
          (fun U' => ((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U') μ := by
        intro U
        refine (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul C_av).mono' ?_ ?_
        · exact (Complex.continuous_ofReal.comp ((continuous_cubicWilsonKernel L N β (evalSepList l_av) hK_cont).comp
            (continuous_const.prodMk continuous_id))).stronglyMeasurable.aestronglyMeasurable.mul
            (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun U' => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have h1 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U).1
          have h2 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U').1
          have hexp : |Real.exp (-(1 / 2 : ℝ) *
              (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U'))| ≤ 1 := by
            rw [abs_of_nonneg (Real.exp_pos _).le]
            exact Real.exp_le_one_iff.mpr (by linarith)
          have hk_bd : |wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U'| ≤ C_av := by
            unfold wilsonKernel
            rw [abs_mul]
            calc |Real.exp _| * |evalSepList l_av U U'|
                ≤ 1 * C_av := mul_le_mul hexp (le_max_of_le_left (hM ⟨(U, U'), Set.mem_univ _, rfl⟩))
                  (abs_nonneg _) zero_le_one
              _ = C_av := one_mul _
          exact mul_le_mul_of_nonneg_right hk_bd (norm_nonneg _)
      have h_out_cont : Continuous (fun U =>
          ∫ U', ((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U' ∂μ) := by
        refine MeasureTheory.continuous_of_dominated (bound := fun U' => C_av * ‖ψ U'‖) ?_ ?_
          (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul C_av) ?_
        · intro U; exact (h_inner_int U).aestronglyMeasurable
        · intro U
          refine Filter.Eventually.of_forall fun U' => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have h1 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U).1
          have h2 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U').1
          have hexp : |Real.exp (-(1 / 2 : ℝ) *
              (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U'))| ≤ 1 := by
            rw [abs_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.mpr (by linarith)
          have hk_bd : |wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U'| ≤ C_av := by
            unfold wilsonKernel; rw [abs_mul]
            calc |Real.exp _| * |evalSepList l_av U U'|
                ≤ 1 * C_av := mul_le_mul hexp (le_max_of_le_left (hM ⟨(U, U'), Set.mem_univ _, rfl⟩))
                  (abs_nonneg _) zero_le_one
              _ = C_av := one_mul _
          exact mul_le_mul_of_nonneg_right hk_bd (norm_nonneg _)
        · refine Filter.Eventually.of_forall fun U' => ?_
          exact (Complex.continuous_ofReal.comp ((continuous_cubicWilsonKernel L N β (evalSepList l_av) hK_cont).comp
            (continuous_id.prodMk continuous_const))).mul continuous_const
      refine (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul (C_av * ‖ψ‖)).mono' ?_ ?_
      · exact (continuous_star.comp_aestronglyMeasurable (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable).mul
          h_out_cont.stronglyMeasurable.aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun U => ?_
        rw [norm_mul, Complex.norm_conj]
        have h_u_bd : ‖∫ U', ((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U' ∂μ‖ ≤
            C_av * ‖ψ‖ := by
          calc ‖∫ U', _ ∂μ‖ ≤ ∫ U', ‖((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U'‖ ∂μ :=
                MeasureTheory.norm_integral_le_integral_norm _
            _ ≤ ∫ U', C_av * ‖ψ U'‖ ∂μ := by
                refine MeasureTheory.integral_mono (h_inner_int U).norm
                  (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul C_av) fun U' => ?_
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                have h1 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U).1
                have h2 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U').1
                have hexp : |Real.exp (-(1 / 2 : ℝ) *
                    (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U'))| ≤ 1 := by
                  rw [abs_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.mpr (by linarith)
                have hk_bd : |wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U'| ≤ C_av := by
                  unfold wilsonKernel; rw [abs_mul]
                  calc |Real.exp _| * |evalSepList l_av U U'|
                      ≤ 1 * C_av := mul_le_mul hexp (le_max_of_le_left (hM ⟨(U, U'), Set.mem_univ _, rfl⟩))
                        (abs_nonneg _) zero_le_one
                    _ = C_av := one_mul _
                exact mul_le_mul_of_nonneg_right hk_bd (norm_nonneg _)
            _ = C_av * ∫ U', ‖ψ U'‖ ∂μ := MeasureTheory.integral_const_mul C_av _
            _ ≤ C_av * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) (le_max_right M 0)
        exact (mul_le_mul_of_nonneg_left h_u_bd (norm_nonneg _)).trans_eq
          (mul_comm _ _)
    have h_int_2 : MeasureTheory.Integrable (fun U => starRingEnd ℂ (ψ U) *
        wilsonIntegralFn L N β (wilson4DKernel L N β) ψ U) μ := by
      have h_eq : (fun U => starRingEnd ℂ (ψ U) * wilsonIntegralFn L N β (wilson4DKernel L N β) ψ U) =ᵐ[μ]
          fun U => ⟪ψ U, (wilson4DTransferOp L N hN β hβ ψ) U⟫_ℂ := by
        filter_upwards [wilsonIntegralOp_apply_ae L N β hβ (wilson4DKernel L N β)
          (continuous_wilson4DKernel L N hN β hβ)
          (fun U U' => (Real.exp_pos _).le.trans (wilson4DKernel_bounds L N hN β hβ U U').1)
          1 zero_le_one
          (fun U U' => (wilson4DKernel_bounds L N hN β hβ U U').2) ψ] with U hU
        have hU' : (wilson4DTransferOp L N hN β hβ ψ) U =
            wilsonIntegralFn L N β (wilson4DKernel L N β) ψ U := by
          simpa [wilson4DTransferOp] using hU
        rw [hU', hcinner]
      exact (MeasureTheory.L2.integrable_inner ψ (wilson4DTransferOp L N hN β hβ ψ)).congr h_eq.symm
    have h_sub_eq : (∫ U, starRingEnd ℂ (ψ U) *
        (∫ U', ((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U' ∂μ) ∂μ).re -
      (∫ U, starRingEnd ℂ (ψ U) *
        wilsonIntegralFn L N β (wilson4DKernel L N β) ψ U ∂μ).re = (∫ U, F_diff U ∂μ).re := by
      rw [← Complex.sub_re, ← MeasureTheory.integral_sub h_int_1 h_int_2]
      congr 1
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      dsimp [F_diff]; ring
    rw [h_sub_eq]
    have h_inner_diff_bd : ∀ U, ‖(∫ U', ((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U' ∂μ) -
        wilsonIntegralFn L N β (wilson4DKernel L N β) ψ U‖ ≤ η * ‖ψ‖ := by
      intro U
      have hK_cont : Continuous (Function.uncurry (evalSepList l_av)) := continuous_evalSepList hl_av_valid
      obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_abs.comp hK_cont)).bddAbove
      let C_av := max M 0
      have hi1 : MeasureTheory.Integrable
          (fun U' => ((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U') μ := by
        refine (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul C_av).mono' ?_ ?_
        · exact (Complex.continuous_ofReal.comp ((continuous_cubicWilsonKernel L N β (evalSepList l_av) hK_cont).comp
            (continuous_const.prodMk continuous_id))).stronglyMeasurable.aestronglyMeasurable.mul
            (MeasureTheory.Lp.memLp ψ).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun U' => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have h1 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U).1
          have h2 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U').1
          have hexp : |Real.exp (-(1 / 2 : ℝ) *
              (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U'))| ≤ 1 := by
            rw [abs_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.mpr (by linarith)
          have hk_bd : |wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U'| ≤ C_av := by
            unfold wilsonKernel; rw [abs_mul]
            calc |Real.exp _| * |evalSepList l_av U U'|
                ≤ 1 * C_av := mul_le_mul hexp (le_max_of_le_left (hM ⟨(U, U'), Set.mem_univ _, rfl⟩))
                  (abs_nonneg _) zero_le_one
              _ = C_av := one_mul _
          exact mul_le_mul_of_nonneg_right hk_bd (norm_nonneg _)
      have hi2 := wilsonKernel_mul_integrable L N β hβ (wilson4DKernel L N β)
        (continuous_wilson4DKernel L N hN β hβ)
        (fun U U' => (Real.exp_pos _).le.trans (wilson4DKernel_bounds L N hN β hβ U U').1)
        1 (fun U U' => (wilson4DKernel_bounds L N hN β hβ U U').2) ψ U
      dsimp [wilsonIntegralFn]
      rw [← MeasureTheory.integral_sub hi1 hi2]
      calc ‖∫ U', (((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U' -
              ((wilsonKernel β (cubicPlaquettes L) (wilson4DKernel L N β) U U' : ℝ) : ℂ) * ψ U') ∂μ‖
          ≤ ∫ U', ‖((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U' -
              ((wilsonKernel β (cubicPlaquettes L) (wilson4DKernel L N β) U U' : ℝ) : ℂ) * ψ U'‖ ∂μ :=
                MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ U', η * ‖ψ U'‖ ∂μ := by
              refine MeasureTheory.integral_mono (hi1.sub hi2).norm
                (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.const_mul η) fun U' => ?_
              have hfac : ((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' : ℝ) : ℂ) * ψ U' -
                  ((wilsonKernel β (cubicPlaquettes L) (wilson4DKernel L N β) U U' : ℝ) : ℂ) * ψ U' =
                  (((wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' -
                    wilsonKernel β (cubicPlaquettes L) (wilson4DKernel L N β) U U' : ℝ) : ℂ)) * ψ U' := by
                push_cast; ring
              rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
              have h_kern_diff : |wilsonKernel β (cubicPlaquettes L) (evalSepList l_av) U U' -
                  wilsonKernel β (cubicPlaquettes L) (wilson4DKernel L N β) U U'| ≤ η := by
                unfold wilsonKernel
                rw [← mul_sub, abs_mul]
                have h1 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U).1
                have h2 := (wilsonAction_bounds β hβ (cubicPlaquettes L) U').1
                have hexp : |Real.exp (-(1 / 2 : ℝ) *
                    (wilsonAction β (cubicPlaquettes L) U + wilsonAction β (cubicPlaquettes L) U'))| ≤ 1 := by
                  rw [abs_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.mpr (by linarith)
                have hk_err := h_err n (le_max_left _ _) U U'
                rw [← hl_av_eval U U'] at hk_err
                calc |Real.exp _| * |evalSepList l_av U U' - wilson4DKernel L N β U U'|
                    ≤ 1 * η := mul_le_mul hexp hk_err (abs_nonneg _) zero_le_one
                  _ = η := one_mul _
              exact mul_le_mul_of_nonneg_right h_kern_diff (norm_nonneg _)
        _ = η * ∫ U', ‖ψ U'‖ ∂μ := MeasureTheory.integral_const_mul η _
        _ ≤ η * ‖ψ‖ := mul_le_mul_of_nonneg_left (l1_le_l2_prob μ ψ) (by dsimp [η, δ]; positivity)
    have h_F_diff_int : MeasureTheory.Integrable F_diff μ := by
      refine (h_int_1.sub h_int_2).congr (Filter.Eventually.of_forall fun U => ?_)
      dsimp [F_diff]
      ring
    calc (∫ U, F_diff U ∂μ).re ≤ ‖∫ U, F_diff U ∂μ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ ≤ ∫ U, ‖F_diff U‖ ∂μ := MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ U, ‖ψ U‖ * (η * ‖ψ‖) ∂μ := by
            refine MeasureTheory.integral_mono h_F_diff_int.norm
              (((MeasureTheory.Lp.memLp ψ).integrable one_le_two).norm.mul_const (η * ‖ψ‖)) fun U => ?_
            dsimp [F_diff]
            rw [norm_mul, Complex.norm_conj]
            exact mul_le_mul_of_nonneg_left (h_inner_diff_bd U) (norm_nonneg _)
      _ = (∫ U, ‖ψ U‖ ∂μ) * (η * ‖ψ‖) := MeasureTheory.integral_mul_const _ _
      _ ≤ ‖ψ‖ * (η * ‖ψ‖) := mul_le_mul_of_nonneg_right (l1_le_l2_prob μ ψ)
            (mul_nonneg (by dsimp [η, δ]; positivity) (norm_nonneg _))
      _ = η * ‖ψ‖ ^ 2 := by ring
  linarith

/--
**Genuine 4D Wilson Lattice Gauge Setup on `cubicTorus3 L`** driven by `wilson4DTransferOp`,
combining compactness, Fubini self-adjointness, Taylor-series reflection positivity,
Perron–Frobenius simple strictly positive vacuum `Ω`, and exact constructive spectral gap.
-/
noncomputable def wilson4DLatticeGaugeSetup (L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    LatticeGaugeSetup (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (HaarGaugeSpace (latticeHaarMeasure L N)) :=
  let K4 := wilson4DKernel L N β
  let hK_cont := continuous_wilson4DKernel L N hN β hβ
  let hK_symm := wilson4DKernel_symm L N β
  let hK_nn : ∀ U U', 0 ≤ K4 U U' := fun U U' =>
    (Real.exp_pos _).le.trans (wilson4DKernel_bounds L N hN β hβ U U').1
  let hK_inv : ∀ g U U', K4 (gaugeAct g U) (gaugeAct g U') = K4 U U' := fun g U U' =>
    wilson4DKernel_gauge_inv_two_sided L N β g g U U'
  let c_min : ℝ := Real.exp (-(2 * β * (Fintype.card (cubicTorus3 L).Link : ℝ)))
  let hc_min : 0 < c_min := Real.exp_pos _
  let hK_lb : ∀ U U', c_min ≤ K4 U U' := fun U U' =>
    (wilson4DKernel_bounds L N hN β hβ U U').1
  let hK_bd : ∀ U U', K4 U U' ≤ 1 := fun U U' =>
    (wilson4DKernel_bounds L N hN β hβ U U').2
  let T_raw := wilsonIntegralOp L N β hβ K4 hK_cont hK_nn 1 zero_le_one hK_bd
  let hT_pos := wilson4DTransferOp_pos L N hN β hβ
  let hpf := wilsonIntegral_perron_frobenius L N β hβ K4 hK_cont hK_symm hK_nn hK_inv
    c_min hc_min hK_lb 1 zero_le_one hK_bd hT_pos
  let Ω := Classical.choose hpf
  let lam0 := Classical.choose (Classical.choose_spec hpf)
  let Δ := Classical.choose (Classical.choose_spec (Classical.choose_spec hpf))
  let hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hpf))
  let hlam0_pos : 0 < lam0 := hspec.1
  let T_norm : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ]
      HaarGaugeSpace (latticeHaarMeasure L N) := ((lam0⁻¹ : ℝ) : ℂ) • T_raw
  { rep := cubicGaugeRep L N
    rep_one := cubicGaugeRep_one L N
    rep_mul := cubicGaugeRep_mul L N
    T := T_norm
    a := 1
    a_pos := one_pos
    T_sa := fun x y => by
      change ⟪((lam0⁻¹ : ℝ) : ℂ) • T_raw x, y⟫_ℂ = ⟪x, ((lam0⁻¹ : ℝ) : ℂ) • T_raw y⟫_ℂ
      rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
      congr 1
      exact wilson4DTransferOp_sa L N hN β hβ x y
    T_pos := fun v => by
      simp only [T_norm, ContinuousLinearMap.smul_apply, inner_smul_right, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (inv_nonneg.mpr hlam0_pos.le) (hT_pos v)
    T_compact := by
      obtain ⟨S, hS_comp, hS_nhds⟩ := wilson4DTransferOp_compact L N hN β hβ
      exact ⟨(((lam0⁻¹ : ℝ) : ℂ) • ·) '' S, hS_comp.image (continuous_const_smul _), by
        filter_upwards [hS_nhds] with v hv
        exact ⟨T_raw v, hv, rfl⟩⟩
    T_gauge_inv := fun g => by
      ext1 ψ
      simp only [T_norm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
      congr 1
      exact congrArg (fun f : HaarGaugeSpace (latticeHaarMeasure L N) →L[ℂ] _ => f ψ)
        (wilsonIntegralOp_gauge_inv L N β hβ K4 hK_cont hK_nn hK_inv 1 zero_le_one hK_bd g)
    Ω := Ω
    Ω_unit := hspec.2.2.1
    Ω_vac := by
      change ((lam0⁻¹ : ℝ) : ℂ) • T_raw Ω = Ω
      have heig : T_raw Ω = (lam0 : ℂ) • Ω := hspec.2.2.2.1
      rw [heig, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0_pos.ne',
        Complex.ofReal_one, one_smul]
    Ω_gauge_inv := hspec.2.2.2.2.1
    Δ := Δ
    Δ_pos := hspec.2.1
    gap := hspec.2.2.2.2.2 }

/-- Exact 4D Wilson `NonAbelianWilsonSetup` on `cubicTorus3 L`. -/
noncomputable def wilson4DNonAbelianSetup (L N : ℕ) [NeZero L] (hN : 2 ≤ N)
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
  K_kin := wilson4DKernel L N β
  K_symm := wilson4DKernel_symm L N β
  K_nonneg := fun U U' =>
    (Real.exp_pos _).le.trans (wilson4DKernel_bounds L N (by omega) β hβ.le U U').1
  K_inv := fun g U U' => wilson4DKernel_gauge_inv_two_sided L N β g g U U'
  gaugeSetup := wilson4DLatticeGaugeSetup L N (by omega) β hβ.le
  SymmIdx := GaugeTransform (cubicTorus3 L) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  symmOp := cubicGaugeRep L N
  symm_comm := fun g => by
    unfold lieBracketCLM
    let S := wilson4DLatticeGaugeSetup L N (by omega) β hβ.le
    change (S.rep g).comp S.T - S.T.comp (S.rep g) = 0
    rw [S.T_gauge_inv g, sub_self]

end Wilson4DPositivityAndGap

end YangMills
