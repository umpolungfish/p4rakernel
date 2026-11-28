
import Imscribing.YangMills.CanonicalLatticeBorchers4D
import Imscribing.YangMills.LatticeChessboardAndTransfer4D

/-!
# Canonical Finite-Volume 4D SU(N) Borchers Sesquilinear Form
-/

namespace Imscribing.YangMills.CanonicalFVBorchers4D

open MeasureTheory
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D
open Imscribing.YangMills.LatticeRP4D
open Imscribing.YangMills.LatticeCutSplit4D
open Imscribing.YangMills.LatticeOSRP4D
open Imscribing.YangMills.LatticeSchwingerRP4D
open Imscribing.YangMills.CenteredTranslation4D
open Imscribing.YangMills.CanonicalHaar4D
open Imscribing.YangMills.CanonicalWilsonBridge
open Imscribing.YangMills.CanonicalHalfRP4D
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.LatticeChessboardTransfer



private instance instNeZeroTwoMul (M : ℕ) [NeZero M] : NeZero (2 * M) :=
  ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne M)⟩

private lemma fvb_gaugeGroup_coe_inv_star {N : ℕ} (A : GaugeGroup N) :
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

private lemma reflectSite_sub_step0_cutMid (M : ℕ) [NeZero M] (x : Lat4 (2 * M))
    (hx : (x 0).val = M - 1) :
    reflectSite (2 * M) x - stepDir (2 * M) 0 = x := by
  have hM : 0 < M := NeZero.pos M
  ext ν
  by_cases hν : ν = 0
  · subst hν
    simp only [reflectSite, stepDir, Pi.sub_apply, ↓reduceIte]
    have h2 : 2 * (x 0 + 1) = 0 := by
      have hsub : 2 * ((x 0).val + 1) = 2 * M := by omega
      have hcast := congrArg (Nat.cast (R := ZMod (2 * M))) hsub
      rw [ZMod.natCast_self] at hcast
      push_cast at hcast
      rw [ZMod.natCast_zmod_val] at hcast
      exact hcast
    linear_combination -h2
  · simp [reflectSite, stepDir, hν]

private lemma reflectSite_sub_step0_cutTop (M : ℕ) [NeZero M] (x : Lat4 (2 * M))
    (hx : (x 0).val = 2 * M - 1) :
    reflectSite (2 * M) x - stepDir (2 * M) 0 = x := by
  have hM : 0 < M := NeZero.pos M
  ext ν
  by_cases hν : ν = 0
  · subst hν
    simp only [reflectSite, stepDir, Pi.sub_apply, ↓reduceIte]
    have h1 : x 0 + 1 = 0 := by
      have hsub : (x 0).val + 1 = 2 * M := by omega
      have hcast := congrArg (Nat.cast (R := ZMod (2 * M))) hsub
      rw [ZMod.natCast_self] at hcast
      push_cast at hcast
      rw [ZMod.natCast_zmod_val] at hcast
      exact hcast
    linear_combination -2 * h1
  · simp [reflectSite, stepDir, hν]

private lemma reflectSite_sub_step0_val {M : ℕ} [NeZero M] (x : Lat4 (2 * M))
    (hx : (x 0).val < 2 * M - 1) :
    ((reflectSite (2 * M) x - stepDir (2 * M) 0) 0).val = 2 * M - 2 - (x 0).val := by
  have hM : 0 < M := NeZero.pos M
  simp only [reflectSite, stepDir, Pi.sub_apply, ↓reduceIte]
  have heq : -(x 0 + 1) - 1 = (((2 * M - 2 - (x 0).val : ℕ) : ZMod (2 * M))) := by
    have hsub : ((x 0).val + (2 * M - 2 - (x 0).val) + 2 : ℕ) = 2 * M := by omega
    have hz := congrArg (Nat.cast (R := ZMod (2 * M))) hsub
    rw [ZMod.natCast_self] at hz
    push_cast at hz
    rw [ZMod.natCast_zmod_val] at hz
    linear_combination -hz
  rw [heq, ZMod.val_natCast_of_lt (by omega)]

private lemma reflectSite_zero_val' {M : ℕ} [NeZero M] (x : Lat4 (2 * M)) :
    ((reflectSite (2 * M) x) 0).val = 2 * M - 1 - (x 0).val := by
  have hM : 0 < M := NeZero.pos M
  have hx_lt : (x 0).val < 2 * M := ZMod.val_lt (x 0)
  simp only [reflectSite, ↓reduceIte]
  have heq : -(x 0 + 1) = (((2 * M - 1 - (x 0).val : ℕ) : ZMod (2 * M))) := by
    have hsub : ((x 0).val + (2 * M - 1 - (x 0).val) + 1 : ℕ) = 2 * M := by omega
    have hz := congrArg (Nat.cast (R := ZMod (2 * M))) hsub
    rw [ZMod.natCast_self] at hz
    push_cast at hz
    rw [ZMod.natCast_zmod_val] at hz
    linear_combination -hz
  rw [heq, ZMod.val_natCast_of_lt (by omega)]

/-- **Exact Swapping-Reflection Symmetry of `glueConfig`:**
    `glueConfig q p = linkReflect (glueConfig p q)` across all 4 link sectors. -/
theorem glueConfig_swap {N M : ℕ} [NeZero M] (p q : HalfVar N M) :
    glueConfig q p = linkReflect (glueConfig p q) := by
  classical
  have hM : 0 < M := NeZero.pos M
  funext x μ
  have hx_lt : (x 0).val < 2 * M := ZMod.val_lt (x 0)
  by_cases hp : IsPosLink M x μ
  · have h_lhs : glueConfig q p x μ = q.1 x μ := by simp [glueConfig, hp]
    rw [h_lhs]
    by_cases hμ : μ = 0
    · subst hμ
      have hx_lt_M1 : (x 0).val < M - 1 := by
        have := hp.1
        have := hp.2 rfl
        omega
      set y := reflectSite (2 * M) x - stepDir (2 * M) 0
      have hy_val : (y 0).val = 2 * M - 2 - (x 0).val :=
        reflectSite_sub_step0_val x (by omega)
      have hnp : ¬ IsPosLink M y 0 := fun ⟨h, _⟩ => by omega
      have hncm : ¬ IsCutLinkMid M y 0 := fun ⟨_, h⟩ => by omega
      have hnct : ¬ IsCutLinkTop M y 0 := fun ⟨_, h⟩ => by omega
      have hy_eq : glueConfig p q y 0 = linkReflect q.1 y 0 := by
        simp [glueConfig, hnp, hncm, hnct]
      have h_rhs : linkReflect (glueConfig p q) x 0 = (glueConfig p q y 0)⁻¹ := by
        simp [linkReflect, y]
      rw [h_rhs, hy_eq]
      have h_inv := congrFun (congrFun (linkReflect_involutive q.1) x) 0
      simpa [linkReflect, y] using h_inv.symm
    · set y := reflectSite (2 * M) x
      have hy_val : (y 0).val = 2 * M - 1 - (x 0).val := reflectSite_zero_val' x
      have hnp : ¬ IsPosLink M y μ := fun ⟨h, _⟩ => by have := hp.1; omega
      have hncm : ¬ IsCutLinkMid M y μ := fun ⟨h, _⟩ => hμ h
      have hnct : ¬ IsCutLinkTop M y μ := fun ⟨h, _⟩ => hμ h
      have hy_eq : glueConfig p q y μ = linkReflect q.1 y μ := by
        simp [glueConfig, hnp, hncm, hnct]
      have h_rhs : linkReflect (glueConfig p q) x μ = glueConfig p q y μ := by
        simp [linkReflect, hμ, y]
      rw [h_rhs, hy_eq]
      have h_inv := congrFun (congrFun (linkReflect_involutive q.1) x) μ
      simpa [linkReflect, hμ, y] using h_inv.symm
  · by_cases hcm : IsCutLinkMid M x μ
    · obtain ⟨rfl, hxM⟩ := hcm
      have h_lhs : glueConfig q p x 0 = (q.2 x)⁻¹ * p.2 x := by
        simp [glueConfig, hp, IsCutLinkMid, hxM]
      have h_sub : reflectSite (2 * M) x - stepDir (2 * M) 0 = x :=
        reflectSite_sub_step0_cutMid M x hxM
      have h_pq : glueConfig p q x 0 = (p.2 x)⁻¹ * q.2 x := by
        simp [glueConfig, hp, IsCutLinkMid, hxM]
      simp [h_lhs, linkReflect, h_sub, h_pq, mul_inv_rev]
    · by_cases hct : IsCutLinkTop M x μ
      · obtain ⟨rfl, hxT⟩ := hct
        have h_lhs : glueConfig q p x 0 = (p.2 x)⁻¹ * q.2 x := by
          simp [glueConfig, hp, hcm, IsCutLinkTop, hxT]
        have h_sub : reflectSite (2 * M) x - stepDir (2 * M) 0 = x :=
          reflectSite_sub_step0_cutTop M x hxT
        have h_pq : glueConfig p q x 0 = (q.2 x)⁻¹ * p.2 x := by
          simp [glueConfig, hp, hcm, IsCutLinkTop, hxT]
        simp [h_lhs, linkReflect, h_sub, h_pq, mul_inv_rev]
      · have h_lhs : glueConfig q p x μ = linkReflect p.1 x μ := by
          simp [glueConfig, hp, hcm, hct]
        rw [h_lhs]
        by_cases hμ : μ = 0
        · subst hμ
          have hx_ge : M ≤ (x 0).val := by
            by_contra hlt
            have hlt' : (x 0).val < M := Nat.lt_of_not_ge hlt
            by_cases hxM : (x 0).val = M - 1
            · exact hcm ⟨rfl, hxM⟩
            · exact hp ⟨hlt', fun _ => hxM⟩
          have hx_lt_2M1 : (x 0).val < 2 * M - 1 := by
            by_contra hge
            exact hct ⟨rfl, by omega⟩
          set y := reflectSite (2 * M) x - stepDir (2 * M) 0
          have hy_val : (y 0).val = 2 * M - 2 - (x 0).val :=
            reflectSite_sub_step0_val x hx_lt_2M1
          have hy_pos : IsPosLink M y 0 := ⟨by omega, fun _ => by omega⟩
          simp [linkReflect, y, glueConfig, hy_pos]
        · have hx_ge : M ≤ (x 0).val := by
            by_contra hlt
            exact hp ⟨Nat.lt_of_not_ge hlt, fun h => absurd h hμ⟩
          set y := reflectSite (2 * M) x
          have hy_val : (y 0).val = 2 * M - 1 - (x 0).val := reflectSite_zero_val' x
          have hy_pos : IsPosLink M y μ := ⟨by omega, fun h => absurd h hμ⟩
          simp [linkReflect, hμ, y, glueConfig, hy_pos]

/-- **Exact Action Symmetry Under Swapping Half-Configurations:** -/
theorem wilsonAction_glueConfig_symm (N M : ℕ) [NeZero N] [NeZero M] (β : ℝ)
    (p q : HalfVar N M) :
    wilsonAction N (2 * M) β (glueConfig q p) = wilsonAction N (2 * M) β (glueConfig p q) := by
  rw [glueConfig_swap p q, wilsonAction_linkReflect]

/-- Canonical glued partition function `Z_glue = ∫∫ exp(-S_W(glue p q)) dμ_half(p) dμ_half(q)`. -/
noncomputable def gluePartitionFn (N M : ℕ) [NeZero N] [NeZero M] (β : ℝ) : ℝ :=
  letI := borel (GaugeGroup N)
  let μ := halfVarHaarMeasure N M
  ∫ p, ∫ q, Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) ∂μ ∂μ

private lemma glueConfig_measurable (N M : ℕ) [NeZero M] :
    letI := borel (GaugeGroup N)
    Measurable (fun pq : HalfVar N M × HalfVar N M => glueConfig pq.1 pq.2) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  haveI : SecondCountableTopology (GaugeGroup N) :=
    Topology.IsInducing.secondCountableTopology
      (⟨rfl⟩ : Topology.IsInducing (Subtype.val : GaugeGroup N → Matrix (Fin N) (Fin N) ℂ))
  haveI : ContinuousInv (GaugeGroup N) :=
    ⟨continuous_induced_rng.mpr (by
      simpa only [Function.comp_def, fvb_gaugeGroup_coe_inv_star] using
        continuous_star.comp continuous_subtype_val)⟩
  haveI : MeasurableMul₂ (GaugeGroup N) := ContinuousMul.measurableMul₂
  haveI : MeasurableInv (GaugeGroup N) := ContinuousInv.measurableInv
  have mp1 : ∀ y ν, Measurable (fun pq : HalfVar N M × HalfVar N M => pq.1.1 y ν) :=
    fun y ν => (measurable_pi_apply ν).comp ((measurable_pi_apply y).comp (measurable_fst.comp measurable_fst))
  have mp2 : ∀ y ν, Measurable (fun pq : HalfVar N M × HalfVar N M => pq.2.1 y ν) :=
    fun y ν => (measurable_pi_apply ν).comp ((measurable_pi_apply y).comp (measurable_fst.comp measurable_snd))
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun μ => ?_
  dsimp [glueConfig]
  split_ifs
  · exact mp1 x μ
  · exact (((measurable_pi_apply _).comp measurable_snd).comp measurable_fst).inv.mul
      (((measurable_pi_apply _).comp measurable_snd).comp measurable_snd)
  · exact (((measurable_pi_apply _).comp measurable_snd).comp measurable_snd).inv.mul
      (((measurable_pi_apply _).comp measurable_snd).comp measurable_fst)
  · dsimp [linkReflect]
    split_ifs
    · exact (mp2 _ _).inv
    · exact mp2 _ _

private lemma glueConfig_action_measurable (N M : ℕ) [NeZero N] [NeZero M] (β : ℝ) :
    letI := borel (GaugeGroup N)
    Measurable (fun pq : HalfVar N M × HalfVar N M =>
      wilsonAction N (2 * M) β (glueConfig pq.1 pq.2)) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  haveI : SecondCountableTopology (GaugeGroup N) :=
    Topology.IsInducing.secondCountableTopology
      (⟨rfl⟩ : Topology.IsInducing (Subtype.val : GaugeGroup N → Matrix (Fin N) (Fin N) ℂ))
  haveI : ContinuousInv (GaugeGroup N) :=
    ⟨continuous_induced_rng.mpr (by
      simpa only [Function.comp_def, fvb_gaugeGroup_coe_inv_star] using
        continuous_star.comp continuous_subtype_val)⟩
  haveI : MeasurableMul₂ (GaugeGroup N) := ContinuousMul.measurableMul₂
  haveI : MeasurableInv (GaugeGroup N) := ContinuousInv.measurableInv
  have hEntry := canonicalGaugeEntryMeasurable N
  have h_act : Measurable (fun U : LinkConfig N (2 * M) => wilsonAction N (2 * M) β U) := by
    unfold wilsonAction realTrace
    refine measurable_const.mul (Finset.measurable_sum _ fun x _ =>
      Finset.measurable_sum _ fun μ _ => Finset.measurable_sum _ fun ν _ => ?_)
    refine measurable_const.sub ((Complex.continuous_re.measurable.comp ?_).div_const _)
    unfold plaquetteHolonomy
    have m1 : Measurable (fun U : LinkConfig N (2 * M) => U x μ) :=
      (measurable_pi_apply _).comp (measurable_pi_apply _)
    have m2 : Measurable (fun U : LinkConfig N (2 * M) => U (x + stepDir (2 * M) μ) ν) :=
      (measurable_pi_apply _).comp (measurable_pi_apply _)
    have m3' : Measurable (fun U : LinkConfig N (2 * M) => U (x + stepDir (2 * M) ν) μ) :=
      (measurable_pi_apply μ).comp (measurable_pi_apply (x + stepDir (2 * M) ν))
    have m3 : Measurable (fun U : LinkConfig N (2 * M) => (U (x + stepDir (2 * M) ν) μ)⁻¹) := m3'.inv
    have m4' : Measurable (fun U : LinkConfig N (2 * M) => U x ν) :=
      (measurable_pi_apply ν).comp (measurable_pi_apply x)
    have m4 : Measurable (fun U : LinkConfig N (2 * M) => (U x ν)⁻¹) := m4'.inv
    have mprod := ((m1.mul m2).mul m3).mul m4
    change Measurable (fun U : LinkConfig N (2 * M) =>
      Matrix.trace ((plaquetteHolonomy U x μ ν : GaugeGroup N) :
        Matrix (Fin N) (Fin N) ℂ))
    exact Finset.measurable_sum _ fun k _ => (hEntry k k).comp mprod
  exact h_act.comp (glueConfig_measurable N M)

theorem gluePartitionFn_pos (N M : ℕ) [NeZero N] [NeZero M] {β : ℝ} (hβ : 0 ≤ β) :
    0 < gluePartitionFn N M β := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI := halfVarHaarMeasure_isProbability N M
  let μ := halfVarHaarMeasure N M
  have h_meas := Real.continuous_exp.measurable.comp (glueConfig_action_measurable N M β).neg
  let c : ℝ := Real.exp (-(32 * β * ((Fintype.card (Lat4 (2 * M)) : ℕ) : ℝ)))
  have hc_pos : 0 < c := Real.exp_pos _
  have h_int_inner : ∀ p : HalfVar N M,
      Integrable (fun q : HalfVar N M => Real.exp (-wilsonAction N (2 * M) β (glueConfig p q))) μ := by
    intro p
    refine Integrable.of_bound
      (h_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact (gibbsWeight_pos_le_one hβ _).2)
  have h_inner_lb : ∀ p : HalfVar N M,
      c ≤ ∫ q, Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) ∂μ := by
    intro p
    have hc_int : c = ∫ _q : HalfVar N M, c ∂μ := by simp [integral_const]
    rw [hc_int]
    refine integral_mono (integrable_const _) (h_int_inner p) fun q => ?_
    exact Real.exp_le_exp.mpr (neg_le_neg (wilsonAction_le hβ _))
  have h_int_outer : Integrable (fun p : HalfVar N M =>
      ∫ q, Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) ∂μ) μ := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun p => ?_)
    · exact h_meas.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)]
      have h1 : (1 : ℝ) = ∫ _q : HalfVar N M, (1 : ℝ) ∂μ := by simp [integral_const]
      rw [h1]
      exact integral_mono (h_int_inner p) (integrable_const _) fun q =>
        (gibbsWeight_pos_le_one hβ _).2
  have hc_out : c = ∫ _p : HalfVar N M, c ∂μ := by simp [integral_const]
  refine lt_of_lt_of_le hc_pos ?_
  unfold gluePartitionFn
  rw [hc_out]
  exact integral_mono (integrable_const _) h_int_outer h_inner_lb

/-- Positive half-torus physical coordinate `(a * ((x 0).val + 1), a * centeredCoord ...)`. -/
def posHalfLatSite (M : ℕ) [NeZero M] (a : ℝ) (x : Lat4 (2 * M)) : ContinuumInterfaces.Spacetime4 :=
  (WithLp.equiv 2 (Fin 4 → ℝ)).symm
    (Fin.cons (a * (((x 0).val : ℝ) + 1))
      (fun j : Fin 3 => a * (centeredCoord (2 * M) (x j.succ) : ℝ)))

/-- Evaluation of a positive-time `PosSchwartzSubmodule n` element on `p : HalfVar N M`. -/
noncomputable def evalPosLat (N M : ℕ) [NeZero N] [NeZero M] (a Z_ren : ℝ) :
    ∀ n : ℕ, PosSchwartzSubmodule n → HalfVar N M → ℂ :=
  fun n fn p =>
    letI := Classical.propDecidable
    (Z_ren ^ n * a ^ (4 * n) : ℂ) *
      ∑ xs : Fin n → Lat4 (2 * M),
        if (∀ k : Fin n, ((xs k) 0).val < M) then
          fn.1 (fun k => posHalfLatSite M a (xs k)) *
            (∏ k : Fin n, (spatialPlaqDensity N (2 * M) p.1 (xs k) : ℂ))
        else 0

theorem evalPosLat_vac (N M : ℕ) [NeZero N] [NeZero M] (a Z_ren : ℝ) (p : HalfVar N M) :
    evalPosLat N M a Z_ren 0 ⟨1, Or.inl rfl⟩ p = 1 := by
  unfold evalPosLat
  simp [Finset.univ_unique]

/-- Evaluation of any `F : BorchersPos` on `HalfVar N M`. -/
noncomputable def evalPosBorchers (N M : ℕ) [NeZero N] [NeZero M] (a Z_ren : ℝ)
    (F : BorchersPos) (p : HalfVar N M) : ℂ :=
  F.sum fun n fn => evalPosLat N M a Z_ren n fn p

theorem evalPosBorchers_vac (N M : ℕ) [NeZero N] [NeZero M] (a Z_ren : ℝ) (p : HalfVar N M) :
    evalPosBorchers N M a Z_ren borchersVac p = 1 := by
  unfold evalPosBorchers borchersVac
  rw [DFinsupp.sum_single_index]
  · exact evalPosLat_vac N M a Z_ren p
  · simp [evalPosLat]

theorem evalPosBorchers_add (N M : ℕ) [NeZero N] [NeZero M] (a Z_ren : ℝ)
    (F G : BorchersPos) (p : HalfVar N M) :
    evalPosBorchers N M a Z_ren (F + G) p =
      evalPosBorchers N M a Z_ren F p + evalPosBorchers N M a Z_ren G p := by
  unfold evalPosBorchers
  rw [DFinsupp.sum_add_index]
  · intro n; simp [evalPosLat]
  · intro n a₁ b₁
    unfold evalPosLat
    simp only [Submodule.coe_add, SchwartzMap.add_apply, add_mul]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun xs _ => ?_
    split_ifs <;> simp

theorem evalPosBorchers_smul (N M : ℕ) [NeZero N] [NeZero M] (a Z_ren : ℝ)
    (c : ℂ) (F : BorchersPos) (p : HalfVar N M) :
    evalPosBorchers N M a Z_ren (c • F) p = c * evalPosBorchers N M a Z_ren F p := by
  unfold evalPosBorchers
  simp only [DFinsupp.sum]
  rw [Finset.mul_sum]
  have h_sub : (c • F).support ⊆ F.support := DFinsupp.support_smul c F
  rw [← Finset.sum_subset h_sub]
  · refine Finset.sum_congr rfl fun n _ => ?_
    simp only [DFinsupp.coe_smul, Pi.smul_apply]
    unfold evalPosLat
    simp only [SetLike.val_smul, SchwartzMap.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, ← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun xs _ => ?_
    by_cases h_cond : (∀ k : Fin n, ((xs k) 0).val < M)
    · simp [h_cond]; ring
    · simp [h_cond]
  · intro n _ hn
    have hn0 : c • F n = 0 := by
      by_contra h_ne
      exact hn (DFinsupp.mem_support_iff.mpr (by simpa [DFinsupp.coe_smul, Pi.smul_apply] using h_ne))
    rcases smul_eq_zero.mp hn0 with hc | hFn
    · simp [hc, evalPosLat]
    · simp [hFn, evalPosLat]

private lemma evalPosBorchers_measurable (N M : ℕ) [NeZero N] [NeZero M] (a Z_ren : ℝ) (F : BorchersPos) :
    letI := borel (GaugeGroup N)
    Measurable (evalPosBorchers N M a Z_ren F) := by
  classical
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  haveI : SecondCountableTopology (GaugeGroup N) :=
    Topology.IsInducing.secondCountableTopology
      (⟨rfl⟩ : Topology.IsInducing (Subtype.val : GaugeGroup N → Matrix (Fin N) (Fin N) ℂ))
  haveI : ContinuousInv (GaugeGroup N) :=
    ⟨continuous_induced_rng.mpr (by
      simpa only [Function.comp_def, fvb_gaugeGroup_coe_inv_star] using
        continuous_star.comp continuous_subtype_val)⟩
  haveI : MeasurableMul₂ (GaugeGroup N) := ContinuousMul.measurableMul₂
  haveI : MeasurableInv (GaugeGroup N) := ContinuousInv.measurableInv
  have hEntry := canonicalGaugeEntryMeasurable N
  have h_site : ∀ x : Lat4 (2 * M),
      Measurable (fun p : HalfVar N M => (spatialPlaqDensity N (2 * M) p.1 x : ℂ)) := by
    intro x
    apply Complex.continuous_ofReal.measurable.comp
    unfold spatialPlaqDensity realTrace
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    refine measurable_const.sub ((Complex.continuous_re.measurable.comp ?_).div_const _)
    unfold plaquetteHolonomy
    have ml1 : Measurable (fun p : HalfVar N M => p.1 x i.succ) :=
      (measurable_pi_apply i.succ).comp ((measurable_pi_apply x).comp measurable_fst)
    have ml2 : Measurable (fun p : HalfVar N M => p.1 (x + stepDir (2 * M) i.succ) j.succ) :=
      (measurable_pi_apply j.succ).comp ((measurable_pi_apply (x + stepDir (2 * M) i.succ)).comp measurable_fst)
    have ml3' : Measurable (fun p : HalfVar N M => p.1 (x + stepDir (2 * M) j.succ) i.succ) :=
      (measurable_pi_apply i.succ).comp ((measurable_pi_apply (x + stepDir (2 * M) j.succ)).comp measurable_fst)
    have ml3 : Measurable (fun p : HalfVar N M => (p.1 (x + stepDir (2 * M) j.succ) i.succ)⁻¹) := ml3'.inv
    have ml4' : Measurable (fun p : HalfVar N M => p.1 x j.succ) :=
      (measurable_pi_apply j.succ).comp ((measurable_pi_apply x).comp measurable_fst)
    have ml4 : Measurable (fun p : HalfVar N M => (p.1 x j.succ)⁻¹) := ml4'.inv
    have mprod := ((ml1.mul ml2).mul ml3).mul ml4
    change Measurable (fun p : HalfVar N M =>
      Matrix.trace ((plaquetteHolonomy p.1 x i.succ j.succ : GaugeGroup N) :
        Matrix (Fin N) (Fin N) ℂ))
    exact Finset.measurable_sum _ fun k _ => (hEntry k k).comp mprod
  unfold evalPosBorchers
  simp only [DFinsupp.sum]
  refine Finset.measurable_sum _ fun n _ => ?_
  unfold evalPosLat
  refine measurable_const.mul (Finset.measurable_sum _ fun xs _ => ?_)
  split_ifs
  · exact measurable_const.mul (Finset.measurable_prod _ fun k _ => h_site (xs k))
  · exact measurable_const

private noncomputable def evalPosLatBound (M : ℕ) [NeZero M] (a Z_ren : ℝ)
    (n : ℕ) (fn : PosSchwartzSubmodule n) : ℝ :=
  letI := Classical.propDecidable
  ‖(Z_ren ^ n * a ^ (4 * n) : ℂ)‖ *
    ∑ xs : Fin n → Lat4 (2 * M),
      if (∀ k : Fin n, ((xs k) 0).val < M) then
        ‖fn.1 (fun k => posHalfLatSite M a (xs k))‖ * (18 : ℝ) ^ n
      else 0

private lemma evalPosLat_norm_le (N M : ℕ) [NeZero N] [NeZero M] (a Z_ren : ℝ)
    (n : ℕ) (fn : PosSchwartzSubmodule n) (p : HalfVar N M) :
    ‖evalPosLat N M a Z_ren n fn p‖ ≤ evalPosLatBound M a Z_ren n fn := by
  unfold evalPosLat evalPosLatBound
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun xs _ => ?_)
  split_ifs
  · rw [norm_mul, norm_prod]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ∏ k : Fin n, ‖(spatialPlaqDensity N (2 * M) p.1 (xs k) : ℂ)‖
        ≤ ∏ _k : Fin n, (18 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => by
            rw [Complex.norm_real, Real.norm_of_nonneg (spatialPlaqDensity_bounds N (2 * M) p.1 _).1]
            exact (spatialPlaqDensity_bounds N (2 * M) p.1 _).2
      _ = (18 : ℝ) ^ n := by simp only [Finset.prod_const, Finset.card_fin]
  · simp only [norm_zero, le_refl]

private lemma evalPosBorchers_bounded (N M : ℕ) [NeZero N] [NeZero M] (a Z_ren : ℝ) (F : BorchersPos) :
    ∃ BF : ℝ, 0 ≤ BF ∧ ∀ p : HalfVar N M, ‖evalPosBorchers N M a Z_ren F p‖ ≤ BF := by
  refine ⟨∑ n ∈ F.support, evalPosLatBound M a Z_ren n (F n),
    Finset.sum_nonneg fun n _ => ?_, fun p => ?_⟩
  · unfold evalPosLatBound
    exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun xs _ => by split_ifs <;> positivity)
  · unfold evalPosBorchers DFinsupp.sum
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => evalPosLat_norm_le N M a Z_ren n (F n) p)

private lemma latticeBorchers_integrable (N M : ℕ) [NeZero N] [NeZero M]
    (a : ℝ) {β : ℝ} (hβ : 0 ≤ β) (Z_ren : ℝ) (F G : BorchersPos) :
    letI := borel (GaugeGroup N)
    let μ := halfVarHaarMeasure N M
    Integrable (fun pq : HalfVar N M × HalfVar N M =>
      star (evalPosBorchers N M a Z_ren F pq.1) *
        evalPosBorchers N M a Z_ren G pq.2 *
        (Real.exp (-wilsonAction N (2 * M) β (glueConfig pq.1 pq.2)) : ℂ)) (μ.prod μ) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI := halfVarHaarMeasure_isProbability N M
  obtain ⟨BF, hBF, hFb⟩ := evalPosBorchers_bounded N M a Z_ren F
  obtain ⟨BG, hBG, hGb⟩ := evalPosBorchers_bounded N M a Z_ren G
  have h_meas : Measurable (fun pq : HalfVar N M × HalfVar N M =>
      star (evalPosBorchers N M a Z_ren F pq.1) *
        evalPosBorchers N M a Z_ren G pq.2 *
        (Real.exp (-wilsonAction N (2 * M) β (glueConfig pq.1 pq.2)) : ℂ)) :=
    ((continuous_star.measurable.comp ((evalPosBorchers_measurable N M a Z_ren F).comp measurable_fst)).mul
      ((evalPosBorchers_measurable N M a Z_ren G).comp measurable_snd)).mul
      (Complex.continuous_ofReal.measurable.comp
        (Real.continuous_exp.measurable.comp (glueConfig_action_measurable N M β).neg))
  refine Integrable.of_bound h_meas.aestronglyMeasurable (BF * BG)
    (Filter.Eventually.of_forall fun pq => ?_)
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc ‖evalPosBorchers N M a Z_ren F pq.1‖ * ‖evalPosBorchers N M a Z_ren G pq.2‖ *
        Real.exp (-wilsonAction N (2 * M) β (glueConfig pq.1 pq.2))
      ≤ BF * BG * 1 := mul_le_mul (mul_le_mul (hFb pq.1) (hGb pq.2) (norm_nonneg _) hBF)
          (gibbsWeight_pos_le_one hβ _).2 (Real.exp_pos _).le (mul_nonneg hBF hBG)
    _ = BF * BG := mul_one _

/-- **Canonical Finite-Volume 4D SU(N) Borchers Sesquilinear Form** on `BorchersPos`. -/
noncomputable def latticeBorchersForm (N M : ℕ) [NeZero N] [NeZero M]
    (a β Z_ren : ℝ) (F G : BorchersPos) : ℂ :=
  letI := borel (GaugeGroup N)
  wilsonGlueRPForm N M β (gluePartitionFn N M β) (halfVarHaarMeasure N M)
    (evalPosBorchers N M a Z_ren F) (evalPosBorchers N M a Z_ren G)

/-- **Unconditional Finite-Volume Reflection Positivity of `latticeBorchersForm`.** -/
theorem latticeBorchersForm_nonneg (N M : ℕ) [NeZero N] [NeZero M]
    (a : ℝ) {β : ℝ} (hβ : 0 ≤ β) (Z_ren : ℝ) (F : BorchersPos) :
    0 ≤ (latticeBorchersForm N M a β Z_ren F F).re := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  haveI : SecondCountableTopology (GaugeGroup N) :=
    Topology.IsInducing.secondCountableTopology
      (⟨rfl⟩ : Topology.IsInducing (Subtype.val : GaugeGroup N → Matrix (Fin N) (Fin N) ℂ))
  haveI : ContinuousInv (GaugeGroup N) :=
    ⟨continuous_induced_rng.mpr (by
      simpa only [Function.comp_def, fvb_gaugeGroup_coe_inv_star] using
        continuous_star.comp continuous_subtype_val)⟩
  haveI : MeasurableMul₂ (GaugeGroup N) := ContinuousMul.measurableMul₂
  haveI : MeasurableInv (GaugeGroup N) := ContinuousInv.measurableInv
  haveI := halfVarHaarMeasure_isProbability N M
  obtain ⟨BF, hBF, hFb⟩ := evalPosBorchers_bounded N M a Z_ren F
  exact wilson4D_normalized_rp_nonneg hβ (gluePartitionFn_pos N M hβ)
    (canonicalGaugeEntryMeasurable N) (halfVarHaarMeasure N M)
    (evalPosBorchers N M a Z_ren F) (evalPosBorchers_measurable N M a Z_ren F) BF hBF hFb

/-- **Exact Vacuum Normalization:** `latticeBorchersForm N M a β Z_ren borchersVac borchersVac = 1`. -/
theorem latticeBorchersForm_vac (N M : ℕ) [NeZero N] [NeZero M]
    (a : ℝ) {β : ℝ} (hβ : 0 ≤ β) (Z_ren : ℝ) :
    latticeBorchersForm N M a β Z_ren borchersVac borchersVac = 1 := by
  letI := borel (GaugeGroup N)
  have hZ := gluePartitionFn_pos N M hβ
  unfold latticeBorchersForm wilsonGlueRPForm
  have hvac : evalPosBorchers N M a Z_ren borchersVac = fun _ => 1 :=
    funext (evalPosBorchers_vac N M a Z_ren)
  rw [hvac]
  simp only [star_one, one_mul]
  have h_in : ∀ p : HalfVar N M,
      (∫ q : HalfVar N M, (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂(halfVarHaarMeasure N M)) =
      ((∫ q : HalfVar N M, Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) ∂(halfVarHaarMeasure N M) : ℝ) : ℂ) :=
    fun p => integral_ofReal
  have h_in_fn : (fun p : HalfVar N M =>
      ∫ q : HalfVar N M, (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂(halfVarHaarMeasure N M)) =
      fun p : HalfVar N M =>
        ((∫ q : HalfVar N M, Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) ∂(halfVarHaarMeasure N M) : ℝ) : ℂ) :=
    funext h_in
  rw [h_in_fn]
  have h_out : (∫ p : HalfVar N M,
      ((∫ q : HalfVar N M, Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) ∂(halfVarHaarMeasure N M) : ℝ) : ℂ)
      ∂(halfVarHaarMeasure N M)) =
      ((∫ p : HalfVar N M,
        ∫ q : HalfVar N M, Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) ∂(halfVarHaarMeasure N M)
        ∂(halfVarHaarMeasure N M) : ℝ) : ℂ) :=
    integral_ofReal
  rw [h_out]
  change ((gluePartitionFn N M β)⁻¹ : ℂ) * (gluePartitionFn N M β : ℂ) = 1
  exact_mod_cast inv_mul_cancel₀ hZ.ne'

/-- **Unconditional Sesquilinearity of `latticeBorchersForm` on `BorchersPos`.** -/
theorem latticeBorchersForm_sesquilinear (N M : ℕ) [NeZero N] [NeZero M]
    (a : ℝ) {β : ℝ} (hβ : 0 ≤ β) (Z_ren : ℝ) :
    (∀ F₁ F₂ G : BorchersPos,
      latticeBorchersForm N M a β Z_ren (F₁ + F₂) G =
        latticeBorchersForm N M a β Z_ren F₁ G + latticeBorchersForm N M a β Z_ren F₂ G) ∧
    (∀ (c : ℂ) (F G : BorchersPos),
      latticeBorchersForm N M a β Z_ren (c • F) G =
        star c * latticeBorchersForm N M a β Z_ren F G) ∧
    (∀ F G₁ G₂ : BorchersPos,
      latticeBorchersForm N M a β Z_ren F (G₁ + G₂) =
        latticeBorchersForm N M a β Z_ren F G₁ + latticeBorchersForm N M a β Z_ren F G₂) ∧
    (∀ (c : ℂ) (F G : BorchersPos),
      latticeBorchersForm N M a β Z_ren F (c • G) =
        c * latticeBorchersForm N M a β Z_ren F G) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI := halfVarHaarMeasure_isProbability N M
  let μ := halfVarHaarMeasure N M
  have h_int_p : ∀ F G p,
      Integrable (fun q : HalfVar N M =>
        star (evalPosBorchers N M a Z_ren F p) * evalPosBorchers N M a Z_ren G q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) μ := by
    intro F G p
    obtain ⟨BF, hBF, hFb⟩ := evalPosBorchers_bounded N M a Z_ren F
    obtain ⟨BG, hBG, hGb⟩ := evalPosBorchers_bounded N M a Z_ren G
    refine Integrable.of_bound ?_ (BF * BG) (Filter.Eventually.of_forall fun q => ?_)
    · exact ((measurable_const.mul (evalPosBorchers_measurable N M a Z_ren G)).mul
        (Complex.continuous_ofReal.measurable.comp
          (Real.continuous_exp.measurable.comp
            ((glueConfig_action_measurable N M β).comp (measurable_const.prodMk measurable_id)).neg))).aestronglyMeasurable
    · rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc ‖evalPosBorchers N M a Z_ren F p‖ * ‖evalPosBorchers N M a Z_ren G q‖ *
            Real.exp (-wilsonAction N (2 * M) β (glueConfig p q))
          ≤ BF * BG * 1 := mul_le_mul (mul_le_mul (hFb p) (hGb q) (norm_nonneg _) hBF)
              (gibbsWeight_pos_le_one hβ _).2 (Real.exp_pos _).le (mul_nonneg hBF hBG)
        _ = BF * BG := mul_one _
  have h_int_outer : ∀ F G,
      Integrable (fun p : HalfVar N M =>
        ∫ q, star (evalPosBorchers N M a Z_ren F p) * evalPosBorchers N M a Z_ren G q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) μ := by
    intro F G
    exact (latticeBorchers_integrable N M a hβ Z_ren F G).integral_prod_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F₁ F₂ G
    unfold latticeBorchersForm wilsonGlueRPForm
    have h_in : ∀ p : HalfVar N M,
        (∫ q, star (evalPosBorchers N M a Z_ren (F₁ + F₂) p) * evalPosBorchers N M a Z_ren G q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) =
        (∫ q, star (evalPosBorchers N M a Z_ren F₁ p) * evalPosBorchers N M a Z_ren G q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) +
        (∫ q, star (evalPosBorchers N M a Z_ren F₂ p) * evalPosBorchers N M a Z_ren G q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) := by
      intro p
      have h_eq : (fun q => star (evalPosBorchers N M a Z_ren (F₁ + F₂) p) *
            evalPosBorchers N M a Z_ren G q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) =
          fun q => (star (evalPosBorchers N M a Z_ren F₁ p) * evalPosBorchers N M a Z_ren G q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) +
            (star (evalPosBorchers N M a Z_ren F₂ p) * evalPosBorchers N M a Z_ren G q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) := by
        funext q; rw [evalPosBorchers_add, star_add]; ring
      rw [h_eq]
      exact integral_add (h_int_p F₁ G p) (h_int_p F₂ G p)
    rw [show (fun p => _) = _ from funext h_in]
    rw [integral_add (h_int_outer F₁ G) (h_int_outer F₂ G), mul_add]
  · intro c F G
    unfold latticeBorchersForm wilsonGlueRPForm
    have h_in : ∀ p : HalfVar N M,
        (∫ q, star (evalPosBorchers N M a Z_ren (c • F) p) * evalPosBorchers N M a Z_ren G q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) =
        star c * (∫ q, star (evalPosBorchers N M a Z_ren F p) * evalPosBorchers N M a Z_ren G q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) := by
      intro p
      have h_eq : (fun q => star (evalPosBorchers N M a Z_ren (c • F) p) *
            evalPosBorchers N M a Z_ren G q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) =
          fun q => star c * (star (evalPosBorchers N M a Z_ren F p) *
            evalPosBorchers N M a Z_ren G q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) := by
        funext q; rw [evalPosBorchers_smul, star_mul]; ring
      rw [h_eq, integral_const_mul]
    rw [show (fun p => _) = _ from funext h_in]
    rw [integral_const_mul]
    ring
  · intro F G₁ G₂
    unfold latticeBorchersForm wilsonGlueRPForm
    have h_in : ∀ p : HalfVar N M,
        (∫ q, star (evalPosBorchers N M a Z_ren F p) * evalPosBorchers N M a Z_ren (G₁ + G₂) q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) =
        (∫ q, star (evalPosBorchers N M a Z_ren F p) * evalPosBorchers N M a Z_ren G₁ q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) +
        (∫ q, star (evalPosBorchers N M a Z_ren F p) * evalPosBorchers N M a Z_ren G₂ q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) := by
      intro p
      have h_eq : (fun q => star (evalPosBorchers N M a Z_ren F p) *
            evalPosBorchers N M a Z_ren (G₁ + G₂) q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) =
          fun q => (star (evalPosBorchers N M a Z_ren F p) * evalPosBorchers N M a Z_ren G₁ q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) +
            (star (evalPosBorchers N M a Z_ren F p) * evalPosBorchers N M a Z_ren G₂ q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) := by
        funext q; rw [evalPosBorchers_add]; ring
      rw [h_eq]
      exact integral_add (h_int_p F G₁ p) (h_int_p F G₂ p)
    rw [show (fun p => _) = _ from funext h_in]
    rw [integral_add (h_int_outer F G₁) (h_int_outer F G₂), mul_add]
  · intro c F G
    unfold latticeBorchersForm wilsonGlueRPForm
    have h_in : ∀ p : HalfVar N M,
        (∫ q, star (evalPosBorchers N M a Z_ren F p) * evalPosBorchers N M a Z_ren (c • G) q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) =
        c * (∫ q, star (evalPosBorchers N M a Z_ren F p) * evalPosBorchers N M a Z_ren G q *
          (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ) := by
      intro p
      have h_eq : (fun q => star (evalPosBorchers N M a Z_ren F p) *
            evalPosBorchers N M a Z_ren (c • G) q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) =
          fun q => c * (star (evalPosBorchers N M a Z_ren F p) *
            evalPosBorchers N M a Z_ren G q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ)) := by
        funext q; rw [evalPosBorchers_smul]; ring
      rw [h_eq, integral_const_mul]
    rw [show (fun p => _) = _ from funext h_in]
    rw [integral_const_mul]
    ring

/-- **Unconditional Finite-Volume Hermitian Symmetry of `latticeBorchersForm`.** -/
theorem latticeBorchersForm_herm (N M : ℕ) [NeZero N] [NeZero M]
    (a : ℝ) {β : ℝ} (hβ : 0 ≤ β) (Z_ren : ℝ) (F G : BorchersPos) :
    latticeBorchersForm N M a β Z_ren G F = star (latticeBorchersForm N M a β Z_ren F G) := by
  letI := borel (GaugeGroup N)
  haveI : BorelSpace (GaugeGroup N) := ⟨rfl⟩
  haveI := halfVarHaarMeasure_isProbability N M
  unfold latticeBorchersForm wilsonGlueRPForm
  rw [star_mul, Complex.star_def, map_inv₀, Complex.conj_ofReal, mul_comm _ ((gluePartitionFn N M β : ℂ)⁻¹)]
  congr 1
  have h_sw :
      (∫ p : HalfVar N M, ∫ q : HalfVar N M,
          (starRingEnd ℂ) (evalPosBorchers N M a Z_ren G p) * evalPosBorchers N M a Z_ren F q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂(halfVarHaarMeasure N M) ∂(halfVarHaarMeasure N M)) =
        (∫ q : HalfVar N M, ∫ p : HalfVar N M,
          (starRingEnd ℂ) (evalPosBorchers N M a Z_ren G p) * evalPosBorchers N M a Z_ren F q *
            (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂(halfVarHaarMeasure N M) ∂(halfVarHaarMeasure N M)) := by
    simpa only [Complex.star_def] using
      integral_integral_swap (latticeBorchers_integrable N M a hβ Z_ren G F)
  rw [h_sw]
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  dsimp only
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  dsimp only
  rw [wilsonAction_glueConfig_symm N M β p q, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- **Unconditional Finite-Volume Cauchy–Schwarz Inequality** on `BorchersPos`. -/
theorem latticeBorchersForm_cauchy_schwarz (N M : ℕ) [NeZero N] [NeZero M]
    (a : ℝ) {β : ℝ} (hβ : 0 ≤ β) (Z_ren : ℝ) (F G : BorchersPos) :
    ‖latticeBorchersForm N M a β Z_ren F G‖ ^ 2 ≤
      (latticeBorchersForm N M a β Z_ren F F).re *
      (latticeBorchersForm N M a β Z_ren G G).re := by
  let B := latticeBorchersForm N M a β Z_ren
  obtain ⟨h_add1, h_smul1, h_add2, h_smul2⟩ := latticeBorchersForm_sesquilinear N M a hβ Z_ren
  have h_quad : ∀ u v : ℂ,
      0 ≤ (star u * u * B F F + star u * v * B F G +
           star v * u * star (B F G) + star v * v * B G G).re := by
    intro u v
    have h_nn := latticeBorchersForm_nonneg N M a hβ Z_ren (u • F + v • G)
    simp only [h_add1, h_add2, h_smul1, h_smul2,
      latticeBorchersForm_herm N M a hβ Z_ren F G] at h_nn
    change 0 ≤ (star u * u * B F F + star u * v * B F G +
         star v * u * star (B F G) + star v * v * B G G).re at *
    convert h_nn using 2
    ring
  have hFF_nn : 0 ≤ (B F F).re := latticeBorchersForm_nonneg N M a hβ Z_ren F
  have hGG_nn : 0 ≤ (B G G).re := latticeBorchersForm_nonneg N M a hβ Z_ren G
  have h_re_real : ∀ (r : ℝ) (z : ℂ), (((r : ℂ) * z)).re = r * z.re := by
    intro r z; simp
  have h_nsq_self : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, RCLike.star_def, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq z
  by_cases hFF0 : (B F F).re = 0
  · by_cases hFG0 : ‖B F G‖ = 0
    · rw [hFG0]; simp; positivity
    · exfalso
      let r : ℝ := -((B G G).re + 1) / (2 * ‖B F G‖ ^ 2)
      have hq := h_quad ((r : ℂ) * B F G) 1
      have h1 : star ((r : ℂ) * B F G) * ((r : ℂ) * B F G) =
          (((r * ‖B F G‖) ^ 2 : ℝ) : ℂ) := by
        rw [star_mul, Complex.star_def, Complex.conj_ofReal]
        calc (star (B F G) * (r : ℂ)) * ((r : ℂ) * B F G)
            = ((r : ℂ) * (r : ℂ)) * (star (B F G) * B F G) := by ring
          _ = ((r ^ 2 : ℝ) : ℂ) * ((‖B F G‖ ^ 2 : ℝ) : ℂ) := by
              rw [h_nsq_self]; push_cast; ring
          _ = (((r * ‖B F G‖) ^ 2 : ℝ) : ℂ) := by push_cast; ring
      have h2 : star ((r : ℂ) * B F G) * 1 * B F G = ((r * ‖B F G‖ ^ 2 : ℝ) : ℂ) := by
        rw [star_mul, Complex.star_def, Complex.conj_ofReal, mul_one]
        calc (star (B F G) * (r : ℂ)) * B F G = (r : ℂ) * (star (B F G) * B F G) := by ring
          _ = ((r * ‖B F G‖ ^ 2 : ℝ) : ℂ) := by rw [h_nsq_self]; push_cast; rfl
      have h3 : star (1 : ℂ) * ((r : ℂ) * B F G) * star (B F G) =
          ((r * ‖B F G‖ ^ 2 : ℝ) : ℂ) := by
        rw [star_one, one_mul, mul_assoc, mul_comm (B F G), h_nsq_self]
        push_cast; rfl
      rw [h1, h2, h3] at hq
      simp only [star_one, one_mul, Complex.add_re, h_re_real, hFF0, mul_zero, zero_add,
        Complex.ofReal_re] at hq
      have hFG2 : 0 < 2 * ‖B F G‖ ^ 2 := by positivity
      have hr : 2 * (r * ‖B F G‖ ^ 2) = -((B G G).re + 1) := by
        dsimp [r]; field_simp [hFG2.ne']
      linarith
  · have hFF_pos : 0 < (B F F).re := lt_of_le_of_ne hFF_nn (Ne.symm hFF0)
    have hq := h_quad (B F G) (-((B F F).re : ℂ))
    have h1 : star (B F G) * B F G = ((‖B F G‖ ^ 2 : ℝ) : ℂ) := h_nsq_self _
    have h2 : star (B F G) * (-((B F F).re : ℂ)) * B F G =
        ((-(B F F).re * ‖B F G‖ ^ 2 : ℝ) : ℂ) := by
      calc star (B F G) * (-((B F F).re : ℂ)) * B F G
          = (-((B F F).re : ℂ)) * (star (B F G) * B F G) := by ring
        _ = ((-(B F F).re * ‖B F G‖ ^ 2 : ℝ) : ℂ) := by rw [h1]; push_cast; ring
    have h3 : star (-((B F F).re : ℂ)) * B F G * star (B F G) =
        ((-(B F F).re * ‖B F G‖ ^ 2 : ℝ) : ℂ) := by
      rw [star_neg, Complex.star_def, Complex.conj_ofReal]
      calc (-((B F F).re : ℂ)) * B F G * star (B F G)
          = (-((B F F).re : ℂ)) * (star (B F G) * B F G) := by ring
        _ = ((-(B F F).re * ‖B F G‖ ^ 2 : ℝ) : ℂ) := by rw [h1]; push_cast; ring
    have h4 : star (-((B F F).re : ℂ)) * (-((B F F).re : ℂ)) =
        (((B F F).re ^ 2 : ℝ) : ℂ) := by
      rw [star_neg, Complex.star_def, Complex.conj_ofReal]
      push_cast; ring
    rw [h1, h2, h3, h4] at hq
    simp only [Complex.add_re, h_re_real, Complex.ofReal_re] at hq
    have h_factor : 0 ≤ (B F F).re * ((B F F).re * (B G G).re - ‖B F G‖ ^ 2) := by
      linarith
    nlinarith

end Imscribing.YangMills.CanonicalFVBorchers4D

