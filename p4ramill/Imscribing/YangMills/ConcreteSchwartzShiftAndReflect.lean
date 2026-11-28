
import Imscribing.YangMills.AsymptoticFreedomAndOSClosure
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

namespace Imscribing.YangMills.ConcreteSchwartzShiftAndReflect

open Imscribing.YangMills.ContinuumInterfaces

/-- Standard basis vector `e_μ` in `Spacetime4 = EuclideanSpace ℝ (Fin 4)`. -/
def stdBasis4 (μ : Fin 4) : Spacetime4 :=
  (WithLp.equiv 2 (Fin 4 → ℝ)).symm (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)

@[simp]
lemma stdBasis4_apply (μ ν : Fin 4) : stdBasis4 μ ν = if ν = μ then 1 else 0 := by
  change (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν = _
  simp [Pi.single_apply]

/-- Translation of a Schwartz function by a constant vector `v`. -/
def shiftPos {n : ℕ} (v : Fin n → Spacetime4) (f : EuclideanSchwartz n) :
    EuclideanSchwartz n where
  toFun x := f (x - v)
  smooth' := f.smooth'.comp (contDiff_id.sub contDiff_const)
  decay' k l := by
    have h_eq : ∀ x, iteratedFDeriv ℝ l (fun y => f (y - v)) x = iteratedFDeriv ℝ l f (x - v) := by
      induction l with
      | zero => intro x; ext; simp
      | succ l ih =>
        intro x
        ext L
        rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
        have h_fun : iteratedFDeriv ℝ l (fun z => f (z - v)) =
            fun y => iteratedFDeriv ℝ l f (y - v) := funext ih
        have h_smooth : ContDiff ℝ (⊤ : ℕ∞) (⇑f) := f.smooth'
        have h_diff : Differentiable ℝ (iteratedFDeriv ℝ l (⇑f)) :=
          (h_smooth.iteratedFDeriv_right (m := 1) (i := l)
            (by exact_mod_cast (le_top : (1 + l : ℕ∞) ≤ ⊤))).differentiable one_ne_zero
        have h_has : HasFDerivAt (fun y => iteratedFDeriv ℝ l (⇑f) (y - v))
            ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x - v)).comp
              (ContinuousLinearMap.id ℝ (Fin n → Spacetime4))) x :=
          (h_diff (x - v)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const v)
        rw [h_fun]
        simp only [Function.comp_apply]
        rw [h_has.fderiv]
        simp
    refine ⟨∑ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * ‖v‖ ^ (k - j) * SchwartzMap.seminorm ℂ j l f, fun x => ?_⟩
    rw [h_eq x]
    have hnx : ‖x‖ ^ k ≤ ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ‖x - v‖ ^ j * ‖v‖ ^ (k - j) := by
      have htri : ‖x‖ ≤ ‖x - v‖ + ‖v‖ := by
        simpa [sub_add_cancel] using norm_add_le (x - v) v
      calc ‖x‖ ^ k ≤ (‖x - v‖ + ‖v‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) htri k
        _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ‖x - v‖ ^ j * ‖v‖ ^ (k - j) := by
          rw [add_pow]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l f (x - v)‖
        ≤ (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ‖x - v‖ ^ j * ‖v‖ ^ (k - j)) *
            ‖iteratedFDeriv ℝ l f (x - v)‖ :=
          mul_le_mul_of_nonneg_right hnx (norm_nonneg _)
      _ = ∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℝ) * ‖v‖ ^ (k - j) * (‖x - v‖ ^ j * ‖iteratedFDeriv ℝ l f (x - v)‖) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ ≤ ∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℝ) * ‖v‖ ^ (k - j) * SchwartzMap.seminorm ℂ j l f := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa using SchwartzMap.le_seminorm ℂ j l f (x - v)

/-- Continuous linear map negating the Euclidean time coordinate `0` of every point. -/
def timeReflectCLM (n : ℕ) : (Fin n → Spacetime4) →L[ℝ] (Fin n → Spacetime4) where
  toFun x k := x k - (2 * x k 0) • stdBasis4 0
  map_add' x y := by
    ext k μ
    simp only [Pi.add_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      stdBasis4_apply]
    ring
  map_smul' c x := by
    ext k μ
    simp only [Pi.smul_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, RingHom.id_apply,
      stdBasis4_apply]
    ring
  cont := by
    refine continuous_pi fun k => ?_
    exact (continuous_apply k).sub
      ((continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).comp
        (continuous_apply k))).smul continuous_const)

private lemma timeReflectCLM_norm_eq (n : ℕ) (x : Fin n → Spacetime4) :
    ‖timeReflectCLM n x‖ = ‖x‖ := by
  have h_pt : ∀ k : Fin n, ‖timeReflectCLM n x k‖ = ‖x k‖ := by
    intro k
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Fin.sum_univ_four, timeReflectCLM, LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.coe_mk', PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, stdBasis4_apply,
      Fin.isValue, ↓reduceIte]
    have h10 : (1 : Fin 4) ≠ 0 := by decide
    have h20 : (2 : Fin 4) ≠ 0 := by decide
    have h30 : (3 : Fin 4) ≠ 0 := by decide
    simp only [if_neg h10, if_neg h20, if_neg h30, mul_zero, sub_zero, mul_one,
      Real.norm_eq_abs, sq_abs]
    ring
  rw [Pi.norm_def, Pi.norm_def]
  congr 1
  refine Finset.sup_congr rfl fun k _ => ?_
  exact NNReal.coe_injective (h_pt k)

private lemma timeReflectCLM_opNorm_le (n : ℕ) : ‖timeReflectCLM n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, timeReflectCLM_norm_eq]

private lemma iteratedFDeriv_comp_clm {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F) (f : F → G) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : ℕ) (x : E) :
    iteratedFDeriv ℝ l (fun y => f (L y)) x =
      (iteratedFDeriv ℝ l f (L x)).compContinuousLinearMap (fun _ => L) := by
  induction l generalizing x with
  | zero => ext; simp
  | succ l ih =>
    ext m
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
    have h_fun : iteratedFDeriv ℝ l (fun z => f (L z)) =
        fun y => (iteratedFDeriv ℝ l f (L y)).compContinuousLinearMap (fun _ => L) := funext ih
    have h_diff : Differentiable ℝ (iteratedFDeriv ℝ l f) :=
      (hf.iteratedFDeriv_right (m := 1) (i := l)
        (by exact_mod_cast (le_top : (1 + l : ℕ∞) ≤ ⊤))).differentiable one_ne_zero
    let Φ_lin : ContinuousMultilinearMap ℝ (fun _ : Fin l => F) G →ₗ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E) G :=
      { toFun := fun M => M.compContinuousLinearMap (fun _ => L)
        map_add' := fun M₁ M₂ => by ext v; simp
        map_smul' := fun c M => by ext v; simp }
    let Φ : ContinuousMultilinearMap ℝ (fun _ : Fin l => F) G →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E) G :=
      LinearMap.mkContinuous Φ_lin (‖L‖ ^ l) fun M => by
        simpa [Φ_lin, mul_comm] using M.norm_compContinuousLinearMap_le (fun _ => L)
    have h_comp : HasFDerivAt (fun y => Φ (iteratedFDeriv ℝ l f (L y)))
        (Φ.comp ((fderiv ℝ (iteratedFDeriv ℝ l f) (L x)).comp L)) x :=
      Φ.hasFDerivAt.comp x ((h_diff (L x)).hasFDerivAt.comp x L.hasFDerivAt)
    rw [h_fun]
    change fderiv ℝ (fun y => Φ (iteratedFDeriv ℝ l f (L y))) x (m 0) (Fin.tail m) = _
    rw [h_comp.fderiv]
    simp [Φ, Φ_lin]
    rfl

/-- Euclidean time-reflection on `EuclideanSchwartz n`. -/
def timeReflect {n : ℕ} (f : EuclideanSchwartz n) : EuclideanSchwartz n where
  toFun x := f (timeReflectCLM n x)
  smooth' := f.smooth'.comp (timeReflectCLM n).contDiff
  decay' k l := by
    refine ⟨SchwartzMap.seminorm ℂ k l f, fun x => ?_⟩
    rw [iteratedFDeriv_comp_clm (timeReflectCLM n) (⇑f) f.smooth' l x]
    have h1 : ‖(iteratedFDeriv ℝ l f (timeReflectCLM n x)).compContinuousLinearMap
        (fun _ => timeReflectCLM n)‖ ≤ ‖iteratedFDeriv ℝ l f (timeReflectCLM n x)‖ := by
      calc ‖(iteratedFDeriv ℝ l f (timeReflectCLM n x)).compContinuousLinearMap
            (fun _ => timeReflectCLM n)‖
          ≤ ‖iteratedFDeriv ℝ l f (timeReflectCLM n x)‖ * ∏ _i : Fin l, ‖timeReflectCLM n‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖iteratedFDeriv ℝ l f (timeReflectCLM n x)‖ * ∏ _i : Fin l, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Finset.prod_le_prod (fun _ _ => norm_nonneg (timeReflectCLM n))
                fun _ _ => timeReflectCLM_opNorm_le n)
              (norm_nonneg (iteratedFDeriv ℝ l f (timeReflectCLM n x)))
        _ = ‖iteratedFDeriv ℝ l f (timeReflectCLM n x)‖ := by simp
    calc ‖x‖ ^ k * ‖(iteratedFDeriv ℝ l f (timeReflectCLM n x)).compContinuousLinearMap
          (fun _ => timeReflectCLM n)‖
        ≤ ‖timeReflectCLM n x‖ ^ k * ‖iteratedFDeriv ℝ l f (timeReflectCLM n x)‖ := by
          rw [timeReflectCLM_norm_eq]
          exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (norm_nonneg x) k)
      _ ≤ SchwartzMap.seminorm ℂ k l f := SchwartzMap.le_seminorm ℂ k l f (timeReflectCLM n x)

private lemma iteratedFDeriv_conj_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (l : ℕ) (x : E) :
    iteratedFDeriv ℝ l (fun y => star (g y)) x =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap (iteratedFDeriv ℝ l g x) := by
  induction l generalizing x with
  | zero => ext; simp [Complex.star_def]
  | succ l ih =>
    ext m
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
    have h_fun : iteratedFDeriv ℝ l (fun z => star (g z)) =
        fun y => (Complex.conjCLE : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap
          (iteratedFDeriv ℝ l g y) := funext ih
    have h_diff : Differentiable ℝ (iteratedFDeriv ℝ l g) :=
      (hg.iteratedFDeriv_right (m := 1) (i := l)
        (by exact_mod_cast (le_top : (1 + l : ℕ∞) ≤ ⊤))).differentiable one_ne_zero
    let Φ_lin : ContinuousMultilinearMap ℝ (fun _ : Fin l => E) ℂ →ₗ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E) ℂ :=
      { toFun := fun M => (Complex.conjCLE : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap M
        map_add' := fun M₁ M₂ => by ext v; simp
        map_smul' := fun c M => by ext v; simp }
    have h_conj_le : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by simp [Complex.conjCLE_apply]
    let Φ : ContinuousMultilinearMap ℝ (fun _ : Fin l => E) ℂ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E) ℂ :=
      LinearMap.mkContinuous Φ_lin 1 fun M => by
        calc ‖Φ_lin M‖ ≤ ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ * ‖M‖ :=
              ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
          _ ≤ 1 * ‖M‖ := mul_le_mul_of_nonneg_right h_conj_le (norm_nonneg M)
    have h_comp : HasFDerivAt (fun y => Φ (iteratedFDeriv ℝ l g y))
        (Φ.comp (fderiv ℝ (iteratedFDeriv ℝ l g) x)) x :=
      Φ.hasFDerivAt.comp x (h_diff x).hasFDerivAt
    rw [h_fun]
    change fderiv ℝ (fun y => Φ (iteratedFDeriv ℝ l g y)) x (m 0) (Fin.tail m) = _
    rw [h_comp.fderiv]
    simp [Φ, Φ_lin]

/-- Euclidean time-reflection followed by complex conjugation on `EuclideanSchwartz n`. -/
def reflectConjSchwartz (n : ℕ) (f : EuclideanSchwartz n) : EuclideanSchwartz n where
  toFun x := star ((timeReflect f) x)
  smooth' := (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (timeReflect f).smooth'
  decay' k l := by
    refine ⟨SchwartzMap.seminorm ℂ k l (timeReflect f), fun x => ?_⟩
    rw [iteratedFDeriv_conj_left (⇑(timeReflect f)) (timeReflect f).smooth' l x]
    have h1 : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ l (timeReflect f) x)‖ ≤ ‖iteratedFDeriv ℝ l (timeReflect f) x‖ := by
      calc ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap
            (iteratedFDeriv ℝ l (timeReflect f) x)‖
          ≤ ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ * ‖iteratedFDeriv ℝ l (timeReflect f) x‖ :=
            ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ 1 * ‖iteratedFDeriv ℝ l (timeReflect f) x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
              simp [Complex.conjCLE_apply]
        _ = ‖iteratedFDeriv ℝ l (timeReflect f) x‖ := one_mul _
    calc ‖x‖ ^ k * ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap
          (iteratedFDeriv ℝ l (timeReflect f) x)‖
        ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (timeReflect f) x‖ :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (norm_nonneg x) _)
      _ ≤ SchwartzMap.seminorm ℂ k l (timeReflect f) :=
          SchwartzMap.le_seminorm ℂ k l (timeReflect f) x

end Imscribing.YangMills.ConcreteSchwartzShiftAndReflect