import Imscribing.YangMills.AsymptoticFreedomAndOSClosure
import Imscribing.YangMills.ConcreteSchwartzShiftAndReflect
import Imscribing.YangMills.ConcreteSchwartzReflectOps
import Imscribing.YangMills.BorchersPairingFromSchwinger
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section

namespace Imscribing.YangMills.ConcreteTensorSchwartz

open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.BorchersSchwinger
open Imscribing.YangMills.ConcreteSchwartzShiftAndReflect
open Imscribing.YangMills.ConcreteReflectOps

def projLeft (m n : ℕ) :
    (Fin (m + n) → Spacetime4) →L[ℝ] (Fin m → Spacetime4) where
  toFun x k := x (Fin.castAdd n k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_pi fun k => continuous_apply (Fin.castAdd n k)

def projRight (m n : ℕ) :
    (Fin (m + n) → Spacetime4) →L[ℝ] (Fin n → Spacetime4) where
  toFun x k := x (Fin.natAdd m k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_pi fun k => continuous_apply (Fin.natAdd m k)

private lemma projLeft_opNorm_le (m n : ℕ) : ‖projLeft m n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, Pi.norm_def]
    refine NNReal.coe_le_coe.mpr (Finset.sup_le fun k _ => ?_)
    exact Finset.le_sup (f := fun i => ‖x i‖₊) (Finset.mem_univ (Fin.castAdd n k))

private lemma projRight_opNorm_le (m n : ℕ) : ‖projRight m n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, Pi.norm_def]
    refine NNReal.coe_le_coe.mpr (Finset.sup_le fun k _ => ?_)
    exact Finset.le_sup (f := fun i => ‖x i‖₊) (Finset.mem_univ (Fin.natAdd m k))

private lemma norm_le_projLeft_add_projRight (m n : ℕ) (x : Fin (m + n) → Spacetime4) :
    ‖x‖ ≤ ‖projLeft m n x‖ + ‖projRight m n x‖ := by
  rw [Pi.norm_def]
  change ((Finset.univ.sup fun b => ‖x b‖₊ : NNReal) : ℝ) ≤ ((‖projLeft m n x‖₊ + ‖projRight m n x‖₊ : NNReal) : ℝ)
  refine NNReal.coe_le_coe.mpr (Finset.sup_le fun k _ => ?_)
  by_cases hk : k.val < m
  · have h_eq : k = Fin.castAdd n ⟨k.val, hk⟩ := Fin.ext rfl
    rw [h_eq]
    have hle : (‖projLeft m n x ⟨k.val, hk⟩‖₊ : ℝ) ≤ ‖projLeft m n x‖ :=
      norm_le_pi_norm (projLeft m n x) ⟨k.val, hk⟩
    exact_mod_cast le_trans hle (le_add_of_nonneg_right (norm_nonneg _))
  · have hm : m ≤ k.val := Nat.le_of_not_lt hk
    have hk_lt : k.val - m < n := by omega
    have h_eq : k = Fin.natAdd m ⟨k.val - m, hk_lt⟩ := by
      ext; simp [Nat.add_sub_cancel' hm]
    rw [h_eq]
    have hle : (‖projRight m n x ⟨k.val - m, hk_lt⟩‖₊ : ℝ) ≤ ‖projRight m n x‖ :=
      norm_le_pi_norm (projRight m n x) ⟨k.val - m, hk_lt⟩
    exact_mod_cast le_trans hle (le_add_of_nonneg_left (norm_nonneg _))

private lemma iteratedFDeriv_comp_clm' {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F) (f : F → G) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : ℕ) (x : E) :
    iteratedFDeriv ℝ l (fun y => f (L y)) x =
      (iteratedFDeriv ℝ l f (L x)).compContinuousLinearMap (fun _ => L) := by
  induction l generalizing x with
  | zero => ext; simp
  | succ l ih =>
    ext v
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
    have h_fun : iteratedFDeriv ℝ l (fun z => f (L z)) =
        fun y => (iteratedFDeriv ℝ l f (L y)).compContinuousLinearMap (fun _ => L) := funext ih
    have h_diff : Differentiable ℝ (iteratedFDeriv ℝ l f) :=
      (hf.iteratedFDeriv_right (m := 1) (i := l)
        (by exact_mod_cast (le_top : (1 + l : ℕ∞) ≤ ⊤))).differentiable one_ne_zero
    let Φ_lin : ContinuousMultilinearMap ℝ (fun _ : Fin l => F) G →ₗ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E) G :=
      { toFun := fun M => M.compContinuousLinearMap (fun _ => L)
        map_add' := fun M₁ M₂ => by ext w; simp
        map_smul' := fun c M => by ext w; simp }
    let Φ : ContinuousMultilinearMap ℝ (fun _ : Fin l => F) G →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E) G :=
      LinearMap.mkContinuous Φ_lin (‖L‖ ^ l) fun M => by
        simpa [Φ_lin, mul_comm] using M.norm_compContinuousLinearMap_le (fun _ => L)
    have h_comp : HasFDerivAt (fun y => Φ (iteratedFDeriv ℝ l f (L y)))
        (Φ.comp ((fderiv ℝ (iteratedFDeriv ℝ l f) (L x)).comp L)) x :=
      Φ.hasFDerivAt.comp x ((h_diff (L x)).hasFDerivAt.comp x L.hasFDerivAt)
    rw [h_fun]
    change fderiv ℝ (fun y => Φ (iteratedFDeriv ℝ l f (L y))) x (v 0) (Fin.tail v) = _
    rw [h_comp.fderiv]
    simp [Φ, Φ_lin]
    rfl

/-- Tensor product of two Schwartz functions `f : EuclideanSchwartz m` and `g : EuclideanSchwartz n`. -/
def tensorSchwartz {m n : ℕ} (f : EuclideanSchwartz m) (g : EuclideanSchwartz n) :
    EuclideanSchwartz (m + n) where
  toFun x := f (projLeft m n x) * g (projRight m n x)
  smooth' := (f.smooth'.comp (projLeft m n).contDiff).mul (g.smooth'.comp (projRight m n).contDiff)
  decay' k l := by
    refine ⟨∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (l + 1),
      (k.choose j : ℝ) * (l.choose i : ℝ) *
        SchwartzMap.seminorm ℂ j i f * SchwartzMap.seminorm ℂ (k - j) (l - i) g, fun x => ?_⟩
    have hl_top : (l : WithTop ℕ∞) ≤ (⊤ : ℕ∞) := by exact_mod_cast (le_top : (l : ℕ∞) ≤ ⊤)
    have hf_smooth : ContDiff ℝ l (fun y => f (projLeft m n y)) :=
      (f.smooth'.comp (projLeft m n).contDiff).of_le hl_top
    have hg_smooth : ContDiff ℝ l (fun y => g (projRight m n y)) :=
      (g.smooth'.comp (projRight m n).contDiff).of_le hl_top
    have h_leib :
        ‖iteratedFDeriv ℝ l (fun y => f (projLeft m n y) * g (projRight m n y)) x‖ ≤
          ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y => f (projLeft m n y)) x‖ *
            ‖iteratedFDeriv ℝ (l - i) (fun y => g (projRight m n y)) x‖ :=
      norm_iteratedFDeriv_mul_le hf_smooth hg_smooth x le_rfl
    have h_f_norm : ∀ i, ‖iteratedFDeriv ℝ i (fun y => f (projLeft m n y)) x‖ ≤
        ‖iteratedFDeriv ℝ i f (projLeft m n x)‖ := by
      intro i
      rw [iteratedFDeriv_comp_clm' (projLeft m n) (⇑f) f.smooth' i x]
      calc ‖(iteratedFDeriv ℝ i f (projLeft m n x)).compContinuousLinearMap (fun _ => projLeft m n)‖
          ≤ ‖iteratedFDeriv ℝ i f (projLeft m n x)‖ * ∏ _t : Fin i, ‖projLeft m n‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖iteratedFDeriv ℝ i f (projLeft m n x)‖ * ∏ _t : Fin i, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Finset.prod_le_prod (fun _ _ => norm_nonneg (projLeft m n))
                fun _ _ => projLeft_opNorm_le m n)
              (norm_nonneg (iteratedFDeriv ℝ i f (projLeft m n x)))
        _ = ‖iteratedFDeriv ℝ i f (projLeft m n x)‖ := by simp
    have h_g_norm : ∀ i, ‖iteratedFDeriv ℝ i (fun y => g (projRight m n y)) x‖ ≤
        ‖iteratedFDeriv ℝ i g (projRight m n x)‖ := by
      intro i
      rw [iteratedFDeriv_comp_clm' (projRight m n) (⇑g) g.smooth' i x]
      calc ‖(iteratedFDeriv ℝ i g (projRight m n x)).compContinuousLinearMap (fun _ => projRight m n)‖
          ≤ ‖iteratedFDeriv ℝ i g (projRight m n x)‖ * ∏ _t : Fin i, ‖projRight m n‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖iteratedFDeriv ℝ i g (projRight m n x)‖ * ∏ _t : Fin i, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Finset.prod_le_prod (fun _ _ => norm_nonneg (projRight m n))
                fun _ _ => projRight_opNorm_le m n)
              (norm_nonneg (iteratedFDeriv ℝ i g (projRight m n x)))
        _ = ‖iteratedFDeriv ℝ i g (projRight m n x)‖ := by simp
    have h_xk : ‖x‖ ^ k ≤ ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ‖projLeft m n x‖ ^ j * ‖projRight m n x‖ ^ (k - j) := by
      calc ‖x‖ ^ k ≤ (‖projLeft m n x‖ + ‖projRight m n x‖) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_le_projLeft_add_projRight m n x) k
        _ = ∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ) * ‖projLeft m n x‖ ^ j * ‖projRight m n x‖ ^ (k - j) := by
            rw [add_pow]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    have h_l_bd :
        ‖iteratedFDeriv ℝ l (fun y => f (projLeft m n y) * g (projRight m n y)) x‖ ≤
          ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i f (projLeft m n x)‖ *
            ‖iteratedFDeriv ℝ (l - i) g (projRight m n x)‖ := by
      refine le_trans h_leib (Finset.sum_le_sum fun i _ => ?_)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (h_f_norm i) (Nat.cast_nonneg _))
        (h_g_norm (l - i)) (norm_nonneg _) (by positivity)
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => f (projLeft m n y) * g (projRight m n y)) x‖
        ≤ (∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ) * ‖projLeft m n x‖ ^ j * ‖projRight m n x‖ ^ (k - j)) *
            (∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i f (projLeft m n x)‖ *
              ‖iteratedFDeriv ℝ (l - i) g (projRight m n x)‖) :=
          mul_le_mul h_xk h_l_bd (norm_nonneg _) (Finset.sum_nonneg fun j _ => by positivity)
      _ = ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (l + 1),
            (k.choose j : ℝ) * (l.choose i : ℝ) *
              (‖projLeft m n x‖ ^ j * ‖iteratedFDeriv ℝ i f (projLeft m n x)‖) *
              (‖projRight m n x‖ ^ (k - j) * ‖iteratedFDeriv ℝ (l - i) g (projRight m n x)‖) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (l + 1),
            (k.choose j : ℝ) * (l.choose i : ℝ) *
              SchwartzMap.seminorm ℂ j i f * SchwartzMap.seminorm ℂ (k - j) (l - i) g := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => ?_
          have hf_s : ‖projLeft m n x‖ ^ j * ‖iteratedFDeriv ℝ i f (projLeft m n x)‖ ≤
              SchwartzMap.seminorm ℂ j i f := SchwartzMap.le_seminorm ℂ j i f (projLeft m n x)
          have hg_s : ‖projRight m n x‖ ^ (k - j) * ‖iteratedFDeriv ℝ (l - i) g (projRight m n x)‖ ≤
              SchwartzMap.seminorm ℂ (k - j) (l - i) g :=
            SchwartzMap.le_seminorm ℂ (k - j) (l - i) g (projRight m n x)
          have hmul : (‖projLeft m n x‖ ^ j * ‖iteratedFDeriv ℝ i f (projLeft m n x)‖) *
              (‖projRight m n x‖ ^ (k - j) * ‖iteratedFDeriv ℝ (l - i) g (projRight m n x)‖) ≤
              SchwartzMap.seminorm ℂ j i f * SchwartzMap.seminorm ℂ (k - j) (l - i) g :=
            mul_le_mul hf_s hg_s (by positivity) (apply_nonneg _ _)
          have hconst : 0 ≤ (k.choose j : ℝ) * (l.choose i : ℝ) := by positivity
          calc (k.choose j : ℝ) * (l.choose i : ℝ) *
                (‖projLeft m n x‖ ^ j * ‖iteratedFDeriv ℝ i f (projLeft m n x)‖) *
                (‖projRight m n x‖ ^ (k - j) * ‖iteratedFDeriv ℝ (l - i) g (projRight m n x)‖)
              = ((k.choose j : ℝ) * (l.choose i : ℝ)) *
                  ((‖projLeft m n x‖ ^ j * ‖iteratedFDeriv ℝ i f (projLeft m n x)‖) *
                    (‖projRight m n x‖ ^ (k - j) * ‖iteratedFDeriv ℝ (l - i) g (projRight m n x)‖)) := by ring
            _ ≤ ((k.choose j : ℝ) * (l.choose i : ℝ)) *
                  (SchwartzMap.seminorm ℂ j i f * SchwartzMap.seminorm ℂ (k - j) (l - i) g) :=
                mul_le_mul_of_nonneg_left hmul hconst
            _ = (k.choose j : ℝ) * (l.choose i : ℝ) *
                  SchwartzMap.seminorm ℂ j i f * SchwartzMap.seminorm ℂ (k - j) (l - i) g := by ring

private def timeShiftVec (n : ℕ) (t : ℝ) : Fin n → Spacetime4 :=
  fun _ => t • stdBasis4 0

private lemma timeShiftVec_add (n : ℕ) (s t : ℝ) :
    timeShiftVec n (s + t) = timeShiftVec n s + timeShiftVec n t := by
  ext k μ; simp [timeShiftVec, add_smul]

private lemma timeShiftVec_norm_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖timeShiftVec n t‖ ≤ t := by
  by_cases hn : n = 0
  · subst hn
    have h0 : timeShiftVec 0 t = 0 := by ext k; exact k.elim0
    rw [h0, norm_zero]
    exact ht
  · rw [Pi.norm_def, show t = ((⟨t, ht⟩ : NNReal) : ℝ) from rfl]
    refine NNReal.coe_le_coe.mpr (Finset.sup_le fun k _ => ?_)
    have hk : ‖timeShiftVec n t k‖ = t := by
      dsimp [timeShiftVec]
      rw [norm_smul, Real.norm_of_nonneg ht]
      have hb : ‖stdBasis4 0‖ = 1 := by
        rw [EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_four]
      rw [hb, mul_one]
    exact_mod_cast hk.le

private lemma timeShift_mem_pos {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (f : PosSchwartzSubmodule n) :
    ConcreteSchwartzShiftAndReflect.shiftPos (timeShiftVec n t) f.1 ∈ PosSchwartzSubmodule n := by
  rcases f.2 with rfl | hpos
  · exact Or.inl rfl
  · right
    intro x hx i
    have h1 := hpos (x - timeShiftVec n t) hx i
    simp only [Pi.sub_apply, timeShiftVec, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      stdBasis4_apply, ↓reduceIte, mul_one] at h1
    linarith

private def concreteShiftPos (t : ℝ) (n : ℕ) :
    PosSchwartzSubmodule n →ₗ[ℂ] PosSchwartzSubmodule n :=
  if ht : 0 ≤ t then
    { toFun := fun f => ⟨ConcreteSchwartzShiftAndReflect.shiftPos (timeShiftVec n t) f.1,
        timeShift_mem_pos ht f⟩
      map_add' := fun f g => by ext x; rfl
      map_smul' := fun c f => by ext x; rfl }
  else LinearMap.id

/-- Concrete reflection-positive tensor product data on `SchwartzMap`. -/
noncomputable def concreteReflectTensorData : ReflectTensorData where
  reflectConj := ConcreteReflectOps.reflectConjSchwartz
  reflectConj_zero_one := by ext x; change (starRingEnd ℂ) (1 : ℂ) = 1; exact map_one _
  reflectConj_add := ConcreteReflectOps.reflectConjSchwartz_add
  reflectConj_smul := ConcreteReflectOps.reflectConjSchwartz_smul
  reflectConj_seminorm_le := fun m j f => by
    refine SchwartzMap.seminorm_le_bound ℂ j 0 (ConcreteReflectOps.reflectConjSchwartz m f)
      (apply_nonneg _ _) fun x => ?_
    simp only [norm_iteratedFDeriv_zero, ConcreteReflectOps.reflectConjSchwartz_apply, norm_star]
    rw [← ConcreteReflectOps.euclidTimeReflect_norm m x]
    simpa [norm_iteratedFDeriv_zero] using
      SchwartzMap.le_seminorm ℂ j 0 f (ConcreteReflectOps.euclidTimeReflect m x)
  tensor := @tensorSchwartz
  tensor_zero_one := by ext x; change (1 : ℂ) * 1 = 1; exact one_mul 1
  tensor_add_left := fun m n f₁ f₂ g => by ext x; exact add_mul (f₁ (projLeft m n x)) (f₂ (projLeft m n x)) (g (projRight m n x))
  tensor_smul_left := fun m n c f g => by ext x; exact mul_assoc c (f (projLeft m n x)) (g (projRight m n x))
  tensor_add_right := fun m n f g₁ g₂ => by ext x; exact mul_add (f (projLeft m n x)) (g₁ (projRight m n x)) (g₂ (projRight m n x))
  tensor_smul_right := fun m n c f g => by ext x; change f (projLeft m n x) * (c * g (projRight m n x)) = c * (f (projLeft m n x) * g (projRight m n x)); ring
  tensor_seminorm_le := fun m n k => by
    refine ⟨∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ),
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _, fun f g => ?_⟩
    have h_bd : 0 ≤ (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) *
        (∑ j ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ j 0 f) *
        (∑ j ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ j 0 g) := by
      refine mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        (Finset.sum_nonneg fun _ _ => apply_nonneg _ _))
        (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
    refine SchwartzMap.seminorm_le_bound ℂ k 0 (tensorSchwartz f g) h_bd fun x => ?_
    simp only [norm_iteratedFDeriv_zero]
    change ‖x‖ ^ k * ‖f (projLeft m n x) * g (projRight m n x)‖ ≤ _
    rw [norm_mul]
    have h_xk : ‖x‖ ^ k ≤ ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ‖projLeft m n x‖ ^ j * ‖projRight m n x‖ ^ (k - j) := by
      calc ‖x‖ ^ k ≤ (‖projLeft m n x‖ + ‖projRight m n x‖) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_le_projLeft_add_projRight m n x) k
        _ = ∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ) * ‖projLeft m n x‖ ^ j * ‖projRight m n x‖ ^ (k - j) := by
            rw [add_pow]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    calc ‖x‖ ^ k * (‖f (projLeft m n x)‖ * ‖g (projRight m n x)‖)
        ≤ (∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ) * ‖projLeft m n x‖ ^ j * ‖projRight m n x‖ ^ (k - j)) *
            (‖f (projLeft m n x)‖ * ‖g (projRight m n x)‖) :=
          mul_le_mul_of_nonneg_right h_xk (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
            ((‖projLeft m n x‖ ^ j * ‖f (projLeft m n x)‖) *
              (‖projRight m n x‖ ^ (k - j) * ‖g (projRight m n x)‖)) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
            (SchwartzMap.seminorm ℂ j 0 f * SchwartzMap.seminorm ℂ (k - j) 0 g) := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_
            (by positivity) (apply_nonneg _ _)) (Nat.cast_nonneg _)
          · simpa [norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℂ j 0 f (projLeft m n x)
          · simpa [norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℂ (k - j) 0 g (projRight m n x)
      _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
            ((∑ a ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ a 0 f) *
              (∑ b ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ b 0 g)) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (mul_le_mul
            (Finset.single_le_sum (f := fun a => SchwartzMap.seminorm ℂ a 0 f) (fun a _ => apply_nonneg _ _) hj)
            (Finset.single_le_sum (f := fun b => SchwartzMap.seminorm ℂ b 0 g) (fun b _ => apply_nonneg _ _)
              (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)))
            (apply_nonneg _ _)
            (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)) (Nat.cast_nonneg _)
      _ = (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) *
            (∑ j ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ j 0 f) *
            (∑ j ∈ Finset.range (k + 1), SchwartzMap.seminorm ℂ j 0 g) := by
          rw [← Finset.sum_mul]; ring
  shiftPos := concreteShiftPos
  shiftPos_vac := fun t ht => by
    refine Subtype.ext (DFunLike.ext _ _ fun x => ?_)
    simp only [concreteShiftPos, dif_pos ht, LinearMap.coe_mk, AddHom.coe_mk,
      ConcreteSchwartzShiftAndReflect.shiftPos]
    rfl
  shiftPos_add := fun s t hs ht n f => by
    have hst : 0 ≤ s + t := add_nonneg hs ht
    refine Subtype.ext (DFunLike.ext _ _ fun x => ?_)
    simp only [concreteShiftPos, dif_pos hst, dif_pos hs, dif_pos ht, LinearMap.coe_mk,
      AddHom.coe_mk, ConcreteSchwartzShiftAndReflect.shiftPos, timeShiftVec_add]
    change f.1 (x - (timeShiftVec n s + timeShiftVec n t)) =
      f.1 ((x - timeShiftVec n s) - timeShiftVec n t)
    congr 1
    abel
  shiftPos_seminorm_le := fun n k f => by
    let C_s : ℝ := ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * SchwartzMap.seminorm ℂ i 0 f.1
    refine ⟨C_s, Finset.sum_nonneg fun i _ =>
      mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _), fun t ht j hj => ?_⟩
    have h_bd : 0 ≤ C_s * (1 + t) ^ k :=
      mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
        (pow_nonneg (by linarith) _)
    refine SchwartzMap.seminorm_le_bound ℂ j 0 (concreteShiftPos t n f).1 h_bd fun x => ?_
    have hfx : (concreteShiftPos t n f).1 x = f.1 (x - timeShiftVec n t) := by
      simp only [concreteShiftPos, dif_pos ht, LinearMap.coe_mk, AddHom.coe_mk,
        ConcreteSchwartzShiftAndReflect.shiftPos]
      exact congrArg f.1 (by abel)
    rw [norm_iteratedFDeriv_zero, hfx]
    have hnx : ‖x‖ ^ j ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖x - timeShiftVec n t‖ ^ i * ‖timeShiftVec n t‖ ^ (j - i) := by
      have htri : ‖x‖ ≤ ‖x - timeShiftVec n t‖ + ‖timeShiftVec n t‖ := by
        simpa [sub_add_cancel] using norm_add_le (x - timeShiftVec n t) (timeShiftVec n t)
      calc ‖x‖ ^ j ≤ (‖x - timeShiftVec n t‖ + ‖timeShiftVec n t‖) ^ j :=
            pow_le_pow_left₀ (norm_nonneg _) htri j
        _ = ∑ i ∈ Finset.range (j + 1),
              (j.choose i : ℝ) * ‖x - timeShiftVec n t‖ ^ i * ‖timeShiftVec n t‖ ^ (j - i) := by
            rw [add_pow]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    calc ‖x‖ ^ j * ‖f.1 (x - timeShiftVec n t)‖
        ≤ (∑ i ∈ Finset.range (j + 1),
              (j.choose i : ℝ) * ‖x - timeShiftVec n t‖ ^ i * ‖timeShiftVec n t‖ ^ (j - i)) *
            ‖f.1 (x - timeShiftVec n t)‖ :=
          mul_le_mul_of_nonneg_right hnx (norm_nonneg _)
      _ = ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * ‖timeShiftVec n t‖ ^ (j - i) *
              (‖x - timeShiftVec n t‖ ^ i * ‖f.1 (x - timeShiftVec n t)‖) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ ≤ ∑ i ∈ Finset.range (j + 1),
            (k.choose i : ℝ) * (1 + t) ^ k * SchwartzMap.seminorm ℂ i 0 f.1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h_ch : (j.choose i : ℝ) ≤ (k.choose i : ℝ) :=
            Nat.cast_le.mpr (Nat.choose_le_choose i hj)
          have h_tv : ‖timeShiftVec n t‖ ^ (j - i) ≤ (1 + t) ^ k := by
            have hle1 : ‖timeShiftVec n t‖ ≤ 1 + t := le_trans (timeShiftVec_norm_le n ht) (by linarith)
            have hle2 : ‖timeShiftVec n t‖ ^ (j - i) ≤ (1 + t) ^ (j - i) :=
              pow_le_pow_left₀ (norm_nonneg _) hle1 (j - i)
            have h1t : 1 ≤ 1 + t := by linarith
            have hexp : j - i ≤ k := le_trans (Nat.sub_le j i) hj
            exact le_trans hle2 (pow_le_pow_right₀ h1t hexp)
          have h_sf : ‖x - timeShiftVec n t‖ ^ i * ‖f.1 (x - timeShiftVec n t)‖ ≤
              SchwartzMap.seminorm ℂ i 0 f.1 := by
            simpa [norm_iteratedFDeriv_zero] using
              SchwartzMap.le_seminorm ℂ i 0 f.1 (x - timeShiftVec n t)
          exact mul_le_mul (mul_le_mul h_ch h_tv (by positivity) (Nat.cast_nonneg _)) h_sf
            (by positivity) (by positivity)
      _ ≤ ∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * (1 + t) ^ k * SchwartzMap.seminorm ℂ i 0 f.1 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.add_le_add_right hj 1)) ?_
          intro i _ _
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
            (apply_nonneg _ _)
      _ = C_s * (1 + t) ^ k := by
          dsimp [C_s]; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; ring

theorem concreteReflectTensorData_shiftPos_zero (n : ℕ) (f : PosSchwartzSubmodule n) :
    concreteReflectTensorData.shiftPos 0 n f = f := by
  refine Subtype.ext (DFunLike.ext _ _ fun x => ?_)
  have h0 : timeShiftVec n 0 = 0 := by ext k μ; simp [timeShiftVec]
  have hfx : (concreteShiftPos 0 n f).1 x = f.1 (x - timeShiftVec n 0) := by
    simp only [concreteShiftPos, dif_pos le_rfl, LinearMap.coe_mk, AddHom.coe_mk,
      ConcreteSchwartzShiftAndReflect.shiftPos]
    rfl
  change (concreteShiftPos 0 n f).1 x = f.1 x
  rw [hfx, h0, sub_zero]

theorem concreteReflectTensorData_shiftPos_coe {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (f : PosSchwartzSubmodule n) :
    (concreteReflectTensorData.shiftPos t n f).1 =
      ConcreteSchwartzShiftAndReflect.shiftPos (fun _ => t • stdBasis4 0) f.1 := by
  ext x
  have hfx : (concreteShiftPos t n f).1 x = f.1 (x - timeShiftVec n t) := by
    simp only [concreteShiftPos, dif_pos ht, LinearMap.coe_mk, AddHom.coe_mk,
      ConcreteSchwartzShiftAndReflect.shiftPos]
    rfl
  change (concreteShiftPos t n f).1 x = f.1 (x - fun _ => t • stdBasis4 0)
  rw [hfx]
  rfl

end Imscribing.YangMills.ConcreteTensorSchwartz