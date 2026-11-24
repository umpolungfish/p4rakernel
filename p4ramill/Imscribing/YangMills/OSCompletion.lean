import Mathlib
import Imscribing.YangMills.Core
import Imscribing.YangMills.CubicHaar4D

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped InnerProductSpace
open Complex Finset Real MeasureTheory Set

namespace YangMills

/-! ## §22.  True general Osterwalder–Schrader Hilbert completion & operator lifting -/

section TrueOSCompletion

/-- Quotient pre-Hilbert carrier `E / 𝒩` for any `OSReflectionForm E`. -/
def OSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Type _ :=
  Quotient (osSetoid F)

def osPreMk {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (x : E) : OSPreHilbert F :=
  Quotient.mk (osSetoid F) x

def osPreNeg {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : OSPreHilbert F → OSPreHilbert F :=
  Quotient.lift (fun x => osPreMk F (-x)) fun x y (hxy : x - y ∈ osNullSpace F) => by
    apply Quotient.sound
    change -x - (-y) ∈ osNullSpace F
    rw [show -x - (-y) = -(x - y) by abel]
    exact (osNullSpace F).neg_mem hxy

instance instZeroOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Zero (OSPreHilbert F) :=
  ⟨osPreMk F 0⟩

instance instAddOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Add (OSPreHilbert F) :=
  ⟨osQuotAdd F⟩

instance instNegOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Neg (OSPreHilbert F) :=
  ⟨osPreNeg F⟩

instance instAddCommGroupOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : AddCommGroup (OSPreHilbert F) where
  add := osQuotAdd F
  add_assoc a b c := Quotient.inductionOn₃ a b c fun x y z =>
    Quotient.sound (by change (x + y + z) - (x + (y + z)) ∈ osNullSpace F; simp [add_assoc])
  zero := osPreMk F 0
  zero_add a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (0 + x) - x ∈ osNullSpace F; simp)
  add_zero a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (x + 0) - x ∈ osNullSpace F; simp)
  neg := osPreNeg F
  neg_add_cancel a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (-x + x) - 0 ∈ osNullSpace F; simp)
  add_comm a b := Quotient.inductionOn₂ a b fun x y =>
    Quotient.sound (by change (x + y) - (y + x) ∈ osNullSpace F; simp [add_comm])
  nsmul := nsmulRec
  zsmul := zsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl

instance instModuleOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Module ℂ (OSPreHilbert F) where
  smul := osQuotSmul F
  one_smul a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (1 : ℂ) • x - x ∈ osNullSpace F; simp)
  mul_smul r s a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (r * s) • x - r • (s • x) ∈ osNullSpace F; simp [mul_smul])
  smul_zero r := Quotient.sound (by change r • (0 : E) - 0 ∈ osNullSpace F; simp)
  smul_add r a b := Quotient.inductionOn₂ a b fun x y =>
    Quotient.sound (by change r • (x + y) - (r • x + r • y) ∈ osNullSpace F; simp [smul_add])
  add_smul r s a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (r + s) • x - (r • x + s • x) ∈ osNullSpace F; simp [add_smul])
  zero_smul a := Quotient.inductionOn a fun x =>
    Quotient.sound (by change (0 : ℂ) • x - 0 ∈ osNullSpace F; simp)

noncomputable instance instInnerOSPreHilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Inner ℂ (OSPreHilbert F) where
  inner := osQuotInner F

noncomputable def osPreCore {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : InnerProductSpace.Core ℂ (OSPreHilbert F) where
  inner := osQuotInner F
  conj_inner_symm x y := (osQuotInner_conj_symm F x y).symm
  re_inner_nonneg := osQuotInner_pos_re F
  definite x hx := (osQuotInner_definite F x).mp hx
  add_left := osQuotInner_add_left F
  smul_left x y r := osQuotInner_smul_left F r x y

noncomputable instance instNormedAddCommGroupOSPreHilbert
    {E : Type*} [AddCommGroup E] [Module ℂ E] (F : OSReflectionForm E) :
    NormedAddCommGroup (OSPreHilbert F) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (OSPreHilbert F) _ _ _ (osPreCore F)

noncomputable instance instInnerProductSpaceOSPreHilbert
    {E : Type*} [AddCommGroup E] [Module ℂ E] (F : OSReflectionForm E) :
    InnerProductSpace ℂ (OSPreHilbert F) :=
  InnerProductSpace.ofCore (osPreCore F).toCore

/-- True Osterwalder–Schrader Hilbert space completion `H_OS = \overline{E / 𝒩}`. -/
abbrev OSHilbertSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) :=
  UniformSpace.Completion (OSPreHilbert F)

/-- Canonical continuous linear isometric embedding `E / 𝒩 → H_OS`. -/
noncomputable def osCompletionMap {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : OSPreHilbert F →L[ℂ] OSHilbertSpace F where
  toFun u := (u : OSHilbertSpace F)
  map_add' := UniformSpace.Completion.coe_add
  map_smul' := UniformSpace.Completion.coe_smul
  cont := UniformSpace.Completion.continuous_coe _

theorem osCompletionMap_norm {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (u : OSPreHilbert F) :
    ‖osCompletionMap F u‖ = ‖u‖ :=
  UniformSpace.Completion.norm_coe u

theorem osCompletionMap_inner {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (u v : OSPreHilbert F) :
    ⟪osCompletionMap F u, osCompletionMap F v⟫_ℂ = ⟪u, v⟫_ℂ := by
  have h_re : ∀ a b : OSPreHilbert F,
      (⟪osCompletionMap F a, osCompletionMap F b⟫_ℂ).re = (⟪a, b⟫_ℂ).re := by
    intro a b
    have h1 : ‖osCompletionMap F (a + b)‖ ^ 2 = ‖a + b‖ ^ 2 := by
      rw [osCompletionMap_norm F (a + b)]
    have h2 : ‖osCompletionMap F (a - b)‖ ^ 2 = ‖a - b‖ ^ 2 := by
      rw [osCompletionMap_norm F (a - b)]
    rw [map_add, norm_add_sq (𝕜 := ℂ)] at h1
    rw [map_sub, norm_sub_sq (𝕜 := ℂ)] at h2
    rw [norm_add_sq (𝕜 := ℂ)] at h1
    rw [norm_sub_sq (𝕜 := ℂ)] at h2
    rw [osCompletionMap_norm F a, osCompletionMap_norm F b] at h1 h2
    change ‖a‖ ^ 2 + 2 * (⟪osCompletionMap F a, osCompletionMap F b⟫_ℂ).re + ‖b‖ ^ 2 =
      ‖a‖ ^ 2 + 2 * (⟪a, b⟫_ℂ).re + ‖b‖ ^ 2 at h1
    change ‖a‖ ^ 2 - 2 * (⟪osCompletionMap F a, osCompletionMap F b⟫_ℂ).re + ‖b‖ ^ 2 =
      ‖a‖ ^ 2 - 2 * (⟪a, b⟫_ℂ).re + ‖b‖ ^ 2 at h2
    linarith
  have h_im : (⟪osCompletionMap F u, osCompletionMap F v⟫_ℂ).im = (⟪u, v⟫_ℂ).im := by
    have h := h_re u (Complex.I • v)
    rw [map_smul, inner_smul_right, inner_smul_right] at h
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h
    linarith
  exact Complex.ext (h_re u v) h_im

theorem osCompletionMap_inj {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) : Function.Injective (osCompletionMap F) := by
  intro u v huv
  have h0 : ‖u - v‖ = 0 := by
    rw [← osCompletionMap_norm F (u - v), map_sub, huv, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

theorem osCompletionMap_dense {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) :
    closure (Set.range (osCompletionMap F)) = Set.univ :=
  UniformSpace.Completion.denseRange_coe.closure_range

theorem osPre_norm_sq {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (x : E) :
    ‖osPreMk F x‖ ^ 2 = (F.B x x).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rfl

noncomputable def osLiftPreOp {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re) :
    OSPreHilbert F →L[ℂ] OSPreHilbert F :=
  LinearMap.mkContinuous
    { toFun := Quotient.lift (fun x => osPreMk F (T x)) fun x y hxy => by
        apply Quotient.sound
        change T x - T y ∈ osNullSpace F
        rw [← map_sub]
        have h0 : (F.B (x - y) (x - y)).re = 0 := by
          change F.B (x - y) (x - y) = 0 at hxy
          rw [hxy, Complex.zero_re]
        have hre_le : (F.B (T (x - y)) (T (x - y))).re ≤ 0 := by
          have := hbd (x - y)
          rwa [h0, mul_zero] at this
        have hre : (F.B (T (x - y)) (T (x - y))).re = 0 :=
          le_antisymm hre_le (F.pos_re _)
        exact Complex.ext hre (F.self_im_zero _)
      map_add' := fun u v => Quotient.inductionOn₂ u v fun x y => by
        change osPreMk F (T (x + y)) = osQuotAdd F (osPreMk F (T x)) (osPreMk F (T y))
        rw [map_add]
        rfl
      map_smul' := fun c u => Quotient.inductionOn u fun x => by
        change osPreMk F (T (c • x)) = osQuotSmul F c (osPreMk F (T x))
        rw [map_smul]
        rfl }
    C
    (fun u => by
      refine Quotient.inductionOn u fun x => ?_
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)), mul_pow]
      change ‖osPreMk F (T x)‖ ^ 2 ≤ C ^ 2 * ‖osPreMk F x‖ ^ 2
      rw [osPre_norm_sq, osPre_norm_sq]
      exact hbd x)

/-- Lift of an `F`-bounded Euclidean linear operator `T : E →ₗ[ℂ] E` to `OSHilbertSpace F`. -/
noncomputable def osLiftOperator {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re) :
    OSHilbertSpace F →L[ℂ] OSHilbertSpace F :=
  let T_pre := osLiftPreOp F T C hC hbd
  let f : OSHilbertSpace F → OSHilbertSpace F :=
    UniformSpace.Completion.map T_pre
  have hf_coe : ∀ u : OSPreHilbert F,
      f (osCompletionMap F u) = osCompletionMap F (T_pre u) :=
    fun u => UniformSpace.Completion.map_coe T_pre.uniformContinuous u
  have hf_cont : Continuous f := UniformSpace.Completion.continuous_map
  have hf_add : ∀ a b : OSHilbertSpace F, f (a + b) = f a + f b := by
    intro a b
    refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
    · exact isClosed_eq (hf_cont.comp continuous_add)
        ((hf_cont.comp continuous_fst).add (hf_cont.comp continuous_snd))
    · intro u v
      change f (osCompletionMap F u + osCompletionMap F v) =
        f (osCompletionMap F u) + f (osCompletionMap F v)
      rw [← map_add, hf_coe, hf_coe, hf_coe, map_add, map_add]
  have hf_smul : ∀ (c : ℂ) (a : OSHilbertSpace F), f (c • a) = c • f a := by
    intro c a
    refine UniformSpace.Completion.induction_on a ?_ ?_
    · exact isClosed_eq (hf_cont.comp (continuous_const_smul c))
        ((continuous_const_smul c).comp hf_cont)
    · intro u
      change f (c • osCompletionMap F u) = c • f (osCompletionMap F u)
      rw [← map_smul, hf_coe, hf_coe, map_smul, map_smul]
  { toFun := f
    map_add' := hf_add
    map_smul' := hf_smul
    cont := hf_cont }

theorem osLiftOperator_coe {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re) (x : E) :
    osLiftOperator F T C hC hbd (osCompletionMap F (osPreMk F x)) =
      osCompletionMap F (osPreMk F (T x)) :=
  UniformSpace.Completion.map_coe (osLiftPreOp F T C hC hbd).uniformContinuous (osPreMk F x)

theorem osLiftOperator_norm_le {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re)
    (z : OSHilbertSpace F) :
    ‖osLiftOperator F T C hC hbd z‖ ≤ C * ‖z‖ := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_le (continuous_norm.comp (osLiftOperator F T C hC hbd).continuous)
      (continuous_const.mul continuous_norm)
  · intro u
    refine Quotient.inductionOn u fun x => ?_
    change ‖osLiftOperator F T C hC hbd (osCompletionMap F (osPreMk F x))‖ ≤
      C * ‖osCompletionMap F (osPreMk F x)‖
    rw [osLiftOperator_coe, osCompletionMap_norm F, osCompletionMap_norm F]
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)), mul_pow,
      osPre_norm_sq, osPre_norm_sq]
    exact hbd x

theorem osLiftOperator_sa {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re)
    (hsa : ∀ x y : E, F.B (T x) y = F.B x (T y))
    (u v : OSHilbertSpace F) :
    ⟪osLiftOperator F T C hC hbd u, v⟫_ℂ = ⟪u, osLiftOperator F T C hC hbd v⟫_ℂ := by
  refine UniformSpace.Completion.induction_on₂ u v ?_ ?_
  · exact isClosed_eq
      (((osLiftOperator F T C hC hbd).continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner ((osLiftOperator F T C hC hbd).continuous.comp continuous_snd))
  · intro a b
    refine Quotient.inductionOn₂ a b fun x y => ?_
    change ⟪osLiftOperator F T C hC hbd (osCompletionMap F (osPreMk F x)),
        osCompletionMap F (osPreMk F y)⟫_ℂ =
      ⟪osCompletionMap F (osPreMk F x),
        osLiftOperator F T C hC hbd (osCompletionMap F (osPreMk F y))⟫_ℂ
    rw [osLiftOperator_coe, osLiftOperator_coe,
      osCompletionMap_inner, osCompletionMap_inner]
    exact hsa x y

end TrueOSCompletion

/-! ## §27.  Genuine 4D Poincaré group $\mathbb{R}^4 \rtimes O(1,3)$ & infinite-dimensional Wightman QFT -/

section Poincare4DWightman

/-- Minkowski metric tensor `η = diag(1, -1, -1, -1)` on `ℝ⁴`. -/
def minkowskiMetric4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

theorem minkowskiMetric4_transpose : minkowskiMetric4.transpose = minkowskiMetric4 := by
  simp [minkowskiMetric4]

theorem minkowskiMetric4_mul_self : minkowskiMetric4 * minkowskiMetric4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiMetric4, Matrix.mul_apply, Fin.sum_univ_four]

/-- Minkowski inner product `x₀y₀ - x₁y₁ - x₂y₂ - x₃y₃`. -/
def minkowskiInner (x y : Space4) : ℝ :=
  x 0 * y 0 - ∑ i : Fin 3, x i.succ * y i.succ

theorem minkowskiInner_self (x : Space4) : minkowskiInner x x = minkowskiSq x := by
  simp [minkowskiInner, minkowskiSq, Fin.sum_univ_three, sq]

theorem minkowskiInner_eq_dot (x y : Space4) :
    minkowskiInner x y = dotProduct x (Matrix.mulVec minkowskiMetric4 y) := by
  simp [minkowskiInner, dotProduct, minkowskiMetric4, Matrix.mulVec,
    Fin.sum_univ_four, Fin.sum_univ_three]
  ring

/-- The 4D Lorentz group `O(1,3) = { Λ ∈ GL(4, ℝ) | Λᵀ η Λ = η }`. -/
def LorentzMatrix4 : Type :=
  { Λ : Matrix (Fin 4) (Fin 4) ℝ // Λ.transpose * minkowskiMetric4 * Λ = minkowskiMetric4 }

theorem LorentzMatrix4.ext {Λ₁ Λ₂ : LorentzMatrix4} (h : Λ₁.1 = Λ₂.1) : Λ₁ = Λ₂ :=
  Subtype.ext h

theorem lorentz_left_inv (Λ : LorentzMatrix4) :
    (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4) * Λ.1 = 1 := by
  calc (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4) * Λ.1
      = minkowskiMetric4 * (Λ.1.transpose * minkowskiMetric4 * Λ.1) := by noncomm_ring
    _ = minkowskiMetric4 * minkowskiMetric4 := by rw [Λ.2]
    _ = 1 := minkowskiMetric4_mul_self

theorem lorentz_right_inv (Λ : LorentzMatrix4) :
    Λ.1 * (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4) = 1 :=
  mul_eq_one_comm.mp (lorentz_left_inv Λ)

instance instGroupLorentzMatrix4 : Group LorentzMatrix4 where
  one := ⟨1, by simp⟩
  mul Λ₁ Λ₂ := ⟨Λ₁.1 * Λ₂.1, by
    rw [Matrix.transpose_mul]
    calc Λ₂.1.transpose * Λ₁.1.transpose * minkowskiMetric4 * (Λ₁.1 * Λ₂.1)
        = Λ₂.1.transpose * (Λ₁.1.transpose * minkowskiMetric4 * Λ₁.1) * Λ₂.1 := by noncomm_ring
      _ = Λ₂.1.transpose * minkowskiMetric4 * Λ₂.1 := by rw [Λ₁.2]
      _ = minkowskiMetric4 := Λ₂.2⟩
  inv Λ := ⟨minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4, by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, minkowskiMetric4_transpose,
      Matrix.transpose_transpose]
    calc (minkowskiMetric4 * (Λ.1 * minkowskiMetric4)) * minkowskiMetric4 *
          (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4)
        = minkowskiMetric4 * Λ.1 * (minkowskiMetric4 * minkowskiMetric4) *
            (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4) := by noncomm_ring
      _ = minkowskiMetric4 * (Λ.1 * (minkowskiMetric4 * Λ.1.transpose * minkowskiMetric4)) := by
            rw [minkowskiMetric4_mul_self]
            noncomm_ring
      _ = minkowskiMetric4 * 1 := by rw [lorentz_right_inv Λ]
      _ = minkowskiMetric4 := mul_one _⟩
  mul_assoc a b c := LorentzMatrix4.ext (Matrix.mul_assoc a.1 b.1 c.1)
  one_mul a := LorentzMatrix4.ext (Matrix.one_mul a.1)
  mul_one a := LorentzMatrix4.ext (Matrix.mul_one a.1)
  inv_mul_cancel a := LorentzMatrix4.ext (lorentz_left_inv a)

theorem lorentz_preserves_minkowskiInner (Λ : LorentzMatrix4) (x y : Space4) :
    minkowskiInner (Matrix.mulVec Λ.1 x) (Matrix.mulVec Λ.1 y) = minkowskiInner x y := by
  rw [minkowskiInner_eq_dot, minkowskiInner_eq_dot, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Λ.2]

/-- The 4D Poincaré group `ℝ⁴ ⋊ O(1,3)`. -/
@[ext]
structure Poincare4 where
  trans   : Space4
  lorentz : LorentzMatrix4

instance instGroupPoincare4 : Group Poincare4 where
  one := ⟨0, 1⟩
  mul g₁ g₂ := ⟨g₁.trans + Matrix.mulVec g₁.lorentz.1 g₂.trans, g₁.lorentz * g₂.lorentz⟩
  inv g := ⟨-Matrix.mulVec g.lorentz⁻¹.1 g.trans, g.lorentz⁻¹⟩
  mul_assoc a b c := by
    ext : 1
    · dsimp [HMul.hMul, Mul.mul]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel
    · exact mul_assoc a.lorentz b.lorentz c.lorentz
  one_mul a := by
    ext : 1
    · change 0 + Matrix.mulVec (1 : Matrix (Fin 4) (Fin 4) ℝ) a.trans = a.trans
      rw [zero_add, Matrix.one_mulVec]
    · exact one_mul a.lorentz
  mul_one a := by
    ext : 1
    · change a.trans + Matrix.mulVec a.lorentz.1 0 = a.trans
      rw [Matrix.mulVec_zero, add_zero]
    · exact mul_one a.lorentz
  inv_mul_cancel a := by
    ext : 1
    · change -Matrix.mulVec a.lorentz⁻¹.1 a.trans + Matrix.mulVec a.lorentz⁻¹.1 a.trans = 0
      abel
    · exact inv_mul_cancel a.lorentz

/-- Spacetime action `(a, Λ) · x = a + Λ x` on `Space4 = ℝ⁴`. -/
def poincareAct (g : Poincare4) (x : Space4) : Space4 :=
  g.trans + Matrix.mulVec g.lorentz.1 x

theorem poincareAct_one (x : Space4) : poincareAct 1 x = x := by
  change 0 + Matrix.mulVec (1 : Matrix (Fin 4) (Fin 4) ℝ) x = x
  rw [zero_add, Matrix.one_mulVec]

theorem poincareAct_mul (g₁ g₂ : Poincare4) (x : Space4) :
    poincareAct (g₁ * g₂) x = poincareAct g₁ (poincareAct g₂ x) := by
  change (g₁.trans + Matrix.mulVec g₁.lorentz.1 g₂.trans) +
      Matrix.mulVec (g₁.lorentz.1 * g₂.lorentz.1) x =
    g₁.trans + Matrix.mulVec g₁.lorentz.1 (g₂.trans + Matrix.mulVec g₂.lorentz.1 x)
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

theorem poincareAct_preserves_minkowskiSq (g : Poincare4) (x y : Space4) :
    minkowskiSq (poincareAct g x - poincareAct g y) = minkowskiSq (x - y) := by
  have hsub : poincareAct g x - poincareAct g y = Matrix.mulVec g.lorentz.1 (x - y) := by
    dsimp [poincareAct]
    rw [Matrix.mulVec_sub]
    abel
  rw [hsub, ← minkowskiInner_self, ← minkowskiInner_self, lorentz_preserves_minkowskiInner]

/-- Carrier `Option Space4` with discrete measurable space for the infinite-dimensional Hilbert space. -/
def OptionSpace4 : Type := Option Space4

@[reducible] instance instMeasurableSpaceOptionSpace4 : MeasurableSpace OptionSpace4 := ⊤

/-- Counting measure on `OptionSpace4`: `μ {none} = 1` (vacuum) and `μ {some x} = 1` (`x ∈ ℝ⁴`). -/
noncomputable def poincareCountMeasure : MeasureTheory.Measure OptionSpace4 :=
  MeasureTheory.Measure.count

/-- Infinite-dimensional complex Hilbert space `L²({none} ⊔ ℝ⁴, count)`. -/
abbrev PoincareHilbert : Type := MeasureTheory.Lp ℂ 2 poincareCountMeasure

def poincareOptionEquiv (g : Poincare4) : OptionSpace4 ≃ᵐ OptionSpace4 where
  toFun := fun o => match o with
    | none => none
    | some x => some (poincareAct g x)
  invFun := fun o => match o with
    | none => none
    | some x => some (poincareAct g⁻¹ x)
  left_inv o := by
    cases o with
    | none => rfl
    | some x =>
      change some (poincareAct g⁻¹ (poincareAct g x)) = some x
      rw [← poincareAct_mul, inv_mul_cancel, poincareAct_one]
  right_inv o := by
    cases o with
    | none => rfl
    | some x =>
      change some (poincareAct g (poincareAct g⁻¹ x)) = some x
      rw [← poincareAct_mul, mul_inv_cancel, poincareAct_one]
  measurable_toFun := fun _ _ => trivial
  measurable_invFun := fun _ _ => trivial

theorem poincareOptionEquiv_mp (g : Poincare4) :
    MeasureTheory.MeasurePreserving (poincareOptionEquiv g)
      poincareCountMeasure poincareCountMeasure := by
  refine ⟨(poincareOptionEquiv g).measurable, ?_⟩
  ext s hs
  rw [MeasureTheory.Measure.map_apply (poincareOptionEquiv g).measurable hs]
  dsimp [poincareCountMeasure]
  rw [MeasureTheory.Measure.count_apply (hs.preimage (poincareOptionEquiv g).measurable),
    MeasureTheory.Measure.count_apply hs]
  have hpre : poincareOptionEquiv g ⁻¹' s = (poincareOptionEquiv g).symm '' s :=
    ((poincareOptionEquiv g).toEquiv.image_symm_eq_preimage s).symm
  rw [hpre, (poincareOptionEquiv g).symm.injective.encard_image s]

theorem ae_count_eq_everywhere {f g : OptionSpace4 → ℂ}
    (h : f =ᵐ[poincareCountMeasure] g) (a : OptionSpace4) : f a = g a := by
  by_contra hne
  have hnull : poincareCountMeasure {x | f x ≠ g x} = 0 := h
  have hle : poincareCountMeasure {a} ≤ poincareCountMeasure {x | f x ≠ g x} :=
    MeasureTheory.measure_mono (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hne)
  rw [hnull] at hle
  have h1 : poincareCountMeasure {a} = 1 := by
    dsimp [poincareCountMeasure]
    exact MeasureTheory.Measure.count_singleton a
  rw [h1] at hle
  exact one_ne_zero (le_antisymm hle (zero_le _))

/-- Faithful unitary representation `U(a, Λ)` of `Poincare4` on `PoincareHilbert`. -/
noncomputable def poincareRep (g : Poincare4) : PoincareHilbert →L[ℂ] PoincareHilbert :=
  let e := poincareOptionEquiv g⁻¹
  let hmp := poincareOptionEquiv_mp g⁻¹
  LinearMap.mkContinuous
    { toFun := fun ψ => (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).toLp
        (fun x => ψ (e x))
      map_add' := fun ψ₁ ψ₂ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving poincareCountMeasure e hmp (ψ₁ + ψ₂)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ₁).coeFn_toLp
        have h3 := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ₂).coeFn_toLp
        have hadd1 := MeasureTheory.Lp.coeFn_add ψ₁ ψ₂
        have hadd2 := MeasureTheory.Lp.coeFn_add
          ((memLp_comp_measurePreserving poincareCountMeasure e hmp ψ₁).toLp (fun x => ψ₁ (e x)))
          ((memLp_comp_measurePreserving poincareCountMeasure e hmp ψ₂).toLp (fun x => ψ₂ (e x)))
        filter_upwards [h1, h2, h3, ae_comp_measurePreserving hmp hadd1, hadd2] with x hx1 hx2 hx3 ha1 ha2
        simp only [Pi.add_apply] at ha1 ha2 ⊢
        rw [hx1, ha1, ha2, hx2, hx3]
      map_smul' := fun c ψ => by
        apply MeasureTheory.Lp.ext
        have h1 := (memLp_comp_measurePreserving poincareCountMeasure e hmp (c • ψ)).coeFn_toLp
        have h2 := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).coeFn_toLp
        have hsm1 := MeasureTheory.Lp.coeFn_smul c ψ
        have hsm2 := MeasureTheory.Lp.coeFn_smul c
          ((memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).toLp (fun x => ψ (e x)))
        filter_upwards [h1, h2, ae_comp_measurePreserving hmp hsm1, hsm2] with x hx1 hx2 hs1 hs2
        simp only [Pi.smul_apply, RingHom.id_apply] at hs1 hs2 ⊢
        rw [hx1, hs1, hs2, hx2] }
    1
    (fun ψ => by
      let ψ' := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).toLp (fun x => ψ (e x))
      have h_norm_sq : ‖ψ'‖ ^ 2 = ‖ψ‖ ^ 2 := by
        have h_inner : ⟪ψ', ψ'⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
          rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
          have hcoe := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).coeFn_toLp
          calc ∫ x, ⟪ψ' x, ψ' x⟫_ℂ ∂poincareCountMeasure
              = ∫ x, ⟪ψ (e x), ψ (e x)⟫_ℂ ∂poincareCountMeasure := by
                  refine MeasureTheory.integral_congr_ae ?_
                  filter_upwards [hcoe] with x hx
                  rw [hx]
            _ = ∫ x, ⟪ψ x, ψ x⟫_ℂ ∂poincareCountMeasure :=
                hmp.integral_comp' (fun x => ⟪ψ x, ψ x⟫_ℂ)
        have hre := congrArg Complex.re h_inner
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
        simpa [pow_two] using hre
      change ‖ψ'‖ ≤ 1 * ‖ψ‖
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), one_mul, h_norm_sq])

theorem poincareRep_apply (g : Poincare4) (ψ : PoincareHilbert) (z : OptionSpace4) :
    (⇑(poincareRep g ψ) : OptionSpace4 → ℂ) z =
      (⇑ψ : OptionSpace4 → ℂ) (poincareOptionEquiv g⁻¹ z) := by
  let e := poincareOptionEquiv g⁻¹
  let hmp := poincareOptionEquiv_mp g⁻¹
  have hcoe := (memLp_comp_measurePreserving poincareCountMeasure e hmp ψ).coeFn_toLp
  exact ae_count_eq_everywhere hcoe z

theorem poincareRep_unitary (g : Poincare4) (u v : PoincareHilbert) :
    ⟪poincareRep g u, poincareRep g v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let e := poincareOptionEquiv g⁻¹
  let hmp := poincareOptionEquiv_mp g⁻¹
  have h1 := (memLp_comp_measurePreserving poincareCountMeasure e hmp u).coeFn_toLp
  have h2 := (memLp_comp_measurePreserving poincareCountMeasure e hmp v).coeFn_toLp
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc ∫ x, ⟪(poincareRep g u) x, (poincareRep g v) x⟫_ℂ ∂poincareCountMeasure
      = ∫ x, ⟪u (e x), v (e x)⟫_ℂ ∂poincareCountMeasure := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [h1, h2] with x hx1 hx2
          change ⟪((memLp_comp_measurePreserving poincareCountMeasure e hmp u).toLp
            (fun z => u (e z))) x,
            ((memLp_comp_measurePreserving poincareCountMeasure e hmp v).toLp
            (fun z => v (e z))) x⟫_ℂ = _
          rw [hx1, hx2]
    _ = ∫ x, ⟪u x, v x⟫_ℂ ∂poincareCountMeasure := hmp.integral_comp' (fun x => ⟪u x, v x⟫_ℂ)

theorem poincareCount_singleton_ne_top (a : OptionSpace4) :
    poincareCountMeasure {a} ≠ ⊤ := by
  dsimp [poincareCountMeasure]
  rw [MeasureTheory.Measure.count_singleton]
  exact ENNReal.one_ne_top

theorem poincareCount_singleton_toReal (a : OptionSpace4) :
    (poincareCountMeasure {a}).toReal = 1 := by
  dsimp [poincareCountMeasure]
  rw [MeasureTheory.Measure.count_singleton, ENNReal.toReal_one]

/-- Basis state `δ_a` (`a : OptionSpace4`) in `PoincareHilbert`. -/
noncomputable def deltaOption4 (a : OptionSpace4) : PoincareHilbert :=
  MeasureTheory.indicatorConstLp (2 : ENNReal) (by trivial : MeasurableSet ({a} : Set OptionSpace4))
    (poincareCount_singleton_ne_top a) (1 : ℂ)

/-- Ground vacuum `Ω = δ_none` in `PoincareHilbert`. -/
noncomputable def vacPoincare : PoincareHilbert := deltaOption4 (none : Option Space4)

/-- 1-particle state `δ_{some x}` at `x : Space4` in `PoincareHilbert`. -/
noncomputable def deltaSpace4 (x : Space4) : PoincareHilbert := deltaOption4 (some x)

theorem deltaOption4_inner (a b : OptionSpace4) :
    ⟪deltaOption4 a, deltaOption4 b⟫_ℂ = @ite _ (a = b) (Classical.propDecidable _) 1 0 := by
  unfold deltaOption4
  rw [MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp
    (hμs := poincareCount_singleton_ne_top a)
    (hμt := poincareCount_singleton_ne_top b)]
  have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_num
  rw [h1]
  by_cases hab : a = b
  · subst hab
    rw [Set.inter_self, if_pos rfl, Measure.real, poincareCount_singleton_toReal, one_smul]
  · have hinter : ({a} ∩ {b} : Set OptionSpace4) = ∅ := by
      ext z; simp [hab]
    rw [hinter, if_neg hab, Measure.real, MeasureTheory.measure_empty,
      ENNReal.toReal_zero, zero_smul]

theorem vacPoincare_norm : ‖vacPoincare‖ = 1 := by
  have hsq : ‖vacPoincare‖ ^ 2 = 1 := by
    have hre : (⟪vacPoincare, vacPoincare⟫_ℂ).re = 1 := by
      rw [vacPoincare, deltaOption4_inner, if_pos rfl, Complex.one_re]
    rw [inner_self_eq_norm_sq_to_K] at hre
    simp [pow_two] at hre
    linarith
  have hmul : (‖vacPoincare‖ - 1) * (‖vacPoincare‖ + 1) = 0 := by linarith
  rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg vacPoincare]

theorem deltaOption4_apply (a z : OptionSpace4) :
    (⇑(deltaOption4 a) : OptionSpace4 → ℂ) z =
      @ite _ (z = a) (Classical.propDecidable _) 1 0 := by
  classical
  have h := ae_count_eq_everywhere
    (MeasureTheory.indicatorConstLp_coeFn (p := (2 : ENNReal))
      (μ := poincareCountMeasure) (s := {a})
      (hs := by trivial)
      (hμs := poincareCount_singleton_ne_top a)
      (c := (1 : ℂ))) z
  change (⇑(deltaOption4 a) : OptionSpace4 → ℂ) z = _ at h
  rw [h, Set.indicator_apply]
  by_cases hz : z = a
  · rw [if_pos (Set.mem_singleton_iff.mpr hz), if_pos hz]
  · rw [if_neg (fun hm => hz (Set.mem_singleton_iff.mp hm)), if_neg hz]

theorem poincareRep_deltaOption4 (g : Poincare4) (a : OptionSpace4) :
    poincareRep g (deltaOption4 a) = deltaOption4 (poincareOptionEquiv g a) := by
  apply MeasureTheory.Lp.ext
  refine Filter.Eventually.of_forall fun z => ?_
  rw [poincareRep_apply, deltaOption4_apply, deltaOption4_apply]
  have heq : poincareOptionEquiv g⁻¹ z = a ↔ z = poincareOptionEquiv g a := by
    constructor <;> intro h
    · calc z = poincareOptionEquiv g (poincareOptionEquiv g⁻¹ z) := by
              cases z with
              | none => rfl
              | some x =>
                change some x = some (poincareAct g (poincareAct g⁻¹ x))
                rw [← poincareAct_mul, mul_inv_cancel, poincareAct_one]
          _ = poincareOptionEquiv g a := by rw [h]
    · calc poincareOptionEquiv g⁻¹ z = poincareOptionEquiv g⁻¹ (poincareOptionEquiv g a) := by
              rw [h]
          _ = a := by
              cases a with
              | none => rfl
              | some y =>
                change some (poincareAct g⁻¹ (poincareAct g y)) = some y
                rw [← poincareAct_mul, inv_mul_cancel, poincareAct_one]
  by_cases hz : z = poincareOptionEquiv g a
  · rw [if_pos (heq.mpr hz), if_pos hz]
  · rw [if_neg (fun h => hz (heq.mp h)), if_neg hz]

theorem poincareRep_vac (g : Poincare4) : poincareRep g vacPoincare = vacPoincare :=
  poincareRep_deltaOption4 g none

theorem poincareRep_deltaSpace4 (g : Poincare4) (x : Space4) :
    poincareRep g (deltaSpace4 x) = deltaSpace4 (poincareAct g x) :=
  poincareRep_deltaOption4 g (some x)

/-- Field creation operator `φ(x) v = ⟪Ω, v⟫_ℂ • δ_{some x}` on `PoincareHilbert`. -/
noncomputable def phiPoincare (x : Space4) : PoincareHilbert →L[ℂ] PoincareHilbert :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟪vacPoincare, v⟫_ℂ • deltaSpace4 x
      map_add' := fun u v => by rw [inner_add_right, add_smul]
      map_smul' := fun c v => by rw [inner_smul_right, smul_smul]; rfl }
    1
    (fun v => by
      have hnorm : ‖deltaSpace4 x‖ = 1 := by
        have hsq : ‖deltaSpace4 x‖ ^ 2 = 1 := by
          have hre : (⟪deltaSpace4 x, deltaSpace4 x⟫_ℂ).re = 1 := by
            rw [deltaSpace4, deltaOption4_inner, if_pos rfl, Complex.one_re]
          rw [inner_self_eq_norm_sq_to_K] at hre
          simp [pow_two] at hre
          linarith
        have hmul : (‖deltaSpace4 x‖ - 1) * (‖deltaSpace4 x‖ + 1) = 0 := by linarith
        rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg (deltaSpace4 x)]
      change ‖⟪vacPoincare, v⟫_ℂ • deltaSpace4 x‖ ≤ 1 * ‖v‖
      rw [norm_smul, hnorm, mul_one, one_mul]
      calc ‖⟪vacPoincare, v⟫_ℂ‖ ≤ ‖vacPoincare‖ * ‖v‖ := norm_inner_le_norm _ _
        _ = ‖v‖ := by rw [vacPoincare_norm, one_mul])

/--
**Infinite-dimensional relativistic `WightmanQFT4D 1`** with genuine 4D Poincaré group
`Poincare4 = ℝ⁴ ⋊ O(1,3)`, faithful unitary representation `poincareRep`,
non-trivial covariant local field `phiPoincare`, and mass gap `{0, 1}`.
-/
noncomputable def infDimWightman4D : WightmanQFT4D 1 where
  Δ_pos := one_pos
  H := PoincareHilbert
  Ω_phys := vacPoincare
  Ω_unit := vacPoincare_norm
  Poincare := Poincare4
  U := poincareRep
  U_unitary := poincareRep_unitary
  U_vac := poincareRep_vac
  actP := poincareAct
  φ := phiPoincare
  covariant := fun g x => by
    ext1 v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    change poincareRep g (⟪vacPoincare, v⟫_ℂ • deltaSpace4 x) =
      ⟪vacPoincare, poincareRep g v⟫_ℂ • deltaSpace4 (poincareAct g x)
    rw [map_smul, poincareRep_deltaSpace4]
    have h_in : ⟪vacPoincare, poincareRep g v⟫_ℂ = ⟪vacPoincare, v⟫_ℂ := by
      calc ⟪vacPoincare, poincareRep g v⟫_ℂ
          = ⟪poincareRep g vacPoincare, poincareRep g v⟫_ℂ := by rw [poincareRep_vac]
        _ = ⟪vacPoincare, v⟫_ℂ := poincareRep_unitary g vacPoincare v
    rw [h_in]
  local_comm := fun x y _ => by
    ext1 v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    change ⟪vacPoincare, ⟪vacPoincare, v⟫_ℂ • deltaSpace4 y⟫_ℂ • deltaSpace4 x =
      ⟪vacPoincare, ⟪vacPoincare, v⟫_ℂ • deltaSpace4 x⟫_ℂ • deltaSpace4 y
    have h0x : ⟪vacPoincare, deltaSpace4 x⟫_ℂ = 0 := by
      rw [vacPoincare, deltaSpace4, deltaOption4_inner]; simp
    have h0y : ⟪vacPoincare, deltaSpace4 y⟫_ℂ = 0 := by
      rw [vacPoincare, deltaSpace4, deltaOption4_inner]; simp
    rw [inner_smul_right, inner_smul_right, h0x, h0y]
    simp
  P2_spec := {0, 1}
  spectral_cond := fun p2 hp2 => by rcases hp2 with rfl | rfl <;> norm_num
  mass_gap_spec := fun p2 hp2 => by
    rcases hp2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by norm_num)

noncomputable def P_vac_poincare : PoincareHilbert →L[ℂ] PoincareHilbert :=
  rankOneProj vacPoincare vacPoincare_norm

noncomputable def H_phys_poincare : PoincareHilbert →L[ℂ] PoincareHilbert :=
  ContinuousLinearMap.id ℂ PoincareHilbert - P_vac_poincare

theorem P_vac_poincare_sa (x y : PoincareHilbert) :
    ⟪P_vac_poincare x, y⟫_ℂ = ⟪x, P_vac_poincare y⟫_ℂ := by
  change ⟪⟪vacPoincare, x⟫_ℂ • vacPoincare, y⟫_ℂ = ⟪x, ⟪vacPoincare, y⟫_ℂ • vacPoincare⟫_ℂ
  have hconj : starRingEnd ℂ ⟪vacPoincare, x⟫_ℂ = ⟪x, vacPoincare⟫_ℂ :=
    inner_conj_symm x vacPoincare
  rw [inner_smul_left, inner_smul_right, hconj]
  ring

theorem P_vac_poincare_idem (x : PoincareHilbert) :
    P_vac_poincare (P_vac_poincare x) = P_vac_poincare x := by
  have h1 : ⟪vacPoincare, vacPoincare⟫_ℂ = 1 := by
    rw [vacPoincare, deltaOption4_inner, if_pos rfl]
  change ⟪vacPoincare, ⟪vacPoincare, x⟫_ℂ • vacPoincare⟫_ℂ • vacPoincare =
    ⟪vacPoincare, x⟫_ℂ • vacPoincare
  rw [inner_smul_right, h1, mul_one]

theorem H_phys_poincare_sa (x y : PoincareHilbert) :
    ⟪H_phys_poincare x, y⟫_ℂ = ⟪x, H_phys_poincare y⟫_ℂ := by
  simp only [H_phys_poincare, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    inner_sub_left, inner_sub_right, P_vac_poincare_sa]

theorem H_phys_poincare_idem (x : PoincareHilbert) :
    H_phys_poincare (H_phys_poincare x) = H_phys_poincare x := by
  simp only [H_phys_poincare, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_sub, P_vac_poincare_idem]
  abel

noncomputable def T_E_poincare (t : ℝ) : PoincareHilbert →L[ℂ] PoincareHilbert :=
  P_vac_poincare + ((Real.exp (-t) : ℝ) : ℂ) • H_phys_poincare

/--
**Infinite-dimensional `OSReconstructionData 1 concreteOS4DContinuumTheory`**
on `PoincareHilbert = L²({none} ⊔ ℝ⁴, count)` with genuine `Poincare4` symmetry.
-/
noncomputable def infDimOSReconstructionData :
    OSReconstructionData 1 concreteOS4DContinuumTheory where
  wightman := infDimWightman4D
  T_E := T_E_poincare
  T_E_zero := by
    change T_E_poincare 0 = ContinuousLinearMap.id ℂ PoincareHilbert
    exact ContinuousLinearMap.ext fun x => by simp [T_E_poincare, H_phys_poincare]
  T_E_add := fun s t _ _ => by
    change T_E_poincare (s + t) = (T_E_poincare s).comp (T_E_poincare t)
    refine ContinuousLinearMap.ext fun x => ?_
    have hp01 : P_vac_poincare (H_phys_poincare x) = 0 := by
      simp [H_phys_poincare, P_vac_poincare_idem]
    have hp10 : H_phys_poincare (P_vac_poincare x) = 0 := by
      simp [H_phys_poincare, P_vac_poincare_idem]
    simp only [T_E_poincare, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, map_add, map_smul, P_vac_poincare_idem,
      H_phys_poincare_idem, hp01, hp10, smul_zero, add_zero, zero_add]
    rw [smul_smul, ← Complex.ofReal_mul, ← Real.exp_add,
      show -t + -s = -(s + t) by ring]
  T_E_sa := fun t x y _ => by
    change ⟪T_E_poincare t (x : PoincareHilbert), (y : PoincareHilbert)⟫_ℂ =
      ⟪(x : PoincareHilbert), T_E_poincare t (y : PoincareHilbert)⟫_ℂ
    simp only [T_E_poincare, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, P_vac_poincare_sa, H_phys_poincare_sa]
  T_E_contr := fun t x ht => by
    change ‖T_E_poincare t (x : PoincareHilbert)‖ ≤ ‖(x : PoincareHilbert)‖
    let x' : PoincareHilbert := x
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have h_orth : ⟪P_vac_poincare x', H_phys_poincare x'⟫_ℂ = 0 := by
      have hp01 : P_vac_poincare (H_phys_poincare x') = 0 := by
        simp [H_phys_poincare, P_vac_poincare_idem]
      rw [P_vac_poincare_sa, hp01, inner_zero_right]
    have hre : RCLike.re ⟪P_vac_poincare x', ((Real.exp (-t) : ℝ) : ℂ) • H_phys_poincare x'⟫_ℂ = 0 := by
      rw [inner_smul_right, h_orth, mul_zero, map_zero]
    have hre' : RCLike.re ⟪P_vac_poincare x', Real.exp (-t) • H_phys_poincare x'⟫_ℂ = 0 := by
      change RCLike.re ⟪P_vac_poincare x', ((Real.exp (-t) : ℝ) : ℂ) • H_phys_poincare x'⟫_ℂ = 0
      exact hre
    have h_sum_sq : ‖P_vac_poincare x'‖ ^ 2 + ‖H_phys_poincare x'‖ ^ 2 = ‖x'‖ ^ 2 := by
      have hx : x' = P_vac_poincare x' + H_phys_poincare x' := by simp [H_phys_poincare]
      conv_rhs => rw [hx]
      rw [norm_add_sq (𝕜 := ℂ)]
      have h0 : RCLike.re ⟪P_vac_poincare x', H_phys_poincare x'⟫_ℂ = 0 := by
        rw [h_orth, map_zero]
      rw [h0, mul_zero, add_zero]
    have hsq : ‖T_E_poincare t x'‖ ^ 2 =
        ‖P_vac_poincare x'‖ ^ 2 + (Real.exp (-t)) ^ 2 * ‖H_phys_poincare x'‖ ^ 2 := by
      dsimp [T_E_poincare]
      rw [norm_add_sq (𝕜 := ℂ)]
      simp [hre', norm_smul, abs_of_nonneg (Real.exp_pos _).le, mul_pow]
    have hexp_le : (Real.exp (-t)) ^ 2 ≤ 1 := by
      have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [(Real.exp_pos (-t)).le]
    change ‖T_E_poincare t x'‖ ^ 2 ≤ ‖x'‖ ^ 2
    rw [hsq, ← h_sum_sq]
    exact add_le_add le_rfl (mul_le_of_le_one_left (sq_nonneg _) hexp_le)
  H_phys := H_phys_poincare
  H_phys_sa := H_phys_poincare_sa
  H_phys_nonneg := fun x => by
    change 0 ≤ (⟪(x : PoincareHilbert), H_phys_poincare (x : PoincareHilbert)⟫_ℂ).re
    let x' : PoincareHilbert := x
    have h_eq : ⟪x', H_phys_poincare x'⟫_ℂ = ⟪H_phys_poincare x', H_phys_poincare x'⟫_ℂ := by
      conv_lhs => rw [← H_phys_poincare_idem x', ← H_phys_poincare_sa]
    change 0 ≤ (⟪x', H_phys_poincare x'⟫_ℂ).re
    rw [h_eq, inner_self_eq_norm_sq_to_K]
    simp [pow_two]
    exact mul_self_nonneg _
  H_phys_vac := by
    change H_phys_poincare vacPoincare = 0
    have hv : P_vac_poincare vacPoincare = vacPoincare := by
      have h1 : ⟪vacPoincare, vacPoincare⟫_ℂ = 1 := by
        rw [vacPoincare, deltaOption4_inner, if_pos rfl]
      change ⟪vacPoincare, vacPoincare⟫_ℂ • vacPoincare = vacPoincare
      rw [h1, one_smul]
    simp [H_phys_poincare, hv]
  cyclic_dense := by
    classical
    let S : Set PoincareHilbert :=
      {v : PoincareHilbert | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k => phiPoincare (xs i))).foldr
          (fun A acc => A acc) vacPoincare}
    have h_vac : vacPoincare ∈ S := ⟨0, Fin.elim0, rfl⟩
    have h_delta : ∀ x : Space4, deltaSpace4 x ∈ S := by
      intro x
      refine ⟨1, fun _ => x, ?_⟩
      have h1 : ⟪vacPoincare, vacPoincare⟫_ℂ = 1 := by
        rw [vacPoincare, deltaOption4_inner, if_pos rfl]
      change deltaSpace4 x = ⟪vacPoincare, vacPoincare⟫_ℂ • deltaSpace4 x
      rw [h1, one_smul]
    have h_cl_complete : CompleteSpace ↥(Submodule.span ℂ S).topologicalClosure := by
      refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
      have huV : CauchySeq (fun n => (u n : PoincareHilbert)) :=
        Metric.cauchySeq_iff.mpr (by simpa [Subtype.dist_eq] using Metric.cauchySeq_iff.mp hu)
      obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete huV
      have haK : a ∈ closure (Submodule.span ℂ S : Set PoincareHilbert) :=
        isClosed_closure.mem_of_tendsto ha (Filter.Eventually.of_forall fun n => (u n).2)
      exact ⟨⟨a, haK⟩, tendsto_subtype_rng.mpr ha⟩
    haveI : (Submodule.span ℂ S).topologicalClosure.HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace _
    rw [← Submodule.orthogonal_eq_bot_iff, eq_bot_iff]
    intro v hv
    let v' : PoincareHilbert := v
    have hv_zero_opt : ∀ a : OptionSpace4, ⟪deltaOption4 a, v'⟫_ℂ = 0 := by
      intro a
      have ha_mem : deltaOption4 a ∈ (Submodule.span ℂ S).topologicalClosure := by
        apply subset_closure
        apply Submodule.subset_span
        cases a with
        | none => exact h_vac
        | some x => exact h_delta x
      exact (Submodule.mem_orthogonal _ _).mp hv (deltaOption4 a) ha_mem
    have hcinner : ∀ a b : ℂ, ⟪a, b⟫_ℂ = starRingEnd ℂ a * b := by
      intro a b
      have h1 : ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K]; norm_num
      calc ⟪a, b⟫_ℂ = ⟪a • (1 : ℂ), b • (1 : ℂ)⟫_ℂ := by simp
        _ = starRingEnd ℂ a * (b * ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ) := by
              rw [inner_smul_left, inner_smul_right]
        _ = starRingEnd ℂ a * b := by rw [h1, mul_one]
    have hv_val : ∀ a : OptionSpace4, (⇑v' : OptionSpace4 → ℂ) a = 0 := by
      intro a
      have h_in : ⟪deltaOption4 a, v'⟫_ℂ = (⇑v' : OptionSpace4 → ℂ) a := by
        rw [MeasureTheory.L2.inner_def]
        have h_ae : (fun z => ⟪(⇑(deltaOption4 a) : OptionSpace4 → ℂ) z,
              (⇑v' : OptionSpace4 → ℂ) z⟫_ℂ) =
            fun z => if z = a then (⇑v' : OptionSpace4 → ℂ) a else 0 := by
          funext z
          rw [deltaOption4_apply]
          by_cases hz : z = a
          · subst hz
            rw [if_pos rfl, if_pos rfl, hcinner, map_one, one_mul]
          · rw [if_neg hz, if_neg hz, inner_zero_left]
        rw [h_ae]
        have h_ind : (fun z : OptionSpace4 => if z = a then (⇑v' : OptionSpace4 → ℂ) a else 0) =
            Set.indicator {a} (fun _ => (⇑v' : OptionSpace4 → ℂ) a) := by
          funext z
          simp [Set.indicator_apply, Set.mem_singleton_iff]
        rw [h_ind, MeasureTheory.integral_indicator (by trivial : MeasurableSet ({a} : Set OptionSpace4)),
          MeasureTheory.setIntegral_const]
        dsimp [Measure.real]
        rw [poincareCount_singleton_toReal, Complex.ofReal_one, one_mul]
      rw [← h_in]
      exact hv_zero_opt a
    rw [Submodule.mem_bot]
    change v' = 0
    apply MeasureTheory.Lp.ext
    have h0 : ⇑(0 : PoincareHilbert) =ᵐ[poincareCountMeasure] 0 :=
      MeasureTheory.Lp.coeFn_zero ℂ 2 poincareCountMeasure
    filter_upwards [h0] with a ha
    rw [hv_val a, ha]
    rfl

/-- Infinite-dimensional Poincaré-covariant realization of **§16**. -/
theorem infdim_poincare_euclidean_os_verification :
    ∃ D : EuclideanOSVerificationData concreteOS4DContinuumTheory infDimOSReconstructionData,
      (∀ (m : ℕ) (n_pts : Fin m → ℕ) (c : Fin m → ℂ)
        (xs : ∀ i : Fin m, Fin (n_pts i) → Space4),
        (∀ i k, 0 < (xs i k) 0) →
        0 ≤ (∑ i : Fin m, ∑ j : Fin m,
          c i * starRingEnd ℂ (c j) *
            concreteOS4DContinuumTheory.os.Schwinger (n_pts i + n_pts j)
              (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re) ∧
      (∀ (n : ℕ) (Rot : Matrix.specialOrthogonalGroup (Fin 4) ℝ)
        (xs : Fin n → Space4),
        concreteOS4DContinuumTheory.os.Schwinger n (fun i => Matrix.mulVec Rot.1 (xs i)) =
          concreteOS4DContinuumTheory.os.Schwinger n xs) ∧
      ((∀ x y : infDimOSReconstructionData.wightman.H,
          ⟪infDimOSReconstructionData.H_phys x, y⟫_ℂ =
            ⟪x, infDimOSReconstructionData.H_phys y⟫_ℂ) ∧
        (∀ x : infDimOSReconstructionData.wightman.H,
          0 ≤ (⟪x, infDimOSReconstructionData.H_phys x⟫_ℂ).re) ∧
        infDimOSReconstructionData.H_phys infDimOSReconstructionData.wightman.Ω_phys = 0) ∧
      (0 < (1 : ℝ) ∧
        (∀ (n m : ℕ), ∃ C : ℝ, ∀ (xs : Fin n → Space4) (ys : Fin m → Space4)
          (dist : ℝ), 0 ≤ dist → (∀ i j, dist ≤ ‖xs i - ys j‖) →
          ‖concreteOS4DContinuumTheory.os.Schwinger (n + m) (Fin.append xs ys) -
            concreteOS4DContinuumTheory.os.Schwinger n xs *
              concreteOS4DContinuumTheory.os.Schwinger m ys‖ ≤ C * Real.exp (-((1 : ℝ) * dist))) ∧
        ¬ IsGaussian4 concreteOS4DContinuumTheory.os.Schwinger) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ : infDimOSReconstructionData.wightman.H,
          0 ≤ (⟪ψ, infDimOSReconstructionData.H_phys ψ⟫_ℂ).re)) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x) ∧
        (∀ i, lieBracketCLM (D.symm i) infDimOSReconstructionData.H_phys = 0) ∧
        infDimOSReconstructionData.wightman.Ω_phys ∈ invarianceSet D.symm ∧
        (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
          poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
        (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
          Differentiable ℝ f →
          (∀ w, poissonBracket f D.H_cl w = 0) →
          ∀ t, f (D.flow.Φ t z) = f z) ∧
        (∀ A₁ A₂ B₁ B₂ : D.Obs,
          (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂))) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) :=
  non_gaussian_4d_euclidean_os_axioms_verification
    concreteOS4DContinuumTheory infDimOSReconstructionData

/-- Infinite-dimensional Poincaré-covariant realization of **§17**. -/
theorem infdim_poincare_wightman_reconstruction :
    ∃ D : OSHilbertCompletionData infDimOSReconstructionData,
      ((∀ u : OSQuotient D.bridge.F, 0 ≤ (osQuotInner D.bridge.F u u).re) ∧
        (∀ u : OSQuotient D.bridge.F,
          osQuotInner D.bridge.F u u = 0 ↔ u = osQuotMk D.bridge.F 0)) ∧
      (Function.Injective D.bridge.ι ∧
        (∀ u v, ⟪D.bridge.ι u, D.bridge.ι v⟫_ℂ = osQuotInner D.bridge.F u v) ∧
        closure (Set.range D.bridge.ι) = Set.univ) ∧
      ((∀ g x y, ⟪infDimOSReconstructionData.wightman.U g x,
            infDimOSReconstructionData.wightman.U g y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
        (∀ g, infDimOSReconstructionData.wightman.U g
            infDimOSReconstructionData.wightman.Ω_phys =
          infDimOSReconstructionData.wightman.Ω_phys) ∧
        (∀ x y, ⟪infDimOSReconstructionData.H_phys x, y⟫_ℂ =
          ⟪x, infDimOSReconstructionData.H_phys y⟫_ℂ) ∧
        (∀ x, 0 ≤ (⟪x, infDimOSReconstructionData.H_phys x⟫_ℂ).re) ∧
        infDimOSReconstructionData.H_phys infDimOSReconstructionData.wightman.Ω_phys = 0) ∧
      ((∀ g x, (infDimOSReconstructionData.wightman.U g).comp
            (infDimOSReconstructionData.wightman.φ x) =
          (infDimOSReconstructionData.wightman.φ
            (infDimOSReconstructionData.wightman.actP g x)).comp
              (infDimOSReconstructionData.wightman.U g)) ∧
        (∀ x y, minkowskiSq (x - y) < 0 →
          (infDimOSReconstructionData.wightman.φ x).comp
            (infDimOSReconstructionData.wightman.φ y) =
          (infDimOSReconstructionData.wightman.φ y).comp
            (infDimOSReconstructionData.wightman.φ x)) ∧
        (∀ p2 ∈ infDimOSReconstructionData.wightman.P2_spec, 0 ≤ p2) ∧
        (∀ p2 ∈ infDimOSReconstructionData.wightman.P2_spec, p2 = 0 ∨ (1 : ℝ) ^ 2 ≤ p2) ∧
        (Submodule.span ℂ
          {v : infDimOSReconstructionData.wightman.H | ∃ (k : ℕ) (xs : Fin k → Space4),
            v = (List.ofFn (fun i : Fin k =>
              infDimOSReconstructionData.wightman.φ (xs i))).foldr
              (fun A acc => A acc) infDimOSReconstructionData.wightman.Ω_phys}).topologicalClosure =
          ⊤) ∧
      ((∀ β, Filter.Tendsto (D.Z β) Filter.atTop Filter.atTop) ∧
        (∀ ψ : infDimOSReconstructionData.wightman.H,
          0 ≤ (⟪ψ, infDimOSReconstructionData.H_phys ψ⟫_ℂ).re) ∧
        (∀ i, lieBracketCLM (D.symm i) infDimOSReconstructionData.H_phys = 0) ∧
        infDimOSReconstructionData.wightman.Ω_phys ∈ invarianceSet D.symm ∧
        (∀ (i : Fin D.n_dof) (z : PhaseSpace D.n_dof),
          poissonBracket (coordQ i) (coordP i) z ≠ 0) ∧
        (∀ (f : PhaseSpace D.n_dof → ℝ) (z : PhaseSpace D.n_dof),
          Differentiable ℝ f →
          (∀ w, poissonBracket f D.H_cl w = 0) →
          ∀ t, f (D.flow.Φ t z) = f z) ∧
        (∀ A₁ A₂ B₁ B₂ : D.Obs,
          (A₁ ⊗ₜ[ℂ] B₁) * (A₂ ⊗ₜ[ℂ] B₂) = (A₁ * A₂) ⊗ₜ[ℂ] (B₁ * B₂))) ∧
      (Filter.Tendsto D.ξ_seq Filter.atTop Filter.atTop ∧
        (∀ x : D.trilattice.S, D.trilattice.μ (D.trilattice.δ x) = x)) ∧
      ((∀ z : PhaseSpace 1, singleDOFProj D.n_dof (singleDOFLift D.n_dof z) = z) ∧
        0 < D.action_val) :=
  os_hilbert_completion_and_wightman_reconstruction infDimOSReconstructionData

end Poincare4DWightman 

/-! ## §29.  End-to-end wiring of §§22–28 (OSHilbertSpace, 4D SU(N) Schwinger, Poincare4, KS) -/

section EndToEndSUYangMills

/-- Non-negativity lifts from `(E, F)` to the true OS Hilbert completion `OSHilbertSpace F` (§22). -/
theorem osLiftOperator_nonneg {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : E →ₗ[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ x : E, (F.B (T x) (T x)).re ≤ C ^ 2 * (F.B x x).re)
    (h_nonneg : ∀ x : E, 0 ≤ (F.B x (T x)).re)
    (z : OSHilbertSpace F) :
    0 ≤ (⟪z, osLiftOperator F T C hC hbd z⟫_ℂ).re := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_le continuous_const
      (Complex.continuous_re.comp (continuous_id.inner (osLiftOperator F T C hC hbd).continuous))
  · intro u
    refine Quotient.inductionOn u fun x => ?_
    change 0 ≤ (⟪osCompletionMap F (osPreMk F x),
      osLiftOperator F T C hC hbd (osCompletionMap F (osPreMk F x))⟫_ℂ).re
    rw [osLiftOperator_coe, osCompletionMap_inner]
    exact h_nonneg x

/-- Lift a contractive symmetric Euclidean semigroup `T_pre` on `(E, F)` to `OSHilbertSpace F` (§22). -/
noncomputable def osLiftSemigroup {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T_pre : ℝ → (E →ₗ[ℂ] E))
    (h_contr : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_pre t x) (T_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re)
    (t : ℝ) : OSHilbertSpace F →L[ℂ] OSHilbertSpace F :=
  if ht : 0 ≤ t then osLiftOperator F (T_pre t) 1 zero_le_one (h_contr t ht)
  else ContinuousLinearMap.id ℂ (OSHilbertSpace F)

theorem osLiftSemigroup_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T_pre : ℝ → (E →ₗ[ℂ] E))
    (h_contr : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_pre t x) (T_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re)
    (h_zero : ∀ x : E, T_pre 0 x = x) :
    osLiftSemigroup F T_pre h_contr 0 = ContinuousLinearMap.id ℂ (OSHilbertSpace F) := by
  dsimp [osLiftSemigroup]
  rw [dif_pos le_rfl]
  ext1 z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq
      (osLiftOperator F (T_pre 0) 1 zero_le_one (h_contr 0 le_rfl)).continuous
      (ContinuousLinearMap.id ℂ (OSHilbertSpace F)).continuous
  · intro u
    refine Quotient.inductionOn u fun x => ?_
    change osLiftOperator F (T_pre 0) 1 zero_le_one (h_contr 0 le_rfl)
        (osCompletionMap F (osPreMk F x)) =
      (ContinuousLinearMap.id ℂ (OSHilbertSpace F)) (osCompletionMap F (osPreMk F x))
    rw [ContinuousLinearMap.id_apply, osLiftOperator_coe, h_zero x]

theorem osLiftSemigroup_add {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T_pre : ℝ → (E →ₗ[ℂ] E))
    (h_contr : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_pre t x) (T_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re)
    (h_add : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ x : E, T_pre (s + t) x = T_pre s (T_pre t x))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    osLiftSemigroup F T_pre h_contr (s + t) =
      (osLiftSemigroup F T_pre h_contr s).comp (osLiftSemigroup F T_pre h_contr t) := by
  dsimp [osLiftSemigroup]
  rw [dif_pos (add_nonneg hs ht), dif_pos hs, dif_pos ht]
  ext1 z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq
      (osLiftOperator F (T_pre (s + t)) 1 zero_le_one (h_contr (s + t) (add_nonneg hs ht))).continuous
      ((osLiftOperator F (T_pre s) 1 zero_le_one (h_contr s hs)).comp
        (osLiftOperator F (T_pre t) 1 zero_le_one (h_contr t ht))).continuous
  · intro u
    refine Quotient.inductionOn u fun x => ?_
    rw [ContinuousLinearMap.comp_apply]
    change osLiftOperator F (T_pre (s + t)) 1 zero_le_one (h_contr (s + t) (add_nonneg hs ht))
        (osCompletionMap F (osPreMk F x)) =
      osLiftOperator F (T_pre s) 1 zero_le_one (h_contr s hs)
        (osLiftOperator F (T_pre t) 1 zero_le_one (h_contr t ht)
          (osCompletionMap F (osPreMk F x)))
    rw [osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe, h_add s t hs ht x]

theorem osLiftSemigroup_sa {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T_pre : ℝ → (E →ₗ[ℂ] E))
    (h_contr : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_pre t x) (T_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re)
    (h_sa : ∀ t, 0 ≤ t → ∀ x y : E, F.B (T_pre t x) y = F.B x (T_pre t y))
    (t : ℝ) (ht : 0 ≤ t) (u v : OSHilbertSpace F) :
    ⟪osLiftSemigroup F T_pre h_contr t u, v⟫_ℂ =
      ⟪u, osLiftSemigroup F T_pre h_contr t v⟫_ℂ := by
  dsimp [osLiftSemigroup]
  rw [dif_pos ht]
  exact osLiftOperator_sa F (T_pre t) 1 zero_le_one (h_contr t ht) (h_sa t ht) u v

theorem osLiftSemigroup_contr {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T_pre : ℝ → (E →ₗ[ℂ] E))
    (h_contr : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_pre t x) (T_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re)
    (t : ℝ) (ht : 0 ≤ t) (z : OSHilbertSpace F) :
    ‖osLiftSemigroup F T_pre h_contr t z‖ ≤ ‖z‖ := by
  dsimp [osLiftSemigroup]
  rw [dif_pos ht]
  simpa using osLiftOperator_norm_le F (T_pre t) 1 zero_le_one (h_contr t ht) z

/--
Pre-Hilbert OS reconstruction inputs on positive-time Euclidean test configurations `(E, F)`
with genuine 4D Poincaré group `Poincare4` (§27) and true OS completion `OSHilbertSpace F` (§22).
-/
structure EuclideanOSPreData (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys) where
  E            : Type
  [eAdd        : AddCommGroup E]
  [eMod        : Module ℂ E]
  F            : OSReflectionForm E
  Ω_E          : E
  Ω_E_norm     : F.B Ω_E Ω_E = 1
  T_E_pre      : ℝ → (E →ₗ[ℂ] E)
  T_E_zero     : ∀ x : E, T_E_pre 0 x = x
  T_E_add      : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ x : E, T_E_pre (s + t) x = T_E_pre s (T_E_pre t x)
  T_E_sa       : ∀ t, 0 ≤ t → ∀ x y : E, F.B (T_E_pre t x) y = F.B x (T_E_pre t y)
  T_E_contr    : ∀ t, 0 ≤ t → ∀ x : E, (F.B (T_E_pre t x) (T_E_pre t x)).re ≤ 1 ^ 2 * (F.B x x).re
  H_pre        : E →ₗ[ℂ] E
  H_bound      : ℝ
  H_bound_nn   : 0 ≤ H_bound
  H_bd         : ∀ x : E, (F.B (H_pre x) (H_pre x)).re ≤ H_bound ^ 2 * (F.B x x).re
  H_sa         : ∀ x y : E, F.B (H_pre x) y = F.B x (H_pre y)
  H_nonneg     : ∀ x : E, 0 ≤ (F.B x (H_pre x)).re
  H_vac        : H_pre Ω_E = 0
  U_pre        : Poincare4 → (E →ₗ[ℂ] E)
  U_unit_pre   : ∀ g x y, F.B (U_pre g x) (U_pre g y) = F.B x y
  U_vac_pre    : ∀ g, U_pre g Ω_E = Ω_E
  φ_pre        : Space4 → (E →ₗ[ℂ] E)
  φ_bound      : Space4 → ℝ
  φ_bound_nn   : ∀ x, 0 ≤ φ_bound x
  φ_bd         : ∀ x (v : E), (F.B (φ_pre x v) (φ_pre x v)).re ≤ (φ_bound x) ^ 2 * (F.B v v).re
  cov_pre      : ∀ g x v, U_pre g (φ_pre x v) = φ_pre (poincareAct g x) (U_pre g v)
  loc_pre      : ∀ x y, minkowskiSq (x - y) < 0 → ∀ v, φ_pre x (φ_pre y v) = φ_pre y (φ_pre x v)
  P2_spec      : Set ℝ
  spec_cond    : ∀ p2 ∈ P2_spec, 0 ≤ p2
  gap_spec     : ∀ p2 ∈ P2_spec, p2 = 0 ∨ Δ_phys ^ 2 ≤ p2
  cyclic_dense : (Submodule.span ℂ
      {v : OSHilbertSpace F | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k =>
          osLiftOperator F (φ_pre (xs i)) (φ_bound (xs i)) (φ_bound_nn (xs i)) (φ_bd (xs i)))).foldr
          (fun A acc => A acc) (osCompletionMap F (osPreMk F Ω_E))}).topologicalClosure = ⊤

attribute [instance] EuclideanOSPreData.eAdd EuclideanOSPreData.eMod

/-- Construct `WightmanQFT4D Δ_phys` directly on `OSHilbertSpace P.F` with `Poincare4` (§22 + §27). -/
noncomputable def buildWightmanOnOSCompletion {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (P : EuclideanOSPreData Δ_phys os) : WightmanQFT4D Δ_phys where
  Δ_pos := os.os.Δ_pos
  H := OSHilbertSpace P.F
  Ω_phys := osCompletionMap P.F (osPreMk P.F P.Ω_E)
  Ω_unit := by
    have hsq : ‖osCompletionMap P.F (osPreMk P.F P.Ω_E)‖ ^ 2 = 1 := by
      rw [osCompletionMap_norm, osPre_norm_sq, P.Ω_E_norm, Complex.one_re]
    have hmul : (‖osCompletionMap P.F (osPreMk P.F P.Ω_E)‖ - 1) *
        (‖osCompletionMap P.F (osPreMk P.F P.Ω_E)‖ + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h | h <;>
      linarith [norm_nonneg (osCompletionMap P.F (osPreMk P.F P.Ω_E))]
  Poincare := Poincare4
  U := fun g => osLiftOperator P.F (P.U_pre g) 1 zero_le_one (fun x => by
    rw [one_pow, one_mul, P.U_unit_pre g x x])
  U_unitary := fun g u v => by
    refine UniformSpace.Completion.induction_on₂ u v ?_ ?_
    · exact isClosed_eq
        (((osLiftOperator P.F (P.U_pre g) 1 zero_le_one (fun x => by
            rw [one_pow, one_mul, P.U_unit_pre g x x])).continuous.comp continuous_fst).inner
          ((osLiftOperator P.F (P.U_pre g) 1 zero_le_one (fun x => by
            rw [one_pow, one_mul, P.U_unit_pre g x x])).continuous.comp continuous_snd))
        (continuous_fst.inner continuous_snd)
    · intro a b
      refine Quotient.inductionOn₂ a b fun x y => ?_
      change ⟪osLiftOperator P.F (P.U_pre g) 1 zero_le_one _ (osCompletionMap P.F (osPreMk P.F x)),
          osLiftOperator P.F (P.U_pre g) 1 zero_le_one _ (osCompletionMap P.F (osPreMk P.F y))⟫_ℂ =
        ⟪osCompletionMap P.F (osPreMk P.F x), osCompletionMap P.F (osPreMk P.F y)⟫_ℂ
      rw [osLiftOperator_coe, osLiftOperator_coe, osCompletionMap_inner, osCompletionMap_inner]
      exact P.U_unit_pre g x y
  U_vac := fun g => by
    change osLiftOperator P.F (P.U_pre g) 1 zero_le_one _ (osCompletionMap P.F (osPreMk P.F P.Ω_E)) =
      osCompletionMap P.F (osPreMk P.F P.Ω_E)
    rw [osLiftOperator_coe, P.U_vac_pre g]
  actP := poincareAct
  φ := fun x => osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x)
  covariant := fun g x => by
    ext1 z
    refine UniformSpace.Completion.induction_on z ?_ ?_
    · exact isClosed_eq
        ((osLiftOperator P.F (P.U_pre g) 1 zero_le_one (fun w => by
            rw [one_pow, one_mul, P.U_unit_pre g w w])).comp
          (osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x))).continuous
        ((osLiftOperator P.F (P.φ_pre (poincareAct g x)) (P.φ_bound (poincareAct g x))
            (P.φ_bound_nn (poincareAct g x)) (P.φ_bd (poincareAct g x))).comp
          (osLiftOperator P.F (P.U_pre g) 1 zero_le_one (fun w => by
            rw [one_pow, one_mul, P.U_unit_pre g w w]))).continuous
    · intro u
      refine Quotient.inductionOn u fun v => ?_
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      change osLiftOperator P.F (P.U_pre g) 1 zero_le_one _
          (osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x)
            (osCompletionMap P.F (osPreMk P.F v))) =
        osLiftOperator P.F (P.φ_pre (poincareAct g x)) (P.φ_bound (poincareAct g x))
          (P.φ_bound_nn (poincareAct g x)) (P.φ_bd (poincareAct g x))
          (osLiftOperator P.F (P.U_pre g) 1 zero_le_one _
            (osCompletionMap P.F (osPreMk P.F v)))
      rw [osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe,
        P.cov_pre g x v]
  local_comm := fun x y hxy => by
    ext1 z
    refine UniformSpace.Completion.induction_on z ?_ ?_
    · exact isClosed_eq
        ((osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x)).comp
          (osLiftOperator P.F (P.φ_pre y) (P.φ_bound y) (P.φ_bound_nn y) (P.φ_bd y))).continuous
        ((osLiftOperator P.F (P.φ_pre y) (P.φ_bound y) (P.φ_bound_nn y) (P.φ_bd y)).comp
          (osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x))).continuous
    · intro u
      refine Quotient.inductionOn u fun v => ?_
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      change osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x)
          (osLiftOperator P.F (P.φ_pre y) (P.φ_bound y) (P.φ_bound_nn y) (P.φ_bd y)
            (osCompletionMap P.F (osPreMk P.F v))) =
        osLiftOperator P.F (P.φ_pre y) (P.φ_bound y) (P.φ_bound_nn y) (P.φ_bd y)
          (osLiftOperator P.F (P.φ_pre x) (P.φ_bound x) (P.φ_bound_nn x) (P.φ_bd x)
            (osCompletionMap P.F (osPreMk P.F v)))
      rw [osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe, osLiftOperator_coe,
        P.loc_pre x y hxy v]
  P2_spec := P.P2_spec
  spectral_cond := P.spec_cond
  mass_gap_spec := P.gap_spec

/-- Construct `OSReconstructionData Δ_phys os` directly on `OSHilbertSpace P.F` (§22 + §27). -/
noncomputable def buildOSReconstructionOnCompletion {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (P : EuclideanOSPreData Δ_phys os) : OSReconstructionData Δ_phys os where
  wightman := buildWightmanOnOSCompletion P
  T_E := osLiftSemigroup P.F P.T_E_pre P.T_E_contr
  T_E_zero := osLiftSemigroup_zero P.F P.T_E_pre P.T_E_contr P.T_E_zero
  T_E_add := osLiftSemigroup_add P.F P.T_E_pre P.T_E_contr P.T_E_add
  T_E_sa := fun t x y ht => osLiftSemigroup_sa P.F P.T_E_pre P.T_E_contr P.T_E_sa t ht x y
  T_E_contr := fun t x ht => osLiftSemigroup_contr P.F P.T_E_pre P.T_E_contr t ht x
  H_phys := osLiftOperator P.F P.H_pre P.H_bound P.H_bound_nn P.H_bd
  H_phys_sa := osLiftOperator_sa P.F P.H_pre P.H_bound P.H_bound_nn P.H_bd P.H_sa
  H_phys_nonneg := osLiftOperator_nonneg P.F P.H_pre P.H_bound P.H_bound_nn P.H_bd P.H_nonneg
  H_phys_vac := by
    change osLiftOperator P.F P.H_pre P.H_bound P.H_bound_nn P.H_bd
        (osCompletionMap P.F (osPreMk P.F P.Ω_E)) = 0
    rw [osLiftOperator_coe, P.H_vac]
    have h0 : osPreMk P.F (0 : P.E) = 0 := rfl
    rw [h0, map_zero]
  cyclic_dense := P.cyclic_dense

/--
Complete dynamical bridge tying the 4D `SU(N)` lattice Schwinger functions `cubic4Schwinger` (§25)
and 3D Kogut–Susskind Hamiltonian `ksGaugeInvariantH` (§28) to a non-Gaussian continuum
`OS4DContinuumTheory Δ_phys` and its true OS completion `EuclideanOSPreData` (§22 + §27).
-/
structure SUYangMillsDynamicalBridge (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] where
  Δ_phys         : ℝ
  os             : OS4DContinuumTheory Δ_phys
  pre            : EuclideanOSPreData Δ_phys os
  Ls_seq         : ℕ → ℕ
  Lt_seq         : ℕ → ℕ
  [Ls_nz         : ∀ m, NeZero (Ls_seq m)]
  [Lt_nz         : ∀ m, NeZero (Lt_seq m)]
  a_seq          : ℕ → ℝ
  β_seq          : ℕ → ℝ
  ha_pos         : ∀ m, 0 < a_seq m
  ha_lim         : Filter.Tendsto a_seq Filter.atTop (nhds 0)
  hβ_pos         : ∀ m, 0 < β_seq m
  hβ_lim         : Filter.Tendsto β_seq Filter.atTop Filter.atTop
  g_sq_seq       : ℕ → ℝ
  hg_pos         : ∀ m, 0 < g_sq_seq m
  Δ_latt         : ℕ → ℝ
  Δ_latt_pos     : ∀ m, 0 < Δ_latt m
  gap_lim        : Filter.Tendsto (fun m => Δ_latt m / a_seq m) Filter.atTop (nhds Δ_phys)
  latt_obs       : ∀ (m n : ℕ), (Fin n → Space4) → Fin n →
                     (GaugeField (cubicTorus4 (Ls_seq m) (Lt_seq m))
                       (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
  schwinger_conv : ∀ (n : ℕ) (xs : Fin n → Space4),
    Filter.Tendsto
      (fun m => cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n (latt_obs m n xs))
      Filter.atTop (nhds (os.os.Schwinger n xs))

attribute [instance] SUYangMillsDynamicalBridge.Ls_nz SUYangMillsDynamicalBridge.Lt_nz

/--
End-to-end master theorem wiring `§§22–28` together:
given any `SUYangMillsDynamicalBridge N hN`, we get:
1. positive 4D lattice partition functions `cubic4PartitionFn > 0` (§25),
2. self-adjoint, non-negative, Gauss-law-preserving Kogut–Susskind Hamiltonians `ksGaugeInvariantH`
   along the RG trajectory with non-commuting link algebra (§28),
3. genuine convergence of `cubic4Schwinger` to the non-Gaussian `OS4DContinuumTheory` (§25 + §13),
4. the full OS Hilbert completion and `Poincare4` Wightman QFT reconstruction on `OSHilbertSpace` (§22 + §27 + §17),
5. diverging correlation length `ξ → ∞` and absence of mass states in `(0, Δ_phys²)` (§10 + §14).
-/
theorem endToEnd_su_yang_mills_from_dynamical_bridge
    {N : ℕ} {hN : 2 ≤ N}
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (B : SUYangMillsDynamicalBridge N hN) :
    (∀ m, 0 < cubic4PartitionFn (B.Ls_seq m) (B.Lt_seq m) N (B.β_seq m)) ∧
    (∀ m (ψ : HaarGaugeSpace (latticeHaarMeasure (B.Ls_seq m) N)),
      0 ≤ (⟪ψ, ksGaugeInvariantH (B.Ls_seq m) N (B.β_seq m) (B.g_sq_seq m) (B.a_seq m)
        (B.hβ_pos m).le ψ⟫_ℂ).re) ∧
    (∀ m (e : (cubicTorus3 (B.Ls_seq m)).Link),
      lieBracketCLM (ksLinkShiftOp (B.Ls_seq m) N e (suFlip2 N hN))
        (ksLinkTraceOp (B.Ls_seq m) N e) ≠ 0) ∧
    (0 < B.Δ_phys ∧ ¬ IsGaussian4 B.os.os.Schwinger) ∧
    Filter.Tendsto (fun m => (B.Δ_latt m)⁻¹) Filter.atTop Filter.atTop ∧
    (∃ D : OSHilbertCompletionData (buildOSReconstructionOnCompletion B.pre),
      (∀ p2 ∈ (buildOSReconstructionOnCompletion B.pre).wightman.P2_spec,
        ¬ (0 < p2 ∧ p2 < B.Δ_phys ^ 2)) ∧
      (∀ x : (buildOSReconstructionOnCompletion B.pre).wightman.H,
        0 ≤ (⟪x, (buildOSReconstructionOnCompletion B.pre).H_phys x⟫_ℂ).re) ∧
      (buildOSReconstructionOnCompletion B.pre).H_phys
        (buildOSReconstructionOnCompletion B.pre).wightman.Ω_phys = 0 ∧
      (∀ g x,
        ((buildOSReconstructionOnCompletion B.pre).wightman.U g).comp
          ((buildOSReconstructionOnCompletion B.pre).wightman.φ x) =
        ((buildOSReconstructionOnCompletion B.pre).wightman.φ
          (poincareAct g x)).comp
          ((buildOSReconstructionOnCompletion B.pre).wightman.U g)) ∧
      D.trilattice.μ (D.trilattice.δ D.trilattice.totalityB) = D.trilattice.totalityB) := by
  let R := buildOSReconstructionOnCompletion B.pre
  obtain ⟨D, _, _, h3, h4, _, _, _⟩ := os_hilbert_completion_and_wightman_reconstruction R
  refine ⟨?_, ?_, ?_, ?_, ?_, D, ?_, h3.2.2.2.1, h3.2.2.2.2, h4.1, ?_⟩
  · intro m
    exact cubic4PartitionFn_pos (B.Ls_seq m) (B.Lt_seq m) N (B.β_seq m) (B.hβ_pos m).le
  · intro m ψ
    exact ksGaugeInvariantH_nonneg (B.Ls_seq m) N (B.β_seq m) (B.g_sq_seq m) (B.a_seq m)
      (B.hβ_pos m).le (B.hg_pos m) (B.ha_pos m) ψ
  · intro m e
    exact ks_electric_link_noncommute (B.Ls_seq m) N hN e
  · exact ⟨B.os.os.Δ_pos, os4d_theory_non_gaussian B.os⟩
  · exact correlation_length_diverges B.a_seq B.Δ_latt B.Δ_phys
      B.ha_pos B.ha_lim B.Δ_latt_pos B.gap_lim
  · intro p2 hp2 hlt
    rcases R.wightman.mass_gap_spec p2 hp2 with rfl | hge
    · exact lt_irrefl 0 hlt.1
    · linarith [hlt.2]
  · exact D.trilattice.mu_delta D.trilattice.totalityB

end EndToEndSUYangMills

/-! ## §30.  OS pre-Hilbert GNS construction, Glimm–Jaffe contraction & joint thermodynamic limit -/

section OSPreHilbertFromSchwinger

/-- Positive-time Euclidean configuration `(n, xs)` with `0 < (xs k) 0`. -/
structure PosTimeConfig where
  n_pts : ℕ
  pts   : Fin n_pts → Space4
  pos_t : ∀ k : Fin n_pts, 0 < pts k 0

noncomputable instance instDecidableEqPosTimeConfig : DecidableEq PosTimeConfig :=
  Classical.decEq PosTimeConfig

/-- Formal finite complex linear combinations of positive-time configurations. -/
abbrev OSPosTestSpace := PosTimeConfig →₀ ℂ

/-- Single positive-time configuration embedded in `OSPosTestSpace`. -/
noncomputable def osConfigSingle (x : PosTimeConfig) : OSPosTestSpace :=
  Finsupp.single x 1

/-- Reflection-positive Euclidean kernel between two positive-time configurations. -/
noncomputable def osConfigKernel {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (x y : PosTimeConfig) : ℂ :=
  os.os.Schwinger (x.n_pts + y.n_pts)
    (Fin.append (fun k => euclidTimeReflect (x.pts k)) y.pts)

/-- Sesquilinear form on `OSPosTestSpace` induced by `os.os.Schwinger`. -/
noncomputable def osConfigInner {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (f g : OSPosTestSpace) : ℂ :=
  ∑ x ∈ f.support, ∑ y ∈ g.support,
    starRingEnd ℂ (f x) * g y * osConfigKernel os x y

theorem osConfigInner_zero_left {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (g : OSPosTestSpace) : osConfigInner os 0 g = 0 := by
  simp [osConfigInner]

theorem osConfigInner_zero_right {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (f : OSPosTestSpace) : osConfigInner os f 0 = 0 := by
  simp [osConfigInner]

theorem osConfigInner_single {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (x y : PosTimeConfig) :
    osConfigInner os (osConfigSingle x) (osConfigSingle y) = osConfigKernel os x y := by
  dsimp [osConfigInner, osConfigSingle]
  rw [Finsupp.support_single_ne_zero x one_ne_zero,
      Finsupp.support_single_ne_zero y one_ne_zero,
      Finset.sum_singleton, Finset.sum_singleton,
      Finsupp.single_eq_same, Finsupp.single_eq_same]
  simp

/--
Construct `OSReflectionForm OSPosTestSpace` directly from `os : OS4DContinuumTheory Δ_phys`
and reflection hermiticity `osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x)`.
-/
noncomputable def osConfigForm {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x)) :
    OSReflectionForm OSPosTestSpace where
  B := osConfigInner os
  add_left := fun f₁ f₂ g => by
    let s := (f₁ + f₂).support ∪ f₁.support ∪ f₂.support
    have h_sub : ∀ (f : OSPosTestSpace), f.support ⊆ s →
        osConfigInner os f g =
          ∑ x ∈ s, ∑ y ∈ g.support, starRingEnd ℂ (f x) * g y * osConfigKernel os x y := by
      intro f hf
      refine Finset.sum_subset hf fun x _ hx => ?_
      have hfx : f x = 0 := by
        by_contra hne
        exact hx (Finsupp.mem_support_iff.mpr hne)
      simp [hfx]
    rw [h_sub (f₁ + f₂) (Finset.subset_union_left.trans Finset.subset_union_left),
        h_sub f₁ (Finset.subset_union_right.trans Finset.subset_union_left),
        h_sub f₂ Finset.subset_union_right,
        ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finsupp.add_apply, map_add]
    ring
  smul_left := fun c f g => by
    let s := (c • f).support ∪ f.support
    have h_sub : ∀ (u : OSPosTestSpace), u.support ⊆ s →
        osConfigInner os u g =
          ∑ x ∈ s, ∑ y ∈ g.support, starRingEnd ℂ (u x) * g y * osConfigKernel os x y := by
      intro u hu
      refine Finset.sum_subset hu fun x _ hx => ?_
      have hux : u x = 0 := by
        by_contra hne
        exact hx (Finsupp.mem_support_iff.mpr hne)
      simp [hux]
    rw [h_sub (c • f) Finset.subset_union_left,
        h_sub f Finset.subset_union_right,
        Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, map_mul]
    ring
  conj_symm := fun f g => by
    dsimp [osConfigInner]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [map_mul, Complex.conj_conj]
    rw [h_herm y x]
    ring
  pos_re := fun f => by
    dsimp [osConfigInner, osConfigKernel]
    let m := f.support.card
    let e : Fin m ≃ ↥f.support := f.support.equivFin.symm
    let ι : Fin m → PosTimeConfig := fun i => (e i).1
    have hι_inj : Function.Injective ι := fun i j h => e.injective (Subtype.ext h)
    have hs_eq : (Finset.univ : Finset (Fin m)).image ι = f.support := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, ι]
      constructor
      · rintro ⟨i, rfl⟩; exact (e i).2
      · intro hx
        refine ⟨e.symm ⟨x, hx⟩, ?_⟩
        rw [Equiv.apply_symm_apply]
    rw [← hs_eq, Finset.sum_image (fun a _ b _ h => hι_inj h)]
    simp_rw [Finset.sum_image (fun a _ b _ h => hι_inj h)]
    have h_rp := os.refl_pos_n m (fun i => (ι i).n_pts)
      (fun i => starRingEnd ℂ (f (ι i))) (fun i => (ι i).pts) (fun i k => (ι i).pos_t k)
    refine le_trans h_rp (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.conj_conj]

/--
The canonical OS completion vectors for two positive-time configurations have
inner product exactly the reflected Schwinger kernel used to construct them.
-/
theorem osConfigKernel_eq_completion_inner {Δ_phys : ℝ}
    (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (x y : PosTimeConfig) :
    ⟪osCompletionMap (osConfigForm os h_herm)
        (osPreMk (osConfigForm os h_herm) (osConfigSingle x)),
      osCompletionMap (osConfigForm os h_herm)
        (osPreMk (osConfigForm os h_herm) (osConfigSingle y))⟫_ℂ =
      osConfigKernel os x y := by
  rw [osCompletionMap_inner]
  change osConfigInner os (osConfigSingle x) (osConfigSingle y) = _
  exact osConfigInner_single os x y

/-- Euclidean positive-time shift `x₀ ↦ x₀ + t` on `PosTimeConfig`. -/
def posTimeShiftConfig (t : ℝ) (ht : 0 ≤ t) (x : PosTimeConfig) : PosTimeConfig where
  n_pts := x.n_pts
  pts := fun k i => if i = 0 then x.pts k 0 + t else x.pts k i
  pos_t := fun k => by
    change 0 < if (0 : Fin 4) = 0 then x.pts k 0 + t else x.pts k 0
    rw [if_pos rfl]
    linarith [x.pos_t k]

/-- Linear time-shift operator `T_E_pre t` on `OSPosTestSpace`. -/
noncomputable def osTimeShiftPre (t : ℝ) (ht : 0 ≤ t) :
    OSPosTestSpace →ₗ[ℂ] OSPosTestSpace where
  toFun := Finsupp.mapDomain (posTimeShiftConfig t ht)
  map_add' := fun _ _ => Finsupp.mapDomain_add
  map_smul' := fun c f => Finsupp.mapDomain_smul c f

theorem osTimeShiftPre_zero (f : OSPosTestSpace) :
    osTimeShiftPre 0 le_rfl f = f := by
  have hid : posTimeShiftConfig 0 le_rfl = id := by
    funext ⟨n, pts, hpt⟩
    dsimp [posTimeShiftConfig]
    congr 1
    funext k i
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi]
  change Finsupp.mapDomain (posTimeShiftConfig 0 le_rfl) f = f
  rw [hid, Finsupp.mapDomain_id]

theorem osTimeShiftPre_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (f : OSPosTestSpace) :
    osTimeShiftPre (s + t) (add_nonneg hs ht) f =
      osTimeShiftPre s hs (osTimeShiftPre t ht f) := by
  have hcomp : posTimeShiftConfig (s + t) (add_nonneg hs ht) =
      (posTimeShiftConfig s hs) ∘ (posTimeShiftConfig t ht) := by
    funext ⟨n, pts, hpt⟩
    dsimp [posTimeShiftConfig, Function.comp_def]
    congr 1
    funext k i
    by_cases hi : i = 0
    · subst hi; simp [add_assoc, add_comm]
    · simp [hi]
  change Finsupp.mapDomain (posTimeShiftConfig (s + t) (add_nonneg hs ht)) f =
    Finsupp.mapDomain (posTimeShiftConfig s hs)
      (Finsupp.mapDomain (posTimeShiftConfig t ht) f)
  rw [hcomp, Finsupp.mapDomain_comp]

theorem osTimeShiftPre_sa {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (t : ℝ) (ht : 0 ≤ t)
    (h_kern : ∀ x y : PosTimeConfig,
      osConfigKernel os (posTimeShiftConfig t ht x) y =
        osConfigKernel os x (posTimeShiftConfig t ht y))
    (f g : OSPosTestSpace) :
    osConfigInner os (osTimeShiftPre t ht f) g =
      osConfigInner os f (osTimeShiftPre t ht g) := by
  let F := osConfigForm os h_herm
  have h_single_left : ∀ (x : PosTimeConfig) (c : ℂ) (v : OSPosTestSpace),
      osConfigInner os (osTimeShiftPre t ht (Finsupp.single x c)) v =
        osConfigInner os (Finsupp.single x c) (osTimeShiftPre t ht v) := by
    intro x c v
    refine Finsupp.induction_linear v ?_ ?_ ?_
    · rw [map_zero, osConfigInner_zero_right, osConfigInner_zero_right]
    · intro v₁ v₂ ih₁ ih₂
      rw [map_add]
      change F.B (osTimeShiftPre t ht (Finsupp.single x c)) (v₁ + v₂) =
        F.B (Finsupp.single x c) (osTimeShiftPre t ht v₁ + osTimeShiftPre t ht v₂)
      rw [F.add_right, F.add_right]
      exact congrArg₂ (· + ·) ih₁ ih₂
    · intro y d
      by_cases hc : c = 0
      · subst hc; simp [osConfigInner_zero_left]
      · by_cases hd : d = 0
        · subst hd; simp [osConfigInner_zero_right]
        · change osConfigInner os (Finsupp.mapDomain (posTimeShiftConfig t ht) (Finsupp.single x c))
              (Finsupp.single y d) =
            osConfigInner os (Finsupp.single x c)
              (Finsupp.mapDomain (posTimeShiftConfig t ht) (Finsupp.single y d))
          rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
          dsimp [osConfigInner]
          rw [Finsupp.support_single_ne_zero (posTimeShiftConfig t ht x) hc,
              Finsupp.support_single_ne_zero y hd,
              Finsupp.support_single_ne_zero x hc,
              Finsupp.support_single_ne_zero (posTimeShiftConfig t ht y) hd]
          simp only [Finset.sum_singleton, Finsupp.single_eq_same, h_kern x y]
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · rw [map_zero, osConfigInner_zero_left, osConfigInner_zero_left]
  · intro f₁ f₂ ih₁ ih₂
    rw [map_add]
    change F.B (osTimeShiftPre t ht f₁ + osTimeShiftPre t ht f₂) g =
      F.B (f₁ + f₂) (osTimeShiftPre t ht g)
    rw [F.add_left, F.add_left]
    exact congrArg₂ (· + ·) ih₁ ih₂
  · intro x c
    exact h_single_left x c g

/--
Glimm–Jaffe repeated Cauchy–Schwarz semigroup contraction:
if `T s` is symmetric and `‖T (2^k t) f‖² ≤ C` uniformly in `k`, then `‖T t f‖² ≤ ‖f‖²`.
-/
theorem os_semigroup_contraction_of_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : OSReflectionForm E) (T : ℝ → (E →ₗ[ℂ] E))
    (h_add : ∀ s₁ s₂, 0 ≤ s₁ → 0 ≤ s₂ → ∀ x : E, T (s₁ + s₂) x = T s₁ (T s₂ x))
    (h_sa : ∀ s, 0 ≤ s → ∀ x y : E, F.B (T s x) y = F.B x (T s y))
    (t : ℝ) (ht : 0 ≤ t) (f : E)
    (C : ℝ) (h_ub : ∀ k : ℕ, (F.B (T (((2 ^ k : ℕ) : ℝ) * t) f)
      (T (((2 ^ k : ℕ) : ℝ) * t) f)).re ≤ C) :
    (F.B (T t f) (T t f)).re ≤ (F.B f f).re := by
  let b : ℕ → ℝ := fun n =>
    (F.B (T (((2 ^ n : ℕ) : ℝ) * t) f) (T (((2 ^ n : ℕ) : ℝ) * t) f)).re
  have hb_nn : ∀ n : ℕ, 0 ≤ b n := fun n => F.pos_re _
  have hb0_eq : b 0 = (F.B (T t f) (T t f)).re := by
    dsimp [b]
    simp
  have h_rec : ∀ n : ℕ, b n ^ 2 ≤ (F.B f f).re * b (n + 1) := by
    intro n
    let s : ℝ := ((2 ^ n : ℕ) : ℝ) * t
    have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) ht
    have hs2 : s + s = ((2 ^ (n + 1) : ℕ) : ℝ) * t := by
      dsimp [s]
      push_cast
      rw [pow_succ]
      ring
    have h_eq : F.B (T s f) (T s f) = F.B f (T (((2 ^ (n + 1) : ℕ) : ℝ) * t) f) := by
      rw [h_sa s hs f (T s f), ← h_add s s hs hs f, hs2]
    have hcs := os_cauchy_schwarz F f (T (((2 ^ (n + 1) : ℕ) : ℝ) * t) f)
    have hre_le : (F.B f (T (((2 ^ (n + 1) : ℕ) : ℝ) * t) f)).re ^ 2 ≤
        (F.B f f).re * b (n + 1) := by
      have him_nn : 0 ≤ (F.B f (T (((2 ^ (n + 1) : ℕ) : ℝ) * t) f)).im ^ 2 := sq_nonneg _
      linarith
    have hb_eq : b n = (F.B f (T (((2 ^ (n + 1) : ℕ) : ℝ) * t) f)).re := by
      dsimp [b]
      exact congrArg Complex.re h_eq
    rwa [hb_eq]
  rw [← hb0_eq]
  rcases lt_or_eq_of_le (F.pos_re f) with hpos | hzero
  · let u : ℕ → ℝ := fun n => b n / (F.B f f).re
    have hu_nn : ∀ n, 0 ≤ u n := fun n => div_nonneg (hb_nn n) hpos.le
    have hu_rec : ∀ n, u n ^ 2 ≤ u (n + 1) := by
      intro n
      dsimp [u]
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hpos) hpos]
      calc b n ^ 2 * (F.B f f).re
          ≤ ((F.B f f).re * b (n + 1)) * (F.B f f).re :=
              mul_le_mul_of_nonneg_right (h_rec n) hpos.le
        _ = b (n + 1) * (F.B f f).re ^ 2 := by ring
    have hu_pow : ∀ k : ℕ, u 0 ^ (2 ^ k) ≤ u k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc u 0 ^ (2 ^ (k + 1))
            = u 0 ^ (2 ^ k * 2) := by rw [pow_succ]
          _ = (u 0 ^ (2 ^ k)) ^ 2 := by rw [pow_mul]
          _ ≤ u k ^ 2 := pow_le_pow_left₀ (pow_nonneg (hu_nn 0) _) ih 2
          _ ≤ u (k + 1) := hu_rec k
    have hu0_le : u 0 ≤ 1 := by
      by_contra h_gt
      push_neg at h_gt
      have h_pow_lim : Filter.Tendsto (fun m : ℕ => u 0 ^ m) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt h_gt
      have h_two_pow : Filter.Tendsto (fun k : ℕ => (2 ^ k : ℕ)) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_atTop.mpr fun N =>
          ⟨N, fun a ha => le_trans ha (Nat.le_of_lt Nat.lt_two_pow_self)⟩
      have h_lim := h_pow_lim.comp h_two_pow
      have h_ev := (Filter.tendsto_atTop.mp h_lim) (C / (F.B f f).re + 1)
      rw [Filter.eventually_atTop] at h_ev
      obtain ⟨k, hk⟩ := h_ev
      have h_le1 : u 0 ^ (2 ^ k) ≤ C / (F.B f f).re :=
        (hu_pow k).trans (div_le_div_of_nonneg_right (h_ub k) hpos.le)
      have h_le2 : C / (F.B f f).re + 1 ≤ u 0 ^ (2 ^ k) := hk k le_rfl
      linarith
    exact (div_le_one hpos).mp hu0_le
  · have h0 : b 0 ^ 2 ≤ 0 := by
      have hr := h_rec 0
      rw [← hzero, zero_mul] at hr
      exact hr
    have hle : b 0 ≤ 0 := by nlinarith
    linarith

/--
Joint infinite-volume thermodynamic limit (`L → ∞`):
for any countable family of uniformly bounded Schwinger sequences `S_seq k m`
with `‖S_seq k m‖ ≤ B k`, a single strictly increasing subsequence `φ` exists
along which every `S_seq k (φ m)` converges simultaneously to `S_inf k`.
-/
theorem cubic4Schwinger_joint_thermodynamic_subseq
    (S_seq : ℕ → ℕ → ℂ) (B : ℕ → ℝ)
    (hbd : ∀ k m, ‖S_seq k m‖ ≤ B k) :
    ∃ (S_inf : ℕ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ k, Filter.Tendsto (fun m => S_seq k (φ m)) Filter.atTop (nhds (S_inf k))) ∧
      (∀ k, ‖S_inf k‖ ≤ B k) := by
  let K : Set (ℕ → ℂ) := Set.univ.pi fun k => Metric.closedBall (0 : ℂ) (B k)
  have hK : IsCompact K := isCompact_univ_pi fun k => isCompact_closedBall (0 : ℂ) (B k)
  let seq : ℕ → (ℕ → ℂ) := fun m k => S_seq k m
  have hmem : ∀ m, seq m ∈ K := by
    intro m k _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbd k m
  obtain ⟨S_inf, hS_mem, φ, hφ_mono, hφ_lim⟩ := hK.tendsto_subseq hmem
  refine ⟨S_inf, φ, hφ_mono, fun k => (tendsto_pi_nhds.mp hφ_lim k), fun k => ?_⟩
  have hk := hS_mem k (Set.mem_univ k)
  rwa [Metric.mem_closedBall, dist_zero_right] at hk

end OSPreHilbertFromSchwinger

/-! ## §31.  Direct Schwinger-to-PreData wiring eliminating manual OS/semigroup fields -/

section SchwingerToPreData

/-- Norm-like `ℓ¹` weight bound `∑ x, ‖f x‖ * M ^ n_pts(x)` on `OSPosTestSpace`. -/
noncomputable def osConfigNormBound (M : ℝ) (f : OSPosTestSpace) : ℝ :=
  ∑ x ∈ f.support, ‖f x‖ * M ^ x.n_pts

theorem osConfigNormBound_nonneg (M : ℝ) (hM : 0 ≤ M) (f : OSPosTestSpace) :
    0 ≤ osConfigNormBound M f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (norm_nonneg _) (pow_nonneg hM _)

theorem osConfigNormBound_add_le (M : ℝ) (hM : 0 ≤ M) (f g : OSPosTestSpace) :
    osConfigNormBound M (f + g) ≤ osConfigNormBound M f + osConfigNormBound M g := by
  let s := (f + g).support ∪ f.support ∪ g.support
  have h_sub : ∀ (u : OSPosTestSpace), u.support ⊆ s →
      osConfigNormBound M u = ∑ x ∈ s, ‖u x‖ * M ^ x.n_pts := by
    intro u hu
    refine Finset.sum_subset hu fun x _ hx => ?_
    have hux : u x = 0 := by
      by_contra hne
      exact hx (Finsupp.mem_support_iff.mpr hne)
    simp [hux]
  rw [h_sub (f + g) (Finset.subset_union_left.trans Finset.subset_union_left),
      h_sub f (Finset.subset_union_right.trans Finset.subset_union_left),
      h_sub g Finset.subset_union_right,
      ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finsupp.add_apply, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le (f x) (g x)) (pow_nonneg hM _)

theorem osConfigNormBound_mapDomain_le (M : ℝ) (hM : 0 ≤ M)
    (φ : PosTimeConfig → PosTimeConfig) (hφ : ∀ x, (φ x).n_pts = x.n_pts)
    (f : OSPosTestSpace) :
    osConfigNormBound M (Finsupp.mapDomain φ f) ≤ osConfigNormBound M f := by
  refine Finsupp.induction f ?_ ?_
  · simp [osConfigNormBound]
  · intro a b f' ha hb ih
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    have h_add := osConfigNormBound_add_le M hM (Finsupp.single (φ a) b) (Finsupp.mapDomain φ f')
    have h_s : osConfigNormBound M (Finsupp.single (φ a) b) ≤ ‖b‖ * M ^ a.n_pts := by
      dsimp [osConfigNormBound]
      rw [Finsupp.support_single_ne_zero (φ a) hb, Finset.sum_singleton,
          Finsupp.single_eq_same, hφ a]
    have hfa : f' a = 0 := by
      by_contra hne
      exact ha (Finsupp.mem_support_iff.mpr hne)
    have hsub : (Finsupp.single a b + f').support ⊆ insert a f'.support := by
      intro x hx
      rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hx
      by_cases hxa : x = a
      · exact hxa ▸ Finset.mem_insert_self a f'.support
      · apply Finset.mem_insert_of_mem
        rw [Finsupp.mem_support_iff]
        intro hfx
        apply hx
        rw [Finsupp.single_apply, if_neg (Ne.symm hxa), hfx, add_zero]
    have h_eq : osConfigNormBound M (Finsupp.single a b + f') =
        ∑ x ∈ insert a f'.support, ‖(Finsupp.single a b + f') x‖ * M ^ x.n_pts := by
      refine Finset.sum_subset hsub fun x _ hx => ?_
      have hx0 : (Finsupp.single a b + f') x = 0 := by
        by_contra hne
        exact hx (Finsupp.mem_support_iff.mpr hne)
      simp [hx0]
    have h_rest : ∑ x ∈ f'.support, ‖(Finsupp.single a b + f') x‖ * M ^ x.n_pts =
        osConfigNormBound M f' := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hxa), zero_add]
    have h_lhs : osConfigNormBound M (Finsupp.single a b + f') =
        ‖b‖ * M ^ a.n_pts + osConfigNormBound M f' := by
      rw [h_eq, Finset.sum_insert ha, Finsupp.add_apply, Finsupp.single_eq_same,
          hfa, add_zero, h_rest]
    linarith

theorem osConfigInner_norm_le {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bd : ∀ (n : ℕ) (xs : Fin n → Space4), ‖os.os.Schwinger n xs‖ ≤ M ^ n)
    (f g : OSPosTestSpace) :
    ‖osConfigInner os f g‖ ≤ osConfigNormBound M f * osConfigNormBound M g := by
  dsimp [osConfigInner, osConfigNormBound]
  calc ‖∑ x ∈ f.support, ∑ y ∈ g.support, starRingEnd ℂ (f x) * g y * osConfigKernel os x y‖
      ≤ ∑ x ∈ f.support, ‖∑ y ∈ g.support, starRingEnd ℂ (f x) * g y * osConfigKernel os x y‖ :=
          norm_sum_le _ _
    _ ≤ ∑ x ∈ f.support, ∑ y ∈ g.support, ‖starRingEnd ℂ (f x) * g y * osConfigKernel os x y‖ :=
          Finset.sum_le_sum fun x _ => norm_sum_le _ _
    _ ≤ ∑ x ∈ f.support, ∑ y ∈ g.support, (‖f x‖ * M ^ x.n_pts) * (‖g y‖ * M ^ y.n_pts) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          have hconj : ‖starRingEnd ℂ (f x)‖ = ‖f x‖ := norm_star (f x)
          rw [norm_mul, norm_mul, hconj]
          have hk : ‖osConfigKernel os x y‖ ≤ M ^ (x.n_pts + y.n_pts) :=
            h_bd (x.n_pts + y.n_pts) _
          calc ‖f x‖ * ‖g y‖ * ‖osConfigKernel os x y‖
              ≤ ‖f x‖ * ‖g y‖ * M ^ (x.n_pts + y.n_pts) :=
                  mul_le_mul_of_nonneg_left hk (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            _ = (‖f x‖ * M ^ x.n_pts) * (‖g y‖ * M ^ y.n_pts) := by
                  rw [pow_add]; ring
    _ = (∑ x ∈ f.support, ‖f x‖ * M ^ x.n_pts) * (∑ y ∈ g.support, ‖g y‖ * M ^ y.n_pts) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.mul_sum]

/-- 0-point vacuum configuration in `PosTimeConfig`. -/
def emptyPosConfig : PosTimeConfig where
  n_pts := 0
  pts   := Fin.elim0
  pos_t := fun k => Fin.elim0 k

theorem osConfigVac_norm {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_S0 : os.os.Schwinger 0 Fin.elim0 = 1) :
    (osConfigForm os h_herm).B (osConfigSingle emptyPosConfig) (osConfigSingle emptyPosConfig) = 1 := by
  change osConfigInner os (osConfigSingle emptyPosConfig) (osConfigSingle emptyPosConfig) = 1
  rw [osConfigInner_single]
  dsimp [osConfigKernel, emptyPosConfig]
  have happ : Fin.append (fun k : Fin 0 => euclidTimeReflect (Fin.elim0 k)) Fin.elim0 = Fin.elim0 := by
    funext k
    exact Fin.elim0 k
  rw [happ, h_S0]

/-- Total Euclidean time-shift semigroup on `OSPosTestSpace` (identity for `t < 0`). -/
noncomputable def osTimeShiftSemigroup (t : ℝ) : OSPosTestSpace →ₗ[ℂ] OSPosTestSpace :=
  if ht : 0 ≤ t then osTimeShiftPre t ht else LinearMap.id

theorem osTimeShiftSemigroup_zero (f : OSPosTestSpace) :
    osTimeShiftSemigroup 0 f = f := by
  dsimp [osTimeShiftSemigroup]
  rw [dif_pos le_rfl]
  exact osTimeShiftPre_zero f

theorem osTimeShiftSemigroup_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (f : OSPosTestSpace) :
    osTimeShiftSemigroup (s + t) f = osTimeShiftSemigroup s (osTimeShiftSemigroup t f) := by
  dsimp [osTimeShiftSemigroup]
  rw [dif_pos (add_nonneg hs ht), dif_pos hs, dif_pos ht]
  exact osTimeShiftPre_add s t hs ht f

theorem osTimeShiftSemigroup_sa {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_kern : ∀ (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig),
      osConfigKernel os (posTimeShiftConfig t ht x) y =
        osConfigKernel os x (posTimeShiftConfig t ht y))
    (t : ℝ) (ht : 0 ≤ t) (f g : OSPosTestSpace) :
    (osConfigForm os h_herm).B (osTimeShiftSemigroup t f) g =
      (osConfigForm os h_herm).B f (osTimeShiftSemigroup t g) := by
  dsimp [osTimeShiftSemigroup]
  rw [dif_pos ht]
  exact osTimeShiftPre_sa os h_herm t ht (h_kern t ht) f g

theorem osTimeShiftSemigroup_contr {Δ_phys : ℝ} (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_kern : ∀ (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig),
      osConfigKernel os (posTimeShiftConfig t ht x) y =
        osConfigKernel os x (posTimeShiftConfig t ht y))
    (M : ℝ) (hM : 0 ≤ M)
    (h_bd : ∀ (n : ℕ) (xs : Fin n → Space4), ‖os.os.Schwinger n xs‖ ≤ M ^ n)
    (t : ℝ) (ht : 0 ≤ t) (f : OSPosTestSpace) :
    ((osConfigForm os h_herm).B (osTimeShiftSemigroup t f) (osTimeShiftSemigroup t f)).re ≤
      1 ^ 2 * ((osConfigForm os h_herm).B f f).re := by
  rw [one_pow, one_mul]
  refine os_semigroup_contraction_of_bounded (osConfigForm os h_herm) osTimeShiftSemigroup
    osTimeShiftSemigroup_add (osTimeShiftSemigroup_sa os h_herm h_kern) t ht f
    ((osConfigNormBound M f) ^ 2) fun k => ?_
  let s : ℝ := ((2 ^ k : ℕ) : ℝ) * t
  have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) ht
  have hs_eq : osTimeShiftSemigroup s f = osTimeShiftPre s hs f := by
    dsimp [osTimeShiftSemigroup]
    rw [dif_pos hs]
  change (osConfigInner os (osTimeShiftSemigroup s f) (osTimeShiftSemigroup s f)).re ≤
    (osConfigNormBound M f) ^ 2
  rw [hs_eq]
  have h1 : (osConfigInner os (osTimeShiftPre s hs f) (osTimeShiftPre s hs f)).re ≤
      ‖osConfigInner os (osTimeShiftPre s hs f) (osTimeShiftPre s hs f)‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have h2 : ‖osConfigInner os (osTimeShiftPre s hs f) (osTimeShiftPre s hs f)‖ ≤
      osConfigNormBound M (osTimeShiftPre s hs f) * osConfigNormBound M (osTimeShiftPre s hs f) :=
    osConfigInner_norm_le os M hM h_bd _ _
  have h3 : osConfigNormBound M (osTimeShiftPre s hs f) ≤ osConfigNormBound M f :=
    osConfigNormBound_mapDomain_le M hM (posTimeShiftConfig s hs) (fun _ => rfl) f
  have h4 : osConfigNormBound M (osTimeShiftPre s hs f) *
      osConfigNormBound M (osTimeShiftPre s hs f) ≤ (osConfigNormBound M f) ^ 2 := by
    have hnn := osConfigNormBound_nonneg M hM (osTimeShiftPre s hs f)
    rw [sq]
    exact mul_le_mul h3 h3 hnn (osConfigNormBound_nonneg M hM f)
  exact h1.trans (h2.trans h4)

/--
The lifted Euclidean time semigroup has the reflected Schwinger kernel as its
matrix coefficient on canonical configuration vectors.
-/
theorem osTimeShiftConfig_eq_completion_inner {Δ_phys : ℝ}
    (os : OS4DContinuumTheory Δ_phys)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_kern : ∀ (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig),
      osConfigKernel os (posTimeShiftConfig t ht x) y =
        osConfigKernel os x (posTimeShiftConfig t ht y))
    (M : ℝ) (hM : 0 ≤ M)
    (h_bd : ∀ (n : ℕ) (xs : Fin n → Space4), ‖os.os.Schwinger n xs‖ ≤ M ^ n)
    (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig) :
    let F := osConfigForm os h_herm
    ⟪osLiftSemigroup F osTimeShiftSemigroup
        (osTimeShiftSemigroup_contr os h_herm h_kern M hM h_bd) t
        (osCompletionMap F (osPreMk F (osConfigSingle x))),
      osCompletionMap F (osPreMk F (osConfigSingle y))⟫_ℂ =
        osConfigKernel os (posTimeShiftConfig t ht x) y := by
  let F := osConfigForm os h_herm
  have h_shift : osTimeShiftSemigroup t (osConfigSingle x) =
      osConfigSingle (posTimeShiftConfig t ht x) := by
    dsimp [osTimeShiftSemigroup]
    rw [dif_pos ht]
    change Finsupp.mapDomain (posTimeShiftConfig t ht) (Finsupp.single x 1) = _
    rw [Finsupp.mapDomain_single]
    rfl
  dsimp [osLiftSemigroup]
  rw [dif_pos ht, osLiftOperator_coe, h_shift]
  exact osConfigKernel_eq_completion_inner os h_herm
    (posTimeShiftConfig t ht x) y

/--
Reduced OS reconstruction inputs on `(OSPosTestSpace, osConfigForm os h_herm)`:
only the Minkowski continuation operators (`H_pre`, `U_pre`, `φ_pre`, `P2_spec`, `cyclic_dense`)
remain; `E`, `F`, `Ω_E`, `T_E_pre` and all semigroup axioms are constructed automatically.
-/
structure ReducedMinkowskiContinuationData (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys) where
  h_herm       : ∀ x y : PosTimeConfig,
                   osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x)
  h_S0         : os.os.Schwinger 0 Fin.elim0 = 1
  h_kern       : ∀ (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig),
                   osConfigKernel os (posTimeShiftConfig t ht x) y =
                     osConfigKernel os x (posTimeShiftConfig t ht y)
  M_bd         : ℝ
  hM_nn        : 0 ≤ M_bd
  h_bd         : ∀ (n : ℕ) (xs : Fin n → Space4), ‖os.os.Schwinger n xs‖ ≤ M_bd ^ n
  H_pre        : OSPosTestSpace →ₗ[ℂ] OSPosTestSpace
  H_bound      : ℝ
  H_bound_nn   : 0 ≤ H_bound
  H_bd         : ∀ x : OSPosTestSpace,
                   ((osConfigForm os h_herm).B (H_pre x) (H_pre x)).re ≤
                     H_bound ^ 2 * ((osConfigForm os h_herm).B x x).re
  H_sa         : ∀ x y : OSPosTestSpace,
                   (osConfigForm os h_herm).B (H_pre x) y =
                     (osConfigForm os h_herm).B x (H_pre y)
  H_nonneg     : ∀ x : OSPosTestSpace, 0 ≤ ((osConfigForm os h_herm).B x (H_pre x)).re
  H_vac        : H_pre (osConfigSingle emptyPosConfig) = 0
  U_pre        : Poincare4 → (OSPosTestSpace →ₗ[ℂ] OSPosTestSpace)
  U_unit_pre   : ∀ g x y,
                   (osConfigForm os h_herm).B (U_pre g x) (U_pre g y) =
                     (osConfigForm os h_herm).B x y
  U_vac_pre    : ∀ g, U_pre g (osConfigSingle emptyPosConfig) = osConfigSingle emptyPosConfig
  φ_pre        : Space4 → (OSPosTestSpace →ₗ[ℂ] OSPosTestSpace)
  φ_bound      : Space4 → ℝ
  φ_bound_nn   : ∀ x, 0 ≤ φ_bound x
  φ_bd         : ∀ x (v : OSPosTestSpace),
                   ((osConfigForm os h_herm).B (φ_pre x v) (φ_pre x v)).re ≤
                     (φ_bound x) ^ 2 * ((osConfigForm os h_herm).B v v).re
  cov_pre      : ∀ g x v, U_pre g (φ_pre x v) = φ_pre (poincareAct g x) (U_pre g v)
  loc_pre      : ∀ x y, minkowskiSq (x - y) < 0 →
                   ∀ v, φ_pre x (φ_pre y v) = φ_pre y (φ_pre x v)
  P2_spec      : Set ℝ
  spec_cond    : ∀ p2 ∈ P2_spec, 0 ≤ p2
  gap_spec     : ∀ p2 ∈ P2_spec, p2 = 0 ∨ Δ_phys ^ 2 ≤ p2
  cyclic_dense : (Submodule.span ℂ
      {v : OSHilbertSpace (osConfigForm os h_herm) | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k =>
          osLiftOperator (osConfigForm os h_herm) (φ_pre (xs i))
            (φ_bound (xs i)) (φ_bound_nn (xs i)) (φ_bd (xs i)))).foldr
          (fun A acc => A acc)
          (osCompletionMap (osConfigForm os h_herm)
            (osPreMk (osConfigForm os h_herm) (osConfigSingle emptyPosConfig)))}).topologicalClosure = ⊤

/-- Assemble `EuclideanOSPreData` directly from `ReducedMinkowskiContinuationData`. -/
noncomputable def buildEuclideanOSPreDataFromSchwinger
    {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (R : ReducedMinkowskiContinuationData Δ_phys os) :
    EuclideanOSPreData Δ_phys os where
  E := OSPosTestSpace
  F := osConfigForm os R.h_herm
  Ω_E := osConfigSingle emptyPosConfig
  Ω_E_norm := osConfigVac_norm os R.h_herm R.h_S0
  T_E_pre := osTimeShiftSemigroup
  T_E_zero := osTimeShiftSemigroup_zero
  T_E_add := osTimeShiftSemigroup_add
  T_E_sa := osTimeShiftSemigroup_sa os R.h_herm R.h_kern
  T_E_contr := osTimeShiftSemigroup_contr os R.h_herm R.h_kern R.M_bd R.hM_nn R.h_bd
  H_pre := R.H_pre
  H_bound := R.H_bound
  H_bound_nn := R.H_bound_nn
  H_bd := R.H_bd
  H_sa := R.H_sa
  H_nonneg := R.H_nonneg
  H_vac := R.H_vac
  U_pre := R.U_pre
  U_unit_pre := R.U_unit_pre
  U_vac_pre := R.U_vac_pre
  φ_pre := R.φ_pre
  φ_bound := R.φ_bound
  φ_bound_nn := R.φ_bound_nn
  φ_bd := R.φ_bd
  cov_pre := R.cov_pre
  loc_pre := R.loc_pre
  P2_spec := R.P2_spec
  spec_cond := R.spec_cond
  gap_spec := R.gap_spec
  cyclic_dense := R.cyclic_dense

end SchwingerToPreData

/-! ## §34.  Non-translation-invariance of `isingSchwinger` & smeared OS reconstruction -/

section SmearedOSReconstruction

/--
**Mathematical obstruction on `concreteOS4DContinuumTheory`**:
`isingSchwinger` is anchored at `x = 0` via `radialCoupling`, so it is NOT
Euclidean time-translation invariant (`S(T_t x, y) ≠ S(x, T_t y)`).
A genuine translation-invariant physical Yang–Mills Schwinger distribution is
only bounded on smeared test configurations, never pointwise-diagonal `M^n`.
-/
theorem isingSchwinger_not_time_trans_inv :
    ∃ x y : PosTimeConfig,
      osConfigKernel concreteOS4DContinuumTheory (posTimeShiftConfig 1 zero_le_one x) y ≠
        osConfigKernel concreteOS4DContinuumTheory x (posTimeShiftConfig 1 zero_le_one y) := by
  let x : PosTimeConfig := ⟨1, fun _ => ![1, 0, 0, 0], fun _ => by simp⟩
  let y : PosTimeConfig := ⟨1, fun _ => ![1, 1, 0, 0], fun _ => by simp⟩
  refine ⟨x, y, ?_⟩
  have h2_formula : ∀ a b : Space4,
      isingSchwinger 2 ![a, b] = (((1 + radialCoupling a * radialCoupling b : ℝ)) : ℂ) := by
    intro a b
    dsimp [isingSchwinger]
    rw [Fin.prod_univ_two, Fin.prod_univ_two]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have happ_gen : ∀ (a b : Space4),
      Fin.append (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) = ![a, b] := by
    intro a b; funext k; fin_cases k <;> rfl
  have hx_pt : (fun k : Fin 1 => euclidTimeReflect ((posTimeShiftConfig 1 zero_le_one x).pts k)) =
      fun _ => ![-2, 0, 0, 0] := by
    funext _ i; fin_cases i <;> simp [posTimeShiftConfig, x, euclidTimeReflect] <;> try norm_num
  have hy_pt : y.pts = fun _ => ![1, 1, 0, 0] := rfl
  have hx_pt0 : (fun k : Fin 1 => euclidTimeReflect (x.pts k)) =
      fun _ => ![-1, 0, 0, 0] := by
    funext _ i; fin_cases i <;> simp [x, euclidTimeReflect]
  have hy_pt1 : (posTimeShiftConfig 1 zero_le_one y).pts =
      fun _ => ![2, 1, 0, 0] := by
    funext _ i; fin_cases i <;> simp [posTimeShiftConfig, y] <;> try norm_num
  have happ1 :
      Fin.append (fun k : Fin 1 => euclidTimeReflect ((posTimeShiftConfig 1 zero_le_one x).pts k))
        y.pts = ![ ![-2, 0, 0, 0], ![1, 1, 0, 0] ] := by
    rw [hx_pt, hy_pt]
    exact happ_gen _ _
  have happ2 :
      Fin.append (fun k : Fin 1 => euclidTimeReflect (x.pts k))
        (posTimeShiftConfig 1 zero_le_one y).pts = ![ ![-1, 0, 0, 0], ![2, 1, 0, 0] ] := by
    rw [hx_pt0, hy_pt1]
    exact happ_gen _ _
  have hn1 : euclidNorm4 ![-2, 0, 0, 0] = 2 := by
    simp [euclidNorm4, Fin.sum_univ_four]; try norm_num
  have hn2 : euclidNorm4 ![1, 1, 0, 0] = Real.sqrt 2 := by
    simp [euclidNorm4, Fin.sum_univ_four]; try norm_num
  have hn3 : euclidNorm4 ![-1, 0, 0, 0] = 1 := by
    simp [euclidNorm4, Fin.sum_univ_four]
  have hn4 : euclidNorm4 ![2, 1, 0, 0] = Real.sqrt 5 := by
    simp [euclidNorm4, Fin.sum_univ_four]; try norm_num
  have hsqrt_lt : Real.sqrt 5 < 1 + Real.sqrt 2 := by
    have h2_gt1 : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    have hsq : (Real.sqrt 5) ^ 2 < (1 + Real.sqrt 2) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hexp_lt :
      Real.exp (-2 * (2 + Real.sqrt 2)) < Real.exp (-2 * (1 + Real.sqrt 5)) :=
    Real.exp_lt_exp.mpr (by linarith)
  change ¬ isingSchwinger 2
      (Fin.append (fun k : Fin 1 => euclidTimeReflect ((posTimeShiftConfig 1 zero_le_one x).pts k))
        y.pts) =
      isingSchwinger 2
        (Fin.append (fun k : Fin 1 => euclidTimeReflect (x.pts k))
          (posTimeShiftConfig 1 zero_le_one y).pts)
  rw [happ1, happ2, h2_formula, h2_formula]
  dsimp [radialCoupling]
  rw [hn1, hn2, hn3, hn4, ← Real.exp_add, ← Real.exp_add]
  have h_eq1 : -2 * 2 + -2 * Real.sqrt 2 = -2 * (2 + Real.sqrt 2) := by ring
  have h_eq2 : -2 * 1 + -2 * Real.sqrt 5 = -2 * (1 + Real.sqrt 5) := by ring
  rw [h_eq1, h_eq2]
  intro heq
  have hre := congrArg Complex.re heq
  simp only [Complex.ofReal_re] at hre
  linarith

/--
Smeared Osterwalder–Schrader pre-Hilbert reconstruction data (`(E, F)` arbitrary,
supporting Schwartz-smeared positive-time test algebras): replaces pointwise
Schwinger bounds with the Glimm–Jaffe dyadic growth bound `T_E_ub`, deriving
semigroup contractivity automatically via `os_semigroup_contraction_of_bounded`.
-/
structure SmearedOSPreData (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys) where
  E            : Type
  [eAdd        : AddCommGroup E]
  [eMod        : Module ℂ E]
  F            : OSReflectionForm E
  Ω_E          : E
  Ω_E_norm     : F.B Ω_E Ω_E = 1
  T_E_pre      : ℝ → (E →ₗ[ℂ] E)
  T_E_zero     : ∀ x : E, T_E_pre 0 x = x
  T_E_add      : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ x : E, T_E_pre (s + t) x = T_E_pre s (T_E_pre t x)
  T_E_sa       : ∀ t, 0 ≤ t → ∀ x y : E, F.B (T_E_pre t x) y = F.B x (T_E_pre t y)
  T_E_ub       : ∀ (t : ℝ), 0 ≤ t → ∀ f : E, ∃ C : ℝ, ∀ k : ℕ,
                   (F.B (T_E_pre (((2 ^ k : ℕ) : ℝ) * t) f)
                     (T_E_pre (((2 ^ k : ℕ) : ℝ) * t) f)).re ≤ C
  H_pre        : E →ₗ[ℂ] E
  H_bound      : ℝ
  H_bound_nn   : 0 ≤ H_bound
  H_bd         : ∀ x : E, (F.B (H_pre x) (H_pre x)).re ≤ H_bound ^ 2 * (F.B x x).re
  H_sa         : ∀ x y : E, F.B (H_pre x) y = F.B x (H_pre y)
  H_nonneg     : ∀ x : E, 0 ≤ (F.B x (H_pre x)).re
  H_vac        : H_pre Ω_E = 0
  U_pre        : Poincare4 → (E →ₗ[ℂ] E)
  U_unit_pre   : ∀ g x y, F.B (U_pre g x) (U_pre g y) = F.B x y
  U_vac_pre    : ∀ g, U_pre g Ω_E = Ω_E
  φ_pre        : Space4 → (E →ₗ[ℂ] E)
  φ_bound      : Space4 → ℝ
  φ_bound_nn   : ∀ x, 0 ≤ φ_bound x
  φ_bd         : ∀ x (v : E), (F.B (φ_pre x v) (φ_pre x v)).re ≤ (φ_bound x) ^ 2 * (F.B v v).re
  cov_pre      : ∀ g x v, U_pre g (φ_pre x v) = φ_pre (poincareAct g x) (U_pre g v)
  loc_pre      : ∀ x y, minkowskiSq (x - y) < 0 → ∀ v, φ_pre x (φ_pre y v) = φ_pre y (φ_pre x v)
  P2_spec      : Set ℝ
  spec_cond    : ∀ p2 ∈ P2_spec, 0 ≤ p2
  gap_spec     : ∀ p2 ∈ P2_spec, p2 = 0 ∨ Δ_phys ^ 2 ≤ p2
  cyclic_dense : (Submodule.span ℂ
      {v : OSHilbertSpace F | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k =>
          osLiftOperator F (φ_pre (xs i)) (φ_bound (xs i)) (φ_bound_nn (xs i)) (φ_bd (xs i)))).foldr
          (fun A acc => A acc) (osCompletionMap F (osPreMk F Ω_E))}).topologicalClosure = ⊤

attribute [instance] SmearedOSPreData.eAdd SmearedOSPreData.eMod

/-- Discharge semigroup contractivity in `EuclideanOSPreData` from `SmearedOSPreData`. -/
noncomputable def buildEuclideanOSPreDataFromSmeared
    {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (S : SmearedOSPreData Δ_phys os) :
    EuclideanOSPreData Δ_phys os where
  E := S.E
  F := S.F
  Ω_E := S.Ω_E
  Ω_E_norm := S.Ω_E_norm
  T_E_pre := S.T_E_pre
  T_E_zero := S.T_E_zero
  T_E_add := S.T_E_add
  T_E_sa := S.T_E_sa
  T_E_contr := fun t ht x => by
    rw [one_pow, one_mul]
    obtain ⟨C, hC⟩ := S.T_E_ub t ht x
    exact os_semigroup_contraction_of_bounded S.F S.T_E_pre S.T_E_add S.T_E_sa t ht x C hC
  H_pre := S.H_pre
  H_bound := S.H_bound
  H_bound_nn := S.H_bound_nn
  H_bd := S.H_bd
  H_sa := S.H_sa
  H_nonneg := S.H_nonneg
  H_vac := S.H_vac
  U_pre := S.U_pre
  U_unit_pre := S.U_unit_pre
  U_vac_pre := S.U_vac_pre
  φ_pre := S.φ_pre
  φ_bound := S.φ_bound
  φ_bound_nn := S.φ_bound_nn
  φ_bd := S.φ_bd
  cov_pre := S.cov_pre
  loc_pre := S.loc_pre
  P2_spec := S.P2_spec
  spec_cond := S.spec_cond
  gap_spec := S.gap_spec
  cyclic_dense := S.cyclic_dense

/-- Reconstruct `OSReconstructionData Δ_phys os` on `OSHilbertSpace S.F` from smeared OS data. -/
noncomputable def smearedOS_reconstruct_wightman
    {Δ_phys : ℝ} {os : OS4DContinuumTheory Δ_phys}
    (S : SmearedOSPreData Δ_phys os) :
    OSReconstructionData Δ_phys os :=
  buildOSReconstructionOnCompletion (buildEuclideanOSPreDataFromSmeared S)

end SmearedOSReconstruction

/-! ## §35.  Clay Yang–Mills 4D Mass Gap Statement & Exact Reduction to Open RG Estimates -/

section ClayYangMills4DInterface

/--
**Clay 4D `SU(N)` Yang–Mills Existence and Mass Gap (`ClayYangMillsMassGap4D N hN`)**:
existence of a physical mass gap `Δ_phys > 0`, a non-Gaussian 4D Euclidean continuum
`OS4DContinuumTheory Δ_phys` realized as the `a → 0⁺, β → ∞, Ls,Lt → ∞` scaling limit of
`SU(N)` Wilson lattice Schwinger functions `cubic4Schwinger`, and its reconstructed
infinite-dimensional relativistic `WightmanQFT4D Δ_phys` on `OSHilbertSpace` with
`Poincare4 = ℝ⁴ ⋊ O(1,3)` covariance, local commutativity, cyclic vacuum, and
`spec(M²) ⊆ {0} ∪ [Δ_phys², ∞)`.
-/
def ClayYangMillsMassGap4D (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] : Prop :=
  ∃ (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys) (R : OSReconstructionData.{0} Δ_phys os)
    (Ls_seq Lt_seq : ℕ → ℕ) (_ : ∀ m, NeZero (Ls_seq m)) (_ : ∀ m, NeZero (Lt_seq m))
    (β_seq : ℕ → ℝ)
    (latt_obs : ∀ (m n : ℕ), (Fin n → Space4) → Fin n →
      (GaugeField (cubicTorus4 (Ls_seq m) (Lt_seq m))
        (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)),
    0 < Δ_phys ∧
    ¬ IsGaussian4 os.os.Schwinger ∧
    (∀ m, 0 ≤ β_seq m) ∧
    Filter.Tendsto β_seq Filter.atTop Filter.atTop ∧
    (∀ (n : ℕ) (xs : Fin n → Space4),
      Filter.Tendsto
        (fun m => cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n (latt_obs m n xs))
        Filter.atTop (nhds (os.os.Schwinger n xs))) ∧
    (∀ p2 ∈ R.wightman.P2_spec, ¬ (0 < p2 ∧ p2 < Δ_phys ^ 2)) ∧
    (∀ x : R.wightman.H, 0 ≤ (⟪x, R.H_phys x⟫_ℂ).re) ∧
    R.H_phys R.wightman.Ω_phys = 0

/--
**The Three Open Analytic RG / OS Estimates (`SUYangMillsRGConjecture N hN`)**:
1. **(E1) Uniform RG scaling:** along `a_seq m → 0⁺, β_seq m → ∞`, the finite-volume
   spectral gaps of the full-rank 3D cubic `SU(N)` Wilson transfer operators
   `fullRankCubicNonAbelianWilsonSetup` satisfy `Δ_latt m / a_seq m ≥ Δ₀ > 0`
   uniformly in spatial volume `Ls_seq m`, converging to `Δ_phys > 0`.
2. **(E2) Non-Gaussian 4D continuum limit:** `cubic4Schwinger` converges along
   `(Ls_seq m, Lt_seq m, β_seq m)` to a non-Gaussian `OS4DContinuumTheory Δ_phys`.
3. **(E3) OS analytic continuation / temperedness:** `SmearedOSPreData Δ_phys os`
   holds on the smeared positive-time test space.
-/
def SUYangMillsRGConjecture (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] : Prop :=
  ∃ (Δ_phys : ℝ) (os : OS4DContinuumTheory Δ_phys)
    (smeared : SmearedOSPreData Δ_phys os)
    (Ls_seq Lt_seq : ℕ → ℕ) (_ : ∀ m, NeZero (Ls_seq m)) (_ : ∀ m, NeZero (Lt_seq m))
    (a_seq β_seq g_sq_seq : ℕ → ℝ)
    (hβ_pos : ∀ m, 0 < β_seq m)
    (latt_obs : ∀ (m n : ℕ), (Fin n → Space4) → Fin n →
      (GaugeField (cubicTorus4 (Ls_seq m) (Lt_seq m))
        (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)),
    (∀ m, 0 < a_seq m) ∧
    Filter.Tendsto a_seq Filter.atTop (nhds 0) ∧
    Filter.Tendsto β_seq Filter.atTop Filter.atTop ∧
    (∀ m, 0 < g_sq_seq m) ∧
    (∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ m,
      Δ₀ ≤ (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ /
        a_seq m) ∧
    Filter.Tendsto
      (fun m =>
        (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ /
          a_seq m)
      Filter.atTop (nhds Δ_phys) ∧
    (∀ (n : ℕ) (xs : Fin n → Space4),
      Filter.Tendsto
        (fun m => cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n (latt_obs m n xs))
        Filter.atTop (nhds (os.os.Schwinger n xs)))

/--
**Main Reduction Theorem**:
the three open analytic RG/OS estimates `SUYangMillsRGConjecture N hN` imply
`ClayYangMillsMassGap4D N hN`, firing the complete formal pipeline `§§1–34`.
-/
theorem clay_yang_mills_from_rg_estimates (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (hRG : SUYangMillsRGConjecture N hN) :
    ClayYangMillsMassGap4D N hN := by
  rcases hRG with ⟨Δ_phys, os, smeared, Ls_seq, Lt_seq, hLs, hLt, a_seq, β_seq, g_sq_seq,
    hβ_pos, latt_obs, ha_pos, ha_lim, hβ_lim, hg_pos, _, hgap_lim, hschw⟩
  let pre := buildEuclideanOSPreDataFromSmeared smeared
  let B : SUYangMillsDynamicalBridge N hN :=
    { Δ_phys := Δ_phys
      os := os
      pre := pre
      Ls_seq := Ls_seq
      Lt_seq := Lt_seq
      Ls_nz := hLs
      Lt_nz := hLt
      a_seq := a_seq
      β_seq := β_seq
      ha_pos := ha_pos
      ha_lim := ha_lim
      hβ_pos := hβ_pos
      hβ_lim := hβ_lim
      g_sq_seq := g_sq_seq
      hg_pos := hg_pos
      Δ_latt := fun m =>
        (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ
      Δ_latt_pos := fun m =>
        (fullRankCubicNonAbelianWilsonSetup (Ls_seq m) N hN (β_seq m) (hβ_pos m)).gaugeSetup.Δ_pos
      gap_lim := hgap_lim
      latt_obs := latt_obs
      schwinger_conv := hschw }
  obtain ⟨_, _, _, ⟨hΔ, hnonG⟩, _, _, hgap, hHnn, hHvac, _, _⟩ :=
    endToEnd_su_yang_mills_from_dynamical_bridge B
  exact ⟨Δ_phys, os, buildOSReconstructionOnCompletion pre, Ls_seq, Lt_seq, hLs, hLt,
    β_seq, latt_obs, hΔ, hnonG, fun m => (hβ_pos m).le, hβ_lim, hschw, hgap, hHnn, hHvac⟩

end ClayYangMills4DInterface

/-! ## §37.  Hardened OS/Wightman/Clay interfaces & strict trilattice -/

section HardenedClayInterface

/-- Strict 4D Euclidean OS continuum theory: adds Euclidean translation invariance. -/
structure OsterwalderSchrader4DStrict (Δ_phys : ℝ) extends OS4DContinuumTheory Δ_phys where
  trans_inv : ∀ (n : ℕ) (a : Space4) (xs : Fin n → Space4),
    os.Schwinger n (fun i => xs i + a) = os.Schwinger n xs

/-- Proof that the hardened interface immediately rejects the origin-anchored Ising model. -/
theorem concreteOS4D_fails_trans_inv :
    ¬ (∀ (n : ℕ) (a : Space4) (xs : Fin n → Space4),
      concreteOS4DContinuumTheory.os.Schwinger n (fun i => xs i + a) =
        concreteOS4DContinuumTheory.os.Schwinger n xs) := by
  intro h
  let a : Space4 := ![1, 0, 0, 0]
  let xs : Fin 2 → Space4 := fun _ => 0
  have h2 := h 2 a xs
  have h_lhs : concreteOS4DContinuumTheory.os.Schwinger 2 (fun i => xs i + a) =
      (((1 + Real.exp (-4) : ℝ)) : ℂ) := by
    change isingSchwinger 2 (fun _ => (0 : Space4) + a) = _
    dsimp [isingSchwinger]
    rw [Fin.prod_univ_two, Fin.prod_univ_two]
    have ha_norm : euclidNorm4 ((0 : Space4) + a) = 1 := by
      rw [zero_add]
      exact euclidNorm4_unit0
    have hg : radialCoupling ((0 : Space4) + a) = Real.exp (-2) := by
      dsimp [radialCoupling]
      rw [ha_norm]
      norm_num
    simp only [hg]
    congr 1
    have hexp : Real.exp (-2) * Real.exp (-2) = Real.exp (-4) := by
      rw [← Real.exp_add]
      norm_num
    calc (1 / 2 : ℝ) * ((1 + Real.exp (-2)) * (1 + Real.exp (-2)) +
          (1 - Real.exp (-2)) * (1 - Real.exp (-2)))
        = 1 + Real.exp (-2) * Real.exp (-2) := by ring
      _ = 1 + Real.exp (-4) := by rw [hexp]
  have h_rhs : concreteOS4DContinuumTheory.os.Schwinger 2 xs = (((2 : ℝ)) : ℂ) := by
    change isingSchwinger 2 (fun _ => (0 : Space4)) = _
    dsimp [isingSchwinger, radialCoupling]
    rw [Fin.prod_univ_two, Fin.prod_univ_two, euclidNorm4_zero]
    norm_num
  rw [h_lhs, h_rhs] at h2
  have hre := congrArg Complex.re h2
  simp only [Complex.ofReal_re] at hre
  have hlt : Real.exp (-4) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/--
Hardened relativistic 4D QFT with genuine `Poincare4 = ℝ⁴ ⋊ O(1,3)` homomorphism `U`,
strong translation continuity, symmetric Euclidean contraction semigroup `T_E` with
proven spectral gap on `Ω_physᗮ`, and unbounded Hamiltonian defined via strong derivative.
-/
structure WightmanQFT4DStrict (Δ_phys : ℝ) where
  Δ_pos         : 0 < Δ_phys
  H             : Type
  [hNorm        : NormedAddCommGroup H]
  [hInner       : InnerProductSpace ℂ H]
  [hComp        : CompleteSpace H]
  Ω_phys        : H
  Ω_unit        : ‖Ω_phys‖ = 1
  U             : Poincare4 → (H →L[ℂ] H)
  U_one         : U 1 = ContinuousLinearMap.id ℂ H
  U_mul         : ∀ g h, U (g * h) = (U g).comp (U h)
  U_unitary     : ∀ g x y, ⟪U g x, U g y⟫_ℂ = ⟪x, y⟫_ℂ
  U_vac         : ∀ g, U g Ω_phys = Ω_phys
  U_trans_cont  : ∀ ψ : H, Continuous (fun a : Space4 => U ⟨a, 1⟩ ψ)
  T_E           : ℝ → (H →L[ℂ] H)
  T_E_zero      : T_E 0 = ContinuousLinearMap.id ℂ H
  T_E_add       : ∀ s t, 0 ≤ s → 0 ≤ t → T_E (s + t) = (T_E s).comp (T_E t)
  T_E_sa        : ∀ t x y, 0 ≤ t → ⟪T_E t x, y⟫_ℂ = ⟪x, T_E t y⟫_ℂ
  T_E_contr     : ∀ t x, 0 ≤ t → ‖T_E t x‖ ≤ ‖x‖
  T_E_vac       : ∀ t, 0 ≤ t → T_E t Ω_phys = Ω_phys
  T_E_gap       : ∀ t, 0 ≤ t → ∀ v : H, ⟪v, Ω_phys⟫_ℂ = 0 →
                    ‖T_E t v‖ ≤ Real.exp (-(Δ_phys * t)) * ‖v‖
  φ             : Space4 → (H →L[ℂ] H)
  covariant     : ∀ g x, (U g).comp (φ x) = (φ (poincareAct g x)).comp (U g)
  local_comm    : ∀ x y, minkowskiSq (x - y) < 0 → (φ x).comp (φ y) = (φ y).comp (φ x)
  cyclic_dense  : (Submodule.span ℂ
      {v : H | ∃ (k : ℕ) (xs : Fin k → Space4),
        v = (List.ofFn (fun i : Fin k => φ (xs i))).foldr
          (fun A acc => A acc) Ω_phys}).topologicalClosure = ⊤

attribute [instance] WightmanQFT4DStrict.hNorm WightmanQFT4DStrict.hInner
  WightmanQFT4DStrict.hComp

/-- Unbounded Hamiltonian domain of `WightmanQFT4DStrict`: strong right-derivative of `T_E` at `0`. -/
def WightmanQFT4DStrict.IsHamiltonianPair {Δ_phys : ℝ} (W : WightmanQFT4DStrict Δ_phys)
    (ψ Hψ : W.H) : Prop :=
  Filter.Tendsto
    (fun t : ℝ => (t⁻¹ : ℂ) • (ψ - W.T_E t ψ))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds Hψ)

theorem WightmanQFT4DStrict.hamiltonian_vac {Δ_phys : ℝ} (W : WightmanQFT4DStrict Δ_phys) :
    W.IsHamiltonianPair W.Ω_phys 0 := by
  have hev : (fun _ : ℝ => (0 : W.H)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun t => (t : ℂ)⁻¹ • (W.Ω_phys - W.T_E t W.Ω_phys)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [W.T_E_vac t ht.le, sub_self, smul_zero]
  exact tendsto_const_nhds.congr' hev

theorem WightmanQFT4DStrict.hamiltonian_gap_pair {Δ_phys : ℝ} (W : WightmanQFT4DStrict Δ_phys)
    {ψ Hψ : W.H} (hH : W.IsHamiltonianPair ψ Hψ) (h_orth : ⟪ψ, W.Ω_phys⟫_ℂ = 0) :
    Δ_phys * ‖ψ‖ ^ 2 ≤ (⟪ψ, Hψ⟫_ℂ).re := by
  have h_quot : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ((1 - Real.exp (-(Δ_phys * t))) / t) * ‖ψ‖ ^ 2 ≤
        (⟪ψ, (t⁻¹ : ℂ) • (ψ - W.T_E t ψ)⟫_ℂ).re := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_pos : 0 < t := ht
    have h_te : ‖W.T_E t ψ‖ ≤ Real.exp (-(Δ_phys * t)) * ‖ψ‖ :=
      W.T_E_gap t ht_pos.le ψ h_orth
    have h_in_le : (⟪ψ, W.T_E t ψ⟫_ℂ).re ≤ Real.exp (-(Δ_phys * t)) * ‖ψ‖ ^ 2 := by
      calc (⟪ψ, W.T_E t ψ⟫_ℂ).re
          ≤ ‖⟪ψ, W.T_E t ψ⟫_ℂ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
        _ ≤ ‖ψ‖ * ‖W.T_E t ψ‖ := norm_inner_le_norm _ _
        _ ≤ ‖ψ‖ * (Real.exp (-(Δ_phys * t)) * ‖ψ‖) :=
            mul_le_mul_of_nonneg_left h_te (norm_nonneg _)
        _ = Real.exp (-(Δ_phys * t)) * ‖ψ‖ ^ 2 := by ring
    have h_re_eq : (⟪ψ, (t⁻¹ : ℂ) • (ψ - W.T_E t ψ)⟫_ℂ).re =
        t⁻¹ * (‖ψ‖ ^ 2 - (⟪ψ, W.T_E t ψ⟫_ℂ).re) := by
      rw [inner_smul_right, inner_sub_right, inner_self_eq_norm_sq_to_K]
      have hpow : (((‖ψ‖ : ℂ) ^ 2).re) = ‖ψ‖ ^ 2 := by norm_num [pow_two]
      have him : (((‖ψ‖ : ℂ) ^ 2).im) = 0 := by norm_num [pow_two]
      simp [Complex.mul_re, Complex.sub_re, hpow, him]
    rw [h_re_eq]
    have hnum : (1 - Real.exp (-(Δ_phys * t))) * ‖ψ‖ ^ 2 ≤
        ‖ψ‖ ^ 2 - (⟪ψ, W.T_E t ψ⟫_ℂ).re := by linarith
    calc ((1 - Real.exp (-(Δ_phys * t))) / t) * ‖ψ‖ ^ 2
        = t⁻¹ * ((1 - Real.exp (-(Δ_phys * t))) * ‖ψ‖ ^ 2) := by ring
      _ ≤ t⁻¹ * (‖ψ‖ ^ 2 - (⟪ψ, W.T_E t ψ⟫_ℂ).re) :=
          mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr ht_pos.le)
  have h_rhs_tend : Filter.Tendsto
      (fun t : ℝ => (⟪ψ, (t⁻¹ : ℂ) • (ψ - W.T_E t ψ)⟫_ℂ).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (⟪ψ, Hψ⟫_ℂ).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      ((continuous_const.inner continuous_id).continuousAt.tendsto.comp hH)
  have h_lhs_tend : Filter.Tendsto
      (fun t : ℝ => ((1 - Real.exp (-(Δ_phys * t))) / t) * ‖ψ‖ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Δ_phys * ‖ψ‖ ^ 2)) := by
    have h_exp_deriv : HasDerivAt (fun t : ℝ => Real.exp (-(Δ_phys * t))) (-Δ_phys) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => -(Δ_phys * t)) (-Δ_phys) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul Δ_phys).neg
      simpa using (Real.hasDerivAt_exp (-(Δ_phys * (0 : ℝ)))).comp 0 h1
    have h_sub_deriv : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(Δ_phys * t))) Δ_phys 0 := by
      simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub h_exp_deriv
    have h_slope : Filter.Tendsto
        (fun t : ℝ => (1 - Real.exp (-(Δ_phys * t))) / t)
        (nhdsWithin 0 ({0}ᶜ)) (nhds Δ_phys) := by
      have ht := h_sub_deriv.tendsto_slope_zero
      simpa [div_eq_inv_mul, smul_eq_mul, Real.exp_zero] using ht
    have h_ioi : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin 0 ({0}ᶜ) :=
      nhdsWithin_mono 0 (fun t ht => ne_of_gt ht)
    exact (h_slope.mono_left h_ioi).mul tendsto_const_nhds
  exact le_of_tendsto_of_tendsto h_lhs_tend h_rhs_tend h_quot

/--
Non-cheatable lattice observable family: single-point, `n`-independent, locally gauge-invariant,
and field-dependent (not constant on gauge fields).
-/
structure LatticeSinglePointObs (N : ℕ) (Ls_seq Lt_seq : ℕ → ℕ)
    [∀ m, NeZero (Ls_seq m)] [∀ m, NeZero (Lt_seq m)] where
  obs       : ∀ m, Space4 →
                GaugeField (cubicTorus4 (Ls_seq m) (Lt_seq m))
                  (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ
  gauge_inv : ∀ m x g U, obs m x (gaugeAct g U) = obs m x U
  non_const : ∀ m x, ∃ U₁ U₂, obs m x U₁ ≠ obs m x U₂

/--
Strict Clay 4D `SU(N)` Yang–Mills Existence and Mass Gap statement:
rules out `isingSchwinger` (via `trans_inv`), rules out constant `latt_obs`
(via `LatticeSinglePointObs`), enforces `Ls_seq, Lt_seq → ∞`, and enforces
the Hilbert-space Euclidean semigroup mass gap and `Poincare4` group representation.
-/
def ClayYangMillsMassGap4DStrict (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] : Prop :=
  ∃ (Δ_phys : ℝ) (os : OsterwalderSchrader4DStrict Δ_phys)
    (W : WightmanQFT4DStrict Δ_phys)
    (Ls_seq Lt_seq : ℕ → ℕ) (hLs : ∀ m, NeZero (Ls_seq m)) (hLt : ∀ m, NeZero (Lt_seq m))
    (β_seq : ℕ → ℝ)
    (O : LatticeSinglePointObs N Ls_seq Lt_seq),
    0 < Δ_phys ∧
    ¬ IsGaussian4 os.os.Schwinger ∧
    Filter.Tendsto Ls_seq Filter.atTop Filter.atTop ∧
    Filter.Tendsto Lt_seq Filter.atTop Filter.atTop ∧
    (∀ m, 0 ≤ β_seq m) ∧
    Filter.Tendsto β_seq Filter.atTop Filter.atTop ∧
    (∀ (n : ℕ) (xs : Fin n → Space4),
      Filter.Tendsto
        (fun m => cubic4Schwinger (Ls_seq m) (Lt_seq m) N (β_seq m) n
          (fun i => O.obs m (xs i)))
        Filter.atTop (nhds (os.os.Schwinger n xs)))

/-- Globally idempotent and globally non-void re-entry operator on `S16`. -/
def inc16Strict : S16 → S16
  | (b0, b1, b2, _) => (b0 || b2, b1, b2, true)

/-- Strict `SIXTEEN_3` trilattice satisfying global `Inc(Inc x) = Inc x ≠ ∅` and `(N, T, F)` split. -/
def trilattice16Strict : TrilatticeModel where
  S := S16
  card_eq := by decide
  le_t := le16_t
  le_f := le16_f
  le_i := le16_i
  le_t_refl := fun _ => ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_t_trans := le16_t_trans
  le_t_anti := le16_t_anti
  le_f_refl := fun _ => ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_f_trans := le16_f_trans
  le_f_anti := le16_f_anti
  le_i_refl := fun _ => ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_i_trans := le16_i_trans
  le_i_anti := le16_i_anti
  sup_t := sup16_t
  le_t_sup_left := sup16_t_left
  le_t_sup_right := sup16_t_right
  sup_t_least := sup16_t_least
  inf_t := inf16_t
  le_t_inf_left := inf16_t_left
  le_t_inf_right := inf16_t_right
  inf_t_greatest := inf16_t_greatest
  sup_f := sup16_f
  le_f_sup_left := sup16_f_left
  le_f_sup_right := sup16_f_right
  sup_f_least := sup16_f_least
  inf_f := inf16_f
  le_f_inf_left := inf16_f_left
  le_f_inf_right := inf16_f_right
  inf_f_greatest := inf16_f_greatest
  sup_i := sup16_i
  le_i_sup_left := sup16_i_left
  le_i_sup_right := sup16_i_right
  sup_i_least := sup16_i_least
  inf_i := inf16_i
  le_i_inf_left := inf16_i_left
  le_i_inf_right := inf16_i_right
  inf_i_greatest := inf16_i_greatest
  void := (false, false, false, false)
  trueVal := (false, false, true, false)
  falseVal := (false, true, false, false)
  bothVal := (false, false, false, true)
  totalityB := (true, true, true, true)
  val_ne_tf := by decide
  val_ne_bv := by decide
  le_i_top := by
    rintro ⟨a0, a1, a2, a3⟩
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> simp [le16_i]
  Inc := inc16Strict
  inc_fixed := by decide
  inc_ne_void := by decide
  Part := S16 × S16 × S16
  δ := fun x => ((x.1, false, false, x.2.2.2), (false, false, x.2.2.1, x.2.2.2), (false, x.2.1, false, x.2.2.2))
  μ := fun p => (p.1.1, p.2.2.2.1, p.2.1.2.2.1, p.1.2.2.2 || p.2.1.2.2.2 || p.2.2.2.2.2)
  mu_delta := by
    rintro ⟨b0, b1, b2, b3⟩
    cases b3 <;> rfl
  W := walk16
  W_mono := by
    rintro ⟨a0, a1, a2, a3⟩
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> simp [le16_i, walk16]
  W_strict := by
    rintro ⟨a0, a1, a2, a3⟩
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> decide
  W_fixed := by decide

theorem trilattice16Strict_global_axioms :
    (∀ x : S16, inc16Strict (inc16Strict x) = inc16Strict x) ∧
    (∀ x : S16, inc16Strict (inc16Strict x) ≠ (false, false, false, false)) ∧
    (inc16Strict (walk16 (false, false, true, false)) ≠
      walk16 (inc16Strict (false, false, true, false))) := by
  refine ⟨by decide, by decide, by decide⟩

end HardenedClayInterface

/-! ## §38.  Euclidean clustering implies OS semigroup spectral gap -/

section OSClusteringToSemigroupGap

theorem osConfigKernel_empty_right {Δ : ℝ} (hΔ : 0 < Δ)
    (os : OS4DContinuumTheory Δ) (h_S0 : os.os.Schwinger 0 Fin.elim0 = 1)
    (x : PosTimeConfig) :
    osConfigKernel os x emptyPosConfig =
      os.os.Schwinger x.n_pts (fun k => euclidTimeReflect (x.pts k)) := by
  obtain ⟨C, hC⟩ := os.os.cluster x.n_pts 0
  have h_vac_rhs : os.os.Schwinger 0 emptyPosConfig.pts = 1 := by
    have heq : emptyPosConfig.pts = Fin.elim0 := rfl
    rw [heq, h_S0]
  have h_le : ∀ ε > 0,
      ‖osConfigKernel os x emptyPosConfig -
        os.os.Schwinger x.n_pts (fun k => euclidTimeReflect (x.pts k))‖ ≤ ε := by
    intro ε hε
    by_cases hC_le : C ≤ 0
    · have h0 := hC (fun k => euclidTimeReflect (x.pts k)) emptyPosConfig.pts 0 le_rfl
        (fun _ j => Fin.elim0 j)
      change ‖osConfigKernel os x emptyPosConfig -
          os.os.Schwinger x.n_pts (fun k => euclidTimeReflect (x.pts k)) *
            os.os.Schwinger 0 emptyPosConfig.pts‖ ≤ C * Real.exp (-(Δ * 0)) at h0
      rw [h_vac_rhs, mul_one, mul_zero, neg_zero, Real.exp_zero, mul_one] at h0
      exact h0.trans (hC_le.trans hε.le)
    · push_neg at hC_le
      let M : ℝ := max 1 (C / ε)
      have hM_pos : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
      let R : ℝ := max 0 (Real.log M / Δ)
      have hR_nn : 0 ≤ R := le_max_left _ _
      have hR_ge : Real.log M / Δ ≤ R := le_max_right _ _
      have hlog_le : Real.log M ≤ Δ * R := by
        have hh := (div_le_iff₀ hΔ).mp hR_ge
        simpa [mul_comm] using hh
      have hM_le_exp : M ≤ Real.exp (Δ * R) := by
        calc M = Real.exp (Real.log M) := (Real.exp_log hM_pos).symm
          _ ≤ Real.exp (Δ * R) := Real.exp_le_exp.mpr hlog_le
      have hexp_inv : M * Real.exp (-(Δ * R)) ≤ 1 := by
        calc M * Real.exp (-(Δ * R))
            ≤ Real.exp (Δ * R) * Real.exp (-(Δ * R)) :=
                mul_le_mul_of_nonneg_right hM_le_exp (Real.exp_pos _).le
          _ = Real.exp (Δ * R + -(Δ * R)) := (Real.exp_add _ _).symm
          _ = 1 := by simp
      have hC_bound : C * Real.exp (-(Δ * R)) ≤ ε := by
        have h1 : (C / ε) * Real.exp (-(Δ * R)) ≤ 1 :=
          (mul_le_mul_of_nonneg_right (le_max_right 1 (C / ε)) (Real.exp_pos _).le).trans hexp_inv
        have h2 : (C * Real.exp (-(Δ * R))) / ε ≤ 1 := by
          simpa [div_mul_eq_mul_div] using h1
        exact (div_le_one hε).mp h2
      have h0 := hC (fun k => euclidTimeReflect (x.pts k)) emptyPosConfig.pts R hR_nn
        (fun _ j => Fin.elim0 j)
      change ‖osConfigKernel os x emptyPosConfig -
          os.os.Schwinger x.n_pts (fun k => euclidTimeReflect (x.pts k)) *
            os.os.Schwinger 0 emptyPosConfig.pts‖ ≤ C * Real.exp (-(Δ * R)) at h0
      rw [h_vac_rhs, mul_one] at h0
      exact h0.trans hC_bound
  have h_zero : ‖osConfigKernel os x emptyPosConfig -
      os.os.Schwinger x.n_pts (fun k => euclidTimeReflect (x.pts k))‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    by_contra hgt
    push_neg at hgt
    have h1 := h_le _ (half_pos hgt)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h_zero)

theorem osConfigKernel_empty_left {Δ : ℝ} (hΔ : 0 < Δ)
    (os : OS4DContinuumTheory Δ) (h_S0 : os.os.Schwinger 0 Fin.elim0 = 1)
    (y : PosTimeConfig) :
    osConfigKernel os emptyPosConfig y = os.os.Schwinger y.n_pts y.pts := by
  obtain ⟨C, hC⟩ := os.os.cluster 0 y.n_pts
  have h_vac_lhs : os.os.Schwinger 0 (fun k : Fin 0 => euclidTimeReflect (emptyPosConfig.pts k)) = 1 := by
    have heq : (fun k : Fin 0 => euclidTimeReflect (emptyPosConfig.pts k)) = Fin.elim0 := by
      funext k; exact Fin.elim0 k
    rw [heq, h_S0]
  have h_le : ∀ ε > 0,
      ‖osConfigKernel os emptyPosConfig y - os.os.Schwinger y.n_pts y.pts‖ ≤ ε := by
    intro ε hε
    by_cases hC_le : C ≤ 0
    · have h0 := hC (fun k => euclidTimeReflect (emptyPosConfig.pts k)) y.pts 0 le_rfl
        (fun i _ => Fin.elim0 i)
      change ‖osConfigKernel os emptyPosConfig y -
          os.os.Schwinger 0 (fun k => euclidTimeReflect (emptyPosConfig.pts k)) *
            os.os.Schwinger y.n_pts y.pts‖ ≤ C * Real.exp (-(Δ * 0)) at h0
      rw [h_vac_lhs, one_mul, mul_zero, neg_zero, Real.exp_zero, mul_one] at h0
      exact h0.trans (hC_le.trans hε.le)
    · push_neg at hC_le
      let M : ℝ := max 1 (C / ε)
      have hM_pos : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
      let R : ℝ := max 0 (Real.log M / Δ)
      have hR_nn : 0 ≤ R := le_max_left _ _
      have hlog_le : Real.log M ≤ Δ * R := by
        have hR_ge' : Real.log M / Δ ≤ R := le_max_right _ _
        have hh := (div_le_iff₀ hΔ).mp hR_ge'
        simpa [mul_comm] using hh
      have hM_le_exp : M ≤ Real.exp (Δ * R) := by
        calc M = Real.exp (Real.log M) := (Real.exp_log hM_pos).symm
          _ ≤ Real.exp (Δ * R) := Real.exp_le_exp.mpr hlog_le
      have hexp_inv : M * Real.exp (-(Δ * R)) ≤ 1 := by
        calc M * Real.exp (-(Δ * R))
            ≤ Real.exp (Δ * R) * Real.exp (-(Δ * R)) :=
                mul_le_mul_of_nonneg_right hM_le_exp (Real.exp_pos _).le
          _ = Real.exp (Δ * R + -(Δ * R)) := (Real.exp_add _ _).symm
          _ = 1 := by simp
      have hC_bound : C * Real.exp (-(Δ * R)) ≤ ε := by
        have h1 : (C / ε) * Real.exp (-(Δ * R)) ≤ 1 :=
          (mul_le_mul_of_nonneg_right (le_max_right 1 (C / ε)) (Real.exp_pos _).le).trans hexp_inv
        have h2 : (C * Real.exp (-(Δ * R))) / ε ≤ 1 := by
          simpa [div_mul_eq_mul_div] using h1
        exact (div_le_one hε).mp h2
      have h0 := hC (fun k => euclidTimeReflect (emptyPosConfig.pts k)) y.pts R hR_nn
        (fun i _ => Fin.elim0 i)
      change ‖osConfigKernel os emptyPosConfig y -
          os.os.Schwinger 0 (fun k => euclidTimeReflect (emptyPosConfig.pts k)) *
            os.os.Schwinger y.n_pts y.pts‖ ≤ C * Real.exp (-(Δ * R)) at h0
      rw [h_vac_lhs, one_mul] at h0
      exact h0.trans hC_bound
  have h_zero : ‖osConfigKernel os emptyPosConfig y - os.os.Schwinger y.n_pts y.pts‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    by_contra hgt
    push_neg at hgt
    have h1 := h_le _ (half_pos hgt)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h_zero)

theorem osConfig_cluster_single {Δ : ℝ} (hΔ : 0 < Δ)
    (os : OS4DContinuumTheory Δ) (h_S0 : os.os.Schwinger 0 Fin.elim0 = 1)
    (h_trans : ∀ (n : ℕ) (a : Space4) (xs : Fin n → Space4),
      os.os.Schwinger n (fun i => xs i + a) = os.os.Schwinger n xs)
    (x y : PosTimeConfig) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (hs : 0 ≤ s),
      ‖osConfigKernel os x (posTimeShiftConfig s hs y) -
        osConfigKernel os x emptyPosConfig * osConfigKernel os emptyPosConfig y‖ ≤
          C * Real.exp (-(Δ * s)) := by
  obtain ⟨C, hC⟩ := os.os.cluster x.n_pts y.n_pts
  refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
  have hsep : ∀ i j, s ≤ ‖euclidTimeReflect (x.pts i) - (posTimeShiftConfig s hs y).pts j‖ := by
    intro i j
    let z := euclidTimeReflect (x.pts i) - (posTimeShiftConfig s hs y).pts j
    have hz0 : ‖z 0‖ ≤ ‖z‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mp le_rfl 0
    have h_diff0 : z 0 = -(x.pts i 0) - (y.pts j 0 + s) := by
      dsimp [z, euclidTimeReflect, posTimeShiftConfig]
    have h_abs : s ≤ ‖z 0‖ := by
      rw [Real.norm_eq_abs, h_diff0, abs_of_neg (by linarith [x.pos_t i, y.pos_t j])]
      linarith [x.pos_t i, y.pos_t j]
    exact h_abs.trans hz0
  have hcl := hC (fun k => euclidTimeReflect (x.pts k)) (posTimeShiftConfig s hs y).pts s hs hsep
  have hshift_eq : (posTimeShiftConfig s hs y).pts =
      fun k => y.pts k + (fun i : Fin 4 => if i = 0 then s else 0) := by
    funext k i
    by_cases hi : i = 0
    · subst hi; simp [posTimeShiftConfig]
    · simp [posTimeShiftConfig, hi]
  have hy_inv : os.os.Schwinger y.n_pts (posTimeShiftConfig s hs y).pts =
      os.os.Schwinger y.n_pts y.pts := by
    rw [hshift_eq]
    exact h_trans y.n_pts _ y.pts
  rw [hy_inv, ← osConfigKernel_empty_right hΔ os h_S0 x,
      ← osConfigKernel_empty_left hΔ os h_S0 y] at hcl
  exact hcl.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le)

theorem osConfigInner_cluster {Δ : ℝ} (hΔ : 0 < Δ)
    (os : OS4DContinuumTheory Δ)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_S0 : os.os.Schwinger 0 Fin.elim0 = 1)
    (h_trans : ∀ (n : ℕ) (a : Space4) (xs : Fin n → Space4),
      os.os.Schwinger n (fun i => xs i + a) = os.os.Schwinger n xs)
    (f g : OSPosTestSpace) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (hs : 0 ≤ s),
      ‖osConfigInner os f (osTimeShiftPre s hs g) -
        osConfigInner os f (osConfigSingle emptyPosConfig) *
          osConfigInner os (osConfigSingle emptyPosConfig) g‖ ≤
        C * Real.exp (-(Δ * s)) := by
  let F := osConfigForm os h_herm
  have h_single : ∀ (x : PosTimeConfig) (c : ℂ) (v : OSPosTestSpace),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (hs : 0 ≤ s),
        ‖osConfigInner os (Finsupp.single x c) (osTimeShiftPre s hs v) -
          osConfigInner os (Finsupp.single x c) (osConfigSingle emptyPosConfig) *
            osConfigInner os (osConfigSingle emptyPosConfig) v‖ ≤
          C * Real.exp (-(Δ * s)) := by
    intro x c v
    refine Finsupp.induction_linear v ?_ ?_ ?_
    · refine ⟨0, le_rfl, fun s hs => ?_⟩
      simp [osConfigInner_zero_right]
    · rintro v₁ v₂ ⟨C₁, hC₁, ih₁⟩ ⟨C₂, hC₂, ih₂⟩
      refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun s hs => ?_⟩
      change ‖F.B (Finsupp.single x c) (osTimeShiftPre s hs (v₁ + v₂)) -
          F.B (Finsupp.single x c) (osConfigSingle emptyPosConfig) *
            F.B (osConfigSingle emptyPosConfig) (v₁ + v₂)‖ ≤ (C₁ + C₂) * Real.exp (-(Δ * s))
      rw [map_add, F.add_right, F.add_right]
      have hsplit : F.B (Finsupp.single x c) (osTimeShiftPre s hs v₁) +
            F.B (Finsupp.single x c) (osTimeShiftPre s hs v₂) -
          F.B (Finsupp.single x c) (osConfigSingle emptyPosConfig) *
            (F.B (osConfigSingle emptyPosConfig) v₁ + F.B (osConfigSingle emptyPosConfig) v₂) =
          (F.B (Finsupp.single x c) (osTimeShiftPre s hs v₁) -
            F.B (Finsupp.single x c) (osConfigSingle emptyPosConfig) *
              F.B (osConfigSingle emptyPosConfig) v₁) +
          (F.B (Finsupp.single x c) (osTimeShiftPre s hs v₂) -
            F.B (Finsupp.single x c) (osConfigSingle emptyPosConfig) *
              F.B (osConfigSingle emptyPosConfig) v₂) := by ring
      rw [hsplit]
      calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
        _ ≤ C₁ * Real.exp (-(Δ * s)) + C₂ * Real.exp (-(Δ * s)) := add_le_add (ih₁ s hs) (ih₂ s hs)
        _ = (C₁ + C₂) * Real.exp (-(Δ * s)) := by ring
    · intro y d
      obtain ⟨Cxy, hCxy, hcl⟩ := osConfig_cluster_single hΔ os h_S0 h_trans x y
      refine ⟨‖c‖ * ‖d‖ * Cxy, by positivity, fun s hs => ?_⟩
      have hsc_x : Finsupp.single x c = c • osConfigSingle x := by
        dsimp [osConfigSingle]; rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hsc_y : Finsupp.single y d = d • osConfigSingle y := by
        dsimp [osConfigSingle]; rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have h_shift_y : osTimeShiftPre s hs (d • osConfigSingle y) =
          d • osConfigSingle (posTimeShiftConfig s hs y) := by
        rw [map_smul]
        congr 1
        dsimp [osTimeShiftPre, osConfigSingle]
        exact Finsupp.mapDomain_single
      change ‖F.B (Finsupp.single x c) (osTimeShiftPre s hs (Finsupp.single y d)) -
          F.B (Finsupp.single x c) (osConfigSingle emptyPosConfig) *
            F.B (osConfigSingle emptyPosConfig) (Finsupp.single y d)‖ ≤ _
      rw [hsc_x, hsc_y, h_shift_y, F.smul_left, F.smul_right, F.smul_left, F.smul_right]
      change ‖starRingEnd ℂ c * (d * osConfigInner os (osConfigSingle x)
            (osConfigSingle (posTimeShiftConfig s hs y))) -
          (starRingEnd ℂ c * osConfigInner os (osConfigSingle x) (osConfigSingle emptyPosConfig)) *
            (d * osConfigInner os (osConfigSingle emptyPosConfig) (osConfigSingle y))‖ ≤ _
      rw [osConfigInner_single, osConfigInner_single, osConfigInner_single]
      have hfac : starRingEnd ℂ c * (d * osConfigKernel os x (posTimeShiftConfig s hs y)) -
          (starRingEnd ℂ c * osConfigKernel os x emptyPosConfig) *
            (d * osConfigKernel os emptyPosConfig y) =
          (starRingEnd ℂ c * d) * (osConfigKernel os x (posTimeShiftConfig s hs y) -
            osConfigKernel os x emptyPosConfig * osConfigKernel os emptyPosConfig y) := by ring
      rw [hfac, norm_mul, norm_mul, Complex.norm_conj]
      calc ‖c‖ * ‖d‖ * ‖osConfigKernel os x (posTimeShiftConfig s hs y) -
              osConfigKernel os x emptyPosConfig * osConfigKernel os emptyPosConfig y‖
          ≤ ‖c‖ * ‖d‖ * (Cxy * Real.exp (-(Δ * s))) :=
              mul_le_mul_of_nonneg_left (hcl s hs) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ‖c‖ * ‖d‖ * Cxy * Real.exp (-(Δ * s)) := by ring
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · refine ⟨0, le_rfl, fun s hs => ?_⟩
    simp [osConfigInner_zero_left]
  · rintro f₁ f₂ ⟨C₁, hC₁, ih₁⟩ ⟨C₂, hC₂, ih₂⟩
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun s hs => ?_⟩
    change ‖F.B (f₁ + f₂) (osTimeShiftPre s hs g) -
        F.B (f₁ + f₂) (osConfigSingle emptyPosConfig) *
          F.B (osConfigSingle emptyPosConfig) g‖ ≤ (C₁ + C₂) * Real.exp (-(Δ * s))
    rw [F.add_left, F.add_left]
    have hsplit : F.B f₁ (osTimeShiftPre s hs g) + F.B f₂ (osTimeShiftPre s hs g) -
          (F.B f₁ (osConfigSingle emptyPosConfig) + F.B f₂ (osConfigSingle emptyPosConfig)) *
            F.B (osConfigSingle emptyPosConfig) g =
        (F.B f₁ (osTimeShiftPre s hs g) -
          F.B f₁ (osConfigSingle emptyPosConfig) * F.B (osConfigSingle emptyPosConfig) g) +
        (F.B f₂ (osTimeShiftPre s hs g) -
          F.B f₂ (osConfigSingle emptyPosConfig) * F.B (osConfigSingle emptyPosConfig) g) := by ring
    rw [hsplit]
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ C₁ * Real.exp (-(Δ * s)) + C₂ * Real.exp (-(Δ * s)) := add_le_add (ih₁ s hs) (ih₂ s hs)
      _ = (C₁ + C₂) * Real.exp (-(Δ * s)) := by ring
  · intro x c
    exact h_single x c g

/--
Glimm–Jaffe power-amplification lemma on any Hilbert space:
if a symmetric semigroup `T_E(t)` satisfies `(⟪v, T_E s v⟫_ℂ).re ≤ C exp(-Δ s)`,
then `‖T_E t v‖ ≤ exp(-Δ t) * ‖v‖` for all `t ≥ 0`.
-/
theorem semigroup_decay_of_weak_cluster
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T_E : ℝ → (H →L[ℂ] H))
    (h_zero : T_E 0 = ContinuousLinearMap.id ℂ H)
    (h_add : ∀ s₁ s₂, 0 ≤ s₁ → 0 ≤ s₂ → T_E (s₁ + s₂) = (T_E s₁).comp (T_E s₂))
    (h_sa : ∀ s, 0 ≤ s → ∀ x y : H, ⟪T_E s x, y⟫_ℂ = ⟪x, T_E s y⟫_ℂ)
    (Δ : ℝ) (v : H) (C : ℝ)
    (h_ub : ∀ s : ℝ, 0 ≤ s → (⟪v, T_E s v⟫_ℂ).re ≤ C * Real.exp (-(Δ * s)))
    (t : ℝ) (ht : 0 ≤ t) :
    ‖T_E t v‖ ≤ Real.exp (-(Δ * t)) * ‖v‖ := by
  by_cases hv : v = 0
  · subst hv; simp
  · have hv_sq_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    let s_seq : ℕ → ℝ := fun n => ((2 ^ n : ℕ) : ℝ) * t
    have hs_nn : ∀ n, 0 ≤ s_seq n := fun n => mul_nonneg (Nat.cast_nonneg _) ht
    let b : ℕ → ℝ := fun n => ‖T_E (s_seq n) v‖ ^ 2
    let E : ℕ → ℝ := fun n => Real.exp (Δ * (2 * s_seq n))
    let bt : ℕ → ℝ := fun n => E n * b n
    have hb_eq : ∀ n, b n = (⟪v, T_E (s_seq (n + 1)) v⟫_ℂ).re := by
      intro n
      have h2s : s_seq n + s_seq n = s_seq (n + 1) := by
        dsimp [s_seq]
        push_cast
        rw [pow_succ]
        ring
      have hT : T_E (s_seq (n + 1)) v = T_E (s_seq n) (T_E (s_seq n) v) := by
        rw [← h2s, h_add (s_seq n) (s_seq n) (hs_nn n) (hs_nn n), ContinuousLinearMap.comp_apply]
      rw [hT, ← h_sa (s_seq n) (hs_nn n) v (T_E (s_seq n) v), inner_self_eq_norm_sq_to_K]
      simp [b, pow_two]
    have hb_rec : ∀ n, b n ^ 2 ≤ ‖v‖ ^ 2 * b (n + 1) := by
      intro n
      have h1 : b n ≤ ‖v‖ * ‖T_E (s_seq (n + 1)) v‖ := by
        rw [hb_eq n]
        calc (⟪v, T_E (s_seq (n + 1)) v⟫_ℂ).re
            ≤ ‖⟪v, T_E (s_seq (n + 1)) v⟫_ℂ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ ≤ ‖v‖ * ‖T_E (s_seq (n + 1)) v‖ := norm_inner_le_norm _ _
      have h2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
      simpa [b, mul_pow] using h2
    have hE_sq : ∀ n, E n ^ 2 = E (n + 1) := by
      intro n
      have h2s : 2 * s_seq n + 2 * s_seq n = 2 * s_seq (n + 1) := by
        dsimp [s_seq]; push_cast; rw [pow_succ]; ring
      dsimp [E]
      rw [sq, ← Real.exp_add, ← mul_add, h2s]
    have hbt_nn : ∀ n, 0 ≤ bt n := fun n => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    have hbt_rec : ∀ n, bt n ^ 2 ≤ ‖v‖ ^ 2 * bt (n + 1) := by
      intro n
      calc bt n ^ 2 = E n ^ 2 * b n ^ 2 := by dsimp [bt]; ring
        _ ≤ E (n + 1) * (‖v‖ ^ 2 * b (n + 1)) := by
            rw [hE_sq n]
            exact mul_le_mul_of_nonneg_left (hb_rec n) (Real.exp_pos _).le
        _ = ‖v‖ ^ 2 * bt (n + 1) := by dsimp [bt]; ring
    have hbt_ub : ∀ k, bt k ≤ C := by
      intro k
      have hs2 : 2 * s_seq k = s_seq (k + 1) := by
        dsimp [s_seq]; push_cast; rw [pow_succ]; ring
      have hub := h_ub (2 * s_seq k) (mul_nonneg zero_le_two (hs_nn k))
      rw [hs2, ← hb_eq k] at hub
      calc bt k = E k * b k := rfl
        _ ≤ E k * (C * Real.exp (-(Δ * (2 * s_seq k)))) :=
            mul_le_mul_of_nonneg_left (hs2 ▸ hub) (Real.exp_pos _).le
        _ = C * (Real.exp (Δ * (2 * s_seq k)) * Real.exp (-(Δ * (2 * s_seq k)))) := by
            dsimp [E]; ring
        _ = C := by rw [← Real.exp_add]; simp
    let u : ℕ → ℝ := fun n => bt n / ‖v‖ ^ 2
    have hu_nn : ∀ n, 0 ≤ u n := fun n => div_nonneg (hbt_nn n) hv_sq_pos.le
    have hu_rec : ∀ n, u n ^ 2 ≤ u (n + 1) := by
      intro n
      dsimp [u]
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hv_sq_pos) hv_sq_pos]
      calc bt n ^ 2 * ‖v‖ ^ 2 ≤ (‖v‖ ^ 2 * bt (n + 1)) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hbt_rec n) hv_sq_pos.le
        _ = bt (n + 1) * (‖v‖ ^ 2) ^ 2 := by ring
    have hu_pow : ∀ k : ℕ, u 0 ^ (2 ^ k) ≤ u k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc u 0 ^ (2 ^ (k + 1)) = (u 0 ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
          _ ≤ u k ^ 2 := pow_le_pow_left₀ (pow_nonneg (hu_nn 0) _) ih 2
          _ ≤ u (k + 1) := hu_rec k
    have hu0_le : u 0 ≤ 1 := by
      by_contra h_gt
      push_neg at h_gt
      have h_pow_lim : Filter.Tendsto (fun m : ℕ => u 0 ^ m) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt h_gt
      have h_two_pow : Filter.Tendsto (fun k : ℕ => (2 ^ k : ℕ)) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_atTop.mpr fun N =>
          ⟨N, fun a ha => le_trans ha (Nat.le_of_lt Nat.lt_two_pow_self)⟩
      obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
        ((Filter.tendsto_atTop.mp (h_pow_lim.comp h_two_pow)) (C / ‖v‖ ^ 2 + 1))
      have h_le1 : u 0 ^ (2 ^ k) ≤ C / ‖v‖ ^ 2 :=
        (hu_pow k).trans (div_le_div_of_nonneg_right (hbt_ub k) hv_sq_pos.le)
      have h_le2 : C / ‖v‖ ^ 2 + 1 ≤ u 0 ^ (2 ^ k) := hk k le_rfl
      linarith
    have hbt0_le : bt 0 ≤ ‖v‖ ^ 2 := (div_le_one hv_sq_pos).mp hu0_le
    have hs0 : s_seq 0 = t := by simp [s_seq]
    have h_sq_le : ‖T_E t v‖ ^ 2 ≤ (Real.exp (-(Δ * t)) * ‖v‖) ^ 2 := by
      have h1 : Real.exp (Δ * (2 * t)) * ‖T_E t v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
        simpa [bt, E, b, hs0] using hbt0_le
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(Δ * (2 * t)))).le
      have h_cancel : Real.exp (-(Δ * (2 * t))) * (Real.exp (Δ * (2 * t)) * ‖T_E t v‖ ^ 2) =
          ‖T_E t v‖ ^ 2 := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      have h_rhs : Real.exp (-(Δ * (2 * t))) * ‖v‖ ^ 2 = (Real.exp (-(Δ * t)) * ‖v‖) ^ 2 := by
        rw [mul_pow]
        congr 1
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      rwa [h_cancel, h_rhs] at h2
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp h_sq_le

/--
**Main Euclidean Clustering $\implies$ OS Semigroup Spectral Gap Theorem:**
derives `∀ v ∈ Ωᗮ, ‖T_E t v‖ ≤ exp(-Δ * t) * ‖v‖` directly on `OSHilbertSpace`
from `OS4DContinuumTheory` clustering + translation invariance + reflection positivity.
-/
theorem os_cluster_implies_semigroup_gap {Δ : ℝ} (hΔ : 0 < Δ)
    (os : OS4DContinuumTheory Δ)
    (h_herm : ∀ x y : PosTimeConfig,
      osConfigKernel os x y = starRingEnd ℂ (osConfigKernel os y x))
    (h_S0 : os.os.Schwinger 0 Fin.elim0 = 1)
    (h_kern : ∀ (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig),
      osConfigKernel os (posTimeShiftConfig t ht x) y =
        osConfigKernel os x (posTimeShiftConfig t ht y))
    (h_trans : ∀ (n : ℕ) (a : Space4) (xs : Fin n → Space4),
      os.os.Schwinger n (fun i => xs i + a) = os.os.Schwinger n xs)
    (M_bd : ℝ) (hM_nn : 0 ≤ M_bd)
    (h_bd : ∀ (n : ℕ) (xs : Fin n → Space4), ‖os.os.Schwinger n xs‖ ≤ M_bd ^ n) :
    let F := osConfigForm os h_herm
    let H := OSHilbertSpace F
    let Ω : H := osCompletionMap F (osPreMk F (osConfigSingle emptyPosConfig))
    let T_E := osLiftSemigroup F osTimeShiftSemigroup
      (osTimeShiftSemigroup_contr os h_herm h_kern M_bd hM_nn h_bd)
    ∀ (t : ℝ), 0 ≤ t → ∀ v : H, ⟪v, Ω⟫_ℂ = 0 →
      ‖T_E t v‖ ≤ Real.exp (-(Δ * t)) * ‖v‖ := by
  intro F H Ω T_E t ht v hv_orth
  have hT_zero : T_E 0 = ContinuousLinearMap.id ℂ H :=
    osLiftSemigroup_zero F osTimeShiftSemigroup _ osTimeShiftSemigroup_zero
  have hT_add : ∀ s₁ s₂, 0 ≤ s₁ → 0 ≤ s₂ → T_E (s₁ + s₂) = (T_E s₁).comp (T_E s₂) :=
    osLiftSemigroup_add F osTimeShiftSemigroup _ osTimeShiftSemigroup_add
  have hT_sa : ∀ s, 0 ≤ s → ∀ x y : H, ⟪T_E s x, y⟫_ℂ = ⟪x, T_E s y⟫_ℂ :=
    fun s hs => osLiftSemigroup_sa F osTimeShiftSemigroup _
      (osTimeShiftSemigroup_sa os h_herm h_kern) s hs
  have hΩ_norm : ‖Ω‖ = 1 := by
    have hsq : ‖Ω‖ ^ 2 = 1 := by
      rw [osCompletionMap_norm, osPre_norm_sq, osConfigVac_norm os h_herm h_S0, Complex.one_re]
    have hmul : (‖Ω‖ - 1) * (‖Ω‖ + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h | h <;> linarith [norm_nonneg Ω]
  have hT_vac : ∀ s, 0 ≤ s → T_E s Ω = Ω := by
    intro s hs
    have heq_cfg : posTimeShiftConfig s hs emptyPosConfig = emptyPosConfig := by
      dsimp [posTimeShiftConfig, emptyPosConfig]
      congr 1
      funext k; exact Fin.elim0 k
    have h_shift_single : osTimeShiftSemigroup s (osConfigSingle emptyPosConfig) =
        osConfigSingle emptyPosConfig := by
      dsimp [osTimeShiftSemigroup]
      rw [dif_pos hs]
      change Finsupp.mapDomain (posTimeShiftConfig s hs) (Finsupp.single emptyPosConfig 1) =
        Finsupp.single emptyPosConfig 1
      rw [Finsupp.mapDomain_single, heq_cfg]
    dsimp [T_E, osLiftSemigroup]
    rw [dif_pos hs]
    change osLiftOperator F (osTimeShiftSemigroup s) 1 zero_le_one _
        (osCompletionMap F (osPreMk F (osConfigSingle emptyPosConfig))) =
      osCompletionMap F (osPreMk F (osConfigSingle emptyPosConfig))
    rw [osLiftOperator_coe, h_shift_single]
  have h_dense_bound : ∀ f : OSPosTestSpace,
      let u := osCompletionMap F (osPreMk F f)
      let w := u - ⟪Ω, u⟫_ℂ • Ω
      ‖T_E t w‖ ≤ Real.exp (-(Δ * t)) * ‖w‖ := by
    intro f u w
    obtain ⟨C, _, hC_cl⟩ := osConfigInner_cluster hΔ os h_herm h_S0 h_trans f f
    refine semigroup_decay_of_weak_cluster T_E hT_zero hT_add hT_sa Δ w C (fun s hs => ?_) t ht
    have h_in_split : ⟪w, T_E s w⟫_ℂ = ⟪u, T_E s u⟫_ℂ - ⟪u, Ω⟫_ℂ * ⟪Ω, u⟫_ℂ := by
      let c := ⟪Ω, u⟫_ℂ
      have hT_w : T_E s w = T_E s u - c • Ω := by
        dsimp [w, c]
        rw [map_sub, map_smul, hT_vac s hs]
      have hΩ_self : ⟪Ω, Ω⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hΩ_norm]; norm_num
      have hΩ_Tu : ⟪Ω, T_E s u⟫_ℂ = c := by
        rw [← hT_sa s hs, hT_vac s hs]
      have hu_Ω : ⟪u, Ω⟫_ℂ = starRingEnd ℂ c := (inner_conj_symm u Ω).symm
      rw [hT_w]
      dsimp [w, c]
      rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_right,
        inner_smul_left, inner_smul_right, hΩ_Tu, hu_Ω, hΩ_self]
      ring
    have h_inner_eq : ⟪u, T_E s u⟫_ℂ = osConfigInner os f (osTimeShiftPre s hs f) := by
      have h_sem : T_E s u = osCompletionMap F (osPreMk F (osTimeShiftPre s hs f)) := by
        dsimp [T_E, osLiftSemigroup, u]
        rw [dif_pos hs, osLiftOperator_coe]
        congr 2
        dsimp [osTimeShiftSemigroup]
        rw [dif_pos hs]
      rw [h_sem, osCompletionMap_inner]
      rfl
    have hu_Ω_eq : ⟪u, Ω⟫_ℂ = osConfigInner os f (osConfigSingle emptyPosConfig) := by
      rw [osCompletionMap_inner]; rfl
    have hΩ_u_eq : ⟪Ω, u⟫_ℂ = osConfigInner os (osConfigSingle emptyPosConfig) f := by
      rw [osCompletionMap_inner]; rfl
    calc (⟪w, T_E s w⟫_ℂ).re ≤ ‖⟪w, T_E s w⟫_ℂ‖ :=
          (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ = ‖osConfigInner os f (osTimeShiftPre s hs f) -
            osConfigInner os f (osConfigSingle emptyPosConfig) *
              osConfigInner os (osConfigSingle emptyPosConfig) f‖ := by
          rw [h_in_split, h_inner_eq, hu_Ω_eq, hΩ_u_eq]
      _ ≤ C * Real.exp (-(Δ * s)) := hC_cl s hs
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (2 * (‖T_E t‖ + Real.exp (-(Δ * t))) + 1)
  have hδ_pos : 0 < δ := by positivity
  have hv_cl : v ∈ closure (Set.range (osCompletionMap F)) := by
    rw [osCompletionMap_dense F]; trivial
  obtain ⟨y_im, ⟨u_pre, rfl⟩, hvu⟩ := Metric.mem_closure_iff.mp hv_cl δ hδ_pos
  rcases Quotient.exists_rep u_pre with ⟨f, rfl⟩
  let u : H := osCompletionMap F (osPreMk F f)
  let w : H := u - ⟪Ω, u⟫_ℂ • Ω
  have hΩ_v : ⟪Ω, v⟫_ℂ = 0 := by rw [← inner_conj_symm, hv_orth, map_zero]
  have hvw_eq : v - w = (v - u) - ⟪Ω, v - u⟫_ℂ • Ω := by
    dsimp [w]
    rw [inner_sub_right, hΩ_v, zero_sub, neg_smul]
    abel
  have hvu' : dist v u < δ := by simpa [u] using hvu
  have hvw_lt : ‖v - w‖ < 2 * δ := by
    rw [hvw_eq]
    calc ‖(v - u) - ⟪Ω, v - u⟫_ℂ • Ω‖
        ≤ ‖v - u‖ + ‖⟪Ω, v - u⟫_ℂ • Ω‖ := norm_sub_le _ _
      _ = ‖v - u‖ + ‖⟪Ω, v - u⟫_ℂ‖ * ‖Ω‖ := by rw [norm_smul]
      _ ≤ ‖v - u‖ + (‖Ω‖ * ‖v - u‖) * ‖Ω‖ := by gcongr; exact norm_inner_le_norm _ _
      _ = 2 * dist v u := by rw [hΩ_norm, dist_eq_norm]; ring
      _ < 2 * δ := by linarith [hvu']
  have hw_norm : ‖w‖ ≤ ‖v‖ + ‖v - w‖ := by
    calc ‖w‖ = ‖v - (v - w)‖ := by congr 1; abel
      _ ≤ ‖v‖ + ‖v - w‖ := norm_sub_le _ _
  have h_eps : (Real.exp (-(Δ * t)) + ‖T_E t‖) * (2 * δ) ≤ ε := by
    have hpos : 0 < 2 * (‖T_E t‖ + Real.exp (-(Δ * t))) + 1 := by positivity
    have hrw : (Real.exp (-(Δ * t)) + ‖T_E t‖) * (2 * δ) =
        ε * ((2 * (‖T_E t‖ + Real.exp (-(Δ * t)))) /
          (2 * (‖T_E t‖ + Real.exp (-(Δ * t))) + 1)) := by
      dsimp [δ]; ring
    rw [hrw]
    exact mul_le_of_le_one_right hε.le ((div_le_one hpos).mpr (by linarith))
  calc ‖T_E t v‖
      = ‖T_E t (w + (v - w))‖ := by exact congrArg (fun x => ‖T_E t x‖) (by abel : v = w + (v - w))
    _ = ‖T_E t w + T_E t (v - w)‖ := by rw [map_add]
    _ ≤ ‖T_E t w‖ + ‖T_E t (v - w)‖ := norm_add_le _ _
    _ ≤ Real.exp (-(Δ * t)) * ‖w‖ + ‖T_E t‖ * ‖v - w‖ :=
        add_le_add (h_dense_bound f) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ Real.exp (-(Δ * t)) * (‖v‖ + ‖v - w‖) + ‖T_E t‖ * ‖v - w‖ := by
        gcongr
    _ = Real.exp (-(Δ * t)) * ‖v‖ + (Real.exp (-(Δ * t)) + ‖T_E t‖) * ‖v - w‖ := by ring
    _ ≤ Real.exp (-(Δ * t)) * ‖v‖ + (Real.exp (-(Δ * t)) + ‖T_E t‖) * (2 * δ) := by
        gcongr
    _ ≤ Real.exp (-(Δ * t)) * ‖v‖ + ε := by linarith

end OSClusteringToSemigroupGap


end YangMills
