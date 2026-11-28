import Imscribing.YangMills.ConcreteTensorProductSchwartz
import Imscribing.YangMills.OSBorchersBridge

/-!
# Concrete 3D Spatial Translation Unitaries on `OSHilbert`

Constructs the global 3D spatial translation unitary group `U_space : (Fin 3 → ℝ) → H →ₗᵢ[ℂ] H`
directly on `H = UniformSpace.Completion (BorchersPos ⧸ N₀)` (`0 sorry`):
1. `shiftSpaceSchwartz`: spatial shift `x ↦ f (x - (0, v))` preserving `PosSchwartzSubmodule n`.
2. `spatialTranslationUnitaryGroup`: proves `U_space 0 = id`, `U_space (u + v) = U_space u ∘ U_space v`,
   and vacuum invariance `U_space v Ω = Ω` whenever `pre.B` is spatially translation invariant.
3. `spatialTranslation_commutes_with_os_semigroup`: `U_space v (T t x) = T t (U_space v x)`.
-/

namespace Imscribing.YangMills.SpatialISO3Unitaries

open scoped InnerProductSpace
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.OSCompletion
open Imscribing.YangMills.OSBorchers
open Imscribing.YangMills.BorchersReconstruction

/-- Purely spatial translation vector `(0, v₀, v₁, v₂)` across all `n` coordinates. -/
def spaceShiftVec (n : ℕ) (v : Fin 3 → ℝ) : Fin n → Spacetime4 :=
  fun _ => (WithLp.equiv 2 (Fin 4 → ℝ)).symm ![0, v 0, v 1, v 2]

theorem spaceShiftVec_zero (n : ℕ) : spaceShiftVec n 0 = 0 := by
  ext k μ; fin_cases μ <;> simp [spaceShiftVec]

theorem spaceShiftVec_add (n : ℕ) (u v : Fin 3 → ℝ) :
    spaceShiftVec n (u + v) = spaceShiftVec n u + spaceShiftVec n v := by
  ext k μ; fin_cases μ <;> simp [spaceShiftVec]

private lemma iteratedFDeriv_comp_sub_space {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (h_all_diff : ∀ m : ℕ, Differentiable ℝ (iteratedFDeriv ℝ m f))
    (v : E) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m (fun y => f (y - v)) x = iteratedFDeriv ℝ m f (x - v) := by
  induction m generalizing x with
  | zero => ext; simp [iteratedFDeriv_zero_eq_comp]
  | succ m ih =>
      ext L
      rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
      have h_eq : (fun y => iteratedFDeriv ℝ m (fun z => f (z - v)) y) =
          fun y => iteratedFDeriv ℝ m f (y - v) := funext ih
      have h_fd : fderiv ℝ (fun y => iteratedFDeriv ℝ m f (y - v)) x =
          fderiv ℝ (iteratedFDeriv ℝ m f) (x - v) := by
        have h_hd := ((h_all_diff m (x - v)).hasFDerivAt).comp x ((hasFDerivAt_id x).sub_const v)
        simpa using h_hd.fderiv
      simp only [ContinuousMultilinearMap.comp_apply, continuousMultilinearCurryLeftEquiv_symm_apply,
        h_eq, h_fd]

/-- Concrete 3D spatial translation `f ↦ (x ↦ f (x - (0, v)))` on `EuclideanSchwartz n`. -/
noncomputable def shiftSpaceSchwartz (n : ℕ) (v : Fin 3 → ℝ) (f : EuclideanSchwartz n) :
    EuclideanSchwartz n where
  toFun x := f (x - spaceShiftVec n v)
  smooth' := (f.smooth').comp (contDiff_id.sub contDiff_const)
  decay' k m := by
    have h_all_diff : ∀ j : ℕ, Differentiable ℝ (iteratedFDeriv ℝ j f) := fun j =>
      (f.smooth'.iteratedFDeriv_right (m := j) le_top).differentiable (by simp)
    obtain ⟨C₀, hC₀⟩ := f.decay' 0 m
    obtain ⟨Ck, hCk⟩ := f.decay' k m
    have hC₀_nn : 0 ≤ C₀ := le_trans (by positivity) (hC₀ 0)
    have hCk_nn : 0 ≤ Ck := le_trans (by positivity) (hCk 0)
    refine ⟨(2 : ℝ) ^ k * (Ck + ‖spaceShiftVec n v‖ ^ k * C₀), fun x => ?_⟩
    rw [iteratedFDeriv_comp_sub_space f h_all_diff (spaceShiftVec n v) m x]
    have h_tri : ‖x‖ ≤ ‖x - spaceShiftVec n v‖ + ‖spaceShiftVec n v‖ := by
      simpa [sub_add_cancel] using norm_add_le (x - spaceShiftVec n v) (spaceShiftVec n v)
    have h_pow : ‖x‖ ^ k ≤ (2 : ℝ) ^ k * (‖x - spaceShiftVec n v‖ ^ k + ‖spaceShiftVec n v‖ ^ k) := by
      have h1 : ‖x‖ ^ k ≤ (‖x - spaceShiftVec n v‖ + ‖spaceShiftVec n v‖) ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) h_tri k
      have h_max : ‖x - spaceShiftVec n v‖ + ‖spaceShiftVec n v‖ ≤
          2 * max ‖x - spaceShiftVec n v‖ ‖spaceShiftVec n v‖ := by
        linarith [le_max_left ‖x - spaceShiftVec n v‖ ‖spaceShiftVec n v‖,
          le_max_right ‖x - spaceShiftVec n v‖ ‖spaceShiftVec n v‖]
      have h2 := pow_le_pow_left₀ (by positivity) h_max k
      rw [mul_pow] at h2
      have h_max_le : (max ‖x - spaceShiftVec n v‖ ‖spaceShiftVec n v‖) ^ k ≤
          ‖x - spaceShiftVec n v‖ ^ k + ‖spaceShiftVec n v‖ ^ k := by
        rcases le_total ‖x - spaceShiftVec n v‖ ‖spaceShiftVec n v‖ with h | h
        · rw [max_eq_right h]; linarith [pow_nonneg (norm_nonneg (x - spaceShiftVec n v)) k]
        · rw [max_eq_left h]; linarith [pow_nonneg (norm_nonneg (spaceShiftVec n v)) k]
      exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left h_max_le (by positivity)))
    have h_iter_nn : 0 ≤ ‖iteratedFDeriv ℝ m f (x - spaceShiftVec n v)‖ := norm_nonneg _
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f (x - spaceShiftVec n v)‖
          ≤ (2 : ℝ) ^ k * (‖x - spaceShiftVec n v‖ ^ k + ‖spaceShiftVec n v‖ ^ k) *
              ‖iteratedFDeriv ℝ m f (x - spaceShiftVec n v)‖ :=
            mul_le_mul_of_nonneg_right h_pow h_iter_nn
      _ = (2 : ℝ) ^ k * (‖x - spaceShiftVec n v‖ ^ k * ‖iteratedFDeriv ℝ m f (x - spaceShiftVec n v)‖ +
            ‖spaceShiftVec n v‖ ^ k * (‖x - spaceShiftVec n v‖ ^ 0 *
              ‖iteratedFDeriv ℝ m f (x - spaceShiftVec n v)‖)) := by simp; ring
      _ ≤ (2 : ℝ) ^ k * (Ck + ‖spaceShiftVec n v‖ ^ k * C₀) := by
            gcongr
            · exact hCk (x - spaceShiftVec n v)
            · exact hC₀ (x - spaceShiftVec n v)

@[simp]
theorem shiftSpaceSchwartz_apply (n : ℕ) (v : Fin 3 → ℝ) (f : EuclideanSchwartz n)
    (x : Fin n → Spacetime4) :
    shiftSpaceSchwartz n v f x = f (x - spaceShiftVec n v) := rfl

theorem shiftSpaceSchwartz_mem_pos {n : ℕ} (v : Fin 3 → ℝ)
    (f : PosSchwartzSubmodule n) :
    shiftSpaceSchwartz n v f.1 ∈ PosSchwartzSubmodule n := by
  rcases f.2 with rfl | hpos
  · exact Or.inl rfl
  · right
    intro x hx i
    have h1 := hpos (x - spaceShiftVec n v) hx i
    simp only [Pi.sub_apply, spaceShiftVec, PiLp.sub_apply, WithLp.equiv_symm_pi_apply,
      Matrix.cons_val_zero, sub_zero] at h1
    exact h1

/-- Linear 3D spatial translation on `PosSchwartzSubmodule n` for ALL `v : Fin 3 → ℝ`. -/
noncomputable def shiftSpacePos (v : Fin 3 → ℝ) (n : ℕ) :
    PosSchwartzSubmodule n →ₗ[ℂ] PosSchwartzSubmodule n where
  toFun f := ⟨shiftSpaceSchwartz n v f.1, shiftSpaceSchwartz_mem_pos v f⟩
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

/-- Global 3D spatial translation operator on `BorchersPos`. -/
noncomputable def borchersSpaceShift (v : Fin 3 → ℝ) : BorchersPos →ₗ[ℂ] BorchersPos :=
  DFinsupp.mapRange.linearMap (shiftSpacePos v)

theorem borchersSpaceShift_zero (F : BorchersPos) :
    borchersSpaceShift 0 F = F := by
  unfold borchersSpaceShift
  ext n x
  simp [DFinsupp.mapRange.linearMap_apply, shiftSpacePos, spaceShiftVec_zero]

theorem borchersSpaceShift_add (u v : Fin 3 → ℝ) (F : BorchersPos) :
    borchersSpaceShift (u + v) F = borchersSpaceShift u (borchersSpaceShift v F) := by
  unfold borchersSpaceShift
  ext n x
  simp only [DFinsupp.mapRange.linearMap_apply, shiftSpacePos, LinearMap.coe_mk, AddHom.coe_mk,
    shiftSpaceSchwartz_apply, spaceShiftVec_add]
  congr 1
  abel

theorem borchersSpaceShift_vac (v : Fin 3 → ℝ) :
    borchersSpaceShift v borchersVac = borchersVac := by
  unfold borchersSpaceShift borchersVac
  ext n x
  by_cases hn : n = 0
  · subst hn
    simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.single_eq_same, shiftSpacePos,
      LinearMap.coe_mk, AddHom.coe_mk, shiftSpaceSchwartz_apply]
    have h0 : x - spaceShiftVec 0 v = x := by ext i; exact i.elim0
    simp [h0]
  · simp [DFinsupp.mapRange.linearMap_apply, DFinsupp.single_eq_of_ne hn]

/-- **3D Spatial Translation Unitary Group on `OSHilbert`:**
    Given any `pre : EuclideanPreData BorchersPos` whose form `B` is invariant under
    3D spatial translations and `borchersSpaceShift v pre.e₀ = pre.e₀`, descends to an
    exact unitary representation `U_space : (Fin 3 → ℝ) → H →ₗᵢ[ℂ] H` fixing `Ω`. -/
noncomputable def spatialTranslationUnitaryGroup
    (pre : EuclideanPreData BorchersPos)
    (h_inv : ∀ (v : Fin 3 → ℝ) (F G : BorchersPos),
      pre.B (borchersSpaceShift v F) (borchersSpaceShift v G) = pre.B F G)
    (h_vac : ∀ v : Fin 3 → ℝ, borchersSpaceShift v pre.e₀ = pre.e₀) :
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
    let H := UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)
    let Ω : H := ((Submodule.Quotient.mk pre.e₀ : BorchersPos ⧸ nullSubmodule pre) : H)
    { U_space : (Fin 3 → ℝ) → H →ₗᵢ[ℂ] H //
      U_space 0 = LinearIsometry.id ∧
      (∀ u v : Fin 3 → ℝ, ∀ x : H, U_space (u + v) x = U_space u (U_space v x)) ∧
      (∀ v : Fin 3 → ℝ, U_space v Ω = Ω) ∧
      (∀ (v : Fin 3 → ℝ) (F : BorchersPos),
        U_space v ((Submodule.Quotient.mk F : BorchersPos ⧸ nullSubmodule pre) : H) =
          ((Submodule.Quotient.mk (borchersSpaceShift v F) : BorchersPos ⧸ nullSubmodule pre) : H)) } := by
  intro core
  letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
  set H₀ := BorchersPos ⧸ nullSubmodule pre
  set H := UniformSpace.Completion H₀
  have h_null : ∀ (v : Fin 3 → ℝ) {F : BorchersPos},
      F ∈ nullSubmodule pre → borchersSpaceShift v F ∈ nullSubmodule pre := by
    intro v F hF
    change (pre.B (borchersSpaceShift v F) (borchersSpaceShift v F)).re = 0
    rw [h_inv v F F]
    exact hF
  let U₀ : (Fin 3 → ℝ) → H₀ →ₗ[ℂ] H₀ := fun v =>
    (nullSubmodule pre).liftQ ((Submodule.mkQ (nullSubmodule pre)).comp (borchersSpaceShift v))
      (fun F hF => by
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact h_null v hF)
  have hU₀_mk : ∀ v (F : BorchersPos),
      U₀ v (Submodule.Quotient.mk F) = Submodule.Quotient.mk (borchersSpaceShift v F) :=
    fun _ _ => rfl
  have hU₀_norm : ∀ v (x : H₀), ‖U₀ v x‖ = ‖x‖ := by
    intro v x
    induction x using Submodule.Quotient.induction_on with
    | _ F =>
      have hsq : ‖U₀ v (Submodule.Quotient.mk F)‖ ^ 2 = ‖(Submodule.Quotient.mk F : H₀)‖ ^ 2 := by
        have h1 : (⟪U₀ v (Submodule.Quotient.mk F), U₀ v (Submodule.Quotient.mk F)⟫_ℂ).re =
            ‖U₀ v (Submodule.Quotient.mk F)‖ ^ 2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        have h2 : (⟪(Submodule.Quotient.mk F : H₀), Submodule.Quotient.mk F⟫_ℂ).re =
            ‖(Submodule.Quotient.mk F : H₀)‖ ^ 2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        rw [← h1, ← h2, hU₀_mk]
        change (pre.B (borchersSpaceShift v F) (borchersSpaceShift v F)).re = (pre.B F F).re
        rw [h_inv v F F]
      nlinarith [norm_nonneg (U₀ v (Submodule.Quotient.mk F)),
        norm_nonneg (Submodule.Quotient.mk F : H₀)]
  let U_clm : (Fin 3 → ℝ) → H →L[ℂ] H := fun v =>
    liftContractionToCompletion (U₀ v) (fun x => le_of_eq (hU₀_norm v x))
  have hU_coe : ∀ v (x : H₀), U_clm v (x : H) = (U₀ v x : H) := fun v x =>
    liftContractionToCompletion_coe (U₀ v) _ x
  have hU_norm : ∀ v (x : H), ‖U_clm v x‖ = ‖x‖ := by
    intro v x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (continuous_norm.comp (U_clm v).continuous) continuous_norm
    | ih x =>
        rw [hU_coe v x, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
        exact hU₀_norm v x
  let U_space : (Fin 3 → ℝ) → H →ₗᵢ[ℂ] H := fun v =>
    { toLinearMap := (U_clm v).toLinearMap
      norm_map' := hU_norm v }
  refine ⟨U_space, ?_, ?_, ?_, ?_⟩
  · ext x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (U_space 0).continuous continuous_id
    | ih x =>
        induction x using Submodule.Quotient.induction_on with
        | _ F =>
          change U_clm 0 ((Submodule.Quotient.mk F : H₀) : H) = _
          rw [hU_coe 0 _, hU₀_mk 0 F, borchersSpaceShift_zero]
          rfl
  · intro u v x
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
        exact isClosed_eq (U_space (u + v)).continuous
          ((U_space u).continuous.comp (U_space v).continuous)
    | ih x =>
        induction x using Submodule.Quotient.induction_on with
        | _ F =>
          change U_clm (u + v) ((Submodule.Quotient.mk F : H₀) : H) =
            U_clm u (U_clm v ((Submodule.Quotient.mk F : H₀) : H))
          rw [hU_coe (u + v) _, hU_coe v _, hU₀_mk, hU_coe u _, hU₀_mk, hU₀_mk,
              borchersSpaceShift_add]
  · intro v
    change U_clm v ((Submodule.Quotient.mk pre.e₀ : H₀) : H) = _
    rw [hU_coe v _, hU₀_mk, h_vac v]
  · intro v F
    change U_clm v ((Submodule.Quotient.mk F : H₀) : H) = _
    rw [hU_coe v _, hU₀_mk]

/-- **Commutation of `U_space v` with any OS Semigroup `T t` whose `pre.θ t` commutes
    with `borchersSpaceShift v`.** -/
theorem spatialTranslation_commutes_with_os_semigroup
    (pre : EuclideanPreData BorchersPos)
    (h_inv : ∀ (v : Fin 3 → ℝ) (F G : BorchersPos),
      pre.B (borchersSpaceShift v F) (borchersSpaceShift v G) = pre.B F G)
    (h_vac : ∀ v : Fin 3 → ℝ, borchersSpaceShift v pre.e₀ = pre.e₀)
    (h_comm_θ : ∀ (v : Fin 3 → ℝ) (t : ℝ), 0 ≤ t → ∀ F : BorchersPos,
      borchersSpaceShift v (pre.θ t F) = pre.θ t (borchersSpaceShift v F))
    (T : ℝ → _ →L[ℂ] _)
    (hT_coe : ∀ (t : ℝ) (ht : 0 ≤ t) (F : BorchersPos),
      T t ((Submodule.Quotient.mk F : BorchersPos ⧸ nullSubmodule pre) :
        UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)) =
      ((Submodule.Quotient.mk (pre.θ t F) : BorchersPos ⧸ nullSubmodule pre) :
        UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre))) :
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
    let U_space := (spatialTranslationUnitaryGroup pre h_inv h_vac).1
    ∀ (v : Fin 3 → ℝ) (t : ℝ), 0 ≤ t → ∀ x,
      U_space v (T t x) = T t (U_space v x) := by
  intro core
  letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core
  set U_space := (spatialTranslationUnitaryGroup pre h_inv h_vac).1
  have hU_mk := (spatialTranslationUnitaryGroup pre h_inv h_vac).2.2.2.2
  intro v t ht x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq ((U_space v).continuous.comp (T t).continuous)
        ((T t).continuous.comp (U_space v).continuous)
  | ih y =>
      induction y using Submodule.Quotient.induction_on with
      | _ F =>
        rw [hT_coe t ht F, hU_mk v (pre.θ t F), hU_mk v F,
            hT_coe t ht (borchersSpaceShift v F), h_comm_θ v t ht F]

end Imscribing.YangMills.SpatialISO3Unitaries