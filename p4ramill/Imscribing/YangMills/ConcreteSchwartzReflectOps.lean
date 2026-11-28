import Imscribing.YangMills.ConcreteSchwartzShiftAndReflect

/-!
# Concrete Euclidean Time-Reflection + Conjugation on `EuclideanSchwartz`
-/

namespace Imscribing.YangMills.ConcreteReflectOps

open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.ConcreteSchwartzShiftAndReflect

/-- Time-reflection map `Θ : (Fin m → Spacetime4) →L[ℝ] (Fin m → Spacetime4)`. -/
noncomputable def euclidTimeReflect (m : ℕ) : (Fin m → Spacetime4) →L[ℝ] (Fin m → Spacetime4) :=
  timeReflectCLM m

theorem euclidTimeReflect_involutive (m : ℕ) (x : Fin m → Spacetime4) :
    euclidTimeReflect m (euclidTimeReflect m x) = x := by
  ext k μ
  dsimp [euclidTimeReflect, timeReflectCLM]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, stdBasis4_apply, Fin.isValue]
  split_ifs <;> ring

theorem euclidTimeReflect_norm (m : ℕ) (x : Fin m → Spacetime4) :
    ‖euclidTimeReflect m x‖ = ‖x‖ := by
  have h_pt : ∀ k : Fin m, ‖euclidTimeReflect m x k‖ = ‖x k‖ := by
    intro k
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Fin.sum_univ_four, euclidTimeReflect, timeReflectCLM, LinearMap.coe_mk,
      AddHom.coe_mk, ContinuousLinearMap.coe_mk', PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      stdBasis4_apply, Fin.isValue, ↓reduceIte]
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

theorem euclidTimeReflect_opNorm_le (m : ℕ) : ‖euclidTimeReflect m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, euclidTimeReflect_norm]

/-- Concrete `SchwartzMap` time-reflection and complex conjugation `x ↦ star (f (Θ x))`. -/
noncomputable def reflectConjSchwartz (m : ℕ) (f : EuclideanSchwartz m) :
    EuclideanSchwartz m :=
  ConcreteSchwartzShiftAndReflect.reflectConjSchwartz m f

@[simp]
theorem reflectConjSchwartz_apply (m : ℕ) (f : EuclideanSchwartz m) (x : Fin m → Spacetime4) :
    reflectConjSchwartz m f x = star (f (euclidTimeReflect m x)) := rfl

theorem reflectConjSchwartz_involutive (m : ℕ) (f : EuclideanSchwartz m) :
    reflectConjSchwartz m (reflectConjSchwartz m f) = f := by
  ext x
  simp [euclidTimeReflect_involutive]

theorem reflectConjSchwartz_add (m : ℕ) (f g : EuclideanSchwartz m) :
    reflectConjSchwartz m (f + g) = reflectConjSchwartz m f + reflectConjSchwartz m g := by
  ext x; simp

theorem reflectConjSchwartz_smul (m : ℕ) (c : ℂ) (f : EuclideanSchwartz m) :
    reflectConjSchwartz m (c • f) = star c • reflectConjSchwartz m f := by
  ext x; simp

end Imscribing.YangMills.ConcreteReflectOps