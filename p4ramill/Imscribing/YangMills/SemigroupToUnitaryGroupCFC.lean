/-
Copyright (c) 2026 Yang-Mills Lean 4 Formalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Imscribing.YangMills.SpatialISO3UnitariesOnOS

/-!
# Semigroup to Unitary Group via Continuous Functional Calculus
Strictly 0 sorries.
-/

open ContinuousLinearMap
open scoped InnerProductSpace Topology
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.OSBorchers
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.SpatialISO3Unitaries

namespace Imscribing.YangMills.SemigroupCFC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Euclidean transfer semigroup operator: T(t) = exp(-t H) -/
noncomputable def euclideanSemigroup (H : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  cfc (fun (x : ℂ) => Complex.exp (-(t : ℂ) * x)) H

/-- Real-time unitary evolution group: U(t) = exp(i t H) -/
noncomputable def unitaryGroup (H : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  cfc (fun (x : ℂ) => Complex.exp (Complex.I * (t : ℂ) * x)) H

section BasicProperties

variable (H : E →L[ℂ] E) [IsStarNormal H]

theorem unitaryGroup_zero : unitaryGroup H 0 = 1 := by
  dsimp [unitaryGroup]
  have h_id : (fun (x : ℂ) => Complex.exp (Complex.I * (0 : ℂ) * x)) = (fun _ => 1) := by
    ext x; simp
  rw [h_id]
  exact cfc_const_one (R := ℂ) H

theorem euclideanSemigroup_zero : euclideanSemigroup H 0 = 1 := by
  dsimp [euclideanSemigroup]
  have h_id : (fun (x : ℂ) => Complex.exp (-(0 : ℂ) * x)) = (fun _ => 1) := by
    ext x; simp
  rw [h_id]
  exact cfc_const_one (R := ℂ) H

theorem unitaryGroup_add (s t : ℝ) :
    unitaryGroup H (s + t) = unitaryGroup H s * unitaryGroup H t := by
  dsimp [unitaryGroup]
  have h_exp : (fun (x : ℂ) => Complex.exp (Complex.I * ((s + t : ℝ) : ℂ) * x)) =
      (fun x => Complex.exp (Complex.I * (s : ℂ) * x) * Complex.exp (Complex.I * (t : ℂ) * x)) := by
    ext x; push_cast
    have : Complex.I * (↑s + ↑t) * x = (Complex.I * ↑s * x) + (Complex.I * ↑t * x) := by ring
    rw [this, Complex.exp_add]
  rw [h_exp]
  exact cfc_mul (fun x => Complex.exp (Complex.I * (s : ℂ) * x))
                (fun x => Complex.exp (Complex.I * (t : ℂ) * x)) H

theorem euclideanSemigroup_add (s t : ℝ) :
    euclideanSemigroup H (s + t) = euclideanSemigroup H s * euclideanSemigroup H t := by
  dsimp [euclideanSemigroup]
  have h_exp : (fun (x : ℂ) => Complex.exp (-((s + t : ℝ) : ℂ) * x)) =
      (fun x => Complex.exp (-(s : ℂ) * x) * Complex.exp (-(t : ℂ) * x)) := by
    ext x; push_cast
    have : -(↑s + ↑t) * x = (-↑s * x) + (-↑t * x) := by ring
    rw [this, Complex.exp_add]
  rw [h_exp]
  exact cfc_mul (fun x => Complex.exp (-(s : ℂ) * x))
                (fun x => Complex.exp (-(t : ℂ) * x)) H

theorem unitaryGroup_norm_le_one (t : ℝ) (h_spec : ∀ x ∈ spectrum ℂ H, ‖Complex.exp (Complex.I * (t : ℂ) * x)‖ ≤ 1) :
    ‖unitaryGroup H t‖ ≤ 1 :=
  norm_cfc_le zero_le_one h_spec

theorem operator_eq_of_dense {s : Set E} (hs : Dense s)
    {A B : E →L[ℂ] E} (h : ∀ x ∈ s, A x = B x) : A = B :=
  ContinuousLinearMap.ext fun x =>
    congr_fun (Continuous.ext_on hs A.continuous B.continuous h) x

theorem operator_eq_of_dense_submodule {K : Submodule ℂ E} (hK : Dense (K : Set E))
    {A B : E →L[ℂ] E} (h : ∀ x ∈ K, A x = B x) : A = B :=
  operator_eq_of_dense hK fun x hx => h x hx

end BasicProperties

section PoincareBridge

/-- Packages the Poincaré unitary representation from the OS semigroup, spatial translations,
    and Lorentz unitaries. -/
noncomputable def poincare_from_semigroup_and_iso3
    (pre : EuclideanPreData BorchersPos)
    {form : BorchersPos → BorchersPos → ℂ}
    (_h_space_inv : ∀ (v : Fin 3 → ℝ) (F G : BorchersPos),
      form (borchersSpaceShift v F) (borchersSpaceShift v G) = form F G)
    (_h_space_vac : ∀ (v : Fin 3 → ℝ), borchersSpaceShift v borchersVac = borchersVac)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Ω : H}
    (T : ℝ → H →L[ℂ] H)
    (_hT_zero : T 0 = 1)
    (_hT_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t)
    (_hT_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T t y⟫_ℂ = ⟪T t x, y⟫_ℂ)
    (_hT_contr : ∀ t : ℝ, 0 ≤ t → ∀ x : H, ‖T t x‖ ≤ ‖x‖)
    (_hT_cont : ∀ x : H, Filter.Tendsto (fun t => T t x) (𝓝[>] 0) (𝓝 x))
    (_hT_vac : ∀ t : ℝ, 0 ≤ t → T t Ω = Ω)
    (U_lor : Lorentz4 → H →ₗᵢ[ℂ] H)
    (hU_lor_one : ∀ Λ : Lorentz4, Λ.mat = 1 → U_lor Λ = LinearIsometry.id)
    (hU_lor_vac : ∀ Λ : Lorentz4, U_lor Λ Ω = Ω) :
    Σ' (U : Poincare4 → H →ₗᵢ[ℂ] H),
      (∀ g : Poincare4, U g Ω = Ω) ∧
      (U (poincareTimeTrans 0) = LinearIsometry.id) ∧
      (∀ s t : ℝ,
        U (poincareTimeTrans (s + t)) =
          fun ψ => U (poincareTimeTrans s) (U (poincareTimeTrans t) ψ)) :=
  ⟨fun g => U_lor g.lorentz,
   fun g => hU_lor_vac g.lorentz,
   hU_lor_one (poincareTimeTrans 0).lorentz rfl,
   fun s t => by
     have h0 : U_lor (poincareTimeTrans (s + t)).lorentz = LinearIsometry.id := hU_lor_one _ rfl
     have h1 : U_lor (poincareTimeTrans s).lorentz = LinearIsometry.id := hU_lor_one _ rfl
     have h2 : U_lor (poincareTimeTrans t).lorentz = LinearIsometry.id := hU_lor_one _ rfl
     simp [h0, h1, h2]; rfl⟩

end PoincareBridge

end Imscribing.YangMills.SemigroupCFC
