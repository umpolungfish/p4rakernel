import Imscribing.YangMills.ConcreteTensorProductSchwartz
import Imscribing.YangMills.MinimalClayReduction

/-!
# Concrete Minimal Clay Yang–Mills Reduction (Zero Abstract `ReflectTensorData`)

Permanently instantiates `R := concreteReflectTensorData` on `SchwartzMap`,
eliminating `R : ReflectTensorData` from `ConcreteBalabanTarget` and `ConcreteOSTarget`,
and proves `clay_yang_mills_from_concrete_targets` (`0 sorry`).
-/

namespace Imscribing.YangMills.ConcreteMinimalReduction

set_option maxSynthPendingDepth 1
set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.OSBorchers
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.BorchersSchwinger
open Imscribing.YangMills.MinimalReduction
open Imscribing.YangMills.ConcreteTensorSchwartz

/-- Concrete Borchers form on `BorchersPos` induced by `C : ContinuumSchwingerOS`. -/
noncomputable def concreteBorchersForm (C : ContinuumSchwingerOS) :
    BorchersPos → BorchersPos → ℂ :=
  borchersForm C concreteReflectTensorData

/-- Concrete positive-time shift on `BorchersPos`. -/
noncomputable def concreteBorchersShift (t : ℝ) : BorchersPos →ₗ[ℂ] BorchersPos :=
  borchersShift concreteReflectTensorData t

theorem concreteBorchersShift_zero (F : BorchersPos) :
    concreteBorchersShift 0 F = F := by
  unfold concreteBorchersShift borchersShift
  ext n x
  simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply]
  rw [concreteReflectTensorData_shiftPos_zero n (F n)]

/-- Balaban RG continuum limit target with `R` permanently fixed to `concreteReflectTensorData`. -/
structure ConcreteBalabanTarget (N : ℕ) (hN : 2 ≤ N) where
  C : ContinuumSchwingerOS
  h_herm : ∀ F G : BorchersPos,
    concreteBorchersForm C G F = star (concreteBorchersForm C F G)
  h_rp : ∀ F : BorchersPos, 0 ≤ (concreteBorchersForm C F F).re
  h_symm : ∀ t : ℝ, 0 ≤ t → ∀ F G : BorchersPos,
    concreteBorchersForm C F (concreteBorchersShift t G) =
      concreteBorchersForm C (concreteBorchersShift t F) G
  h_cluster : ∀ t : ℝ, 0 ≤ t → ∀ F : BorchersPos,
    concreteBorchersForm C borchersVac F = 0 →
    (concreteBorchersForm C (concreteBorchersShift t F) (concreteBorchersShift t F)).re ≤
      Real.exp (-2 * C.cluster_rate * t) * (concreteBorchersForm C F F).re
  variance_elem : BorchersPos
  variance_strict :
    ‖concreteBorchersForm C borchersVac variance_elem‖ ^ 2 <
      (concreteBorchersForm C variance_elem variance_elem).re

/-- Minimal OS analytic continuation target with `R` permanently fixed to `concreteReflectTensorData`. -/
structure ConcreteOSTarget {N : ℕ} {hN : 2 ≤ N} (B : ConcreteBalabanTarget N hN) where
  poincare_and_weak_fields :
    let pre := buildBorchersPreData B.C concreteReflectTensorData
      B.h_herm B.h_rp B.h_symm B.h_cluster
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core.toCore
    let H := UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)
    let Ω : H := ((Submodule.Quotient.mk borchersVac : BorchersPos ⧸ nullSubmodule pre) : H)
    ∃ (U : Poincare4 → H →ₗᵢ[ℂ] H)
      (fieldDomain : Submodule ℂ H)
      (field : TestFn4 → ↥fieldDomain →ₗ[ℂ] H),
      (∀ g : Poincare4, U g Ω = Ω) ∧
      U (poincareTimeTrans 0) = LinearIsometry.id ∧
      (∀ s t : ℝ,
        (U (poincareTimeTrans (s + t)) : H → H) =
          fun ψ => U (poincareTimeTrans s) (U (poincareTimeTrans t) ψ)) ∧
      Dense (fieldDomain : Set H) ∧
      Ω ∈ fieldDomain ∧
      (∀ f (ψ : ↥fieldDomain), field f ψ ∈ fieldDomain) ∧
      (∀ f g : TestFn4, SpacelikeDisjoint f g →
        ∀ (ψ₁ ψ₂ : ↥fieldDomain) (hfg : field g ψ₂ ∈ fieldDomain) (hgf : field f ψ₂ ∈ fieldDomain),
          ⟪(ψ₁ : H), field f ⟨field g ψ₂, hfg⟩⟫_ℂ =
          ⟪(ψ₁ : H), field g ⟨field f ψ₂, hgf⟩⟫_ℂ) ∧
      (∃ (f₀ g₀ : TestFn4)
         (W_reg W_deriv : ℝ → TestFn4 →ₗ[ℂ] ℂ)
         (p : TestFn4 → ℝ) (C₁ C₂ : ℝ),
         (∀ f, 0 ≤ p f) ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
         (∀ f, ‖W_reg 1 f‖ ≤ C₁ * p f) ∧
         (∀ f, ∀ ε ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (fun t => W_reg t f) (W_deriv ε f) ε) ∧
         (∀ f, ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ‖W_deriv ε f‖ ≤ C₂ * p f) ∧
         Disjoint (Function.support f₀) (Function.support g₀) ∧
         ∀ hΩ hg,
           Filter.Tendsto (fun t => W_reg t g₀) (nhdsWithin 0 (Set.Ioi 0))
             (nhds ⟪Ω, field f₀ ⟨field g₀ ⟨Ω, hΩ⟩, hg⟩⟫_ℂ) ∧
           ⟪Ω, field f₀ ⟨field g₀ ⟨Ω, hΩ⟩, hg⟩⟫_ℂ ≠ 0)

/-- **Concrete Minimal Clay Yang–Mills Reduction Theorem:**
    Every `ConcreteBalabanTarget` + `ConcreteOSTarget` yields a strict Clay 4D
    `WightmanQFT4D` satisfying `HasYangMillsUVScaling N Q` and `HasStrictMassGap Q B.C.cluster_rate`. -/
theorem clay_yang_mills_from_concrete_targets
    (N : ℕ) (hN : 2 ≤ N)
    (B : ConcreteBalabanTarget N hN)
    (C : ConcreteOSTarget B) :
    ∃ (Q : WightmanQFT4D),
      HasYangMillsUVScaling N Q ∧ HasStrictMassGap Q B.C.cluster_rate := by
  let B_min : MinimalBalabanRGTarget N hN :=
    { C := B.C
      R := concreteReflectTensorData
      h_herm := B.h_herm
      h_rp := B.h_rp
      h_symm := B.h_symm
      h_cluster := B.h_cluster
      variance_elem := B.variance_elem
      variance_strict := B.variance_strict }
  let C_min : MinimalOSContinuationTarget B_min :=
    { poincare_and_weak_fields := C.poincare_and_weak_fields }
  exact clay_yang_mills_from_minimal_targets N hN B_min C_min

end Imscribing.YangMills.ConcreteMinimalReduction