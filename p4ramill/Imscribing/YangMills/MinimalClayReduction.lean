import Imscribing.YangMills.SchwingerToClayMaster
import Imscribing.YangMills.LatticeChessboardAndTransfer4D
import Imscribing.YangMills.PoincareLieAlgebraAndNelson

/-!
# Minimal Irreducible Clay Yang–Mills Reduction

Collects the discharged stack and states the strictly minimal residual targets:
1. `MinimalBalabanRGTarget`: weak-coupling continuum limit of smeared 4D SU(N)
   Wilson expectations along `(ymSpacing, ymBetaAF N)` producing `ContinuumSchwingerOS`
   with `ReflectTensorData`, Euclidean reflection positivity, and uniform clustering `Δ > 0`.
2. `MinimalOSContinuationTarget`: Fourier–Laplace tube analytic continuation of
   `C` to Poincaré unitaries `U` and weak-local smeared fields `field` with `iε`-IBP control.
-/

namespace Imscribing.YangMills.MinimalReduction

set_option maxSynthPendingDepth 1
set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.OSBorchers
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.BorchersSchwinger
open Imscribing.YangMills.SchwingerClayMaster

/-- Strictly minimal Balaban RG continuum limit target for 4D SU(N) Yang–Mills. -/
structure MinimalBalabanRGTarget (N : ℕ) (hN : 2 ≤ N) where
  C : ContinuumSchwingerOS
  R : ReflectTensorData
  h_herm : ∀ F G : BorchersPos, borchersForm C R G F = star (borchersForm C R F G)
  h_rp : ∀ F : BorchersPos, 0 ≤ (borchersForm C R F F).re
  h_symm : ∀ t : ℝ, 0 ≤ t → ∀ F G : BorchersPos,
    borchersForm C R F (borchersShift R t G) = borchersForm C R (borchersShift R t F) G
  h_cluster : ∀ t : ℝ, 0 ≤ t → ∀ F : BorchersPos,
    borchersForm C R borchersVac F = 0 →
    (borchersForm C R (borchersShift R t F) (borchersShift R t F)).re ≤
      Real.exp (-2 * C.cluster_rate * t) * (borchersForm C R F F).re
  variance_elem : BorchersPos
  variance_strict :
    ‖borchersForm C R borchersVac variance_elem‖ ^ 2 <
      (borchersForm C R variance_elem variance_elem).re

/-- Strictly minimal Osterwalder–Schrader Poincaré + weak-field continuation target
    on the already-constructed Hilbert completion `Completion (BorchersPos ⧸ N₀)`. -/
structure MinimalOSContinuationTarget {N : ℕ} {hN : 2 ≤ N}
    (B : MinimalBalabanRGTarget N hN) where
  poincare_and_weak_fields :
    let pre := buildBorchersPreData B.C B.R B.h_herm B.h_rp B.h_symm B.h_cluster
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

/-- **Minimal Clay Reduction Theorem:**
    Discharges all Hilbert completion, contractivity, generator construction,
    vacuum uniqueness, spectral gap, boundary temperedness, and operator
    microcausality obligations unconditionally. -/
theorem clay_yang_mills_from_minimal_targets
    (N : ℕ) (hN : 2 ≤ N)
    (B : MinimalBalabanRGTarget N hN)
    (C : MinimalOSContinuationTarget B) :
    ∃ (Q : WightmanQFT4D),
      HasYangMillsUVScaling N Q ∧ HasStrictMassGap Q B.C.cluster_rate := by
  let D : ContinuumWightmanBridgeData N :=
    { hN := hN
      C := B.C
      R := B.R
      h_herm := B.h_herm
      h_rp := B.h_rp
      h_symm := B.h_symm
      h_cluster := B.h_cluster
      variance_elem := B.variance_elem
      variance_strict := B.variance_strict
      poincare_and_weak_fields := by
        obtain ⟨U, fieldDomain, field, hU_vac, hU_zero, hU_add, h_dense, hΩ_dom,
          h_maps, h_weak_loc, f₀, g₀, W_reg, W_deriv, p, C₁, C₂,
          hp_nn, hC₁, hC₂, h_at1, h_deriv, h_dbound, h_disj, h_2pt⟩ := C.poincare_and_weak_fields
        refine ⟨U, fieldDomain, field, hU_vac, hU_zero, hU_add, h_dense, hΩ_dom,
          h_maps, ?_, f₀, g₀, W_reg, W_deriv, p, C₁, C₂,
          hp_nn, hC₁, hC₂, h_at1, h_deriv, h_dbound, h_disj, h_2pt⟩
        intro f g hfg ψ₁ ψ₂
        exact h_weak_loc f g hfg ψ₁ ψ₂ (h_maps g ψ₂) (h_maps f ψ₂) }
  exact clay_yang_mills_from_continuum_schwinger D

end Imscribing.YangMills.MinimalReduction