import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.NormedSpace.Extend
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Imscribing.YangMills.SpatialISO3UnitariesOnOS

/-!
# Direct Minkowski Time-Translation Unitary Group from Any OS Contraction Semigroup

Constructs `U₀ : ℝ → H →ₗᵢ[ℂ] H` (`exp(-i s H)`) directly from any strongly
continuous symmetric contraction semigroup `T : ℝ → H →L[ℂ] H` using the
C⋆-algebra `continuousFunctionalCalculus` on `A = T 1` (`0 sorry`).
-/

namespace Imscribing.YangMills.SemigroupCFC

open scoped InnerProductSpace Topology
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.OSBorchers
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.UnitaryExtension
open Imscribing.YangMills.SpatialISO3Unitaries

section CFCTimeGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma clm_isSelfAdjoint_of_symm (M : H →L[ℂ] H)
    (h_symm : ∀ x y : H, ⟪x, M y⟫_ℂ = ⟪M x, y⟫_ℂ) :
    IsSelfAdjoint M := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, h_symm x y]
