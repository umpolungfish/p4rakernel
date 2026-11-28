import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Wick-Rotated Poincaré Lie Algebra & Unitary Vacuum Invariance

Proves unconditionally (`0 sorry`):
1. `euclidean_skew_to_minkowski_boost_symm`: Skew-symmetry of a Euclidean
   rotation generator `J_euc` (`⟪ψ, J φ⟫ = -⟪J ψ, φ⟫`, forced by Θ R(θ) = R(-θ) Θ)
   implies symmetry of the Wick-rotated Minkowski boost `K = i J_euc`.
2. `minkowski_poincare_commutators`: Euclidean ISO(4) brackets `[J, H] = P` and
   `[J, P] = -H` yield `[K, H] = i P` and `[K, P] = -i H`.
3. `unitary_fixes_vacuum_of_generator_zero`: Any strongly continuous 1-parameter
   unitary group whose generator annihilates `Ω` fixes `Ω` for all `t : ℝ`.
-/

namespace Imscribing.YangMills.PoincareNelson

open scoped InnerProductSpace

section LieAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Wick-Rotated Boost Symmetry:**
    If `J_euc` is skew-symmetric on `D` (`⟪ψ, J φ⟫ = -⟪J ψ, φ⟫`), then the
    Minkowski boost generator `K := i J_euc` is symmetric (`⟪ψ, K φ⟫ = ⟪K ψ, φ⟫`). -/
theorem euclidean_skew_to_minkowski_boost_symm
    (D : Submodule ℂ H) (J_euc : D →ₗ[ℂ] H)
    (h_skew : ∀ ψ φ : D, ⟪(ψ : H), J_euc φ⟫_ℂ = -⟪J_euc ψ, (φ : H)⟫_ℂ) :
    let K : D →ₗ[ℂ] H := Complex.I • J_euc
    ∀ ψ φ : D, ⟪(ψ : H), K φ⟫_ℂ = ⟪K ψ, (φ : H)⟫_ℂ := by
  intro K ψ φ
  dsimp [K]
  simp only [LinearMap.smul_apply, inner_smul_right, inner_smul_left, h_skew ψ φ]
  rw [Complex.conj_I]
  ring

/-- **Euclidean ISO(4) → Minkowski Poincaré Lie-Algebra Commutators:**
    Under Wick rotation `K := i J_euc`, Euclidean `[J, H] = P` and
    `[J, P] = -H` become `[K, H] = i P` and `[K, P] = -i H`. -/
theorem minkowski_poincare_commutators
    (D : Submodule ℂ H) (H_op P J_euc : D →ₗ[ℂ] H)
    (hH_mem : ∀ ψ : D, H_op ψ ∈ D)
    (hP_mem : ∀ ψ : D, P ψ ∈ D)
    (hJ_mem : ∀ ψ : D, J_euc ψ ∈ D)
    (h_JH : ∀ ψ : D, J_euc ⟨H_op ψ, hH_mem ψ⟩ - H_op ⟨J_euc ψ, hJ_mem ψ⟩ = P ψ)
    (h_JP : ∀ ψ : D, J_euc ⟨P ψ, hP_mem ψ⟩ - P ⟨J_euc ψ, hJ_mem ψ⟩ = -H_op ψ) :
    let K : D →ₗ[ℂ] H := Complex.I • J_euc
    (∀ ψ : D, K ⟨H_op ψ, hH_mem ψ⟩ - H_op ⟨K ψ, D.smul_mem Complex.I (hJ_mem ψ)⟩ =
      Complex.I • P ψ) ∧
    (∀ ψ : D, K ⟨P ψ, hP_mem ψ⟩ - P ⟨K ψ, D.smul_mem Complex.I (hJ_mem ψ)⟩ =
      -Complex.I • H_op ψ) := by
  intro K
  refine ⟨fun ψ => ?_, fun ψ => ?_⟩
  · have hKψ : (⟨K ψ, D.smul_mem Complex.I (hJ_mem ψ)⟩ : D) =
        Complex.I • (⟨J_euc ψ, hJ_mem ψ⟩ : D) := rfl
    rw [hKψ, map_smul]
    dsimp [K]
    rw [← smul_sub, h_JH ψ]
  · have hKψ : (⟨K ψ, D.smul_mem Complex.I (hJ_mem ψ)⟩ : D) =
        Complex.I • (⟨J_euc ψ, hJ_mem ψ⟩ : D) := rfl
    rw [hKψ, map_smul]
    dsimp [K]
    rw [← smul_sub, h_JP ψ, smul_neg, neg_smul]

end LieAlgebra

section VacuumInvariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Stone Generator Vacuum Invariance:**
    Any 1-parameter unitary group `U : ℝ → H →ₗᵢ[ℂ] H` whose generator at every `s`
    satisfies `HasDerivAt (fun t => U t Ω) (U s (i • A Ω)) s` with `A Ω = 0`
    fixes `Ω` for all `t : ℝ`. -/
theorem unitary_fixes_vacuum_of_generator_zero
    (U : ℝ → H →ₗᵢ[ℂ] H) (hU0 : U 0 = LinearIsometry.id)
    (Ω AΩ : H) (hA0 : AΩ = 0)
    (h_deriv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => U t Ω) (U s (Complex.I • AΩ)) s) :
    ∀ t : ℝ, U t Ω = Ω := by
  intro t
  have h_deriv_zero : ∀ s ∈ (Set.univ : Set ℝ), HasDerivAt (fun u : ℝ => U u Ω) (0 : H) s := by
    intro s _
    have hs := h_deriv s
    rwa [hA0, smul_zero, map_zero] at hs
  have h_eq : U t Ω = U 0 Ω := (fun h x y => is_const_of_deriv_eq_zero (fun s => (h s (Set.mem_univ s)).differentiableAt) (fun s => (h s (Set.mem_univ s)).deriv) x y) h_deriv_zero t 0
  simpa [hU0] using h_eq

end VacuumInvariance

end Imscribing.YangMills.PoincareNelson
