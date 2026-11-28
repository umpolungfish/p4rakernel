import Imscribing.YangMills.SpatialISO3UnitariesOnOS
import Imscribing.YangMills.SemigroupToUnitaryGroupCFC
import Imscribing.YangMills.ConcreteMinimalClayReduction
import Imscribing.YangMills.OSCanonicalSemigroupContinuity
import Imscribing.YangMills.IBPBoundaryToWightman
import Imscribing.YangMills.DimensionalTransmutationAndBoundary
import Imscribing.YangMills.LorentzBoostAndMinkowskiFields

/-!
# Master Osterwalder–Schrader → Clay Wightman Discharge

Given `B : ConcreteBalabanTarget N hN` and the strictly irreducible analytic-continuation
core `OSAnalyticCore B`, synthesizes `ConcreteOSTarget B` and proves
`HasYangMillsUVScaling N Q ∧ HasStrictMassGap Q B.C.cluster_rate` (`0 sorry`).
The Euclidean semigroup `T` and all six semigroup properties (`T 0 = 1`, semigroup law,
self-adjointness, contractivity, strong right continuity at `0`, and vacuum invariance)
are proved unconditionally from `B` via `concreteBalaban_osSemigroup_exists`.
-/

namespace Imscribing.YangMills.OSMasterDischarge

set_option maxSynthPendingDepth 1
set_option maxHeartbeats 800000

open scoped InnerProductSpace Topology
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.OSCompletion
open Imscribing.YangMills.OSBorchers
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.BorchersSchwinger
open Imscribing.YangMills.ConcreteTensorSchwartz
open Imscribing.YangMills.SpatialISO3Unitaries
open Imscribing.YangMills.SemigroupCFC
open Imscribing.YangMills.OSIBPBoundary
open Imscribing.YangMills.DimTransAndBoundary
open Imscribing.YangMills.ConcreteMinimalReduction
open Imscribing.YangMills.OSCanonicalSemigroupContinuity

/-- Strictly irreducible analytic-continuation core on top of `B : ConcreteBalabanTarget N hN`.
    All Euclidean semigroup properties (`T`, `T 0 = 1`, semigroup law, self-adjointness,
    contractivity, strong right continuity at `0`, vacuum invariance), time-translation
    unitaries `U₀`, spatial-translation unitaries `U_space`, Hamiltonian `H_op`, vacuum
    uniqueness, spectral gap, `M`-step IBP boundary temperedness, and operator
    microcausality are derived automatically. -/
structure OSAnalyticCore {N : ℕ} {hN : 2 ≤ N} (B : ConcreteBalabanTarget N hN) where
  h_space_inv : ∀ (v : Fin 3 → ℝ) (F G : BorchersPos),
    concreteBorchersForm B.C (borchersSpaceShift v F) (borchersSpaceShift v G) =
      concreteBorchersForm B.C F G
  analytic_core :
    let pre := buildBorchersPreData B.C concreteReflectTensorData
      B.h_herm B.h_rp B.h_symm B.h_cluster
    let core := quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core.toCore
    let H := UniformSpace.Completion (BorchersPos ⧸ nullSubmodule pre)
    let Ω : H := ((Submodule.Quotient.mk borchersVac : BorchersPos ⧸ nullSubmodule pre) : H)
    ∃ (U_lor : Lorentz4 → H →ₗᵢ[ℂ] H)
      (fieldDomain : Submodule ℂ H)
      (field : TestFn4 → ↥fieldDomain →ₗ[ℂ] H),
      (∀ Λ : Lorentz4, Λ.mat = 1 → U_lor Λ = LinearIsometry.id) ∧
      (∀ Λ : Lorentz4, U_lor Λ Ω = Ω) ∧
      Dense (fieldDomain : Set H) ∧
      Ω ∈ fieldDomain ∧
      (∀ f (ψ : ↥fieldDomain), field f ψ ∈ fieldDomain) ∧
      (∀ f g : TestFn4, SpacelikeDisjoint f g →
        ∀ (ψ₁ ψ₂ : ↥fieldDomain) (hfg : field g ψ₂ ∈ fieldDomain) (hgf : field f ψ₂ ∈ fieldDomain),
          ⟪(ψ₁ : H), field f ⟨field g ψ₂, hfg⟩⟫_ℂ =
          ⟪(ψ₁ : H), field g ⟨field f ψ₂, hgf⟩⟫_ℂ) ∧
      (∃ (f₀ g₀ : TestFn4)
         (W_reg : ℝ → TestFn4 →ₗ[ℂ] ℂ) (D_ibp : TestFn4 →ₗ[ℂ] TestFn4)
         (M : ℕ) (p : TestFn4 → ℝ),
         (∀ f, 0 ≤ p f) ∧
         (∀ f, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
           HasDerivAt (fun ε => W_reg ε f) (W_reg t (D_ibp f)) t) ∧
         (∀ f, ∀ a : ℝ, 0 < a → a ≤ 1 →
           ContinuousOn (fun t => W_reg t f) (Set.Icc a 1)) ∧
         (∀ g : TestFn4, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
           ‖W_reg t g‖ ≤ p g * t ^ (-(M : ℝ))) ∧
         Disjoint (Function.support f₀) (Function.support g₀) ∧
         ∀ hΩ hg,
           Filter.Tendsto (fun t => W_reg t g₀) (𝓝[>] 0)
             (𝓝 ⟪Ω, field f₀ ⟨field g₀ ⟨Ω, hΩ⟩, hg⟩⟫_ℂ) ∧
           ⟪Ω, field f₀ ⟨field g₀ ⟨Ω, hΩ⟩, hg⟩⟫_ℂ ≠ 0)

/-- **Master OS Discharge Theorem:**
    Synthesizes `ConcreteOSTarget B` and proves `HasYangMillsUVScaling N Q ∧ HasStrictMassGap Q Δ`
    directly from `B : ConcreteBalabanTarget N hN` and `C_core : OSAnalyticCore B`. -/
theorem os_continuation_master_discharge
    (N : ℕ) (hN : 2 ≤ N)
    (B : ConcreteBalabanTarget N hN)
    (C_core : OSAnalyticCore B) :
    ∃ (Q : WightmanQFT4D),
      HasYangMillsUVScaling N Q ∧ HasStrictMassGap Q B.C.cluster_rate := by
  let pre := buildBorchersPreData B.C concreteReflectTensorData
    B.h_herm B.h_rp B.h_symm B.h_cluster
  let core := quotInnerCore pre
  letI : NormedAddCommGroup (BorchersPos ⧸ nullSubmodule pre) := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (BorchersPos ⧸ nullSubmodule pre) := InnerProductSpace.ofCore core.toCore
  obtain ⟨T, hT_zero, hT_add, hT_symm, hT_contr, hT_cont, hT_vac⟩ :=
    concreteBalaban_osSemigroup_exists B
  obtain ⟨U_lor, fieldDomain, field, hU_lor_one, hU_lor_vac, h_dense, hΩ_dom,
    h_maps, h_weak_loc, f₀, g₀, W_reg, D_ibp, M, p, hp_nn, h_deriv, h_cont,
    h_blowup, h_disj, h_2pt⟩ := C_core.analytic_core
  let P_pack := poincare_from_semigroup_and_iso3 pre C_core.h_space_inv
    borchersSpaceShift_vac T hT_zero hT_add hT_symm hT_contr hT_cont hT_vac
    U_lor hU_lor_one hU_lor_vac
  let U := P_pack.1
  have hU_spec := P_pack.2
  obtain ⟨C_ibp, W₀, hC_nn, h_W₀_tend, h_W₀_bd⟩ :=
    os_ibp_polynomial_to_boundary W_reg D_ibp h_deriv h_cont M p hp_nn h_blowup
  let C_target : ConcreteOSTarget B :=
    { poincare_and_weak_fields := by
        refine ⟨U, fieldDomain, field, hU_spec.1, hU_spec.2.1, hU_spec.2.2,
          h_dense, hΩ_dom, h_maps, h_weak_loc, ?_⟩
        refine ⟨f₀, g₀, (fun _ => W₀), (fun _ => 0), (fun f => ‖W₀ f‖), 1, 0,
          fun f => norm_nonneg _, zero_le_one, le_rfl,
          fun f => by simpa using le_rfl,
          fun f ε _ => hasDerivAt_const ε (W₀ f),
          fun f ε _ => by simp,
          h_disj, fun hΩ hg => ?_⟩
        have h_lim1 := h_W₀_tend g₀
        have h_lim2 := (h_2pt hΩ hg).1
        have h_eq : W₀ g₀ = ⟪_, field f₀ ⟨field g₀ ⟨_, hΩ⟩, hg⟩⟫_ℂ :=
          tendsto_nhds_unique h_lim1 h_lim2
        refine ⟨by simpa [h_eq] using tendsto_const_nhds, (h_2pt hΩ hg).2⟩ }
  exact clay_yang_mills_from_concrete_targets N hN B C_target

end Imscribing.YangMills.OSMasterDischarge

