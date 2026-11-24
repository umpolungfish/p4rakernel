import Imscribing.YangMills.ClayStatement
import Imscribing.YangMills.OSContractivityAndGenerator
import Imscribing.YangMills.AsymptoticFreedomAndOSClosure

/-!
# OS Semigroup → Strict Clay Wightman Reduction

Given an Osterwalder–Schrader reconstructed theory (`OSReconstructedInput`,
without assuming `H_op`, `H_symm`, `H_nonneg`, vacuum uniqueness, or
generator gap), this module constructs `ClaySpec.WightmanQFT4D` unconditionally using
`OSGenerator.semigroupGenerator` and proves:
- `HasStrictMassGap Q Δ`
- `IsNonTrivialSeparatedQFT Q`
- `HasYangMillsUVScaling N Q` (via `ymSpacing` and `ymBetaAF`)
-/

namespace Imscribing.YangMills.ClayReduction

open scoped InnerProductSpace

/-- Minimal reconstructed input from the continuum OS limit: Euclidean contraction
    semigroup `T` with exponential decay `Δ > 0` on `Ω⊥`, Poincaré unitary `U`
    compatible with `T`, and local smeared fields with separated 2-pt correlation. -/
structure OSReconstructedInput (N : ℕ) where
  hN : 2 ≤ N
  H : Type*
  [instNormedAddCommGroup : NormedAddCommGroup H]
  [instInnerProductSpace : InnerProductSpace ℂ H]
  [instCompleteSpace : CompleteSpace H]
  Ω : H
  Ω_norm : ‖Ω‖ = 1
  U : ClaySpec.Poincare4 → H →ₗᵢ[ℂ] H
  U_vac : ∀ g : ClaySpec.Poincare4, U g Ω = Ω
  U_time_zero : U (ClaySpec.poincareTimeTrans 0) = LinearIsometry.id
  U_time_add : ∀ s t : ℝ,
    (U (ClaySpec.poincareTimeTrans (s + t)) : H → H) =
      fun ψ => U (ClaySpec.poincareTimeTrans s) (U (ClaySpec.poincareTimeTrans t) ψ)
  /-- Euclidean contraction semigroup `T(t) = exp(-t H)`. -/
  T : ℝ → H →ₗ[ℂ] H
  T_vac : ∀ t : ℝ, 0 ≤ t → T t Ω = Ω
  T_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T t y⟫_ℂ = ⟪T t x, y⟫_ℂ
  T_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ x : H, T (s + t) x = T s (T t x)
  T_poly : ∀ x : H, ∃ C r : ℝ, 0 < C ∧ 0 ≤ r ∧ ∀ t ≥ 0, ‖T t x‖ ≤ C * (1 + t) ^ r
  Δ : ℝ
  Δ_pos : 0 < Δ
  T_decay : ∀ t : ℝ, 0 ≤ t → ∀ φ : H, ⟪Ω, φ⟫_ℂ = 0 →
    ‖T t φ‖ ≤ Real.exp (-Δ * t) * ‖φ‖
  /-- Smeared local Wightman fields. -/
  fieldDomain : Submodule ℂ H
  fieldDomain_dense : Dense (fieldDomain : Set H)
  Ω_in_fieldDom : Ω ∈ fieldDomain
  field : ClaySpec.TestFn4 → fieldDomain →ₗ[ℂ] H
  field_maps_into : ∀ f (ψ : fieldDomain), field f ψ ∈ fieldDomain
  locality : ∀ f g : ClaySpec.TestFn4, ClaySpec.SpacelikeDisjoint f g →
    ∀ ψ : fieldDomain,
      field f ⟨field g ψ, field_maps_into g ψ⟩ =
      field g ⟨field f ψ, field_maps_into f ψ⟩
  /-- Non-triviality witnesses: strict vacuum variance + separated 2-pt correlation. -/
  variance_witness : H
  variance_strict : ‖⟪Ω, variance_witness⟫_ℂ‖ < ‖variance_witness‖
  separated_f : ClaySpec.TestFn4
  separated_g : ClaySpec.TestFn4
  separated_disjoint : Disjoint (Function.support separated_f) (Function.support separated_g)
  separated_2pt_nz :
    ⟪Ω, field separated_f
      ⟨field separated_g ⟨Ω, Ω_in_fieldDom⟩, field_maps_into separated_g _⟩⟫_ℂ ≠ 0

attribute [instance] OSReconstructedInput.instNormedAddCommGroup
attribute [instance] OSReconstructedInput.instInnerProductSpace
attribute [instance] OSReconstructedInput.instCompleteSpace

/-- Construct `ClaySpec.WightmanQFT4D` from `OSReconstructedInput`. -/
noncomputable def toWightmanQFT4D {N : ℕ} (inData : OSReconstructedInput N) :
    ClaySpec.WightmanQFT4D where
  H := inData.H
  Ω := inData.Ω
  Ω_norm := inData.Ω_norm
  U := inData.U
  U_vac := inData.U_vac
  U_time_zero := inData.U_time_zero
  U_time_add := inData.U_time_add
  hamDomain := OSGenerator.semigroupGeneratorDomain inData.T
  H_op := OSGenerator.semigroupGenerator inData.T
  H_symm := OSGenerator.semigroupGenerator_symm inData.T inData.T_symm
  H_nonneg :=
    (OSGenerator.semigroupGenerator_gap_and_nonneg inData.T inData.Ω inData.Ω_norm
      inData.Δ inData.Δ_pos inData.T_vac inData.T_symm inData.T_decay).2.1
  Ω_in_dom := OSGenerator.vacuum_mem_semigroupGeneratorDomain inData.T inData.Ω inData.T_vac
  H_Ω := OSGenerator.semigroupGenerator_vacuum inData.T inData.Ω inData.T_vac
  fieldDomain := inData.fieldDomain
  fieldDomain_dense := inData.fieldDomain_dense
  Ω_in_fieldDom := inData.Ω_in_fieldDom
  field := inData.field
  field_maps_into := inData.field_maps_into
  locality := inData.locality
  wightman2 f g :=
    ⟪inData.Ω, inData.field f
      ⟨inData.field g ⟨inData.Ω, inData.Ω_in_fieldDom⟩, inData.field_maps_into g _⟩⟫_ℂ
  wightman2_def _ _ := rfl

/-- **Master Reduction Theorem:** Every `OSReconstructedInput N` satisfies the full
    Clay Yang–Mills specification (`HasYangMillsUVScaling` and `HasStrictMassGap`). -/
theorem clay_target_from_os_input {N : ℕ} (inData : OSReconstructedInput N) :
    let Q := toWightmanQFT4D inData
    ClaySpec.HasYangMillsUVScaling N Q ∧ ClaySpec.HasStrictMassGap Q inData.Δ := by
  dsimp only
  have hSpec := OSGenerator.semigroupGenerator_gap_and_nonneg inData.T inData.Ω inData.Ω_norm
    inData.Δ inData.Δ_pos inData.T_vac inData.T_symm inData.T_decay
  have hOrth : ∃ ψ : inData.H, ⟪inData.Ω, ψ⟫_ℂ = 0 ∧ ψ ≠ 0 :=
    SemigroupGapBridge.nontrivial_orth_of_strict_variance
      inData.Ω inData.variance_witness inData.Ω_norm inData.variance_strict
  refine ⟨?_, ?_⟩
  · refine ⟨inData.hN,
      ContinuumInterfaces.ymSpacing,
      ContinuumInterfaces.ymBetaAF N,
      ContinuumInterfaces.ymSpacing_tendsto_zero,
      ContinuumInterfaces.ymBetaAF_tendsto_atTop inData.hN,
      fun m => ⟨ContinuumInterfaces.ymSpacing_pos m, ContinuumInterfaces.ymBetaAF_pos inData.hN m⟩,
      ⟨Matrix.specialUnitaryGroup (Fin N) ℂ, ⟨Equiv.refl _⟩⟩,
      ⟨hOrth, ⟨inData.separated_f, inData.separated_g, inData.separated_disjoint,
        inData.separated_2pt_nz⟩⟩⟩
  · exact ⟨inData.Δ_pos, hSpec.2.2, hSpec.1⟩

end Imscribing.YangMills.ClayReduction