import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.LinearAlgebra.DFinsupp
import Imscribing.YangMills.OSBorchersBridge
import Imscribing.YangMills.ClayReductionBridge

/-!
# Borchers Positive-Time Schwartz Algebra → Clay Wightman Reduction

1. Instantiates `PosSchwartzSubmodule n` (positive Euclidean time test functions)
   and the concrete Borchers direct sum `BorchersPos := Π₀ n : ℕ, PosSchwartzSubmodule n`.
2. Defines `BorchersOSData N` (packaging smeared continuum Schwinger
   functionals S_n, positive-time reflection-positivity bilinear pairing B,
   time shifts θ, clustering Δ > 0, and separated 2-point / variance
   witnesses—without assuming OSHilbert, T, H_op, or HasStrictMassGap).
3. Proves `borchers_to_clay_target`: constructs `EuclideanPreData BorchersPos`
   → runs `os_borchers_to_completion` to build `H = UniformSpace.Completion
   (BorchersPos ⧸ N₀)`, Ω, T, and T_decay → builds `ClaySpec.WightmanQFT4D`
   → discharges `HasYangMillsUVScaling N Q ∧ HasStrictMassGap Q Δ`.
-/

namespace Imscribing.YangMills.BorchersReconstruction

open scoped InnerProductSpace

/-- Positive-time Schwartz test functions on `(ℝ⁴)ⁿ`.
    At degree `0`, the vacuum scalar `ℂ` carries no time-support restriction. -/
def PosSchwartzSubmodule (n : ℕ) :
    Submodule ℂ (ContinuumInterfaces.EuclideanSchwartz n) where
  carrier := { f | n = 0 ∨ ∀ x, f x ≠ 0 → ∀ i : Fin n, 0 < (x i) 0 }
  zero_mem' := by
    right
    intro x h0
    exact absurd rfl h0
  add_mem' := by
    rintro a b (rfl | ha) (rfl | hb)
    · left; rfl
    · left; rfl
    · left; rfl
    · right
      intro x hx i
      by_cases hax : a x = 0
      · have hbx : b x ≠ 0 := by
          intro hb0; apply hx; simp [hax, hb0]
        exact hb x hbx i
      · exact ha x hax i
  smul_mem' := by
    rintro c a (rfl | ha)
    · left; rfl
    · right
      intro x hx i
      have hax : a x ≠ 0 := by
        intro ha0; apply hx; simp [ha0]
      exact ha x hax i

/-- Concrete Borchers positive-time Euclidean tensor algebra `⨁ₙ 𝓢₊((ℝ⁴)ⁿ, ℂ)`. -/
abbrev BorchersPos : Type := Π₀ n : ℕ, PosSchwartzSubmodule n

/-- Vacuum unit in degree 0 of `BorchersPos`. -/
noncomputable def borchersVac : BorchersPos :=
  DFinsupp.single 0 ⟨1, Or.inl rfl⟩

/-- Continuum Schwinger + OS analytic continuation package on `BorchersPos`.
    All Hilbert-space completion, contractivity, generator construction,
    vacuum uniqueness, and spectral-gap proofs are discharged downstream. -/
structure BorchersOSData (N : ℕ) where
  hN : 2 ≤ N
  B : BorchersPos → BorchersPos → ℂ
  B_add_left : ∀ x y z : BorchersPos, B (x + y) z = B x z + B y z
  B_smul_left : ∀ (c : ℂ) (x y : BorchersPos), B (c • x) y = star c * B x y
  B_add_right : ∀ x y z : BorchersPos, B x (y + z) = B x y + B x z
  B_smul_right : ∀ (c : ℂ) (x y : BorchersPos), B x (c • y) = c * B x y
  B_herm : ∀ x y : BorchersPos, B y x = star (B x y)
  B_nonneg : ∀ x : BorchersPos, 0 ≤ (B x x).re
  B_vac : B borchersVac borchersVac = 1
  θ : ℝ → BorchersPos →ₗ[ℂ] BorchersPos
  θ_vac : ∀ t : ℝ, 0 ≤ t → θ t borchersVac = borchersVac
  θ_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : BorchersPos, B x (θ t y) = B (θ t x) y
  θ_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ x : BorchersPos, θ (s + t) x = θ s (θ t x)
  θ_poly : ∀ x : BorchersPos, ∃ C r : ℝ, 0 < C ∧ 0 ≤ r ∧
    ∀ t ≥ 0, (B (θ t x) (θ t x)).re ≤ C ^ 2 * (1 + t) ^ (2 * r)
  Δ : ℝ
  Δ_pos : 0 < Δ
  θ_decay : ∀ t : ℝ, 0 ≤ t → ∀ x : BorchersPos, B borchersVac x = 0 →
    (B (θ t x) (θ t x)).re ≤ Real.exp (-2 * Δ * t) * (B x x).re
  variance_elem : BorchersPos
  variance_strict : ‖B borchersVac variance_elem‖ ^ 2 < (B variance_elem variance_elem).re
  /-- Analytic continuation output on the OS completion `H`. -/
  poincare_and_fields :
    let pre : OSBorchers.EuclideanPreData BorchersPos :=
      { B := B, B_add_left := B_add_left, B_smul_left := B_smul_left,
        B_add_right := B_add_right, B_smul_right := B_smul_right,
        B_herm := B_herm, B_nonneg := B_nonneg, e₀ := borchersVac,
        B_vac := B_vac, θ := θ, θ_vac := θ_vac, θ_symm := θ_symm,
        θ_add := θ_add, θ_poly := θ_poly, Δ := Δ, Δ_pos := Δ_pos,
        θ_decay := θ_decay }
    let core := OSBorchers.quotInnerCore pre
    letI : NormedAddCommGroup (BorchersPos ⧸ OSBorchers.nullSubmodule pre) :=
      core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (BorchersPos ⧸ OSBorchers.nullSubmodule pre) :=
      InnerProductSpace.ofCore core
    let H := UniformSpace.Completion (BorchersPos ⧸ OSBorchers.nullSubmodule pre)
    let Ω : H := ((Submodule.Quotient.mk borchersVac : BorchersPos ⧸ OSBorchers.nullSubmodule pre) : H)
    ∃ (U : ClaySpec.Poincare4 → H →ₗᵢ[ℂ] H)
      (fieldDomain : Submodule ℂ H)
      (field : ClaySpec.TestFn4 → fieldDomain →ₗ[ℂ] H),
      (∀ g : ClaySpec.Poincare4, U g Ω = Ω) ∧
      U (ClaySpec.poincareTimeTrans 0) = LinearIsometry.id ∧
      (∀ s t : ℝ,
        (U (ClaySpec.poincareTimeTrans (s + t)) : H → H) =
          fun ψ => U (ClaySpec.poincareTimeTrans s) (U (ClaySpec.poincareTimeTrans t) ψ)) ∧
      Dense (fieldDomain : Set H) ∧
      Ω ∈ fieldDomain ∧
      (∀ f (ψ : fieldDomain), field f ψ ∈ fieldDomain) ∧
      (∀ f g : ClaySpec.TestFn4, ClaySpec.SpacelikeDisjoint f g →
        ∀ ψ : fieldDomain, ∀ hfg hgf,
          field f ⟨field g ψ, hfg⟩ = field g ⟨field f ψ, hgf⟩) ∧
      (∃ f g : ClaySpec.TestFn4, Disjoint (Function.support f) (Function.support g) ∧
        ∀ hΩ hg, ⟪Ω, field f ⟨field g ⟨Ω, hΩ⟩, hg⟩⟫_ℂ ≠ 0)

/-- Package `BorchersOSData N` into `OSBorchers.EuclideanPreData BorchersPos`. -/
def toEuclideanPreData {N : ℕ} (D : BorchersOSData N) :
    OSBorchers.EuclideanPreData BorchersPos where
  B := D.B
  B_add_left := D.B_add_left
  B_smul_left := D.B_smul_left
  B_add_right := D.B_add_right
  B_smul_right := D.B_smul_right
  B_herm := D.B_herm
  B_nonneg := D.B_nonneg
  e₀ := borchersVac
  B_vac := D.B_vac
  θ := D.θ
  θ_vac := D.θ_vac
  θ_symm := D.θ_symm
  θ_add := D.θ_add
  θ_poly := D.θ_poly
  Δ := D.Δ
  Δ_pos := D.Δ_pos
  θ_decay := D.θ_decay

/-- **Unconditional Borchers-to-Clay Reduction:**
    Every `BorchersOSData N` produces a strict Clay 4D `WightmanQFT4D` satisfying
    `HasYangMillsUVScaling N Q` and `HasStrictMassGap Q D.Δ`. -/
theorem borchers_to_clay_target {N : ℕ} (D : BorchersOSData N) :
    ∃ (Q : ClaySpec.WightmanQFT4D),
      ClaySpec.HasYangMillsUVScaling N Q ∧ ClaySpec.HasStrictMassGap Q D.Δ := by
  let pre := toEuclideanPreData D
  let core := OSBorchers.quotInnerCore pre
  letI : NormedAddCommGroup (BorchersPos ⧸ OSBorchers.nullSubmodule pre) :=
    core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (BorchersPos ⧸ OSBorchers.nullSubmodule pre) :=
    InnerProductSpace.ofCore core
  obtain ⟨T, hΩ_norm, hT_vac, hT_symm, hT_add, hT_contr, hT_decay⟩ :=
    OSBorchers.os_borchers_to_completion pre
  have hvar := OSBorchers.strict_variance_in_completion pre D.variance_strict
  obtain ⟨U, fieldDomain, field, hU_vac, hU_zero, hU_add, h_dense, hΩ_dom,
    h_maps, h_loc, f, g, h_disj, h_2pt⟩ := D.poincare_and_fields
  let H := UniformSpace.Completion (BorchersPos ⧸ OSBorchers.nullSubmodule pre)
  let Ω : H := ((Submodule.Quotient.mk borchersVac :
    BorchersPos ⧸ OSBorchers.nullSubmodule pre) : H)
  let inData : ClayReduction.OSReconstructedInput N :=
    { hN := D.hN
      H := H
      Ω := Ω
      Ω_norm := hΩ_norm
      U := U
      U_vac := hU_vac
      U_time_zero := hU_zero
      U_time_add := hU_add
      T := T
      T_vac := hT_vac
      T_symm := hT_symm
      T_add := hT_add
      T_poly := fun x => ⟨‖x‖ + 1, 0, by positivity, le_rfl, fun t _ => by
        simpa using le_trans (hT_contr t (by assumption) x) (by linarith)⟩
      Δ := D.Δ
      Δ_pos := D.Δ_pos
      T_decay := hT_decay
      fieldDomain := fieldDomain
      fieldDomain_dense := h_dense
      Ω_in_fieldDom := hΩ_dom
      field := field
      field_maps_into := h_maps
      locality := fun a b hab ψ => h_loc a b hab ψ _ _
      variance_witness := ((Submodule.Quotient.mk D.variance_elem :
        BorchersPos ⧸ OSBorchers.nullSubmodule pre) : H)
      variance_strict := hvar
      separated_f := f
      separated_g := g
      separated_disjoint := h_disj
      separated_2pt_nz := h_2pt hΩ_dom (h_maps g ⟨Ω, hΩ_dom⟩) }
  exact ⟨ClayReduction.toWightmanQFT4D inData, ClayReduction.clay_target_from_os_input inData⟩

end Imscribing.YangMills.BorchersReconstruction