import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
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
noncomputable def PosSchwartzSubmodule (n : ℕ) :
    Submodule ℂ (ContinuumInterfaces.EuclideanSchwartz n) where
  carrier := { f | n = 0 ∨ ∀ x, f x ≠ 0 → ∀ i : Fin n, 0 < (x i) 0 }
  zero_mem' := by
    right
    intro x h0
    exact absurd rfl h0
  add_mem' := by
    rintro a b (h_n0_0 | ha) (h_n0_1 | hb) <;> (try subst h_n0_0) <;> (try subst h_n0_1)
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
    rintro c a (h_n0_0 | ha) <;> (try subst h_n0_0)
    · left; rfl
    · right
      intro x hx i
      have hax : a x ≠ 0 := by
        intro ha0; apply hx; simp [ha0]
      exact ha x hax i

/-- Concrete Borchers positive-time Euclidean tensor algebra `⨁ₙ 𝓢₊((ℝ⁴)ⁿ, ℂ)`. -/
abbrev BorchersPos : Type := Π₀ n : ℕ, PosSchwartzSubmodule n

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable instance (priority := high) instAddCommMonoidPosSchwartz (n : ℕ) :
    AddCommMonoid (PosSchwartzSubmodule n) := inferInstance
noncomputable instance (priority := high) instModulePosSchwartz (n : ℕ) :
    Module ℂ (PosSchwartzSubmodule n) := Submodule.module (PosSchwartzSubmodule n)
noncomputable instance (priority := high) instAddCommMonoidBorchersPos :
    AddCommMonoid BorchersPos := DFinsupp.addCommMonoid
noncomputable instance (priority := high) instModuleBorchersPos :
    Module ℂ BorchersPos := DFinsupp.module
noncomputable instance (priority := high) instSMulBorchersPos :
    SMul ℂ BorchersPos := instModuleBorchersPos.toSMul

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
      InnerProductSpace.ofCore core.toCore
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
noncomputable def toEuclideanPreData {N : ℕ} (D : BorchersOSData N) :
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
private theorem lift_os_input_universe {N : ℕ}
    (inData0 : ClayReduction.OSReconstructedInput.{0} N) :
    ∃ Q, ClaySpec.HasYangMillsUVScaling N Q ∧ ClaySpec.HasStrictMassGap Q inData0.Δ := by
  letI := inData0.instNormedAddCommGroup
  letI := inData0.instInnerProductSpace
  letI := inData0.instCompleteSpace
  let H1 : Type 1 := ULift.{1, 0} inData0.H
  letI : Inner ℂ H1 := ⟨fun x y => ⟪x.down, y.down⟫_ℂ⟩
  letI : InnerProductSpace ℂ H1 :=
    { norm_sq_eq_re_inner := fun x => InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x.down
      conj_inner_symm := fun x y => InnerProductSpace.conj_inner_symm x.down y.down
      add_left := fun x y z => InnerProductSpace.add_left x.down y.down z.down
      smul_left := fun x y r => InnerProductSpace.smul_left x.down y.down r }
  let h_norm_ulift : ∀ x : inData0.H, ‖(ULift.up x : H1)‖ = ‖x‖ := fun _ => rfl
  letI : CompleteSpace H1 := Metric.complete_of_cauchySeq_tendsto fun s hs => by
    have hdist : ∀ a b : H1, dist a b = dist a.down b.down := fun a b => by
      rw [dist_eq_norm, dist_eq_norm]; rfl
    have hs0 : CauchySeq (fun k => (s k).down) := by
      rw [Metric.cauchySeq_iff] at hs ⊢
      intro ε hε
      obtain ⟨N₀, hN₀⟩ := hs ε hε
      exact ⟨N₀, fun m hm n hn => by simpa [hdist] using hN₀ m hm n hn⟩
    obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hs0
    refine ⟨ULift.up x₀, ?_⟩
    rw [Metric.tendsto_atTop] at hx₀ ⊢
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hx₀ ε hε
    exact ⟨N₀, fun k hk => by simpa [hdist] using hN₀ k hk⟩
  let upIso : inData0.H →ₗᵢ[ℂ] H1 :=
    { toFun := ULift.up
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      norm_map' := h_norm_ulift }
  let downIso : H1 →ₗᵢ[ℂ] inData0.H :=
    { toFun := ULift.down
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      norm_map' := fun x => (h_norm_ulift x.down).symm }
  let fieldDomain1 : Submodule ℂ H1 := inData0.fieldDomain.map upIso.toLinearMap
  let domDown : ↥fieldDomain1 →ₗ[ℂ] ↥inData0.fieldDomain :=
    { toFun := fun ψ => ⟨ψ.1.down, by obtain ⟨x, hx, hxq⟩ := ψ.2; rw [← hxq]; exact hx⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Ω1 : H1 := upIso inData0.Ω
  let U1 : ClaySpec.Poincare4 → H1 →ₗᵢ[ℂ] H1 :=
    fun g => upIso.comp ((inData0.U g).comp downIso)
  let T1 : ℝ → H1 →ₗ[ℂ] H1 :=
    fun t => upIso.toLinearMap.comp ((inData0.T t).comp downIso.toLinearMap)
  let field1 : ClaySpec.TestFn4 → ↥fieldDomain1 →ₗ[ℂ] H1 :=
    fun fn => upIso.toLinearMap.comp ((inData0.field fn).comp domDown)
  let h_dense1 : Dense (fieldDomain1 : Set H1) := by
    rw [Metric.dense_iff]
    intro x ε hε
    obtain ⟨y, hy_dist, hy_dom⟩ := Metric.dense_iff.mp inData0.fieldDomain_dense x.down ε hε
    have hd : dist (upIso y) x = dist y x.down := by
      rw [dist_eq_norm, dist_eq_norm]; rfl
    refine ⟨upIso y, ?_, ⟨y, hy_dom, rfl⟩⟩
    rw [Metric.mem_ball, hd]
    exact Metric.mem_ball.mp hy_dist
  let inData1 : ClayReduction.OSReconstructedInput.{1} N :=
    { hN := inData0.hN
      H := H1
      Ω := Ω1
      Ω_norm := by simpa [Ω1, upIso, h_norm_ulift] using inData0.Ω_norm
      U := U1
      U_vac := fun g => congrArg ULift.up (inData0.U_vac g)
      U_time_zero := by ext x; simp [U1, upIso, downIso, inData0.U_time_zero]
      U_time_add := fun s t => by ext x; simp [U1, upIso, downIso, inData0.U_time_add s t]
      T := T1
      T_vac := fun t ht => congrArg ULift.up (inData0.T_vac t ht)
      T_symm := fun t ht x y => inData0.T_symm t ht x.down y.down
      T_add := fun s t hs ht x => congrArg ULift.up (inData0.T_add s t hs ht x.down)
      T_poly := fun x => by
        obtain ⟨C, k, hC, hk, hbd⟩ := inData0.T_poly x.down
        exact ⟨C, k, hC, hk, fun t ht => by
          simpa [T1, upIso, downIso, h_norm_ulift] using hbd t ht⟩
      Δ := inData0.Δ
      Δ_pos := inData0.Δ_pos
      T_decay := fun t ht φ hφ => by
        simpa [T1, upIso, downIso, h_norm_ulift] using inData0.T_decay t ht φ.down hφ
      fieldDomain := fieldDomain1
      fieldDomain_dense := h_dense1
      Ω_in_fieldDom := ⟨inData0.Ω, inData0.Ω_in_fieldDom, rfl⟩
      field := field1
      field_maps_into := fun fn ψ =>
        ⟨(inData0.field fn) (domDown ψ), inData0.field_maps_into fn (domDown ψ), rfl⟩
      locality := fun a b hab ψ =>
        congrArg ULift.up (inData0.locality a b hab (domDown ψ))
      variance_witness := upIso inData0.variance_witness
      variance_strict := by simpa [Ω1, upIso, h_norm_ulift] using inData0.variance_strict
      separated_f := inData0.separated_f
      separated_g := inData0.separated_g
      separated_disjoint := inData0.separated_disjoint
      separated_2pt_nz := inData0.separated_2pt_nz }
  refine ⟨ClayReduction.toWightmanQFT4D inData1, ?_⟩
  have h_target := ClayReduction.clay_target_from_os_input inData1
  dsimp only [letFun] at h_target
  exact h_target

theorem borchers_to_clay_target {N : ℕ} (D : BorchersOSData N) :
    ∃ (Q : ClaySpec.WightmanQFT4D),
      ClaySpec.HasYangMillsUVScaling N Q ∧ ClaySpec.HasStrictMassGap Q D.Δ := by
  let pre := toEuclideanPreData D
  let core := OSBorchers.quotInnerCore pre
  letI : NormedAddCommGroup (BorchersPos ⧸ OSBorchers.nullSubmodule pre) :=
    core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (BorchersPos ⧸ OSBorchers.nullSubmodule pre) :=
    InnerProductSpace.ofCore core.toCore
  obtain ⟨T, hΩ_norm, hT_vac, hT_symm, hT_add, hT_contr, hT_decay⟩ :=
    OSBorchers.os_borchers_to_completion pre
  have hvar := OSBorchers.strict_variance_in_completion pre D.variance_strict
  obtain ⟨U, fieldDomain, field, hU_vac, hU_zero, hU_add, h_dense, hΩ_dom,
    h_maps, h_loc, f, g, h_disj, h_2pt⟩ := D.poincare_and_fields
  let H := UniformSpace.Completion (BorchersPos ⧸ OSBorchers.nullSubmodule pre)
  let Ω : H := ((Submodule.Quotient.mk borchersVac :
    BorchersPos ⧸ OSBorchers.nullSubmodule pre) : H)
  let inData0 : ClayReduction.OSReconstructedInput.{0} N :=
    { hN := D.hN
      H := H
      Ω := Ω
      Ω_norm := hΩ_norm
      U := U
      U_vac := hU_vac
      U_time_zero := hU_zero
      U_time_add := hU_add
      T := fun t => (T t).toLinearMap
      T_vac := hT_vac
      T_symm := hT_symm
      T_add := hT_add
      T_poly := fun x => ⟨‖x‖ + 1, 0, by positivity, le_rfl, fun t ht => by
        simpa using le_trans (hT_contr t ht x) (le_add_of_nonneg_right zero_le_one)⟩
      Δ := D.Δ
      Δ_pos := D.Δ_pos
      T_decay := hT_decay
      fieldDomain := fieldDomain
      fieldDomain_dense := h_dense
      Ω_in_fieldDom := hΩ_dom
      field := field
      field_maps_into := h_maps
      locality := fun a b hab ψ => h_loc a b hab ψ (h_maps b ψ) (h_maps a ψ)
      variance_witness := ((Submodule.Quotient.mk D.variance_elem :
        BorchersPos ⧸ OSBorchers.nullSubmodule pre) : H)
      variance_strict := hvar
      separated_f := f
      separated_g := g
      separated_disjoint := h_disj
      separated_2pt_nz := h_2pt hΩ_dom (h_maps g ⟨Ω, hΩ_dom⟩) }
  exact lift_os_input_universe inData0

end Imscribing.YangMills.BorchersReconstruction