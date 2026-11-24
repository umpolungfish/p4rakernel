import Imscribing.YangMills.DoeblinTransferGap4D
import Imscribing.YangMills.LatticeTransferOperator4D

/-!
# Quantitative Finite-Volume Spectral Gap on the 4D SU(N) Wilson Transfer Kernel

Applies `DoeblinGap.doeblin_markov_l2_contraction` directly to the Doob-normalized
4D SU(N) Wilson transfer kernel `K_π(U, V) = K_W(U, V) / (λ₀ ψ₀(U) ψ₀(V))`,
proving an explicit positive finite-volume L² contraction rate `ε > 0` from
`wilsonTransferKernel_bounds` and `wilsonTransferKernel_symm` (`0 sorry`).
-/

namespace Imscribing.YangMills.WilsonDoeblinGap4D

open MeasureTheory
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.LatticeTransfer4D
open Imscribing.YangMills.DoeblinGap

/-- Doob ground-state normalized kernel `K_π(U, V) = K_W(U, V) / (λ₀ ψ₀(U) ψ₀(V))`. -/
noncomputable def doobWilsonKernel (N L : ℕ) [NeZero N] (β : ℝ)
    [MeasurableSpace (SpatLat L → GaugeGroup N)] (μ_W : Measure (SpatLat L → GaugeGroup N))
    (λ₀ : ℝ) (ψ₀ : SpatConfig N L → ℝ) (U V : SpatConfig N L) : ℝ :=
  wilsonTransferKernel N L β μ_W U V / (λ₀ * ψ₀ U * ψ₀ V)

/-- **Quantitative Finite-Volume 4D SU(N) Wilson Spectral Gap:**
    Given a positive ground-state eigenfunction `0 < c_lo ≤ ψ₀ ≤ c_hi` with
    eigenvalue `λ₀ > 0` (`∫ K_W(U, V) ψ₀(V) dμ_U = λ₀ ψ₀(U)`) normalized in `L²(μ_U)`,
    the Doob-transformed Wilson transfer operator contracts mean-zero `L²(π)` states
    by `(1 - ε)² ≤ exp(-2ε)` with explicit `ε = min 1 (exp(-21 β |L³|) / (λ₀ c_hi²)) > 0`. -/
theorem wilsonTransfer_finite_volume_doeblin_gap
    (N L : ℕ) [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    [MeasurableSpace (SpatLat L → GaugeGroup N)] (μ_W : Measure (SpatLat L → GaugeGroup N))
    [IsProbabilityMeasure μ_W]
    (h_inv_mp : Measure.map (fun W : SpatLat L → GaugeGroup N => fun x => (W x)⁻¹) μ_W = μ_W)
    (h_inv_meas : Measurable (fun W : SpatLat L → GaugeGroup N => fun x => (W x)⁻¹))
    (h_bond_meas : ∀ U V, Measurable (fun W => Real.exp ((β / (N : ℝ)) * bondTraceSum U V W)))
    [MeasurableSpace (SpatConfig N L)]
    (hK_meas : Measurable (Function.uncurry (wilsonTransferKernel N L β μ_W)))
    (π : Measure (SpatConfig N L)) [IsProbabilityMeasure π]
    (λ₀ : ℝ) (hλ₀ : 0 < λ₀) (ψ₀ : SpatConfig N L → ℝ) (hψ_meas : Measurable ψ₀)
    (c_lo c_hi : ℝ) (hc_lo : 0 < c_lo) (hψ_bounds : ∀ U, c_lo ≤ ψ₀ U ∧ ψ₀ U ≤ c_hi)
    (h_eigen : ∀ U, ∫ V, doobWilsonKernel N L β μ_W λ₀ ψ₀ U V ∂π = 1)
    (φ : SpatConfig N L → ℂ) (hφ_meas : Measurable φ) (Bφ : ℝ) (hφ_bound : ∀ V, ‖φ V‖ ≤ Bφ)
    (h_mean_zero : ∫ V, φ V ∂π = 0) :
    let C := ((Fintype.card (SpatLat L) : ℕ) : ℝ)
    let ε : ℝ := min 1 (Real.exp (-(21 * β * C)) / (λ₀ * c_hi ^ 2))
    0 < ε ∧
    (∫ U, ‖∫ V, (doobWilsonKernel N L β μ_W λ₀ ψ₀ U V : ℂ) * φ V ∂π‖ ^ 2 ∂π) ≤
      Real.exp (-2 * ε) * ∫ V, ‖φ V‖ ^ 2 ∂π := by
  intro C ε
  have hc_hi : 0 < c_hi := lt_of_lt_of_le hc_lo
    (le_trans (hψ_bounds (Classical.arbitrary _)).1 (hψ_bounds (Classical.arbitrary _)).2)
  have h_num_pos : 0 < Real.exp (-(21 * β * C)) := Real.exp_pos _
  have h_den_pos : 0 < λ₀ * c_hi ^ 2 := by positivity
  have hε_pos : 0 < ε := lt_min one_pos (div_pos h_num_pos h_den_pos)
  have hε_le : ε ≤ 1 := min_le_left _ _
  have hK_symm : ∀ U V, doobWilsonKernel N L β μ_W λ₀ ψ₀ U V =
      doobWilsonKernel N L β μ_W λ₀ ψ₀ V U := by
    intro U V
    unfold doobWilsonKernel
    rw [wilsonTransferKernel_symm N L β μ_W h_inv_mp h_inv_meas h_bond_meas U V]
    ring
  have hK_meas_doob : Measurable (Function.uncurry (doobWilsonKernel N L β μ_W λ₀ ψ₀)) := by
    unfold doobWilsonKernel
    have hm_den : Measurable (fun p : SpatConfig N L × SpatConfig N L => λ₀ * ψ₀ p.1 * ψ₀ p.2) :=
      (measurable_const.mul (hψ_meas.comp measurable_fst)).mul (hψ_meas.comp measurable_snd)
    exact hK_meas.div hm_den
  have hK_lb : ∀ U V, ε ≤ doobWilsonKernel N L β μ_W λ₀ ψ₀ U V := by
    intro U V
    obtain ⟨_, hlo, _⟩ := wilsonTransferKernel_bounds N L hβ μ_W h_bond_meas U V
    have hU := hψ_bounds U
    have hV := hψ_bounds V
    have hden_le : λ₀ * ψ₀ U * ψ₀ V ≤ λ₀ * c_hi ^ 2 := by
      have h1 : ψ₀ U * ψ₀ V ≤ c_hi * c_hi :=
        mul_le_mul hU.2 hV.2 (le_trans hc_lo.le hV.1) hc_hi.le
      nlinarith [sq c_hi]
    have hden_pos : 0 < λ₀ * ψ₀ U * ψ₀ V := by
      have hU0 : 0 < ψ₀ U := lt_of_lt_of_le hc_lo hU.1
      have hV0 : 0 < ψ₀ V := lt_of_lt_of_le hc_lo hV.1
      positivity
    have h_div : Real.exp (-(21 * β * C)) / (λ₀ * c_hi ^ 2) ≤
        wilsonTransferKernel N L β μ_W U V / (λ₀ * ψ₀ U * ψ₀ V) :=
      div_le_div₀ h_num_pos.le hlo hden_pos hden_le
    exact le_trans (min_le_right _ _) h_div
  have hK_ub : ∀ U V, doobWilsonKernel N L β μ_W λ₀ ψ₀ U V ≤
      Real.exp (3 * β * C) / (λ₀ * c_lo ^ 2) := by
    intro U V
    obtain ⟨_, _, hhi⟩ := wilsonTransferKernel_bounds N L hβ μ_W h_bond_meas U V
    have hU := hψ_bounds U
    have hV := hψ_bounds V
    have hden_lo : λ₀ * c_lo ^ 2 ≤ λ₀ * ψ₀ U * ψ₀ V := by
      have h1 : c_lo * c_lo ≤ ψ₀ U * ψ₀ V :=
        mul_le_mul hU.1 hV.1 hc_lo.le (le_trans hc_lo.le hU.1)
      nlinarith [sq c_lo]
    have hden_pos : 0 < λ₀ * c_lo ^ 2 := by positivity
    exact div_le_div₀ (Real.exp_pos _).le hhi hden_pos hden_lo
  have h_gap := doeblin_markov_l2_contraction π (doobWilsonKernel N L β μ_W λ₀ ψ₀)
    hK_meas_doob (Real.exp (3 * β * C) / (λ₀ * c_lo ^ 2)) hK_ub hK_symm h_eigen
    hε_pos hε_le hK_lb φ hφ_meas Bφ hφ_bound h_mean_zero
  exact ⟨hε_pos, le_trans h_gap.1 h_gap.2⟩

end Imscribing.YangMills.WilsonDoeblinGap4D