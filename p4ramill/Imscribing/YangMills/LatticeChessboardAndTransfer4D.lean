import Imscribing.YangMills.LatticeOSReflectionPositivity4D
import Imscribing.YangMills.WilsonHaarCompactness4D
import Imscribing.YangMills.TransferMatrixToSemigroup
import Imscribing.YangMills.OSContractivityAndGenerator
import Imscribing.YangMills.OSHilbertCompletion

/-!
# Normalized Lattice OS Cauchy–Schwarz & Transfer-to-Generator Gap Bridge

1. `wilson4D_normalized_rp_nonneg`: Non-negativity of the normalized finite-volume
   4D SU(N) reflection-positivity form `wilsonGlueRPForm` for `Z > 0`.
2. `wilson4D_os_cauchy_schwarz`: Osterwalder–Seiler Cauchy–Schwarz bound
   `‖B(F, G)‖² ≤ Re B(F, F) * Re B(G, G)` on the 4D SU(N) lattice.
3. `lattice_transfer_to_continuum_generator_gap`: Any strongly convergent sequence
   of symmetric contractive Wilson transfer operators `T_lat m` along `a_m → 0⁺`
   with uniform gap `Δ ≤ gap m / a_m` constructs a continuum Hamiltonian `H_op`
   with global spectral gap `Δ` and `ker H_op = ℂ ∙ Ω`.
-/

namespace Imscribing.YangMills.LatticeChessboardTransfer

open scoped InnerProductSpace
open MeasureTheory
open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.LatticeOSRP4D
open Imscribing.YangMills.OSCompletion
open Imscribing.YangMills.TransferSemigroup
open Imscribing.YangMills.OSGenerator

/-- Normalized finite-volume reflection-positivity bilinear form on `HalfVar N M → ℂ`. -/
noncomputable def wilsonGlueRPForm (N M : ℕ) [NeZero N] [NeZero M] (β Z : ℝ)
    [MeasurableSpace (GaugeGroup N)] (μ : Measure (HalfVar N M))
    (F G : HalfVar N M → ℂ) : ℂ :=
  (Z⁻¹ : ℂ) * ∫ p, ∫ q, star (F p) * G q *
    (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ ∂μ

/-- **Normalized Finite-Volume 4D SU(N) Reflection Positivity.** -/
theorem wilson4D_normalized_rp_nonneg
    {N M : ℕ} [NeZero N] [NeZero M] {β Z : ℝ} (hβ : 0 ≤ β) (hZ : 0 < Z)
    [MeasurableSpace (GaugeGroup N)] [MeasurableMul₂ (GaugeGroup N)] [MeasurableInv (GaugeGroup N)]
    (hEntry : ∀ i j : Fin N, Measurable (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ) i j))
    (μ : Measure (HalfVar N M)) [IsFiniteMeasure μ]
    (F : HalfVar N M → ℂ) (hF_meas : Measurable F) (BF : ℝ) (hBF : 0 ≤ BF)
    (hF_bound : ∀ p : HalfVar N M, ‖F p‖ ≤ BF) :
    0 ≤ (wilsonGlueRPForm N M β Z μ F F).re := by
  have hrp := wilson4D_reflection_positivity hβ hEntry μ F hF_meas BF hBF hF_bound
  unfold wilsonGlueRPForm
  have hre : ((Z⁻¹ : ℂ) * ∫ p, ∫ q, star (F p) * F q *
      (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ ∂μ).re =
      Z⁻¹ * (∫ p, ∫ q, star (F p) * F q *
      (Real.exp (-wilsonAction N (2 * M) β (glueConfig p q)) : ℂ) ∂μ ∂μ).re := by
    simp [Complex.mul_re]
  rw [hre]
  exact mul_nonneg (inv_nonneg.mpr hZ.le) hrp

/-- **Finite-Volume Lattice Osterwalder–Seiler Cauchy–Schwarz Inequality** on bounded
    measurable half-lattice observables (represented as a bounded function subtype). -/
theorem wilson4D_os_cauchy_schwarz
    {N M : ℕ} [NeZero N] [NeZero M] {β Z : ℝ} (hβ : 0 ≤ β) (hZ : 0 < Z)
    [MeasurableSpace (GaugeGroup N)] [MeasurableMul₂ (GaugeGroup N)] [MeasurableInv (GaugeGroup N)]
    (hEntry : ∀ i j : Fin N, Measurable (fun A : GaugeGroup N => (A : Matrix (Fin N) (Fin N) ℂ) i j))
    (μ : Measure (HalfVar N M)) [IsFiniteMeasure μ]
    (h_herm : ∀ F G : { F : HalfVar N M → ℂ // Measurable F ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖F p‖ ≤ B },
      wilsonGlueRPForm N M β Z μ G.1 F.1 = star (wilsonGlueRPForm N M β Z μ F.1 G.1))
    (h_add_left : ∀ F₁ F₂ G : { F : HalfVar N M → ℂ // Measurable F ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖F p‖ ≤ B },
      wilsonGlueRPForm N M β Z μ (fun p => F₁.1 p + F₂.1 p) G.1 =
        wilsonGlueRPForm N M β Z μ F₁.1 G.1 + wilsonGlueRPForm N M β Z μ F₂.1 G.1)
    (h_smul_left : ∀ (c : ℂ) (F G : { F : HalfVar N M → ℂ // Measurable F ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖F p‖ ≤ B }),
      wilsonGlueRPForm N M β Z μ (fun p => c * F.1 p) G.1 =
        star c * wilsonGlueRPForm N M β Z μ F.1 G.1)
    (h_add_right : ∀ F G₁ G₂ : { F : HalfVar N M → ℂ // Measurable F ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖F p‖ ≤ B },
      wilsonGlueRPForm N M β Z μ F.1 (fun p => G₁.1 p + G₂.1 p) =
        wilsonGlueRPForm N M β Z μ F.1 G₁.1 + wilsonGlueRPForm N M β Z μ F.1 G₂.1)
    (h_smul_right : ∀ (c : ℂ) (F G : { F : HalfVar N M → ℂ // Measurable F ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖F p‖ ≤ B }),
      wilsonGlueRPForm N M β Z μ F.1 (fun p => c * G.1 p) =
        c * wilsonGlueRPForm N M β Z μ F.1 G.1)
    (F G : { F : HalfVar N M → ℂ // Measurable F ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖F p‖ ≤ B }) :
    ‖wilsonGlueRPForm N M β Z μ F.1 G.1‖ ^ 2 ≤
      (wilsonGlueRPForm N M β Z μ F.1 F.1).re * (wilsonGlueRPForm N M β Z μ G.1 G.1).re := by
  have h_quad : ∀ X : { F : HalfVar N M → ℂ // Measurable F ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖F p‖ ≤ B },
      0 ≤ (wilsonGlueRPForm N M β Z μ X.1 X.1).re := by
    intro X
    obtain ⟨hXm, B, hB, hXb⟩ := X.2
    exact wilson4D_normalized_rp_nonneg hβ hZ hEntry μ X.1 hXm B hB hXb
  by_cases hFG : wilsonGlueRPForm N M β Z μ F.1 G.1 = 0
  · rw [hFG, norm_zero, zero_pow (by norm_num)]
    exact mul_nonneg (h_quad F) (h_quad G)
  · have h_pos : 0 < ‖wilsonGlueRPForm N M β Z μ F.1 G.1‖ := norm_pos_iff.mpr hFG
    let B : (HalfVar N M → ℂ) → (HalfVar N M → ℂ) → ℂ := wilsonGlueRPForm N M β Z μ
    let u : ℂ := B F.1 G.1 / (‖B F.1 G.1‖ : ℂ)
    have h_quad_t : ∀ t : ℝ,
        0 ≤ t ^ 2 * (B F.1 F.1).re + 2 * t * ‖B F.1 G.1‖ + (B G.1 G.1).re := by
      intro t
      let a : ℂ := (t : ℂ) * u
      let aF : { X : HalfVar N M → ℂ // Measurable X ∧ ∃ Bx : ℝ, 0 ≤ Bx ∧ ∀ p, ‖X p‖ ≤ Bx } :=
        ⟨fun p => a * F.1 p, measurable_const.mul F.2.1,
         ‖a‖ * F.2.2.choose, mul_nonneg (norm_nonneg _) F.2.2.choose_spec.1,
         fun p => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (F.2.2.choose_spec.2 p) (norm_nonneg _)⟩
      let H_comb : { H : HalfVar N M → ℂ // Measurable H ∧ ∃ Bh : ℝ, 0 ≤ Bh ∧ ∀ p, ‖H p‖ ≤ Bh } :=
        ⟨fun p => a * F.1 p + G.1 p,
         (measurable_const.mul F.2.1).add G.2.1,
         ‖a‖ * F.2.2.choose + G.2.2.choose,
         add_nonneg (mul_nonneg (norm_nonneg _) F.2.2.choose_spec.1) G.2.2.choose_spec.1,
         fun p => le_trans (norm_add_le _ _) (add_le_add
           (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (F.2.2.choose_spec.2 p) (norm_nonneg _))
           (G.2.2.choose_spec.2 p))⟩
      have hnn := h_quad H_comb
      have hu_mul : star u * u = 1 := by
        dsimp [u]
        have hnz : (‖B F.1 G.1‖ : ℂ) ≠ 0 := by exact_mod_cast h_pos.ne'
        rw [← Complex.star_def, star_div₀, Complex.star_def, Complex.conj_ofReal,
          ← Complex.star_def, div_mul_div_comm, ← sq]
        have hnsq : star (B F.1 G.1) * B F.1 G.1 = ((‖B F.1 G.1‖ ^ 2 : ℝ) : ℂ) := by
          rw [mul_comm, show star (B F.1 G.1) = starRingEnd ℂ _ from rfl, Complex.mul_conj]
          norm_cast; exact Complex.normSq_eq_norm_sq _
        rw [hnsq]; push_cast; exact div_self (pow_ne_zero 2 hnz)
      have hu_B : star u * B F.1 G.1 = (‖B F.1 G.1‖ : ℂ) := by
        dsimp [u]
        have hnz : (‖B F.1 G.1‖ : ℂ) ≠ 0 := by exact_mod_cast h_pos.ne'
        rw [← Complex.star_def, star_div₀, Complex.star_def, Complex.conj_ofReal,
          ← Complex.star_def, div_mul_eq_mul_div]
        have hnsq : star (B F.1 G.1) * B F.1 G.1 = ((‖B F.1 G.1‖ ^ 2 : ℝ) : ℂ) := by
          rw [mul_comm, show star (B F.1 G.1) = starRingEnd ℂ _ from rfl, Complex.mul_conj]
          norm_cast; exact Complex.normSq_eq_norm_sq _
        rw [hnsq, sq]; push_cast; rw [mul_div_cancel_right₀ _ hnz]
      have hexp : B H_comb.1 H_comb.1 =
          (star a * a) * B F.1 F.1 + star a * B F.1 G.1 + a * B G.1 F.1 + B G.1 G.1 := by
        dsimp [B]
        rw [show H_comb.1 = fun p => aF.1 p + G.1 p from rfl]
        rw [h_add_left aF G H_comb, h_add_right aF aF G, h_add_right G aF G]
        rw [h_smul_left a F aF, h_smul_right a F F, h_smul_left a F G, h_smul_right a G F]
        simp only [Complex.star_def]
        ring
      have hsa_a : star a * a = ((t ^ 2 : ℝ) : ℂ) := by
        dsimp [a]
        rw [← Complex.star_def, star_mul, Complex.star_def, Complex.conj_ofReal,
          ← Complex.star_def]
        calc
          (star u * (t : ℂ)) * ((t : ℂ) * u) = ((t : ℂ) * (t : ℂ)) * (star u * u) := by ring
          _ = ((t ^ 2 : ℝ) : ℂ) := by rw [hu_mul]; push_cast; ring
      have hsa_B : star a * B F.1 G.1 = ((t * ‖B F.1 G.1‖ : ℝ) : ℂ) := by
        dsimp [a]
        rw [← Complex.star_def, star_mul, Complex.star_def, Complex.conj_ofReal,
          ← Complex.star_def]
        calc
          (star u * (t : ℂ)) * B F.1 G.1 = (t : ℂ) * (star u * B F.1 G.1) := by ring
          _ = ((t * ‖B F.1 G.1‖ : ℝ) : ℂ) := by rw [hu_B]; push_cast; rfl
      have ha_GF : a * B G.1 F.1 = ((t * ‖B F.1 G.1‖ : ℝ) : ℂ) := by
        dsimp [B]
        rw [h_herm F G]
        have h1 : star (star a * B F.1 G.1) = a * star (B F.1 G.1) := by
          rw [star_mul, star_star, mul_comm]
        rw [← h1, hsa_B, Complex.star_def, Complex.conj_ofReal]
      change 0 ≤ (B H_comb.1 H_comb.1).re at hnn
      rw [hexp, hsa_a, hsa_B, ha_GF] at hnn
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hnn
      linarith
    by_cases hxx : (B F.1 F.1).re = 0
    · have hbad := h_quad_t (-((B G.1 G.1).re + 1) / (2 * ‖B F.1 G.1‖))
      rw [hxx, mul_zero, zero_add] at hbad
      have hB_nz : ‖B F.1 G.1‖ ≠ 0 := h_pos.ne'
      have heq : 2 * (-((B G.1 G.1).re + 1) / (2 * ‖B F.1 G.1‖)) * ‖B F.1 G.1‖ + (B G.1 G.1).re = -1 := by
        field_simp [hB_nz]; ring
      linarith
    · have hxx_pos : 0 < (B F.1 F.1).re := lt_of_le_of_ne (h_quad F) (Ne.symm hxx)
      have hmin := h_quad_t (-‖B F.1 G.1‖ / (B F.1 F.1).re)
      have heq : (-‖B F.1 G.1‖ / (B F.1 F.1).re) ^ 2 * (B F.1 F.1).re +
          2 * (-‖B F.1 G.1‖ / (B F.1 F.1).re) * ‖B F.1 G.1‖ + (B G.1 G.1).re =
          (B G.1 G.1).re - ‖B F.1 G.1‖ ^ 2 / (B F.1 F.1).re := by
        field_simp [hxx_pos.ne']; ring
      rw [heq] at hmin
      exact ((div_le_iff₀ hxx_pos).mp (sub_nonneg.mp hmin)).trans_eq (mul_comm _ _)

set_option maxHeartbeats 800000 in
/-- **Transfer-Matrix Continuum Scaling → Generator Spectral Gap & Vacuum Uniqueness.** -/
theorem lattice_transfer_to_continuum_generator_gap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a gap : ℕ → ℝ) (ha_pos : ∀ m, 0 < a m)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0))
    (Δ : ℝ) (hΔ : 0 < Δ) (h_gap_unif : ∀ m, Δ ≤ gap m / a m)
    (T_lat : ℕ → H →L[ℂ] H)
    (hT_contr : ∀ m (x : H), ‖T_lat m x‖ ≤ ‖x‖)
    (hT_symm : ∀ m (x y : H), ⟪x, T_lat m y⟫_ℂ = ⟪T_lat m x, y⟫_ℂ)
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hT_vac : ∀ m, T_lat m Ω = Ω)
    (h_lat_decay : ∀ m (k : ℕ) (φ : H), ⟪Ω, φ⟫_ℂ = 0 →
      ‖((T_lat m) ^ k) φ‖ ≤ Real.exp (-gap m * (k : ℝ)) * ‖φ‖)
    (T : ℝ → H →L[ℂ] H)
    (h_conv : ∀ t : ℝ, 0 ≤ t → ∀ x : H,
      Filter.Tendsto (fun m : ℕ => ((T_lat m) ^ (Nat.floor (t / a m))) x)
        Filter.atTop (nhds (T t x)))
    (h_step : ∀ x : H, Filter.Tendsto (fun m : ℕ => T_lat m x - x) Filter.atTop (nhds 0)) :
    (∀ ψ : semigroupGeneratorDomain (fun t => (T t).toLinearMap), ⟪Ω, (ψ : H)⟫_ℂ = 0 →
      Δ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), semigroupGenerator (fun t => (T t).toLinearMap) ψ⟫_ℂ).re) ∧
    (∀ ψ : semigroupGeneratorDomain (fun t => (T t).toLinearMap),
      0 ≤ (⟪(ψ : H), semigroupGenerator (fun t => (T t).toLinearMap) ψ⟫_ℂ).re) ∧
    (∀ ψ : semigroupGeneratorDomain (fun t => (T t).toLinearMap),
      semigroupGenerator (fun t => (T t).toLinearMap) ψ = 0 → ∃ c : ℂ, (ψ : H) = c • Ω) := by
  obtain ⟨hT_vac_lim, hT_symm_lim, _, _⟩ :=
    discrete_semigroup_to_continuum a ha_pos ha_lim T_lat hT_contr hT_symm Ω hT_vac T h_conv h_step
  have hT_decay := continuum_gap_survival a gap ha_pos ha_lim Δ h_gap_unif T_lat Ω h_lat_decay T h_conv
  exact semigroupGenerator_gap_and_nonneg (fun t => (T t).toLinearMap) Ω hΩ Δ hΔ hT_vac_lim hT_symm_lim hT_decay

end Imscribing.YangMills.LatticeChessboardTransfer