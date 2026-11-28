import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Imscribing.YangMills.PoincareUnitaryReconstruction
import Imscribing.YangMills.PoincareLieAlgebraAndNelson

/-!
# Nelson Unitary Group Stone Derivative & Global Vacuum Invariance

Proves unconditionally (`0 sorry`):
1. `expSeries_hasDerivAt_zero`: `HasDerivAt (fun t => expSeries D A hA t ψ) (i • A ψ) 0`.
2. `nelson_unitary_hasDerivAt_all`: `HasDerivAt (fun t => U t ψ) (U s (i • A ψ)) s`
   for every `s : ℝ` on the Nelson global unitary group `U`.
3. `nelson_unitary_fixes_vacuum`: `A Ω = 0 → ∀ t : ℝ, U t Ω = Ω`.
-/

namespace Imscribing.YangMills.NelsonStoneDeriv

open scoped InnerProductSpace Topology
open Imscribing.YangMills.AnalyticVectorExp
open Imscribing.YangMills.PoincareUnitary
open Imscribing.YangMills.PoincareNelson

section StoneDeriv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Derivative at Zero of Nelson's Analytic Vector Exponential:**
    `HasDerivAt (fun t => expSeries D A hA t ψ) (Complex.I • (A ψ : H)) 0`. -/
theorem expSeries_hasDerivAt_zero
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    {r : ℝ} (hr : 0 < r) (ψ : D) (h_psi : IsAnalyticVector D A hA ψ r) :
    HasDerivAt (fun t : ℝ => expSeries D A hA t ψ) (Complex.I • (A ψ : H)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  obtain ⟨_, M, hM, hbound⟩ := h_psi
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h_slope_bound : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      ‖slope (fun u => expSeries D A hA u ψ) 0 t - Complex.I • (A ψ : H)‖ ≤
        (2 * M * r ^ 2) * |t| := by
    have h_ball : Set.Ioo (-(2 * r)⁻¹) ((2 * r)⁻¹) \ {0} ∈ 𝓝[≠] (0 : ℝ) :=
      mem_nhdsWithin.mpr ⟨Set.Ioo (-(2 * r)⁻¹) ((2 * r)⁻¹), isOpen_Ioo,
        ⟨neg_lt_zero.mpr (by positivity), by positivity⟩, fun _ hx => ⟨hx.1, hx.2⟩⟩
    filter_upwards [h_ball] with t ⟨ht_ioo, ht_ne⟩
    have ht_abs : |t| < (2 * r)⁻¹ := abs_lt.mpr ⟨ht_ioo.1, ht_ioo.2⟩
    have ht_half : r * |t| ≤ 1 / 2 := by
      have h1 : 2 * r * |t| < 1 := by
        calc 2 * r * |t| < 2 * r * (2 * r)⁻¹ := mul_lt_mul_of_pos_left ht_abs (by positivity)
          _ = 1 := mul_inv_cancel₀ (by positivity)
      linarith
    have ht1 : r * |t| < 1 := by linarith
    have h_sum := expSeries_summable D A hA ⟨hr, M, hM, hbound⟩ ht1
    let u : ℕ → H := fun n =>
      ((Complex.I * (t : ℂ)) ^ n / (n.factorial : ℂ)) • (iterA D A hA n ψ : H)
    have h_sum1 : Summable (fun n => u (n + 1)) := (summable_nat_add_iff 1).mpr h_sum
    have h_sum2 : Summable (fun m => u (m + 2)) := (summable_nat_add_iff 2).mpr h_sum
    have h_tsum_split : expSeries D A hA t ψ =
        (ψ : H) + (Complex.I * (t : ℂ)) • (A ψ : H) + ∑' m : ℕ, u (m + 2) := by
      change (∑' n, u n) = _
      rw [h_sum.tsum_eq_zero_add, h_sum1.tsum_eq_zero_add]
      have hu0 : ((Complex.I * (t : ℂ)) ^ 0 / ((Nat.factorial 0 : ℕ) : ℂ)) •
          (iterA D A hA 0 ψ : H) = (ψ : H) := by simp [iterA_zero]
      have hu1 : u (0 + 1) = (Complex.I * (t : ℂ)) • (A ψ : H) := by
        simp [u, iterA_succ]
      rw [hu0, hu1, ← add_assoc]
    have h_slope_eq : slope (fun u => expSeries D A hA u ψ) 0 t - Complex.I • (A ψ : H) =
        t⁻¹ • ∑' m : ℕ, u (m + 2) := by
      rw [slope_def_module, sub_zero, expSeries_zero, h_tsum_split]
      have h_sub_psi : (ψ : H) + (Complex.I * (t : ℂ)) • (A ψ : H) + ∑' m, u (m + 2) - (ψ : H) =
          (Complex.I * (t : ℂ)) • (A ψ : H) + ∑' m, u (m + 2) := by abel
      rw [h_sub_psi, smul_add]
      have h_t_cancel : t⁻¹ • ((Complex.I * (t : ℂ)) • (A ψ : H)) = Complex.I • (A ψ : H) := by
        rw [← smul_assoc, Complex.real_smul]
        have ht_c : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_ne
        have h_mul : ((t⁻¹ : ℝ) : ℂ) * (Complex.I * (t : ℂ)) = Complex.I := by
          push_cast; field_simp [ht_c]
        rw [h_mul]
      rw [h_t_cancel]
      abel
    rw [h_slope_eq, norm_smul, Real.norm_eq_abs, abs_inv]
    have h_geom : Summable (fun m : ℕ => (M * r ^ 2 * |t| ^ 2) * (1 / 2 : ℝ) ^ m) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have h_term_le : ∀ m : ℕ, ‖u (m + 2)‖ ≤ (M * r ^ 2 * |t| ^ 2) * (1 / 2 : ℝ) ^ m := by
      intro m
      dsimp [u]
      have hfac : (0 : ℝ) < ((m + 2).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      simp only [norm_smul, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs]
      have h_iter := hbound (m + 2)
      have h_num : (|t| ^ (m + 2) / ((m + 2).factorial : ℝ)) * ‖(iterA D A hA (m + 2) ψ : H)‖ ≤
          (|t| ^ (m + 2) / ((m + 2).factorial : ℝ)) *
            (M * r ^ (m + 2) * ((m + 2).factorial : ℝ)) := by gcongr
      have h2 : (|t| ^ (m + 2) / ((m + 2).factorial : ℝ)) *
          (M * r ^ (m + 2) * ((m + 2).factorial : ℝ)) =
          (M * r ^ 2 * |t| ^ 2) * (r * |t|) ^ m := by
        rw [pow_add, pow_add, mul_pow]; field_simp [hfac.ne']; try ring
      have h3 : (M * r ^ 2 * |t| ^ 2) * (r * |t|) ^ m ≤
          (M * r ^ 2 * |t| ^ 2) * (1 / 2 : ℝ) ^ m := by
        gcongr
      exact le_trans h_num (le_trans (le_of_eq h2) h3)
    have h_norm_sum2 : Summable (fun m => ‖u (m + 2)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_le h_geom
    have h_tsum_le : ‖∑' m : ℕ, u (m + 2)‖ ≤ (M * r ^ 2 * |t| ^ 2) * 2 := by
      have h1 : ‖∑' m : ℕ, u (m + 2)‖ ≤ ∑' m : ℕ, ‖u (m + 2)‖ :=
        norm_tsum_le_tsum_norm h_norm_sum2
      have h2 : ∑' m : ℕ, ‖u (m + 2)‖ ≤ ∑' m : ℕ, (M * r ^ 2 * |t| ^ 2) * (1 / 2 : ℝ) ^ m :=
        Summable.tsum_le_tsum h_term_le h_norm_sum2 h_geom
      have h3 : (∑' m : ℕ, (M * r ^ 2 * |t| ^ 2) * (1 / 2 : ℝ) ^ m) =
          (M * r ^ 2 * |t| ^ 2) * 2 := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
      exact le_trans h1 (le_trans h2 (le_of_eq h3))
    have h_mul_le : |t|⁻¹ * ‖∑' m : ℕ, u (m + 2)‖ ≤ |t|⁻¹ * ((M * r ^ 2 * |t| ^ 2) * 2) :=
      mul_le_mul_of_nonneg_left h_tsum_le (inv_nonneg.mpr (abs_nonneg t))
    have h_eq : |t|⁻¹ * ((M * r ^ 2 * |t| ^ 2) * 2) = (2 * M * r ^ 2) * |t| := by
      have hta : |t| ≠ 0 := abs_ne_zero.mpr ht_ne
      field_simp [hta]; try ring
    rwa [h_eq] at h_mul_le
  have h_rhs0 : Filter.Tendsto (fun t : ℝ => (2 * M * r ^ 2) * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have h_abs0 : Filter.Tendsto (fun t : ℝ => |t|) (𝓝[≠] 0) (𝓝 0) :=
      ((continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).trans (by simp)
    simpa using h_abs0.const_mul (2 * M * r ^ 2)
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) h_slope_bound h_rhs0

/-- **Global Stone Derivative for `nelson_global_unitary_group`:**
    For every `ψ ∈ D` and every `s : ℝ`, `HasDerivAt (fun t => U t ψ) (U s (i • A ψ)) s`. -/
theorem nelson_unitary_hasDerivAt_all
    (D : Submodule ℂ H) (h_dense : Dense (D : Set H))
    (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (h_symm : ∀ ψ φ : D, ⟪(ψ : H), A φ⟫_ℂ = ⟪A ψ, (φ : H)⟫_ℂ)
    {r : ℝ} (hr : 0 < r) (h_unif : ∀ ψ : D, IsAnalyticVector D A hA ψ r)
    (ψ : D) (s : ℝ) :
    let U := (nelson_global_unitary_group D h_dense A hA h_symm hr h_unif).1
    HasDerivAt (fun t : ℝ => U t (ψ : H)) (U s (Complex.I • (A ψ : H))) s := by
  intro U
  have h_spec := (nelson_global_unitary_group D h_dense A hA h_symm hr h_unif).2
  have hU_add := h_spec.2.1
  have hU_small := h_spec.2.2
  have h_deriv0 := expSeries_hasDerivAt_zero D A hA hr ψ (h_unif ψ)
  have h_comp0 : HasDerivAt (fun h : ℝ => U s (expSeries D A hA h ψ))
      ((U s).toContinuousLinearMap (Complex.I • (A ψ : H))) 0 :=
    ((U s).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h_deriv0
  have h_shift : HasDerivAt (fun t : ℝ => U s (expSeries D A hA (t - s) ψ))
      (U s (Complex.I • (A ψ : H))) s := by
    have h_slope0 : Filter.Tendsto (slope (fun h : ℝ => U s (expSeries D A hA h ψ)) 0)
        (𝓝[≠] 0) (𝓝 ((U s).toContinuousLinearMap (Complex.I • (A ψ : H)))) :=
      hasDerivAt_iff_tendsto_slope.mp h_comp0
    have h_sub_nhds : Filter.Tendsto (fun t : ℝ => t - s) (𝓝[≠] s) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Filter.Tendsto (fun t : ℝ => t - s) (𝓝 s) (𝓝 (s - s)) :=
          (continuous_id.sub continuous_const).tendsto s
        rw [sub_self] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact sub_ne_zero.mpr ht
    rw [hasDerivAt_iff_tendsto_slope]
    have h_eq_sl : slope (fun t : ℝ => U s (expSeries D A hA (t - s) ψ)) s =
        fun t => slope (fun h : ℝ => U s (expSeries D A hA h ψ)) 0 (t - s) := by
      ext t
      simp [slope_def_module]
    rw [h_eq_sl]
    exact h_slope0.comp h_sub_nhds
  have h_ev : (fun t : ℝ => U s (expSeries D A hA (t - s) ψ)) =ᶠ[𝓝 s]
      (fun t : ℝ => U t (ψ : H)) := by
    have h_mem : Set.Ioo (s - (4 * r)⁻¹) (s + (4 * r)⁻¹) ∈ 𝓝 s :=
      Ioo_mem_nhds (by linarith [show 0 < (4 * r)⁻¹ by positivity])
        (by linarith [show 0 < (4 * r)⁻¹ by positivity])
    filter_upwards [h_mem] with t ht
    have h_abs : |t - s| < (4 * r)⁻¹ := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [← hU_small (t - s) h_abs ψ, ← hU_add s (t - s) (ψ : H), add_sub_cancel]
  exact h_shift.congr_of_eventuallyEq h_ev.symm

/-- **Global Vacuum Invariance on the Nelson Unitary Group:**
    If `A Ω = 0` for `Ω ∈ D`, then `U t Ω = Ω` for all `t : ℝ`. -/
theorem nelson_unitary_fixes_vacuum
    (D : Submodule ℂ H) (h_dense : Dense (D : Set H))
    (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (h_symm : ∀ ψ φ : D, ⟪(ψ : H), A φ⟫_ℂ = ⟪A ψ, (φ : H)⟫_ℂ)
    {r : ℝ} (hr : 0 < r) (h_unif : ∀ ψ : D, IsAnalyticVector D A hA ψ r)
    (Ω : D) (hAΩ : A Ω = 0) :
    let U := (nelson_global_unitary_group D h_dense A hA h_symm hr h_unif).1
    ∀ t : ℝ, U t (Ω : H) = (Ω : H) := by
  intro U
  have hU0 := (nelson_global_unitary_group D h_dense A hA h_symm hr h_unif).2.1
  exact unitary_fixes_vacuum_of_generator_zero U hU0 (Ω : H) (A Ω) hAΩ
    (fun s => nelson_unitary_hasDerivAt_all D h_dense A hA h_symm hr h_unif Ω s)

end StoneDeriv

end Imscribing.YangMills.NelsonStoneDeriv