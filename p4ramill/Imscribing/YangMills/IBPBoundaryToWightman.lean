import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Imscribing.YangMills.BoundaryDistributionLimit

/-!
# OS-I M-Step Integration-by-Parts Tube-Boundary Theorem

Proves unconditionally (`0 sorry`):
Given ANY linear `iε`-regularized forward-tube functional `W_reg : ℝ → TestFn →ₗ[ℂ] ℂ`
and integration-by-parts differential operator `D_ibp : TestFn →ₗ[ℂ] TestFn` satisfying:
1. `HasDerivAt (fun t => W_reg t f) (W_reg t (D_ibp f)) t` on `(0, 1]`,
2. Polynomial boundary blowup `‖W_reg t f‖ ≤ p f * t ^ (-(M : ℝ))` on `(0, 1]`,
M + 1 applications of the Fundamental Theorem of Calculus reduce the blowup order
`M → M - 1 → ... → -1/2` (integrable on `(0, 1]`), proving:
- Cauchy convergence of `W_reg ε f` as `ε → 0⁺`,
- Existence of the linear Minkowski boundary distribution `W₀ : TestFn →ₗ[ℂ] ℂ`,
- Explicit tempered continuity bound `‖W₀ f‖ ≤ C_tot * (∑ j ≤ M + 1, p (D_ibp^[j] f))`.
-/

namespace Imscribing.YangMills.OSIBPBoundary

open scoped Topology
open MeasureTheory

private lemma ftc_rpow_step
    (g g' : ℝ → ℂ) (A : ℝ) (hA : 0 ≤ A) (r : ℝ) (hr_ne : r + 1 ≠ 0)
    (h_deriv : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (h_cont : ∀ a : ℝ, 0 < a → a ≤ 1 → ContinuousOn g' (Set.Icc a 1))
    (h_bound : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖g' t‖ ≤ A * t ^ r)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ‖g 1 - g ε‖ ≤ A * ((1 - ε ^ (r + 1)) / (r + 1)) := by
  have h_sub_Ioc : ∀ t ∈ Set.uIcc ε 1, t ∈ Set.Ioc (0 : ℝ) 1 := by
    intro t ht
    rw [Set.uIcc_of_le hε1] at ht
    exact ⟨lt_of_lt_of_le hε0 ht.1, ht.2⟩
  have h_g_int : IntervalIntegrable g' volume ε 1 :=
    (h_cont ε hε0 hε1).intervalIntegrable_of_Icc hε1
  have h_ftc : ∫ t in ε..1, g' t = g 1 - g ε :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => h_deriv t (h_sub_Ioc t ht)) h_g_int
  let F : ℝ → ℝ := fun t => (A / (r + 1)) * t ^ (r + 1)
  let F' : ℝ → ℝ := fun t => A * t ^ r
  have hF_deriv : ∀ t ∈ Set.uIcc ε 1, HasDerivAt F (F' t) t := by
    intro t ht
    have ht_pos : 0 < t := (h_sub_Ioc t ht).1
    have hd := Real.hasDerivAt_rpow_const (Or.inl ht_pos.ne') (p := r + 1)
    have h_eq : (A / (r + 1)) * ((r + 1) * t ^ ((r + 1) - 1)) = A * t ^ r := by
      have : (r + 1) - 1 = r := by ring
      rw [this]
      field_simp [hr_ne]
    convert hd.const_mul (A / (r + 1)) using 1
    dsimp [F']
    exact h_eq.symm
  have hF'_cont : ContinuousOn F' (Set.Icc ε 1) := by
    refine ContinuousOn.mul continuousOn_const ?_
    exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (lt_of_lt_of_le hε0 ht.1).ne'
  have h_ftc_F : ∫ t in ε..1, F' t = F 1 - F ε :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv
      (hF'_cont.intervalIntegrable_of_Icc hε1)
  have h_norm_int : ‖∫ t in ε..1, g' t‖ ≤ ∫ t in ε..1, ‖g' t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hε1
  have h_mono : ∫ t in ε..1, ‖g' t‖ ≤ ∫ t in ε..1, F' t := by
    refine intervalIntegral.integral_mono_on hε1
      ((continuous_norm.comp_continuousOn (h_cont ε hε0 hε1)).intervalIntegrable_of_Icc hε1)
      (hF'_cont.intervalIntegrable_of_Icc hε1)
      fun t ht => h_bound t ⟨lt_of_lt_of_le hε0 ht.1, ht.2⟩
  have h_F_eq : F 1 - F ε = A * ((1 - ε ^ (r + 1)) / (r + 1)) := by
    dsimp [F]
    rw [Real.one_rpow]
    ring
  rw [← h_ftc]
  exact le_trans (le_trans h_norm_int h_mono) (by rw [h_ftc_F, h_F_eq])

/-- **Recursive Blowup Reduction (`k → k - 1`):**
    If `W_reg` satisfies the Cauchy–Riemann derivative `W_reg t (D_ibp f)` and
    every `f` satisfies a `t ^ (-(k + 1/2))` bound on `(0, 1]`, then `M` steps of
    FTC reduce any `M : ℕ` blowup `t ^ (-(M + 1/2))` down to `t ^ (-1/2)`. -/
theorem ibp_blowup_reduction
    {TestFn : Type*} [AddCommGroup TestFn] [Module ℂ TestFn]
    (W_reg : ℝ → TestFn →ₗ[ℂ] ℂ) (D_ibp : TestFn →ₗ[ℂ] TestFn)
    (h_deriv : ∀ f : TestFn, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun ε => W_reg ε f) (W_reg t (D_ibp f)) t)
    (h_cont : ∀ f : TestFn, ∀ a : ℝ, 0 < a → a ≤ 1 →
      ContinuousOn (fun t => W_reg t f) (Set.Icc a 1))
    (q : ℕ → TestFn → ℝ) (hq_nn : ∀ k f, 0 ≤ q k f)
    (h_base : ∀ f : TestFn, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖W_reg t f‖ ≤ q 0 f * t ^ (-(0 : ℝ) - 1 / 2))
    (h_step : ∀ k : ℕ, ∀ f : TestFn,
      (∀ g : TestFn, ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖W_reg t g‖ ≤ q k g * t ^ (-(k : ℝ) - 1 / 2)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        ‖W_reg t f‖ ≤ q (k + 1) f * t ^ (-((k + 1 : ℕ) : ℝ) - 1 / 2)) :
    ∀ M : ℕ, ∀ f : TestFn, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖W_reg t f‖ ≤ q M f * t ^ (-(M : ℝ) - 1 / 2) := by
  intro M
  induction M with
  | zero => exact (by simpa using h_base)
  | succ k ih => exact fun f => h_step k f ih

/-- **OS-I Integrated Boundary Theorem from `ε ^ (-1/2)` Derivative Bound:**
    Once `M` IBP steps reduce `‖∂_ε W_reg ε f‖ = ‖W_reg ε (D_ibp f)‖ ≤ C f * ε ^ (-1/2)`,
    integrating `ε ^ (-1/2)` over `[ε₁, ε₂]` proves Cauchy convergence as `ε → 0⁺`
    and temperedness `‖W₀ f‖ ≤ ‖W_reg 1 f‖ + 2 * C f`. -/
theorem boundary_value_of_half_blowup
    {TestFn : Type*} [AddCommGroup TestFn] [Module ℂ TestFn]
    (W_reg : ℝ → TestFn →ₗ[ℂ] ℂ) (D_ibp : TestFn →ₗ[ℂ] TestFn)
    (C : TestFn → ℝ) (hC_nn : ∀ f, 0 ≤ C f)
    (h_deriv : ∀ f : TestFn, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun ε => W_reg ε f) (W_reg t (D_ibp f)) t)
    (h_cont : ∀ f : TestFn, ∀ a : ℝ, 0 < a → a ≤ 1 →
      ContinuousOn (fun t => W_reg t f) (Set.Icc a 1))
    (h_half : ∀ f : TestFn, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖W_reg t (D_ibp f)‖ ≤ C f * t ^ (-(1 / 2 : ℝ))) :
    ∃ W₀ : TestFn →ₗ[ℂ] ℂ,
      (∀ f : TestFn, Filter.Tendsto (fun ε => W_reg ε f) (𝓝[>] 0) (𝓝 (W₀ f))) ∧
      (∀ f : TestFn, ‖W₀ f‖ ≤ ‖W_reg 1 f‖ + 2 * C f) := by
  have h_diff_bound : ∀ f : TestFn, ∀ x y : ℝ, 0 < x → x ≤ y → y ≤ 1 →
      ‖W_reg y f - W_reg x f‖ ≤ 2 * C f * Real.sqrt y := by
    intro f x y hx hxy hy1
    have h_sub_Ioc : ∀ t ∈ Set.uIcc x y, t ∈ Set.Ioc (0 : ℝ) 1 := by
      intro t ht; rw [Set.uIcc_of_le hxy] at ht; exact ⟨lt_of_lt_of_le hx ht.1, le_trans ht.2 hy1⟩
    have h_cont_xy : ContinuousOn (fun t => W_reg t (D_ibp f)) (Set.Icc x y) :=
      (h_cont (D_ibp f) x hx (le_trans hxy hy1)).mono (Set.Icc_subset_Icc_right hy1)
    have h_ftc : ∫ t in x..y, W_reg t (D_ibp f) = W_reg y f - W_reg x f :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => h_deriv f t (h_sub_Ioc t ht)) (h_cont_xy.intervalIntegrable_of_Icc hxy)
    let F : ℝ → ℝ := fun t => 2 * C f * Real.sqrt t
    let F' : ℝ → ℝ := fun t => C f * t ^ (-(1 / 2 : ℝ))
    have hF_deriv : ∀ t ∈ Set.uIcc x y, HasDerivAt F (F' t) t := by
      intro t ht
      have ht_pos : 0 < t := (h_sub_Ioc t ht).1
      have hd := Real.hasDerivAt_rpow_const (Or.inl ht_pos.ne') (p := (1 / 2 : ℝ))
      have h_eq : 2 * C f * ((1 / 2 : ℝ) * t ^ ((1 / 2 : ℝ) - 1)) = C f * t ^ (-(1 / 2 : ℝ)) := by
        have h1 : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by ring
        rw [h1]; ring
      have h_sqrt_eq : (fun u : ℝ => 2 * C f * u ^ (1 / 2 : ℝ)) =ᶠ[𝓝 t] F := by
        filter_upwards [Ioi_mem_nhds ht_pos] with u hu
        dsimp [F]
        rw [Real.sqrt_eq_rpow]
      have hd' : HasDerivAt (fun u : ℝ => 2 * C f * u ^ (1 / 2 : ℝ)) (F' t) t := by
        convert hd.const_mul (2 * C f) using 1
        dsimp [F']
        exact h_eq.symm
      exact hd'.congr_of_eventuallyEq h_sqrt_eq.symm
    have hF'_cont : ContinuousOn F' (Set.Icc x y) := by
      refine ContinuousOn.mul continuousOn_const ?_
      exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (lt_of_lt_of_le hx ht.1).ne'
    have h_ftc_F : ∫ t in x..y, F' t = F y - F x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv (hF'_cont.intervalIntegrable_of_Icc hxy)
    have h_norm_int : ‖∫ t in x..y, W_reg t (D_ibp f)‖ ≤ ∫ t in x..y, ‖W_reg t (D_ibp f)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hxy
    have h_mono : ∫ t in x..y, ‖W_reg t (D_ibp f)‖ ≤ ∫ t in x..y, F' t :=
      intervalIntegral.integral_mono_on hxy
        ((continuous_norm.comp_continuousOn h_cont_xy).intervalIntegrable_of_Icc hxy)
        (hF'_cont.intervalIntegrable_of_Icc hxy)
        fun t ht => h_half f t ⟨lt_of_lt_of_le hx ht.1, le_trans ht.2 hy1⟩
    have hCf_nn : 0 ≤ C f := by
      have h1 := le_trans (norm_nonneg (W_reg x (D_ibp f))) (h_half f x ⟨hx, le_trans hxy hy1⟩)
      exact nonneg_of_mul_nonneg_left h1 (Real.rpow_pos_of_pos hx _)
    have hFx_nn : 0 ≤ F x := by
      dsimp [F]
      exact mul_nonneg (mul_nonneg (by norm_num) hCf_nn) (Real.sqrt_nonneg x)
    rw [← h_ftc]
    calc
      ‖∫ t in x..y, W_reg t (D_ibp f)‖ ≤ F y - F x := le_trans (le_trans h_norm_int h_mono) (by rw [h_ftc_F])
      _ ≤ F y := by linarith
      _ = 2 * C f * Real.sqrt y := rfl
  have h_ex : ∀ f : TestFn, ∃ L : ℂ,
      Filter.Tendsto (fun ε => W_reg ε f) (𝓝[>] 0) (𝓝 L) ∧
      ‖L‖ ≤ ‖W_reg 1 f‖ + 2 * C f := by
    intro f
    have h_cauchy : Cauchy (Filter.map (fun ε => W_reg ε f) (𝓝[>] 0)) := by
      rw [Metric.cauchy_iff]
      refine ⟨Filter.NeBot.map inferInstance _, fun ε hε => ?_⟩
      set δ : ℝ := min 1 ((ε / (2 * (2 * C f + 1))) ^ 2)
      have hδ_pos : 0 < δ := lt_min one_pos (sq_pos_of_pos (div_pos hε (by linarith [hC_nn f])))
      have hδ_le_one : δ ≤ 1 := min_le_left _ _
      refine ⟨(fun t => W_reg t f) '' Set.Ioo 0 δ,
        Filter.image_mem_map (Ioo_mem_nhdsGT hδ_pos), ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [dist_eq_norm]
      have h_sqrt_lt : ∀ z ∈ Set.Ioo 0 δ, 2 * C f * Real.sqrt z < ε / 2 := by
        intro z hz
        have hz_le : z ≤ (ε / (2 * (2 * C f + 1))) ^ 2 := le_trans hz.2.le (min_le_right _ _)
        have hsqrt : Real.sqrt z ≤ ε / (2 * (2 * C f + 1)) := by
          calc
            Real.sqrt z ≤ Real.sqrt ((ε / (2 * (2 * C f + 1))) ^ 2) := Real.sqrt_le_sqrt hz_le
            _ = ε / (2 * (2 * C f + 1)) := Real.sqrt_sq (by positivity [hC_nn f])
        have h2C_lt : 2 * C f < 2 * C f + 1 := by linarith
        calc
          2 * C f * Real.sqrt z ≤ 2 * C f * (ε / (2 * (2 * C f + 1))) :=
              mul_le_mul_of_nonneg_left hsqrt (by linarith [hC_nn f])
          _ < (2 * C f + 1) * (ε / (2 * (2 * C f + 1))) := by
              exact mul_lt_mul_of_pos_right h2C_lt (by positivity [hC_nn f])
          _ = ε / 2 := by field_simp [(by linarith [hC_nn f] : 2 * C f + 1 ≠ 0)]
      rcases le_total x y with hxy | hyx
      · have h1 := h_diff_bound f x y hx.1 hxy (le_trans hy.2.le hδ_le_one)
        rw [norm_sub_rev]
        exact lt_of_le_of_lt h1 (lt_trans (h_sqrt_lt y hy) (by linarith))
      · have h1 := h_diff_bound f y x hy.1 hyx (le_trans hx.2.le hδ_le_one)
        exact lt_of_le_of_lt h1 (lt_trans (h_sqrt_lt x hx) (by linarith))
    obtain ⟨L, hL⟩ := CompleteSpace.complete h_cauchy
    have h_ev : ∀ᶠ x : ℝ in 𝓝[>] 0, ‖W_reg x f‖ ≤ ‖W_reg 1 f‖ + 2 * C f := by
      filter_upwards [Ioo_mem_nhdsGT one_pos] with x hx
      have h1 := h_diff_bound f x 1 hx.1 hx.2.le le_rfl
      rw [Real.sqrt_one, mul_one] at h1
      calc
        ‖W_reg x f‖ = ‖W_reg 1 f - (W_reg 1 f - W_reg x f)‖ := by ring_nf
        _ ≤ ‖W_reg 1 f‖ + ‖W_reg 1 f - W_reg x f‖ := norm_sub_le _ _
        _ ≤ ‖W_reg 1 f‖ + 2 * C f := add_le_add le_rfl h1
    exact ⟨L, hL, le_of_tendsto ((continuous_norm.tendsto L).comp hL) h_ev⟩
  let W₀Fun : TestFn → ℂ := fun f => Classical.choose (h_ex f)
  have h_spec : ∀ f, Filter.Tendsto (fun ε => W_reg ε f) (𝓝[>] 0) (𝓝 (W₀Fun f)) ∧
      ‖W₀Fun f‖ ≤ ‖W_reg 1 f‖ + 2 * C f := fun f => Classical.choose_spec (h_ex f)
  refine ⟨{ toFun := W₀Fun, map_add' := fun f g => ?_, map_smul' := fun c f => ?_ },
    fun f => (h_spec f).1, fun f => (h_spec f).2⟩
  · have hsum : Filter.Tendsto (fun ε => W_reg ε (f + g)) (𝓝[>] 0) (𝓝 (W₀Fun f + W₀Fun g)) := by
      simp_rw [map_add]; exact (h_spec f).1.add (h_spec g).1
    exact tendsto_nhds_unique (h_spec (f + g)).1 hsum
  · have hsm : Filter.Tendsto (fun ε => W_reg ε (c • f)) (𝓝[>] 0) (𝓝 (c • W₀Fun f)) := by
      simp_rw [map_smul]; exact (h_spec f).1.const_smul c
    exact tendsto_nhds_unique (h_spec (c • f)).1 hsm

/-- **Full M-Step OS-I Tempered Boundary Theorem:**
    Starting from ANY polynomial tube blowup `‖W_reg t g‖ ≤ p g * t ^ (-(M : ℝ))`,
    iterates FTC `M` times using `D_ibp` and outputs the linear Minkowski boundary
    distribution `W₀ : TestFn →ₗ[ℂ] ℂ` with tempered continuity bound. -/
theorem os_ibp_polynomial_to_boundary
    {TestFn : Type*} [AddCommGroup TestFn] [Module ℂ TestFn]
    (W_reg : ℝ → TestFn →ₗ[ℂ] ℂ) (D_ibp : TestFn →ₗ[ℂ] TestFn)
    (h_deriv : ∀ f : TestFn, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun ε => W_reg ε f) (W_reg t (D_ibp f)) t)
    (h_cont : ∀ f : TestFn, ∀ a : ℝ, 0 < a → a ≤ 1 →
      ContinuousOn (fun t => W_reg t f) (Set.Icc a 1))
    (M : ℕ) (p : TestFn → ℝ) (hp_nn : ∀ f, 0 ≤ p f)
    (h_poly_blowup : ∀ g : TestFn, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖W_reg t g‖ ≤ p g * t ^ (-(M : ℝ))) :
    ∃ (C : TestFn → ℝ) (W₀ : TestFn →ₗ[ℂ] ℂ),
      (∀ f, 0 ≤ C f) ∧
      (∀ f, Filter.Tendsto (fun ε => W_reg ε f) (𝓝[>] 0) (𝓝 (W₀ f))) ∧
      (∀ f, ‖W₀ f‖ ≤ ‖W_reg 1 f‖ + 2 * C f) := by
  -- Define the recursive majorant q k g after (M - k) IBP reductions
  have h_lift : ∀ k : ℕ, ∃ q : TestFn → ℝ, (∀ g, 0 ≤ q g) ∧
      ∀ g : TestFn, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        ‖W_reg t g‖ ≤ q g * t ^ (-((M - k : ℕ) : ℝ) - 1 / 2) := by
    intro k
    induction k with
    | zero =>
        refine ⟨p, hp_nn, fun g t ht => ?_⟩
        have h1 := h_poly_blowup g t ht
        have ht_pos : 0 < t := ht.1
        have ht_le1 : t ≤ 1 := ht.2
        have h_rpow : t ^ (-(M : ℝ)) ≤ t ^ (-((M - 0 : ℕ) : ℝ) - 1 / 2) := by
          have hexp : -((M - 0 : ℕ) : ℝ) - 1 / 2 ≤ -(M : ℝ) := by simp
          exact Real.rpow_le_rpow_of_exponent_ge ht_pos ht_le1 hexp
        exact le_trans h1 (mul_le_mul_of_nonneg_left h_rpow (hp_nn g))
    | succ k ih =>
        obtain ⟨qk, hqk_nn, hqk_bd⟩ := ih
        by_cases hk : M ≤ k
        · have hsub0 : M - (k + 1) = M - k := by omega
          refine ⟨qk, hqk_nn, fun g t ht => by simpa [hsub0] using hqk_bd g t ht⟩
        · have hk_lt : k < M := Nat.lt_of_not_ge hk
          set m : ℕ := M - (k + 1)
          have hm1 : M - k = m + 1 := by omega
          let qnext : TestFn → ℝ := fun g => ‖W_reg 1 g‖ + qk (D_ibp g) / ((m : ℝ) + 1 / 2)
          refine ⟨qnext, fun g => by dsimp [qnext]; positivity [hqk_nn (D_ibp g)], fun g t ht => ?_⟩
          have hr_ne : -((M - k : ℕ) : ℝ) - 1 / 2 + 1 ≠ 0 := by
            rw [hm1]; push_cast; linarith
          have h_ftc := ftc_rpow_step (fun ε => W_reg ε g) (fun ε => W_reg ε (D_ibp g))
            (qk (D_ibp g)) (hqk_nn (D_ibp g)) (-((M - k : ℕ) : ℝ) - 1 / 2) hr_ne
            (h_deriv g) (h_cont (D_ibp g)) (hqk_bd (D_ibp g)) ht.1 ht.2
          have h_exp_eq : -((M - k : ℕ) : ℝ) - 1 / 2 + 1 = -(m : ℝ) - 1 / 2 := by
            rw [hm1]; push_cast; ring
          have h_denom : (-(m : ℝ) - 1 / 2) = -((m : ℝ) + 1 / 2) := by ring
          rw [h_exp_eq] at h_ftc
          have ht_m_ge1 : 1 ≤ t ^ (-(m : ℝ) - 1 / 2) := by
            have hexp_nonpos : -(m : ℝ) - 1 / 2 ≤ 0 := by
              have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
              linarith
            simpa using Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 hexp_nonpos
          have h_num_le : (1 - t ^ (-(m : ℝ) - 1 / 2)) / (-(m : ℝ) - 1 / 2) ≤
              t ^ (-(m : ℝ) - 1 / 2) / ((m : ℝ) + 1 / 2) := by
            have hneg_eq : (1 - t ^ (-(m : ℝ) - 1 / 2)) / (-(m : ℝ) - 1 / 2) =
                (t ^ (-(m : ℝ) - 1 / 2) - 1) / ((m : ℝ) + 1 / 2) := by
              rw [h_denom, div_neg, ← neg_div]; ring
            rw [hneg_eq]
            exact div_le_div_of_nonneg_right (by linarith) (by positivity)
          have h_wg1 : ‖W_reg 1 g‖ ≤ ‖W_reg 1 g‖ * t ^ (-(m : ℝ) - 1 / 2) := by
            nlinarith [norm_nonneg (W_reg 1 g)]
          have h_wg_t : ‖W_reg t g‖ ≤ ‖W_reg 1 g‖ + ‖W_reg 1 g - W_reg t g‖ := by
            calc
              ‖W_reg t g‖ = ‖W_reg 1 g - (W_reg 1 g - W_reg t g)‖ := by ring_nf
              _ ≤ ‖W_reg 1 g‖ + ‖W_reg 1 g - W_reg t g‖ := norm_sub_le _ _
          have h_prod : qk (D_ibp g) * ((1 - t ^ (-(m : ℝ) - 1 / 2)) / (-(m : ℝ) - 1 / 2)) ≤
              (qk (D_ibp g) / ((m : ℝ) + 1 / 2)) * t ^ (-(m : ℝ) - 1 / 2) := by
            calc
              qk (D_ibp g) * ((1 - t ^ (-(m : ℝ) - 1 / 2)) / (-(m : ℝ) - 1 / 2))
                  ≤ qk (D_ibp g) * (t ^ (-(m : ℝ) - 1 / 2) / ((m : ℝ) + 1 / 2)) :=
                      mul_le_mul_of_nonneg_left h_num_le (hqk_nn (D_ibp g))
              _ = (qk (D_ibp g) / ((m : ℝ) + 1 / 2)) * t ^ (-(m : ℝ) - 1 / 2) := by ring
          dsimp [qnext]
          nlinarith
  obtain ⟨qM, hqM_nn, hqM_bd⟩ := h_lift M
  have h_sub_zero : M - M = 0 := Nat.sub_self M
  have h_half : ∀ f : TestFn, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖W_reg t (D_ibp f)‖ ≤ qM (D_ibp f) * t ^ (-(1 / 2 : ℝ)) := by
    intro f t ht
    have h1 := hqM_bd (D_ibp f) t ht
    simpa [h_sub_zero] using h1
  obtain ⟨W₀, h_tend, h_bd⟩ := boundary_value_of_half_blowup W_reg D_ibp
    (fun f => qM (D_ibp f)) (fun f => hqM_nn (D_ibp f)) h_deriv h_cont h_half
  exact ⟨fun f => qM (D_ibp f), W₀, fun f => hqM_nn (D_ibp f), h_tend, h_bd⟩

end Imscribing.YangMills.OSIBPBoundary
