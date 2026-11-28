import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Transfer-Matrix → Continuum Contraction Semigroup & Gap Survival

Proves unconditionally (`0 sorry`):
1. `thermodynamic_clustering_persistence`: uniform-in-volume exponential decay
   survives the thermodynamic limit `L → ∞`.
2. `discrete_semigroup_to_continuum`: discrete transfer powers `T_m^[⌊t / a_m⌋]`
   converging strongly as `a_m → 0⁺` yield a symmetric contraction semigroup `T(t)`.
3. `continuum_gap_survival`: uniform lattice mass gap `Δ ≤ gap_m / a_m` passes
   to `‖T t φ‖ ≤ exp (-Δ * t) * ‖φ‖` for all `φ ⊥ Ω`.
-/

namespace Imscribing.YangMills.TransferSemigroup

open scoped InnerProductSpace Topology

/-- **Thermodynamic Limit Persistence:** Uniform finite-volume clustering rate
    `Δ > 0` passes to the infinite-volume limit `L → ∞`. -/
theorem thermodynamic_clustering_persistence
    {α : Type*} (S_vol : ℕ → α → ℂ) (S_inf : α → ℂ) (C : α → ℝ) (dist : α → ℝ) (Δ : ℝ)
    (h_lim : ∀ x : α, Filter.Tendsto (fun L : ℕ => S_vol L x) Filter.atTop (𝓝 (S_inf x)))
    (h_unif : ∀ x : α, ∀ᶠ L : ℕ in Filter.atTop,
      ‖S_vol L x‖ ≤ C x * Real.exp (-Δ * dist x)) :
    ∀ x : α, ‖S_inf x‖ ≤ C x * Real.exp (-Δ * dist x) := by
  intro x
  have h_norm : Filter.Tendsto (fun L : ℕ => ‖S_vol L x‖) Filter.atTop (𝓝 ‖S_inf x‖) :=
    (continuous_norm.tendsto _).comp (h_lim x)
  exact le_of_tendsto h_norm (h_unif x)

section ContinuumTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private lemma spacing_mul_floor_tendsto
    (a : ℕ → ℝ) (ha_pos : ∀ m, 0 < a m)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0))
    {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto (fun m : ℕ => a m * (Nat.floor (t / a m) : ℝ)) Filter.atTop (nhds t) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h_bound : ∀ m : ℕ, ‖a m * (Nat.floor (t / a m) : ℝ) - t‖ ≤ a m := by
    intro m
    have hm_pos := ha_pos m
    have h1 : (Nat.floor (t / a m) : ℝ) ≤ t / a m :=
      Nat.floor_le (div_nonneg ht hm_pos.le)
    have h2 : t / a m < (Nat.floor (t / a m) : ℝ) + 1 :=
      Nat.lt_floor_add_one (t / a m)
    have h_le : a m * (Nat.floor (t / a m) : ℝ) ≤ t := by
      have := mul_le_mul_of_nonneg_left h1 hm_pos.le
      rwa [mul_div_cancel₀ t hm_pos.ne'] at this
    have h_gt : t - a m < a m * (Nat.floor (t / a m) : ℝ) := by
      have := mul_lt_mul_of_pos_left h2 hm_pos
      rw [mul_div_cancel₀ t hm_pos.ne', mul_add, mul_one] at this
      linarith
    rw [Real.norm_of_nonpos (sub_nonpos.mpr h_le)]
    linarith
  exact squeeze_zero (fun _ => norm_nonneg _) h_bound ha_lim

/-- **Discrete-to-Continuum Transfer-Matrix Semigroup Theorem.**
    Along `a_m → 0⁺`, strong convergence of `T_m^[⌊t / a_m⌋]` to `T t` with
    `T_m^[1] x → x` yields a contractive, symmetric, Ω-preserving semigroup `T`. -/
theorem discrete_semigroup_to_continuum
    (a : ℕ → ℝ) (ha_pos : ∀ m, 0 < a m)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0))
    (T_lat : ℕ → H →L[ℂ] H)
    (hT_contr : ∀ m (x : H), ‖T_lat m x‖ ≤ ‖x‖)
    (hT_symm : ∀ m (x y : H), ⟪x, T_lat m y⟫_ℂ = ⟪T_lat m x, y⟫_ℂ)
    (Ω : H) (hT_vac : ∀ m, T_lat m Ω = Ω)
    (T : ℝ → H →L[ℂ] H)
    (h_conv : ∀ t : ℝ, 0 ≤ t → ∀ x : H,
      Filter.Tendsto (fun m : ℕ => ((T_lat m) ^ (Nat.floor (t / a m))) x)
        Filter.atTop (𝓝 (T t x)))
    (h_step : ∀ x : H, Filter.Tendsto (fun m : ℕ => T_lat m x - x) Filter.atTop (𝓝 0)) :
    (∀ t : ℝ, 0 ≤ t → T t Ω = Ω) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T t y⟫_ℂ = ⟪T t x, y⟫_ℂ) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ x : H, ‖T t x‖ ≤ ‖x‖) ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ x : H, T (s + t) x = T s (T t x)) := by
  have hpow_contr : ∀ m (k : ℕ) (x : H), ‖((T_lat m) ^ k) x‖ ≤ ‖x‖ := by
    intro m k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', ContinuousLinearMap.mul_apply]
        exact le_trans (hT_contr m _) (ih x)
  have hpow_symm : ∀ m (k : ℕ) (x y : H),
      ⟪x, ((T_lat m) ^ k) y⟫_ℂ = ⟪((T_lat m) ^ k) x, y⟫_ℂ := by
    intro m k
    induction k with
    | zero => intro x y; simp
    | succ k ih =>
        intro x y
        rw [pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
        rw [hT_symm m, ih]
        congr 1
        rw [← ContinuousLinearMap.mul_apply, ← pow_succ, pow_succ', ContinuousLinearMap.mul_apply]
  have hpow_vac : ∀ m (k : ℕ), ((T_lat m) ^ k) Ω = Ω := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, hT_vac m]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    have h1 := h_conv t ht Ω
    have h_const : Filter.Tendsto (fun m : ℕ => ((T_lat m) ^ Nat.floor (t / a m)) Ω)
        Filter.atTop (𝓝 Ω) := by
      simp_rw [hpow_vac]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h_const
  · intro t ht x y
    have hx := h_conv t ht x
    have hy := h_conv t ht y
    have h_lhs : Filter.Tendsto (fun m : ℕ => ⟪x, ((T_lat m) ^ Nat.floor (t / a m)) y⟫_ℂ)
        Filter.atTop (𝓝 ⟪x, T t y⟫_ℂ) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h_le : ∀ m : ℕ, ‖⟪x, ((T_lat m) ^ Nat.floor (t / a m)) y⟫_ℂ - ⟪x, T t y⟫_ℂ‖ ≤
          ‖x‖ * ‖((T_lat m) ^ Nat.floor (t / a m)) y - T t y‖ := fun m => by
        rw [← inner_sub_right]
        exact norm_inner_le_norm x _
      have h_mul : Filter.Tendsto (fun m : ℕ => ‖x‖ * ‖((T_lat m) ^ Nat.floor (t / a m)) y - T t y‖)
          Filter.atTop (𝓝 (‖x‖ * 0)) :=
        (tendsto_const_nhds (x := ‖x‖)).mul (tendsto_iff_norm_sub_tendsto_zero.mp hy)
      rw [mul_zero] at h_mul
      exact squeeze_zero (fun _ => norm_nonneg _) h_le h_mul
    have h_rhs : Filter.Tendsto (fun m : ℕ => ⟪((T_lat m) ^ Nat.floor (t / a m)) x, y⟫_ℂ)
        Filter.atTop (𝓝 ⟪T t x, y⟫_ℂ) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h_le : ∀ m : ℕ, ‖⟪((T_lat m) ^ Nat.floor (t / a m)) x, y⟫_ℂ - ⟪T t x, y⟫_ℂ‖ ≤
          ‖((T_lat m) ^ Nat.floor (t / a m)) x - T t x‖ * ‖y‖ := fun m => by
        rw [← inner_sub_left]
        exact norm_inner_le_norm _ y
      have h_mul : Filter.Tendsto (fun m : ℕ => ‖((T_lat m) ^ Nat.floor (t / a m)) x - T t x‖ * ‖y‖)
          Filter.atTop (𝓝 (0 * ‖y‖)) :=
        (tendsto_iff_norm_sub_tendsto_zero.mp hx).mul (tendsto_const_nhds (x := ‖y‖))
      rw [zero_mul] at h_mul
      exact squeeze_zero (fun _ => norm_nonneg _) h_le h_mul
    have h_eq : (fun m : ℕ => ⟪x, ((T_lat m) ^ Nat.floor (t / a m)) y⟫_ℂ) =
        fun m : ℕ => ⟪((T_lat m) ^ Nat.floor (t / a m)) x, y⟫_ℂ := by
      ext m; exact hpow_symm m _ x y
    rw [h_eq] at h_lhs
    exact tendsto_nhds_unique h_lhs h_rhs
  · intro t ht x
    have h_norm : Filter.Tendsto (fun m : ℕ => ‖((T_lat m) ^ Nat.floor (t / a m)) x‖)
        Filter.atTop (𝓝 ‖T t x‖) :=
      (continuous_norm.tendsto _).comp (h_conv t ht x)
    exact le_of_tendsto h_norm (Filter.Eventually.of_forall fun m => hpow_contr m _ x)
  · intro s t hs ht x
    have hst : 0 ≤ s + t := add_nonneg hs ht
    have h_lhs := h_conv (s + t) hst x
    have h_rhs : Filter.Tendsto (fun m : ℕ =>
        ((T_lat m) ^ Nat.floor (s / a m)) (((T_lat m) ^ Nat.floor (t / a m)) x))
        Filter.atTop (𝓝 (T s (T t x))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h_split : ∀ m : ℕ,
          ‖((T_lat m) ^ Nat.floor (s / a m)) (((T_lat m) ^ Nat.floor (t / a m)) x) - T s (T t x)‖ ≤
            ‖((T_lat m) ^ Nat.floor (t / a m)) x - T t x‖ +
            ‖((T_lat m) ^ Nat.floor (s / a m)) (T t x) - T s (T t x)‖ := by
        intro m
        have h_tri := norm_add_le
          (((T_lat m) ^ Nat.floor (s / a m)) (((T_lat m) ^ Nat.floor (t / a m)) x - T t x))
          (((T_lat m) ^ Nat.floor (s / a m)) (T t x) - T s (T t x))
        have h_eq : ((T_lat m) ^ Nat.floor (s / a m)) (((T_lat m) ^ Nat.floor (t / a m)) x - T t x) +
            (((T_lat m) ^ Nat.floor (s / a m)) (T t x) - T s (T t x)) =
            ((T_lat m) ^ Nat.floor (s / a m)) (((T_lat m) ^ Nat.floor (t / a m)) x) - T s (T t x) := by
          rw [map_sub]; abel
        rw [h_eq] at h_tri
        exact le_trans h_tri (add_le_add (hpow_contr m _ _) le_rfl)
      have h_t0 : Filter.Tendsto (fun m : ℕ => ‖((T_lat m) ^ Nat.floor (t / a m)) x - T t x‖)
          Filter.atTop (𝓝 0) := by
        simpa [tendsto_iff_norm_sub_tendsto_zero] using h_conv t ht x
      have h_s0 : Filter.Tendsto (fun m : ℕ => ‖((T_lat m) ^ Nat.floor (s / a m)) (T t x) - T s (T t x)‖)
          Filter.atTop (𝓝 0) := by
        simpa [tendsto_iff_norm_sub_tendsto_zero] using h_conv s hs (T t x)
      exact squeeze_zero (fun _ => norm_nonneg _) h_split (by simpa using h_t0.add h_s0)
    have h_diff : Filter.Tendsto (fun m : ℕ =>
        ((T_lat m) ^ Nat.floor ((s + t) / a m)) x -
        ((T_lat m) ^ Nat.floor (s / a m)) (((T_lat m) ^ Nat.floor (t / a m)) x))
        Filter.atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h_bound : ∀ m : ℕ,
          ‖(((T_lat m) ^ Nat.floor ((s + t) / a m)) x -
            ((T_lat m) ^ Nat.floor (s / a m)) (((T_lat m) ^ Nat.floor (t / a m)) x)) - 0‖ ≤
            ‖T_lat m x - x‖ := by
        intro m
        rw [sub_zero]
        have hm := ha_pos m
        set ks := Nat.floor (s / a m)
        set kt := Nat.floor (t / a m)
        set kst := Nat.floor ((s + t) / a m)
        have h_lo : (ks + kt : ℝ) ≤ (s + t) / a m := by
          have hs1 : (ks : ℝ) ≤ s / a m := Nat.floor_le (div_nonneg hs hm.le)
          have ht1 : (kt : ℝ) ≤ t / a m := Nat.floor_le (div_nonneg ht hm.le)
          rw [add_div]; linarith
        have h_hi : (s + t) / a m < (ks + kt : ℝ) + 2 := by
          have hs2 : s / a m < (ks : ℝ) + 1 := Nat.lt_floor_add_one (s / a m)
          have ht2 : t / a m < (kt : ℝ) + 1 := Nat.lt_floor_add_one (t / a m)
          rw [add_div]; linarith
        have hk_ge : ks + kt ≤ kst := by
          apply Nat.le_floor
          exact_mod_cast h_lo
        have hk_lt : kst < ks + kt + 2 := by
          have h1 : (kst : ℝ) ≤ (s + t) / a m := Nat.floor_le (div_nonneg hst hm.le)
          have h2 : (kst : ℝ) < ((ks + kt + 2 : ℕ) : ℝ) := by
            push_cast; linarith
          exact Nat.cast_lt.mp h2
        have hcomp : ((T_lat m) ^ ks) (((T_lat m) ^ kt) x) = ((T_lat m) ^ (ks + kt)) x := by
          rw [pow_add, ContinuousLinearMap.mul_apply]
        rw [hcomp]
        have h_cases : kst = ks + kt ∨ kst = ks + kt + 1 := by omega
        rcases h_cases with heq | heq
        · rw [heq, sub_self, norm_zero]; exact norm_nonneg _
        · rw [heq, pow_succ, ContinuousLinearMap.mul_apply, ← map_sub]
          exact hpow_contr m (ks + kt) ((T_lat m) x - x)
      have h_step_norm : Filter.Tendsto (fun m : ℕ => ‖T_lat m x - x‖) Filter.atTop (𝓝 0) := by
        simpa using (continuous_norm.tendsto _).comp (h_step x)
      exact squeeze_zero (fun _ => norm_nonneg _) h_bound h_step_norm
    have h_sub_lim : Filter.Tendsto (fun m : ℕ =>
        ((T_lat m) ^ Nat.floor ((s + t) / a m)) x -
        ((T_lat m) ^ Nat.floor (s / a m)) (((T_lat m) ^ Nat.floor (t / a m)) x))
        Filter.atTop (𝓝 (T (s + t) x - T s (T t x))) := h_lhs.sub h_rhs
    exact sub_eq_zero.mp (tendsto_nhds_unique h_sub_lim h_diff)

/-- **Uniform Mass-Gap Survival Under Continuum Scaling Limit.**
    If `Δ ≤ gap m / a m` along `a_m → 0⁺` and `T_m^[⌊t / a_m⌋] φ → T t φ`, then
    `‖T t φ‖ ≤ exp (-Δ * t) * ‖φ‖` for all `φ ⊥ Ω`. -/
theorem continuum_gap_survival
    (a gap : ℕ → ℝ) (ha_pos : ∀ m, 0 < a m)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0))
    (Δ : ℝ) (h_gap_unif : ∀ m, Δ ≤ gap m / a m)
    (T_lat : ℕ → H →L[ℂ] H) (Ω : H)
    (h_lat_decay : ∀ m (k : ℕ) (φ : H), ⟪Ω, φ⟫_ℂ = 0 →
      ‖((T_lat m) ^ k) φ‖ ≤ Real.exp (-gap m * (k : ℝ)) * ‖φ‖)
    (T : ℝ → H →L[ℂ] H)
    (h_conv : ∀ t : ℝ, 0 ≤ t → ∀ φ : H,
      Filter.Tendsto (fun m : ℕ => ((T_lat m) ^ (Nat.floor (t / a m))) φ)
        Filter.atTop (𝓝 (T t φ))) :
    ∀ t : ℝ, 0 ≤ t → ∀ φ : H, ⟪Ω, φ⟫_ℂ = 0 →
      ‖T t φ‖ ≤ Real.exp (-Δ * t) * ‖φ‖ := by
  intro t ht φ hφ
  have h_lhs : Filter.Tendsto (fun m : ℕ => ‖((T_lat m) ^ (Nat.floor (t / a m))) φ‖)
      Filter.atTop (𝓝 ‖T t φ‖) :=
    (continuous_norm.tendsto _).comp (h_conv t ht φ)
  have h_rhs : Filter.Tendsto
      (fun m : ℕ => Real.exp (-Δ * (a m * (Nat.floor (t / a m) : ℝ))) * ‖φ‖)
      Filter.atTop (𝓝 (Real.exp (-Δ * t) * ‖φ‖)) := by
    have h_t := spacing_mul_floor_tendsto a ha_pos ha_lim ht
    have h_exp : Filter.Tendsto
        (fun m : ℕ => Real.exp (-Δ * (a m * (Nat.floor (t / a m) : ℝ))))
        Filter.atTop (𝓝 (Real.exp (-Δ * t))) :=
      (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul h_t)
    exact h_exp.mul_const ‖φ‖
  have h_ev : ∀ m : ℕ,
      ‖((T_lat m) ^ (Nat.floor (t / a m))) φ‖ ≤
        Real.exp (-Δ * (a m * (Nat.floor (t / a m) : ℝ))) * ‖φ‖ := by
    intro m
    have h_dec := h_lat_decay m (Nat.floor (t / a m)) φ hφ
    have h_exp_le : Real.exp (-gap m * (Nat.floor (t / a m) : ℝ)) ≤
        Real.exp (-Δ * (a m * (Nat.floor (t / a m) : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hm := ha_pos m
      have h_mul : Δ * a m ≤ gap m := (le_div_iff₀ hm).mp (h_gap_unif m)
      have h_k : (0 : ℝ) ≤ (Nat.floor (t / a m) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact le_trans h_dec (mul_le_mul_of_nonneg_right h_exp_le (norm_nonneg φ))
  exact le_of_tendsto_of_tendsto h_lhs h_rhs (Filter.Eventually.of_forall h_ev)

end ContinuumTransfer

end Imscribing.YangMills.TransferSemigroup
