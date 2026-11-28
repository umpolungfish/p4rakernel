import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section

namespace Imscribing.YangMills.BoundaryLimit

open Filter Topology

/-- Bootstrapped MVT bound: if `g : ℝ → E` satisfies `HasDerivAt g (g' t) t` with
`‖g' t‖ ≤ C * t ^ (-p)` on `(0, δ)` for `0 ≤ p < 1`, then for `0 < a ≤ b < δ`,
`‖g b - g a‖ ≤ (C / (1 - p)) * (b ^ (1 - p) - a ^ (1 - p))`. -/
theorem norm_sub_le_rpow_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g g' : ℝ → E} {δ C p : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (h_deriv : ∀ t ∈ Set.Ioo 0 δ, HasDerivAt g (g' t) t)
    (h_bound : ∀ t ∈ Set.Ioo 0 δ, ‖g' t‖ ≤ C * t ^ (-p))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < δ) :
    ‖g b - g a‖ ≤ (C / (1 - p)) * (b ^ (1 - p) - a ^ (1 - p)) := by
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have h_cont_g : ContinuousOn g (Set.Icc a b) := by
    intro t ht
    have ht_oo : t ∈ Set.Ioo 0 δ := ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
    exact (h_deriv t ht_oo).continuousAt.continuousWithinAt
  have h_rpow_deriv : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => s ^ (1 - p)) ((1 - p) * t ^ (-p)) t := by
    intro t ht
    have hd := Real.hasDerivAt_rpow_const (p := 1 - p) (Or.inl ht.ne')
    simpa [sub_sub_cancel_left] using hd
  have h_cont_rpow : ContinuousOn (fun t : ℝ => t ^ (1 - p)) (Set.Icc a b) := by
    intro t ht
    exact (h_rpow_deriv t (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt
  suffices h_eps : ∀ ε > 0,
      ‖g b - g a‖ ≤ (C / (1 - p)) * (b ^ (1 - p) - a ^ (1 - p)) + ε * (b - a) by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hba : b = a
    · subst hba
      simp only [sub_self, norm_zero, mul_zero, zero_add]
      exact hε.le
    · have hba_pos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab (Ne.symm hba))
      have h1 := h_eps (ε / (b - a)) (div_pos hε hba_pos)
      rwa [div_mul_cancel₀ _ hba_pos.ne'] at h1
  intro ε hε
  let φ : ℝ → ℝ := fun t => (C / (1 - p)) * (t ^ (1 - p) - a ^ (1 - p)) + ε * (t - a)
  let S : Set ℝ := Set.Icc a b ∩ (fun t => ‖g t - g a‖ - φ t) ⁻¹' Set.Iic 0
  have ha_mem : a ∈ S := ⟨⟨le_rfl, hab⟩, by
    change ‖g a - g a‖ - φ a ≤ 0
    simp only [φ, sub_self, norm_zero, mul_zero, add_zero, sub_zero]
    exact le_rfl⟩
  have hS_closed : IsClosed S := by
    have hcont_sub : ContinuousOn (fun t => ‖g t - g a‖ - φ t) (Set.Icc a b) :=
      (h_cont_g.sub continuousOn_const).norm.sub
        (ContinuousOn.add
          (continuousOn_const.mul (h_cont_rpow.sub continuousOn_const))
          (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
    exact hcont_sub.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hS_bdd : BddAbove S := ⟨b, fun _ ht => ht.1.2⟩
  let c : ℝ := sSup S
  have hc_mem : c ∈ S := hS_closed.csSup_mem ⟨a, ha_mem⟩ hS_bdd
  have hc_le : c ≤ b := hc_mem.1.2
  have hc_ge : a ≤ c := hc_mem.1.1
  have hc_ineq : ‖g c - g a‖ ≤ φ c := sub_nonpos.mp hc_mem.2
  by_contra! h_gt
  have hc_lt : c < b := lt_of_le_of_ne hc_le (fun hcb => by
    rw [hcb] at hc_ineq
    exact not_le_of_gt h_gt hc_ineq)
  have hc_oo : c ∈ Set.Ioo 0 δ := ⟨lt_of_lt_of_le ha hc_ge, lt_trans hc_lt hb⟩
  have hc_pos : 0 < c := hc_oo.1
  have h_deriv_g := h_deriv c hc_oo
  have h_deriv_φ : HasDerivAt φ (C * c ^ (-p) + ε) c := by
    have hr := (h_rpow_deriv c hc_pos).sub_const (a ^ (1 - p))
    have hmul := hr.const_mul (C / (1 - p))
    have he := ((hasDerivAt_id c).sub_const a).const_mul ε
    convert hmul.add he using 1
    rw [← mul_assoc, div_mul_cancel₀ _ h1p.ne', mul_one]
  have hg_close : ∀ᶠ t in 𝓝[>] c, ‖g t - g c‖ ≤ (‖g' c‖ + ε / 4) * (t - c) := by
    have h_diff := h_deriv_g.isLittleO
    have h_ev := h_diff.bound (show 0 < ε / 4 by linarith)
    filter_upwards [nhdsWithin_le_nhds h_ev, self_mem_nhdsWithin] with t ht ht_gt
    have htc : 0 < t - c := sub_pos.mpr ht_gt
    have h1 := norm_sub_norm_le (g t - g c) ((t - c) • g' c)
    have h2 : ‖(t - c) • g' c‖ = (t - c) * ‖g' c‖ := by
      rw [norm_smul, Real.norm_of_nonneg htc.le]
    have h3 : ‖g t - g c - (t - c) • g' c‖ ≤ ε / 4 * ‖t - c‖ := ht
    rw [Real.norm_of_nonneg htc.le] at h3
    nlinarith [h1, h2, h3]
  have hφ_close : ∀ᶠ t in 𝓝[>] c, (C * c ^ (-p) + ε / 2) * (t - c) ≤ φ t - φ c := by
    have h_diff := h_deriv_φ.isLittleO
    have h_ev := h_diff.bound (show 0 < ε / 2 by linarith)
    filter_upwards [nhdsWithin_le_nhds h_ev, self_mem_nhdsWithin] with t ht ht_gt
    have htc : 0 < t - c := sub_pos.mpr ht_gt
    have h1 : ‖φ t - φ c - (t - c) * (C * c ^ (-p) + ε)‖ ≤ ε / 2 * ‖t - c‖ := by
      simpa [smul_eq_mul] using ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htc, abs_le] at h1
    nlinarith [h1.1]
  have hIoo : ∀ᶠ t in 𝓝[>] c, t ∈ Set.Ioo c b := Ioo_mem_nhdsGT hc_lt
  obtain ⟨t, ht_oo, hgt, hφt⟩ := (hIoo.and (hg_close.and hφ_close)).exists
  have ht_mem : t ∈ S := by
    refine ⟨⟨le_trans hc_ge ht_oo.1.le, ht_oo.2.le⟩, ?_⟩
    change ‖g t - g a‖ - φ t ≤ 0
    rw [sub_nonpos]
    have htc : 0 < t - c := sub_pos.mpr ht_oo.1
    have hbnd := h_bound c hc_oo
    have h_tri : ‖g t - g a‖ ≤ ‖g t - g c‖ + ‖g c - g a‖ := by
      simpa using norm_add_le (g t - g c) (g c - g a)
    have h_step : (‖g' c‖ + ε / 4) * (t - c) ≤ (C * c ^ (-p) + ε / 2) * (t - c) := by
      gcongr; linarith
    linarith [h_tri, hgt, hφt, hc_ineq, h_step]
  exact absurd (le_csSup hS_bdd ht_mem) (not_le_of_gt ht_oo.1)

/-- Existence and norm bound of the `ε → 0⁺` boundary limit from a polynomially singular
derivative bound `‖g' t‖ ≤ C * t ^ (-p)` with `0 ≤ p < 1`. -/
theorem boundary_value_of_deriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g g' : ℝ → E} {δ C p : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (h_deriv : ∀ t ∈ Set.Ioo 0 δ, HasDerivAt g (g' t) t)
    (h_bound : ∀ t ∈ Set.Ioo 0 δ, ‖g' t‖ ≤ C * t ^ (-p)) :
    ∃ L : E, Filter.Tendsto g (𝓝[>] 0) (𝓝 L) ∧
      ∀ t ∈ Set.Ioo 0 δ, ‖L - g t‖ ≤ (C / (1 - p)) * t ^ (1 - p) := by
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  haveI : (𝓝[>] (0 : ℝ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_Ioi]; exact Set.self_mem_Ici)
  have h_cauchy : Cauchy (Filter.map g (𝓝[>] 0)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    have hcoeff : 0 < C / (1 - p) + 1 := by positivity
    let r : ℝ := min (δ / 2) ((ε / (2 * (C / (1 - p) + 1))) ^ (1 / (1 - p)))
    have hr_pos : 0 < r := lt_min (half_pos hδ) (Real.rpow_pos_of_pos (by positivity) _)
    refine ⟨g '' Set.Ioo 0 r, Filter.mem_map.mpr (Filter.mem_of_superset (Ioo_mem_nhdsGT hr_pos)
      (fun t ht => ⟨t, ht, rfl⟩)), ?_⟩
    rintro _ ⟨t₁, ht₁, rfl⟩ _ ⟨t₂, ht₂, rfl⟩
    wlog h12 : t₁ ≤ t₂ generalizing t₁ t₂
    · rw [dist_comm]
      exact this t₂ ht₂ t₁ ht₁ (le_of_not_ge h12)
    have ht₂_lt : t₂ < δ := lt_of_lt_of_le ht₂.2 (le_trans (min_le_left _ _) (half_lt_self hδ).le)
    have hMVT := norm_sub_le_rpow_of_hasDerivAt hδ hC hp0 hp1 h_deriv h_bound ht₁.1 h12 ht₂_lt
    have hr_le : t₂ ^ (1 - p) ≤ r ^ (1 - p) :=
      Real.rpow_le_rpow ht₂.1.le ht₂.2.le h1p.le
    have hr2 : r ^ (1 - p) ≤ ε / (2 * (C / (1 - p) + 1)) := by
      calc r ^ (1 - p)
          ≤ ((ε / (2 * (C / (1 - p) + 1))) ^ (1 / (1 - p))) ^ (1 - p) :=
            Real.rpow_le_rpow hr_pos.le (min_le_right _ _) h1p.le
        _ = ε / (2 * (C / (1 - p) + 1)) := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel h1p.ne', Real.rpow_one]
    have ht₁_nn : 0 ≤ t₁ ^ (1 - p) := Real.rpow_nonneg ht₁.1.le _
    rw [dist_eq_norm, norm_sub_rev]
    calc ‖g t₂ - g t₁‖
        ≤ (C / (1 - p)) * (t₂ ^ (1 - p) - t₁ ^ (1 - p)) := hMVT
      _ ≤ (C / (1 - p)) * t₂ ^ (1 - p) := by gcongr; linarith [ht₁_nn]
      _ ≤ (C / (1 - p)) * (ε / (2 * (C / (1 - p) + 1))) := by gcongr; exact le_trans hr_le hr2
      _ ≤ (C / (1 - p) + 1) * (ε / (2 * (C / (1 - p) + 1))) := by gcongr; linarith
      _ = ε / 2 := by field_simp [hcoeff.ne']
      _ < ε := half_lt_self hε
  obtain ⟨L, hL⟩ := CompleteSpace.complete h_cauchy
  refine ⟨L, hL, fun t ht => ?_⟩
  have h_ev : ∀ᶠ s in 𝓝[>] 0, s ∈ Set.Ioo 0 t := Ioo_mem_nhdsGT ht.1
  have h_le : ∀ᶠ s in 𝓝[>] 0, ‖g t - g s‖ ≤ (C / (1 - p)) * t ^ (1 - p) := by
    filter_upwards [h_ev] with s hs
    have hMVT := norm_sub_le_rpow_of_hasDerivAt hδ hC hp0 hp1 h_deriv h_bound hs.1 hs.2.le ht.2
    have hs_nn : 0 ≤ s ^ (1 - p) := Real.rpow_nonneg hs.1.le _
    calc ‖g t - g s‖ ≤ (C / (1 - p)) * (t ^ (1 - p) - s ^ (1 - p)) := hMVT
      _ ≤ (C / (1 - p)) * t ^ (1 - p) := by gcongr; linarith [hs_nn]
  have h_tend : Filter.Tendsto (fun s => ‖g t - g s‖) (𝓝[>] 0) (𝓝 ‖g t - L‖) :=
    (tendsto_const_nhds.sub hL).norm
  simpa [norm_sub_rev] using le_of_tendsto h_tend h_le

/-- Tempered boundary distribution extracted from a family of continuous linear functionals
on a Schwartz space satisfying a uniform seminorm-controlled singular derivative bound. -/
theorem wightman_boundary_tempered {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W_reg W_deriv : ℝ → SchwartzMap E ℂ →L[ℂ] ℂ)
    {δ : ℝ} (hδ : 0 < δ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    {C : ℝ} (hC : 0 ≤ C) {k m : ℕ}
    (h_deriv : ∀ f : SchwartzMap E ℂ, ∀ t ∈ Set.Ioo 0 δ,
      HasDerivAt (fun s => W_reg s f) (W_deriv t f) t)
    (h_bound : ∀ f : SchwartzMap E ℂ, ∀ t ∈ Set.Ioo 0 δ,
      ‖W_deriv t f‖ ≤ C * (SchwartzMap.seminorm ℂ k m f) * t ^ (-p))
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {k₀ m₀ : ℕ} {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 δ)
    (h_init : ∀ f : SchwartzMap E ℂ, ‖W_reg t₀ f‖ ≤ C₀ * SchwartzMap.seminorm ℂ k₀ m₀ f) :
    ∃ W₀ : SchwartzMap E ℂ →ₗ[ℂ] ℂ,
      (∀ f, Filter.Tendsto (fun t => W_reg t f) (𝓝[>] 0) (𝓝 (W₀ f))) ∧
      (∀ f, ‖W₀ f‖ ≤
        (C / (1 - p)) * t₀ ^ (1 - p) * SchwartzMap.seminorm ℂ k m f +
        C₀ * SchwartzMap.seminorm ℂ k₀ m₀ f) := by
  have h_lim : ∀ f : SchwartzMap E ℂ,
      ∃ L : ℂ, Filter.Tendsto (fun t => W_reg t f) (𝓝[>] 0) (𝓝 L) ∧
        ‖L - W_reg t₀ f‖ ≤ (C * SchwartzMap.seminorm ℂ k m f / (1 - p)) * t₀ ^ (1 - p) := by
    intro f
    have hCf : 0 ≤ C * SchwartzMap.seminorm ℂ k m f :=
      mul_nonneg hC (apply_nonneg (SchwartzMap.seminorm ℂ k m) f)
    obtain ⟨L, hL, hLbd⟩ := boundary_value_of_deriv_bound hδ hCf hp0 hp1
      (h_deriv f) (h_bound f)
    exact ⟨L, hL, hLbd t₀ ht₀⟩
  let W₀Fun : SchwartzMap E ℂ → ℂ := fun f => Classical.choose (h_lim f)
  have hW₀_tend : ∀ f, Filter.Tendsto (fun t => W_reg t f) (𝓝[>] 0) (𝓝 (W₀Fun f)) :=
    fun f => (Classical.choose_spec (h_lim f)).1
  refine ⟨{
    toFun := W₀Fun
    map_add' := fun f g => by
      have h1 := (hW₀_tend f).add (hW₀_tend g)
      have h2 : Filter.Tendsto (fun t => W_reg t (f + g)) (𝓝[>] 0) (𝓝 (W₀Fun f + W₀Fun g)) := by
        simpa [map_add] using h1
      exact tendsto_nhds_unique (hW₀_tend (f + g)) h2
    map_smul' := fun c f => by
      have h1 := (tendsto_const_nhds (x := c)).mul (hW₀_tend f)
      have h2 : Filter.Tendsto (fun t => W_reg t (c • f)) (𝓝[>] 0) (𝓝 (c * W₀Fun f)) := by
        simpa [map_smul, smul_eq_mul] using h1
      exact tendsto_nhds_unique (hW₀_tend (c • f)) h2
  }, hW₀_tend, fun f => ?_⟩
  change ‖W₀Fun f‖ ≤ _
  have h_diff := (Classical.choose_spec (h_lim f)).2
  have h_tri : ‖W₀Fun f‖ ≤ ‖W₀Fun f - W_reg t₀ f‖ + ‖W_reg t₀ f‖ := by
    simpa using norm_add_le (W₀Fun f - W_reg t₀ f) (W_reg t₀ f)
  have h_alg : (C * SchwartzMap.seminorm ℂ k m f / (1 - p)) * t₀ ^ (1 - p) =
      (C / (1 - p)) * t₀ ^ (1 - p) * SchwartzMap.seminorm ℂ k m f := by ring
  linarith [h_tri, h_diff, h_init f, h_alg]

end Imscribing.YangMills.BoundaryLimit
