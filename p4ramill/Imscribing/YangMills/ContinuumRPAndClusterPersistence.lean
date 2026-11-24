import Imscribing.YangMills.MinimalClayReduction

/-!
# Continuum Limit Persistence of Reflection Positivity, Clustering & Variance

Proves unconditionally (`0 sorry`) that if a family of finite-volume/regularized
sesquilinear forms `B_m : BorchersPos → BorchersPos → ℂ` converges pointwise on
`BorchersPos` to `borchersForm C R`, then:
1. Hermitian symmetry (`h_herm`), reflection positivity (`h_rp`), and Euclidean
   time-shift symmetry (`h_symm`) pass automatically to the continuum limit.
2. Exponential clustering (`h_cluster`) passes to the limit **even if finite-volume
   orthogonality `B_m m vac F = 0` holds only asymptotically (`B_m m vac F → 0`)**.
3. Strict connected variance (`variance_strict`) persists from any uniform lower bound.
-/

namespace Imscribing.YangMills.ContinuumPersistence

open scoped Topology
open Imscribing.YangMills.ContinuumInterfaces
open Imscribing.YangMills.BorchersReconstruction
open Imscribing.YangMills.BorchersSchwinger
open Imscribing.YangMills.MinimalReduction

/-- **Continuum Limit Persistence of OS Borchers Axioms.** -/
theorem borchers_axioms_of_lattice_limit
    (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (B_m : ℕ → BorchersPos → BorchersPos → ℂ)
    (h_conv : ∀ F G : BorchersPos,
      Filter.Tendsto (fun m : ℕ => B_m m F G) Filter.atTop (𝓝 (borchersForm C R F G)))
    (h_herm_m : ∀ m F G, B_m m G F = star (B_m m F G))
    (h_rp_m : ∀ m F, 0 ≤ (B_m m F F).re)
    (h_symm_m : ∀ m, ∀ t : ℝ, 0 ≤ t → ∀ F G,
      B_m m F (borchersShift R t G) = B_m m (borchersShift R t F) G)
    (h_lin_m : ∀ m,
      (∀ F₁ F₂ G, B_m m (F₁ + F₂) G = B_m m F₁ G + B_m m F₂ G) ∧
      (∀ c F G, B_m m (c • F) G = star c * B_m m F G) ∧
      (∀ F G₁ G₂, B_m m F (G₁ + G₂) = B_m m F G₁ + B_m m F G₂) ∧
      (∀ c F G, B_m m F (c • G) = c * B_m m F G) ∧
      B_m m borchersVac borchersVac = 1)
    (h_cluster_m : ∀ m, ∀ t : ℝ, 0 ≤ t → ∀ G : BorchersPos,
      B_m m borchersVac G = 0 →
      (B_m m (borchersShift R t G) (borchersShift R t G)).re ≤
        Real.exp (-2 * C.cluster_rate * t) * (B_m m G G).re) :
    (∀ F G, borchersForm C R G F = star (borchersForm C R F G)) ∧
    (∀ F, 0 ≤ (borchersForm C R F F).re) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ F G,
      borchersForm C R F (borchersShift R t G) = borchersForm C R (borchersShift R t F) G) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ F : BorchersPos, borchersForm C R borchersVac F = 0 →
      (borchersForm C R (borchersShift R t F) (borchersShift R t F)).re ≤
        Real.exp (-2 * C.cluster_rate * t) * (borchersForm C R F F).re) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F G
    have h1 := h_conv G F
    have h2 : Filter.Tendsto (fun m : ℕ => star (B_m m F G)) Filter.atTop
        (𝓝 (star (borchersForm C R F G))) :=
      (continuous_star.tendsto _).comp (h_conv F G)
    have heq : (fun m : ℕ => B_m m G F) = fun m : ℕ => star (B_m m F G) := by
      ext m; exact h_herm_m m F G
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  · intro F
    have h1 : Filter.Tendsto (fun m : ℕ => (B_m m F F).re) Filter.atTop
        (𝓝 (borchersForm C R F F).re) :=
      (Complex.continuous_re.tendsto _).comp (h_conv F F)
    exact le_of_tendsto h1 (Filter.Eventually.of_forall fun m => h_rp_m m F)
  · intro t ht F G
    have h1 := h_conv F (borchersShift R t G)
    have h2 := h_conv (borchersShift R t F) G
    have heq : (fun m : ℕ => B_m m F (borchersShift R t G)) =
        fun m : ℕ => B_m m (borchersShift R t F) G := by
      ext m; exact h_symm_m m t ht F G
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  · intro t ht F hF_orth
    let c : ℕ → ℂ := fun m => B_m m borchersVac F
    have hc_lim : Filter.Tendsto c Filter.atTop (𝓝 0) := by
      simpa [c, hF_orth] using h_conv borchersVac F
    let G : ℕ → BorchersPos := fun m => F - c m • borchersVac
    have hG_orth : ∀ m : ℕ, B_m m borchersVac (G m) = 0 := by
      intro m
      obtain ⟨_, _, h_add_r, h_smul_r, h_vac⟩ := h_lin_m m
      have hsub_eq : G m = F + (-c m) • borchersVac := by
        dsimp [G]; rw [sub_eq_add_neg, neg_smul]
      rw [hsub_eq, h_add_r, h_smul_r, h_vac]
      dsimp [c]; ring
    have h_ineq_m : ∀ m : ℕ,
        (B_m m (borchersShift R t (G m)) (borchersShift R t (G m))).re ≤
          Real.exp (-2 * C.cluster_rate * t) * (B_m m (G m) (G m)).re :=
      fun m => h_cluster_m m t ht (G m) (hG_orth m)
    have h_expand_G : ∀ m : ℕ, ∀ X : BorchersPos,
        B_m m (F - c m • borchersVac) (F - c m • borchersVac) =
          B_m m F F - c m * B_m m F borchersVac - star (c m) * B_m m borchersVac F +
            (star (c m) * c m) * B_m m borchersVac borchersVac := by
      intro m _
      obtain ⟨h_add_l, h_smul_l, h_add_r, h_smul_r, _⟩ := h_lin_m m
      have hs : F - c m • borchersVac = F + (-c m) • borchersVac := by
        rw [sub_eq_add_neg, neg_smul]
      rw [hs, h_add_l, h_add_r, h_add_r, h_smul_l, h_smul_r, h_smul_r, h_smul_l, h_smul_r]
      simp only [star_neg]
      ring
    have h_shift_G : ∀ m : ℕ,
        borchersShift R t (G m) = borchersShift R t F - c m • borchersVac := by
      intro m
      dsimp [G]
      rw [map_sub, map_smul, borchersShift_vac R t ht]
    have h_expand_shift : ∀ m : ℕ,
        B_m m (borchersShift R t (G m)) (borchersShift R t (G m)) =
          B_m m (borchersShift R t F) (borchersShift R t F) -
            c m * B_m m (borchersShift R t F) borchersVac -
            star (c m) * B_m m borchersVac (borchersShift R t F) +
            (star (c m) * c m) * B_m m borchersVac borchersVac := by
      intro m
      rw [h_shift_G m]
      obtain ⟨h_add_l, h_smul_l, h_add_r, h_smul_r, _⟩ := h_lin_m m
      have hs : borchersShift R t F - c m • borchersVac =
          borchersShift R t F + (-c m) • borchersVac := by
        rw [sub_eq_add_neg, neg_smul]
      rw [hs, h_add_l, h_add_r, h_add_r, h_smul_l, h_smul_r, h_smul_r, h_smul_l, h_smul_r]
      simp only [star_neg]
      ring
    have h_lhs_tend : Filter.Tendsto
        (fun m : ℕ => (B_m m (borchersShift R t (G m)) (borchersShift R t (G m))).re)
        Filter.atTop (𝓝 (borchersForm C R (borchersShift R t F) (borchersShift R t F)).re) := by
      simp_rw [h_expand_shift]
      have hc_star : Filter.Tendsto (fun m => star (c m)) Filter.atTop (𝓝 0) := by
        simpa using (continuous_star.tendsto 0).comp hc_lim
      have h_t1 := h_conv (borchersShift R t F) (borchersShift R t F)
      have h_t2 : Filter.Tendsto (fun m => c m * B_m m (borchersShift R t F) borchersVac)
          Filter.atTop (𝓝 0) := by
        simpa using hc_lim.mul (h_conv (borchersShift R t F) borchersVac)
      have h_t3 : Filter.Tendsto (fun m => star (c m) * B_m m borchersVac (borchersShift R t F))
          Filter.atTop (𝓝 0) := by
        simpa using hc_star.mul (h_conv borchersVac (borchersShift R t F))
      have h_t4 : Filter.Tendsto (fun m => (star (c m) * c m) * B_m m borchersVac borchersVac)
          Filter.atTop (𝓝 0) := by
        simpa using (hc_star.mul hc_lim).mul (h_conv borchersVac borchersVac)
      have hC := ((h_t1.sub h_t2).sub h_t3).add h_t4
      simpa using (Complex.continuous_re.tendsto _).comp hC
    have h_rhs_tend : Filter.Tendsto
        (fun m : ℕ => Real.exp (-2 * C.cluster_rate * t) * (B_m m (G m) (G m)).re)
        Filter.atTop (𝓝 (Real.exp (-2 * C.cluster_rate * t) * (borchersForm C R F F).re)) := by
      have h_G_tend : Filter.Tendsto (fun m => (B_m m (G m) (G m)).re) Filter.atTop
          (𝓝 (borchersForm C R F F).re) := by
        have h_eq_G : ∀ m : ℕ, B_m m (G m) (G m) =
            B_m m F F - c m * B_m m F borchersVac - star (c m) * B_m m borchersVac F +
              (star (c m) * c m) * B_m m borchersVac borchersVac :=
          fun m => h_expand_G m F
        simp_rw [h_eq_G]
        have hc_star : Filter.Tendsto (fun m => star (c m)) Filter.atTop (𝓝 0) := by
          simpa using (continuous_star.tendsto 0).comp hc_lim
        have h_t1 := h_conv F F
        have h_t2 : Filter.Tendsto (fun m => c m * B_m m F borchersVac) Filter.atTop (𝓝 0) := by
          simpa using hc_lim.mul (h_conv F borchersVac)
        have h_t3 : Filter.Tendsto (fun m => star (c m) * B_m m borchersVac F) Filter.atTop (𝓝 0) := by
          simpa using hc_star.mul (h_conv borchersVac F)
        have h_t4 : Filter.Tendsto (fun m => (star (c m) * c m) * B_m m borchersVac borchersVac)
            Filter.atTop (𝓝 0) := by
          simpa using (hc_star.mul hc_lim).mul (h_conv borchersVac borchersVac)
        have hC := ((h_t1.sub h_t2).sub h_t3).add h_t4
        simpa using (Complex.continuous_re.tendsto _).comp hC
      exact le_of_tendsto_of_tendsto h_lhs_tend h_rhs_tend (Filter.Eventually.of_forall h_ineq_m)

/-- **Strict Connected 2-Point Variance Persistence:**
    Any uniform finite-volume connected variance gap `δ > 0` survives the continuum limit. -/
theorem variance_strict_of_lattice_limit
    (C : ContinuumSchwingerOS) (R : ReflectTensorData)
    (B_m : ℕ → BorchersPos → BorchersPos → ℂ) (v : BorchersPos)
    (h_conv_vac : Filter.Tendsto (fun m => B_m m borchersVac v) Filter.atTop
      (𝓝 (borchersForm C R borchersVac v)))
    (h_conv_self : Filter.Tendsto (fun m => B_m m v v) Filter.atTop
      (𝓝 (borchersForm C R v v)))
    {δ : ℝ} (hδ : 0 < δ)
    (h_var_m : ∀ᶠ m : ℕ in Filter.atTop, ‖B_m m borchersVac v‖ ^ 2 + δ ≤ (B_m m v v).re) :
    ‖borchersForm C R borchersVac v‖ ^ 2 < (borchersForm C R v v).re := by
  have h_lhs : Filter.Tendsto (fun m => ‖B_m m borchersVac v‖ ^ 2 + δ) Filter.atTop
      (𝓝 (‖borchersForm C R borchersVac v‖ ^ 2 + δ)) :=
    (((continuous_norm.tendsto _).comp h_conv_vac).pow 2).add tendsto_const_nhds
  have h_rhs : Filter.Tendsto (fun m => (B_m m v v).re) Filter.atTop
      (𝓝 (borchersForm C R v v).re) :=
    (Complex.continuous_re.tendsto _).comp h_conv_self
  have h_le := le_of_tendsto_of_tendsto h_lhs h_rhs h_var_m
  linarith

end Imscribing.YangMills.ContinuumPersistence