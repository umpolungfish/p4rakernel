import Imscribing.YangMills.ClayStatement
import Imscribing.YangMills.AsymptoticFreedomAndOSClosure

/-!
# Dimensional Transmutation, iε Forward-Tube Boundary, & Microcausality Descent
-/

namespace Imscribing.YangMills.DimTransAndBoundary

open scoped InnerProductSpace Topology
open Imscribing.YangMills.ClaySpec
open Imscribing.YangMills.ContinuumInterfaces

/-- **Exact Dimensional Transmutation Scaling along `ymBetaAF`:** -/
theorem ymDimensionalTransmutation_const {N : ℕ} (hN : 2 ≤ N) (m : ℕ) :
    (ymSpacing m)⁻¹ *
      Real.exp (-ymBetaAF N m / (4 * (N : ℝ) * suNOneLoopBeta0 N)) = 1 := by
  have hb0 := suNOneLoopBeta0_pos hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hc : 4 * (N : ℝ) * suNOneLoopBeta0 N ≠ 0 := by positivity
  have ha := ymSpacing_pos m
  unfold ymBetaAF
  have h_arg : -(4 * (N : ℝ) * suNOneLoopBeta0 N * Real.log (1 / ymSpacing m)) /
      (4 * (N : ℝ) * suNOneLoopBeta0 N) = Real.log (ymSpacing m) := by
    rw [neg_div, mul_div_cancel_left₀ _ hc, one_div, Real.log_inv, neg_neg]
  rw [h_arg, Real.exp_log ha, inv_mul_cancel₀ ha.ne']

/-- **Failure of Linear Coupling Scaling:** -/
theorem linearBeta_collapses_to_zero {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun m : ℕ => (ymSpacing m)⁻¹ * Real.exp (-c * ((m : ℝ) + 1)))
      Filter.atTop (𝓝 0) := by
  have h_bound : ∀ m : ℕ,
      (ymSpacing m)⁻¹ * Real.exp (-c * ((m : ℝ) + 1)) ≤
        ((2 / c) ^ 2 * 2) / ((m : ℝ) + 1) := by
    intro m
    have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have ha_inv : (ymSpacing m)⁻¹ = (m : ℝ) + 2 := by
      unfold ymSpacing; rw [one_div, inv_inv]
    rw [ha_inv]
    have h_half : 1 + (c / 2) * ((m : ℝ) + 1) ≤ Real.exp ((c / 2) * ((m : ℝ) + 1)) := by
      linarith [Real.add_one_le_exp ((c / 2) * ((m : ℝ) + 1))]
    have h_exp_sq : (Real.exp ((c / 2) * ((m : ℝ) + 1))) ^ 2 = Real.exp (c * ((m : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h_sq : ((c / 2) * ((m : ℝ) + 1)) ^ 2 ≤ Real.exp (c * ((m : ℝ) + 1)) := by
      have h_le : (c / 2) * ((m : ℝ) + 1) ≤ Real.exp ((c / 2) * ((m : ℝ) + 1)) := by linarith
      have h_nn : 0 ≤ (c / 2) * ((m : ℝ) + 1) := by positivity
      calc
        ((c / 2) * ((m : ℝ) + 1)) ^ 2 ≤ (Real.exp ((c / 2) * ((m : ℝ) + 1))) ^ 2 :=
            pow_le_pow_left₀ h_nn h_le 2
        _ = Real.exp (c * ((m : ℝ) + 1)) := h_exp_sq
    have h_inv_exp : Real.exp (-c * ((m : ℝ) + 1)) = (Real.exp (c * ((m : ℝ) + 1)))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [h_inv_exp]
    have h_m2 : (m : ℝ) + 2 ≤ 2 * ((m : ℝ) + 1) := by
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have h_exp_pos : 0 < Real.exp (c * ((m : ℝ) + 1)) := Real.exp_pos _
    have h_c_pos : 0 < ((c / 2) * ((m : ℝ) + 1)) ^ 2 := by positivity
    calc
      ((m : ℝ) + 2) * (Real.exp (c * ((m : ℝ) + 1)))⁻¹
          ≤ (2 * ((m : ℝ) + 1)) * (((c / 2) * ((m : ℝ) + 1)) ^ 2)⁻¹ := by gcongr
      _ = ((2 / c) ^ 2 * 2) / ((m : ℝ) + 1) := by
            field_simp [hc.ne', hm_pos.ne']
  have h_den : Filter.Tendsto (fun m : ℕ => (m : ℝ) + 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.mpr fun b => Filter.eventually_atTop.mpr ⟨Nat.ceil b, fun m hm => ?_⟩
    have hb : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
    have hm' : (Nat.ceil b : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have h_rhs0 : Filter.Tendsto (fun m : ℕ => ((2 / c) ^ 2 * 2) / ((m : ℝ) + 1))
      Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h_den
  exact squeeze_zero (fun m => mul_nonneg (inv_nonneg.mpr (ymSpacing_pos m).le) (Real.exp_pos _).le)
    h_bound h_rhs0

/-- `i ε`-regularized Minkowski point `z_ε(k) = x(k) + i ε (k + 1) e₀`. -/
def iepsRegularize (n : ℕ) (x : Fin n → ClaySpec.Spacetime4) (ε : ℝ) : Fin n → Fin 4 → ℂ :=
  fun k μ => (x k μ : ℂ) + Complex.I * (ε * ((k : ℕ) + 1 : ℝ) * (if μ = 0 then 1 else 0))

/-- **Forward-Tube Boundary Theorem:** -/
theorem boundary_tube_limit (n : ℕ) (x : Fin n → ClaySpec.Spacetime4) :
    (∀ ε : ℝ, 0 < ε → iepsRegularize n x ε ∈ ForwardTube n) ∧
    Filter.Tendsto (fun ε : ℝ => iepsRegularize n x ε) (𝓝[>] 0)
      (𝓝 (fun k μ => (x k μ : ℂ))) := by
  refine ⟨?_, ?_⟩
  · intro ε hε k
    have him0 : ∀ j : Fin n, (iepsRegularize n x ε j 0).im = ε * ((j : ℕ) + 1 : ℝ) := by
      intro j; simp [iepsRegularize]
    have him_sp : ∀ j : Fin n, ∀ μ : Fin 4, μ ≠ 0 → (iepsRegularize n x ε j μ).im = 0 := by
      intro j μ hμ; simp [iepsRegularize, hμ]
    by_cases hk : (k : ℕ) = 0
    · simp only [hk, ↓reduceDIte, him0, him_sp _ 1 (by decide), him_sp _ 2 (by decide),
        him_sp _ 3 (by decide), Nat.cast_zero, zero_add, mul_one]
      exact ⟨hε, by nlinarith [sq_pos_iff.mpr hε.ne']⟩
    · simp only [hk, ↓reduceDIte, him0, him_sp _ 1 (by decide), him_sp _ 2 (by decide),
        him_sp _ 3 (by decide), sub_zero]
      have hdiff : ε * ((k : ℕ) + 1 : ℝ) - ε * (((k : ℕ) - 1 : ℕ) + 1 : ℝ) = ε := by
        have hk_pos : 1 ≤ (k : ℕ) := Nat.pos_of_ne_zero hk
        have hcast : (((k : ℕ) - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
          exact_mod_cast (Nat.sub_add_cancel hk_pos)
        rw [hcast]; ring
      rw [hdiff]
      exact ⟨hε, by nlinarith [sq_pos_iff.mpr hε.ne']⟩
  · rw [tendsto_pi_nhds]
    intro k
    rw [tendsto_pi_nhds]
    intro μ
    have h_const : Filter.Tendsto (fun _ : ℝ => (x k μ : ℂ)) (𝓝[>] 0) (𝓝 (x k μ : ℂ)) :=
      tendsto_const_nhds
    have h_eps : Filter.Tendsto
        (fun ε : ℝ => Complex.I * (ε * ((k : ℕ) + 1 : ℝ) * (if μ = 0 then (1 : ℂ) else 0)))
        (𝓝[>] 0) (𝓝 0) := by
      by_cases hμ : μ = 0
      · simp only [hμ, ↓reduceIte, mul_one]
        have h0 : Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=
          (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
        simpa using tendsto_const_nhds.mul (h0.mul tendsto_const_nhds)
      · simp only [hμ, ↓reduceIte, mul_zero]
        exact tendsto_const_nhds
    simpa [iepsRegularize] using h_const.add h_eps

/-- Spacelike separation of test functions implies disjoint supports. -/
theorem spacelikeDisjoint_implies_disjoint_supports {f g : TestFn4}
    (h : SpacelikeDisjoint f g) :
    Disjoint (Function.support f) (Function.support g) := by
  rw [Set.disjoint_left]
  intro x hfx hgx
  have hlt := h x x (Function.mem_support.mp hfx) (Function.mem_support.mp hgx)
  simp [minkowskiInner] at hlt

/-- **Microcausality from Weak Matrix Elements on Dense Domain:** -/
theorem microcausality_from_weak_expectation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (fieldDomain : Submodule ℂ H) (h_dense : Dense (fieldDomain : Set H))
    (field : TestFn4 → fieldDomain →ₗ[ℂ] H)
    (field_maps_into : ∀ f (ψ : fieldDomain), field f ψ ∈ fieldDomain)
    {f g : TestFn4}
    (h_weak : ∀ ψ₁ ψ₂ : fieldDomain,
      ⟪(ψ₁ : H), field f ⟨field g ψ₂, field_maps_into g ψ₂⟩⟫_ℂ =
      ⟪(ψ₁ : H), field g ⟨field f ψ₂, field_maps_into f ψ₂⟩⟫_ℂ)
    (ψ : fieldDomain) :
    field f ⟨field g ψ, field_maps_into g ψ⟩ =
    field g ⟨field f ψ, field_maps_into f ψ⟩ := by
  set d : H :=
    field f ⟨field g ψ, field_maps_into g ψ⟩ - field g ⟨field f ψ, field_maps_into f ψ⟩
  have h_orth : ∀ ψ₁ ∈ (fieldDomain : Set H), ⟪ψ₁, d⟫_ℂ = 0 := by
    intro ψ₁ h1
    dsimp [d]
    rw [inner_sub_right, h_weak ⟨ψ₁, h1⟩ ψ, sub_self]
  have h_closed : IsClosed { y : H | ⟪y, d⟫_ℂ = 0 } :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have h_univ : Set.univ ⊆ { y : H | ⟪y, d⟫_ℂ = 0 } := by
    rw [← h_dense.closure_eq]
    exact closure_minimal h_orth h_closed
  have hself : ⟪d, d⟫_ℂ = 0 := h_univ (Set.mem_univ d)
  have hd0 : d = 0 := inner_self_eq_zero.mp hself
  exact sub_eq_zero.mp hd0

end Imscribing.YangMills.DimTransAndBoundary