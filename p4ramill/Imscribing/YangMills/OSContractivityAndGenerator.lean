import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Imscribing.YangMills.SemigroupGapBridge

/-!
# OS Repeated-Squaring Contraction & Explicit Semigroup Generator

1. `os_repeated_squaring_contraction`: Symmetry + semigroup law + polynomial bound
   implies `‖T t x‖ ≤ ‖x‖` for all `t ≥ 0` (OS I / Glimm–Jaffe Prop. 6.1.3).
2. Explicit construction of `semigroupGeneratorDomain T : Submodule ℂ H` and
   `semigroupGenerator T : D(H) →ₗ[ℂ] H`, proving symmetry, `H Ω = 0`, global
   non-negativity `0 ≤ Re ⟨ψ, H ψ⟩`, and vacuum uniqueness `ker H = ℂ ∙ Ω`.
-/

namespace Imscribing.YangMills.OSGenerator

open scoped InnerProductSpace Topology

section Contraction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private lemma norm_sq_le_of_symm_semigroup
    (T : ℝ → H →ₗ[ℂ] H)
    (h_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T t y⟫_ℂ = ⟪T t x, y⟫_ℂ)
    (h_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ x : H, T (s + t) x = T s (T t x))
    (x : H) {s : ℝ} (hs : 0 ≤ s) :
    ‖T s x‖ ^ 2 ≤ ‖x‖ * ‖T (2 * s) x‖ := by
  have h_self : ‖T s x‖ ^ 2 = (⟪T s x, T s x⟫_ℂ).re := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have h_shift : ⟪T s x, T s x⟫_ℂ = ⟪x, T (2 * s) x⟫_ℂ := by
    rw [← h_symm s hs x (T s x), ← h_add s s hs hs x, two_mul]
  have h_cs : (⟪x, T (2 * s) x⟫_ℂ).re ≤ ‖x‖ * ‖T (2 * s) x‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm x (T (2 * s) x))
  rw [h_self, h_shift]
  exact h_cs

private lemma norm_pow_two_pow_le
    (T : ℝ → H →ₗ[ℂ] H)
    (h_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T t y⟫_ℂ = ⟪T t x, y⟫_ℂ)
    (h_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ x : H, T (s + t) x = T s (T t x))
    (x : H) :
    ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
      ‖T t x‖ ^ (2 ^ k) ≤ ‖x‖ ^ (2 ^ k - 1) * ‖T ((2 ^ k : ℝ) * t) x‖ := by
  intro k
  induction k with
  | zero =>
      intro t _
      simp
  | succ k ih =>
      intro t ht
      have h2t : 0 ≤ 2 * t := by linarith
      have h1 : ‖T t x‖ ^ 2 ≤ ‖x‖ * ‖T (2 * t) x‖ :=
        norm_sq_le_of_symm_semigroup T h_symm h_add x ht
      have h2 : (‖T t x‖ ^ 2) ^ (2 ^ k) ≤ (‖x‖ * ‖T (2 * t) x‖) ^ (2 ^ k) :=
        pow_le_pow_left₀ (sq_nonneg _) h1 (2 ^ k)
      have h3 := ih (2 * t) h2t
      have hpow_eq : (‖T t x‖ ^ 2) ^ (2 ^ k) = ‖T t x‖ ^ (2 ^ (k + 1)) := by
        rw [← pow_mul, mul_comm, pow_succ]
      have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hexp_eq : 2 ^ k + (2 ^ k - 1) = 2 ^ (k + 1) - 1 := by
        rw [pow_succ]; omega
      have htime_eq : (2 ^ k : ℝ) * (2 * t) = (2 ^ (k + 1) : ℝ) * t := by
        rw [pow_succ]; ring
      calc
        ‖T t x‖ ^ (2 ^ (k + 1)) = (‖T t x‖ ^ 2) ^ (2 ^ k) := hpow_eq.symm
        _ ≤ (‖x‖ * ‖T (2 * t) x‖) ^ (2 ^ k) := h2
        _ = ‖x‖ ^ (2 ^ k) * ‖T (2 * t) x‖ ^ (2 ^ k) := mul_pow _ _ _
        _ ≤ ‖x‖ ^ (2 ^ k) * (‖x‖ ^ (2 ^ k - 1) * ‖T ((2 ^ k : ℝ) * (2 * t)) x‖) := by
              gcongr
        _ = (‖x‖ ^ (2 ^ k) * ‖x‖ ^ (2 ^ k - 1)) * ‖T ((2 ^ (k + 1) : ℝ) * t) x‖ := by
              rw [htime_eq]; ring
        _ = ‖x‖ ^ (2 ^ (k + 1) - 1) * ‖T ((2 ^ (k + 1) : ℝ) * t) x‖ := by
              rw [← pow_add, hexp_eq]

private lemma not_exp_le_poly_two_pow
    {q D : ℝ} (hq : 1 < q) (hD : 0 < D) (m : ℕ) :
    ¬ ∀ k : ℕ, q ^ (2 ^ k) ≤ D * ((2 ^ k : ℕ) : ℝ) ^ m := by
  intro h
  have hlogq : 0 < Real.log q := Real.log_pos hq
  set c : ℝ := Real.log q / (2 * ((m : ℝ) + 1))
  have hc : 0 < c := by positivity
  have hbound : ∀ k : ℕ,
      (2 ^ k : ℝ) * Real.log q ≤
        Real.log D + (m : ℝ) * (c * (2 ^ k : ℝ) - 1 - Real.log c) := by
    intro k
    have hn_pos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hq_pos : 0 < q := lt_trans zero_lt_one hq
    have hqn_pos : 0 < q ^ (2 ^ k) := pow_pos hq_pos _
    have hk_log := Real.log_le_log hqn_pos (h k)
    have hDn_ne : ((2 ^ k : ℕ) : ℝ) ^ m ≠ 0 := pow_ne_zero _ hn_pos.ne'
    rw [Real.log_pow, Real.log_mul hD.ne' hDn_ne, Real.log_pow] at hk_log
    have hy_pos : 0 < c * ((2 ^ k : ℕ) : ℝ) := mul_pos hc hn_pos
    have h_add_one : Real.log (c * ((2 ^ k : ℕ) : ℝ)) + 1 ≤ c * ((2 ^ k : ℕ) : ℝ) := by
      calc
        Real.log (c * ((2 ^ k : ℕ) : ℝ)) + 1
            ≤ Real.exp (Real.log (c * ((2 ^ k : ℕ) : ℝ))) := Real.add_one_le_exp _
        _ = c * ((2 ^ k : ℕ) : ℝ) := Real.exp_log hy_pos
    have h_log_n : Real.log ((2 ^ k : ℕ) : ℝ) ≤ c * ((2 ^ k : ℕ) : ℝ) - 1 - Real.log c := by
      rw [Real.log_mul hc.ne' hn_pos.ne'] at h_add_one
      linarith
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h_cast : ((2 ^ k : ℕ) : ℝ) = (2 ^ k : ℝ) := by push_cast; rfl
    rw [h_cast] at hk_log h_log_n
    nlinarith
  set K : ℝ := Real.log D - (m : ℝ) * (1 + Real.log c)
  have hlin : ∀ k : ℕ, (2 ^ k : ℝ) * (Real.log q / 2) ≤ K := by
    intro k
    have hk := hbound k
    have hmc : (m : ℝ) * c ≤ Real.log q / 2 := by
      dsimp [c]
      have hm1 : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
      have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hdiv : (m : ℝ) / (2 * ((m : ℝ) + 1)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      calc
        (m : ℝ) * (Real.log q / (2 * ((m : ℝ) + 1)))
            = ((m : ℝ) / (2 * ((m : ℝ) + 1))) * Real.log q := by ring
        _ ≤ (1 / 2) * Real.log q := mul_le_mul_of_nonneg_right hdiv hlogq.le
        _ = Real.log q / 2 := by ring
    have hn_nn : (0 : ℝ) ≤ (2 ^ k : ℝ) := by positivity
    have h_split : (m : ℝ) * (c * (2 ^ k : ℝ) - 1 - Real.log c) =
        ((m : ℝ) * c) * (2 ^ k : ℝ) - (m : ℝ) * (1 + Real.log c) := by ring
    rw [h_split] at hk
    have hmc_n : ((m : ℝ) * c) * (2 ^ k : ℝ) ≤ (Real.log q / 2) * (2 ^ k : ℝ) :=
      mul_le_mul_of_nonneg_right hmc hn_nn
    dsimp [K]
    linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * K / Real.log q)
  have h2k_gt : (k : ℝ) < (2 ^ k : ℝ) := by
    exact_mod_cast (Nat.lt_two_pow_self : k < 2 ^ k)
  have hbig : K < (2 ^ k : ℝ) * (Real.log q / 2) := by
    have hk' : 2 * K / Real.log q < (2 ^ k : ℝ) := lt_trans hk h2k_gt
    calc
      K = (2 * K / Real.log q) * (Real.log q / 2) := by field_simp [hlogq.ne']
      _ < (2 ^ k : ℝ) * (Real.log q / 2) := mul_lt_mul_of_pos_right hk' (by positivity)
  linarith [hlin k]

/-- **Osterwalder–Schrader Repeated-Squaring Contraction Theorem.**
    Any symmetric semigroup on `H` growing at most polynomially in `t` is
    automatically a contraction semigroup (`‖T t x‖ ≤ ‖x‖`). -/
theorem os_repeated_squaring_contraction
    (T : ℝ → H →ₗ[ℂ] H)
    (h_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T t y⟫_ℂ = ⟪T t x, y⟫_ℂ)
    (h_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ x : H, T (s + t) x = T s (T t x))
    (h_poly : ∀ x : H, ∃ C r : ℝ, 0 < C ∧ 0 ≤ r ∧ ∀ t ≥ 0, ‖T t x‖ ≤ C * (1 + t) ^ r) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : H, ‖T t x‖ ≤ ‖x‖ := by
  intro t ht x
  by_cases hx : ‖x‖ = 0
  · have h1 := norm_sq_le_of_symm_semigroup T h_symm h_add x ht
    rw [hx, zero_mul] at h1
    have hzero : ‖T t x‖ = 0 := by nlinarith [norm_nonneg (T t x)]
    linarith
  · have hx_pos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    by_contra hlt
    push_neg at hlt
    set q : ℝ := ‖T t x‖ / ‖x‖
    have hq : 1 < q := (one_lt_div hx_pos).mpr hlt
    obtain ⟨C, r, hC, hr, hCbound⟩ := h_poly x
    set m : ℕ := Nat.ceil r
    have hr_le : r ≤ (m : ℝ) := Nat.le_ceil r
    set D : ℝ := (C / ‖x‖) * (1 + t) ^ m
    have hD : 0 < D := by positivity
    refine not_exp_le_poly_two_pow hq hD m (fun k => ?_)
    have hpow := norm_pow_two_pow_le T h_symm h_add x k t ht
    have h2kt_nn : 0 ≤ (2 ^ k : ℝ) * t := by positivity
    have hbound := hCbound ((2 ^ k : ℝ) * t) h2kt_nn
    have h1_le_2k : (1 : ℝ) ≤ (2 ^ k : ℝ) := by
      exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ k)
    have hbase_ge : 1 ≤ 1 + (2 ^ k : ℝ) * t := by linarith
    have hr_mono : (1 + (2 ^ k : ℝ) * t) ^ r ≤ (1 + (2 ^ k : ℝ) * t) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase_ge hr_le
    have hm_le : 1 + (2 ^ k : ℝ) * t ≤ (1 + t) * ((2 ^ k : ℕ) : ℝ) := by
      have hcast : ((2 ^ k : ℕ) : ℝ) = (2 ^ k : ℝ) := by push_cast; rfl
      rw [hcast]
      nlinarith
    have hpow_m : (1 + (2 ^ k : ℝ) * t) ^ (m : ℝ) ≤ ((1 + t) * ((2 ^ k : ℕ) : ℝ)) ^ m := by
      rw [Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) hm_le m
    have hC_m : ‖T ((2 ^ k : ℝ) * t) x‖ ≤ C * ((1 + t) * ((2 ^ k : ℕ) : ℝ)) ^ m :=
      le_trans hbound (mul_le_mul_of_nonneg_left (le_trans hr_mono hpow_m) hC.le)
    have hx_pow_pos : 0 < ‖x‖ ^ (2 ^ k) := pow_pos hx_pos _
    have hx_split : ‖x‖ ^ (2 ^ k - 1) = ‖x‖ ^ (2 ^ k) / ‖x‖ := by
      have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [eq_div_iff hx_pos.ne', ← pow_succ, Nat.sub_add_cancel hk1]
    rw [div_pow, div_le_iff₀ hx_pow_pos]
    calc
      ‖T t x‖ ^ (2 ^ k) ≤ ‖x‖ ^ (2 ^ k - 1) * ‖T ((2 ^ k : ℝ) * t) x‖ := hpow
      _ ≤ ‖x‖ ^ (2 ^ k - 1) * (C * ((1 + t) * ((2 ^ k : ℕ) : ℝ)) ^ m) := by gcongr
      _ = (‖x‖ ^ (2 ^ k) / ‖x‖) * (C * ((1 + t) ^ m * ((2 ^ k : ℕ) : ℝ) ^ m)) := by
            rw [hx_split, mul_pow]
      _ = D * ((2 ^ k : ℕ) : ℝ) ^ m * ‖x‖ ^ (2 ^ k) := by
            dsimp [D]; ring

end Contraction

section Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Infinitesimal generator domain D(H) = { ψ | lim_{t→0⁺} (ψ - T t ψ)/t exists }. -/
def semigroupGeneratorDomain (T : ℝ → H →ₗ[ℂ] H) : Submodule ℂ H where
  carrier := { ψ : H | ∃ Hψ : H,
    Filter.Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (ψ - T t ψ)) (𝓝[>] 0) (𝓝 Hψ) }
  zero_mem' := ⟨0, by
    simpa [map_zero, sub_zero, smul_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : H)) (𝓝[>] 0) (𝓝 0))⟩
  add_mem' := by
    rintro x y ⟨Hx, hHx⟩ ⟨Hy, hHy⟩
    refine ⟨Hx + Hy, ?_⟩
    have heq : (fun t : ℝ => (t⁻¹ : ℂ) • ((x + y) - T t (x + y))) =
        (fun t : ℝ => (t⁻¹ : ℂ) • (x - T t x) + (t⁻¹ : ℂ) • (y - T t y)) := by
      ext t
      rw [map_add, add_sub_add_comm, smul_add]
    rw [heq]
    exact hHx.add hHy
  smul_mem' := by
    rintro c x ⟨Hx, hHx⟩
    refine ⟨c • Hx, ?_⟩
    have heq : (fun t : ℝ => (t⁻¹ : ℂ) • (c • x - T t (c • x))) =
        (fun t : ℝ => c • ((t⁻¹ : ℂ) • (x - T t x))) := by
      ext t
      rw [map_smul, ← smul_sub, smul_comm]
    rw [heq]
    exact hHx.const_smul c

/-- The infinitesimal generator H_op : D(H) →ₗ[ℂ] H. -/
noncomputable def semigroupGenerator (T : ℝ → H →ₗ[ℂ] H) :
    semigroupGeneratorDomain T →ₗ[ℂ] H where
  toFun ψ := Classical.choose ψ.prop
  map_add' x y := by
    have hx := Classical.choose_spec x.prop
    have hy := Classical.choose_spec y.prop
    have hxy := Classical.choose_spec (x + y).prop
    have hsum : Filter.Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • ((x + y : H) - T t (x + y : H)))
        (𝓝[>] 0) (𝓝 (Classical.choose x.prop + Classical.choose y.prop)) := by
      have heq : (fun t : ℝ => (t⁻¹ : ℂ) • ((x + y : H) - T t (x + y : H))) =
          (fun t : ℝ => (t⁻¹ : ℂ) • (x - T t x) + (t⁻¹ : ℂ) • (y - T t y)) := by
        ext t
        rw [map_add, add_sub_add_comm, smul_add]
      rw [heq]
      exact hx.add hy
  map_smul' c x := by
    have hx := Classical.choose_spec x.prop
    have hcx := Classical.choose_spec (c • x).prop
    have hsm : Filter.Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (c • (x : H) - T t (c • (x : H))))
        (𝓝[>] 0) (𝓝 (c • Classical.choose x.prop)) := by
      have heq : (fun t : ℝ => (t⁻¹ : ℂ) • (c • (x : H) - T t (c • (x : H)))) =
          (fun t : ℝ => c • ((t⁻¹ : ℂ) • (x - T t x))) := by
        ext t
        rw [map_smul, ← smul_sub, smul_comm]
      rw [heq]
      exact hx.const_smul c

theorem semigroupGenerator_tendsto (T : ℝ → H →ₗ[ℂ] H) (ψ : semigroupGeneratorDomain T) :
    Filter.Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • ((ψ : H) - T t ψ))
      (𝓝[>] 0) (𝓝 (semigroupGenerator T ψ)) :=
  Classical.choose_spec ψ.prop

theorem vacuum_mem_semigroupGeneratorDomain
    (T : ℝ → H →ₗ[ℂ] H) (Ω : H) (hT_vac : ∀ t : ℝ, 0 ≤ t → T t Ω = Ω) :
    Ω ∈ semigroupGeneratorDomain T := by
  refine ⟨0, ?_⟩
  have heq : ∀ᶠ t : ℝ in 𝓝[>] 0, (t⁻¹ : ℂ) • (Ω - T t Ω) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [hT_vac t ht.le, sub_self, smul_zero]
  exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)

theorem semigroupGenerator_vacuum
    (T : ℝ → H →ₗ[ℂ] H) (Ω : H) (hT_vac : ∀ t : ℝ, 0 ≤ t → T t Ω = Ω) :
    semigroupGenerator T ⟨Ω, vacuum_mem_semigroupGeneratorDomain T Ω hT_vac⟩ = 0 := by
  have h1 := semigroupGenerator_tendsto T ⟨Ω, vacuum_mem_semigroupGeneratorDomain T Ω hT_vac⟩
  have h2 : Filter.Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (Ω - T t Ω)) (𝓝[>] 0) (𝓝 0) := by
    have heq : ∀ᶠ t : ℝ in 𝓝[>] 0, (t⁻¹ : ℂ) • (Ω - T t Ω) = 0 := by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [hT_vac t ht.le, sub_self, smul_zero]
    exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)
  exact tendsto_nhds_unique h1 h2

/-- Symmetry of the semigroup generator `⟪ψ, H φ⟫ = ⟪H ψ, φ⟫` on `D(H)`. -/
theorem semigroupGenerator_symm
    (T : ℝ → H →ₗ[ℂ] H)
    (h_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T t y⟫_ℂ = ⟪T t x, y⟫_ℂ)
    (ψ φ : semigroupGeneratorDomain T) :
    ⟪(ψ : H), semigroupGenerator T φ⟫_ℂ = ⟪semigroupGenerator T ψ, (φ : H)⟫_ℂ := by
  have h_lhs : Filter.Tendsto
      (fun t : ℝ => ⟪(ψ : H), (t⁻¹ : ℂ) • ((φ : H) - T t φ)⟫_ℂ)
      (𝓝[>] 0) (𝓝 ⟪(ψ : H), semigroupGenerator T φ⟫_ℂ) :=
    ((innerSL ℂ (ψ : H)).continuous.tendsto _).comp (semigroupGenerator_tendsto T φ)
  have h_rhs : Filter.Tendsto
      (fun t : ℝ => ⟪(t⁻¹ : ℂ) • ((ψ : H) - T t ψ), (φ : H)⟫_ℂ)
      (𝓝[>] 0) (𝓝 ⟪semigroupGenerator T ψ, (φ : H)⟫_ℂ) := by
    have hcont : Continuous (fun x : H => ⟪x, (φ : H)⟫_ℂ) := continuous_id.inner continuous_const
    exact (hcont.tendsto _).comp (semigroupGenerator_tendsto T ψ)
  have h_eq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ⟪(ψ : H), (t⁻¹ : ℂ) • ((φ : H) - T t φ)⟫_ℂ =
        ⟪(t⁻¹ : ℂ) • ((ψ : H) - T t ψ), (φ : H)⟫_ℂ := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [inner_smul_right, inner_smul_left, inner_sub_right, inner_sub_left]
    have hstar : star (t⁻¹ : ℂ) = (t⁻¹ : ℂ) := by
      change star (t⁻¹ : ℂ) = (t⁻¹ : ℂ)
      exact Complex.conj_ofReal _
    rw [hstar, h_symm t ht.le (ψ : H) (φ : H)]
  exact tendsto_nhds_unique h_lhs (h_rhs.congr' (h_eq.mono fun _ h => h.symm))

/-- **Global gap + non-negativity + vacuum uniqueness for the explicit generator.** -/
theorem semigroupGenerator_gap_and_nonneg
    (T : ℝ → H →ₗ[ℂ] H) (Ω : H) (hΩ : ‖Ω‖ = 1) (Δ : ℝ) (hΔ : 0 < Δ)
    (hT_vac : ∀ t : ℝ, 0 ≤ t → T t Ω = Ω)
    (h_symm : ∀ t : ℝ, 0 ≤ t → ∀ x y : H, ⟪x, T t y⟫_ℂ = ⟪T t x, y⟫_ℂ)
    (hT_decay : ∀ t : ℝ, 0 ≤ t → ∀ φ : H, ⟪Ω, φ⟫_ℂ = 0 →
      ‖T t φ‖ ≤ Real.exp (-Δ * t) * ‖φ‖) :
    (∀ ψ : semigroupGeneratorDomain T, ⟪Ω, (ψ : H)⟫_ℂ = 0 →
      Δ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), semigroupGenerator T ψ⟫_ℂ).re) ∧
    (∀ ψ : semigroupGeneratorDomain T,
      0 ≤ (⟪(ψ : H), semigroupGenerator T ψ⟫_ℂ).re) ∧
    (∀ ψ : semigroupGeneratorDomain T,
      semigroupGenerator T ψ = 0 → ∃ c : ℂ, (ψ : H) = c • Ω) := by
  have h_gap_orth : ∀ ψ : semigroupGeneratorDomain T, ⟪Ω, (ψ : H)⟫_ℂ = 0 →
      Δ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), semigroupGenerator T ψ⟫_ℂ).re := by
    intro ψ h_orth
    exact SemigroupGapBridge.generator_gap_of_semigroup_decay T Ω Δ hT_decay h_orth
      (semigroupGenerator_tendsto T ψ)
  have h_nonneg : ∀ ψ : semigroupGeneratorDomain T,
      0 ≤ (⟪(ψ : H), semigroupGenerator T ψ⟫_ℂ).re := by
    intro ψ
    set c : ℂ := ⟪Ω, (ψ : H)⟫_ℂ
    set Ω_mem : semigroupGeneratorDomain T :=
      ⟨Ω, vacuum_mem_semigroupGeneratorDomain T Ω hT_vac⟩
    set φ : semigroupGeneratorDomain T := ψ - c • Ω_mem
    have hφ_orth : ⟪Ω, (φ : H)⟫_ℂ = 0 := by
      simp only [φ, Submodule.coe_sub, Submodule.coe_smul, Ω_mem,
        inner_sub_right, inner_smul_right, c]
      have h1 : ⟪Ω, Ω⟫_ℂ = (1 : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, hΩ]; norm_num
      rw [h1]
      ring
    have hH_vac : semigroupGenerator T Ω_mem = 0 := semigroupGenerator_vacuum T Ω hT_vac
    have hH_eq : semigroupGenerator T φ = semigroupGenerator T ψ := by
      simp [φ, map_sub, map_smul, hH_vac]
    have h_orth_H : ⟪Ω, semigroupGenerator T φ⟫_ℂ = 0 := by
      rw [semigroupGenerator_symm T h_symm Ω_mem φ]
      change ⟪semigroupGenerator T Ω_mem, (φ : H)⟫_ℂ = 0
      rw [hH_vac, inner_zero_left]
    have h_inner_eq : ⟪(ψ : H), semigroupGenerator T ψ⟫_ℂ = ⟪(φ : H), semigroupGenerator T φ⟫_ℂ := by
      have hψ_split : (ψ : H) = c • Ω + (φ : H) := by
        simp [φ, Ω_mem]
      rw [hψ_split, ← hH_eq, inner_add_left, inner_smul_left, h_orth_H, mul_zero, zero_add]
    rw [h_inner_eq]
    have h_lb := h_gap_orth φ hφ_orth
    have h_pos : 0 ≤ Δ * ‖(φ : H)‖ ^ 2 := by positivity
    linarith
  have h_ker : ∀ ψ : semigroupGeneratorDomain T,
      semigroupGenerator T ψ = 0 → ∃ c : ℂ, (ψ : H) = c • Ω := by
    intro ψ hzero
    set c : ℂ := ⟪Ω, (ψ : H)⟫_ℂ
    set Ω_mem : semigroupGeneratorDomain T :=
      ⟨Ω, vacuum_mem_semigroupGeneratorDomain T Ω hT_vac⟩
    set φ : semigroupGeneratorDomain T := ψ - c • Ω_mem
    have hφ_orth : ⟪Ω, (φ : H)⟫_ℂ = 0 := by
      simp only [φ, Submodule.coe_sub, Submodule.coe_smul, Ω_mem,
        inner_sub_right, inner_smul_right, c]
      have h1 : ⟪Ω, Ω⟫_ℂ = (1 : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, hΩ]; norm_num
      rw [h1]; ring
    have hH_vac : semigroupGenerator T Ω_mem = 0 := semigroupGenerator_vacuum T Ω hT_vac
    have hH_φ : semigroupGenerator T φ = 0 := by
      simp [φ, map_sub, map_smul, hH_vac, hzero]
    have h_lb := h_gap_orth φ hφ_orth
    rw [hH_φ, inner_zero_right, Complex.zero_re] at h_lb
    have hnorm0 : ‖(φ : H)‖ = 0 := by nlinarith [norm_nonneg (φ : H)]
    have hφ0 : (φ : H) = 0 := norm_eq_zero.mp hnorm0
    exact ⟨c, sub_eq_zero.mp (by simpa [φ, Ω_mem] using hφ0)⟩
  exact ⟨h_gap_orth, h_nonneg, h_ker⟩

end Generator

end Imscribing.YangMills.OSGenerator