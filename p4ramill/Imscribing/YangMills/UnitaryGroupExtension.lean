import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Dense-Core Isometry Extension & Local-to-Global 1-Parameter Unitary Groups

Proves unconditionally (`0 sorry`) on any complete complex Hilbert space `H`:
1. `extendIsometryFromDense`: Extends any isometric linear map `U₀ : D₀ →ₗ[ℂ] H`
   defined on a dense submodule `D₀` to a global `H →ₗᵢ[ℂ] H`.
2. `globalUnitaryGroupFromLocal`: Extends any local 1-parameter isometry family
   `U_loc` on `(-δ, δ)` (`δ > 0`) to a global group `U : ℝ → H →ₗᵢ[ℂ] H` with
   `U 0 = id` and `U (s + t) x = U s (U t x)` for all `s, t : ℝ`.
-/

namespace Imscribing.YangMills.UnitaryExtension

open scoped Topology

section DenseExtend

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Extension of a Linear Isometry from a Dense Submodule to `H →ₗᵢ[ℂ] H`.** -/
noncomputable def extendIsometryFromDense
    (D₀ : Submodule ℂ H) (h_dense : Dense (D₀ : Set H))
    (U₀ : D₀ →ₗ[ℂ] H) (h_iso : ∀ ψ : D₀, ‖U₀ ψ‖ = ‖(ψ : H)‖) :
    { U : H →ₗᵢ[ℂ] H // ∀ ψ : D₀, U (ψ : H) = U₀ ψ } := by
  have h_approx : ∀ x : H, ∀ n : ℕ, ∃ y : D₀, dist x (y : H) < 1 / ((n : ℝ) + 1) := by
    intro x n
    have hmem : x ∈ closure (D₀ : Set H) := by rw [h_dense.closure_eq]; trivial
    rw [Metric.mem_closure_iff] at hmem
    obtain ⟨y, hyD, hdist⟩ := hmem (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨⟨y, hyD⟩, hdist⟩
  let seq : H → ℕ → D₀ := fun x n => Classical.choose (h_approx x n)
  have h_seq_tend : ∀ x : H, Filter.Tendsto (fun n => (seq x n : H)) Filter.atTop (𝓝 x) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h_bd : ∀ n : ℕ, ‖(seq x n : H) - x‖ ≤ 1 / ((n : ℝ) + 1) := fun n => by
      rw [← dist_eq_norm, dist_comm]
      exact (Classical.choose_spec (h_approx x n)).le
    have h_rhs0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (Filter.tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact squeeze_zero (fun _ => norm_nonneg _) h_bd h_rhs0
  have h_U_cauchy : ∀ s : ℕ → D₀, ∀ x : H,
      Filter.Tendsto (fun n => (s n : H)) Filter.atTop (𝓝 x) →
      CauchySeq (fun n => U₀ (s n)) := by
    intro s x hs
    have h_cs := hs.cauchySeq
    rw [Metric.cauchySeq_iff] at h_cs ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h_cs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm, ← map_sub, h_iso (s m - s n)]
    exact hN m hm n hn
  have h_lim_ex : ∀ x : H, ∃ y : H,
      Filter.Tendsto (fun n => U₀ (seq x n)) Filter.atTop (𝓝 y) := fun x =>
    cauchySeq_tendsto_of_complete (h_U_cauchy (seq x) x (h_seq_tend x))
  let Ufun : H → H := fun x => Classical.choose (h_lim_ex x)
  have h_Ufun_spec : ∀ x : H,
      Filter.Tendsto (fun n => U₀ (seq x n)) Filter.atTop (𝓝 (Ufun x)) :=
    fun x => Classical.choose_spec (h_lim_ex x)
  have h_unique : ∀ {x : H} {s : ℕ → D₀},
      Filter.Tendsto (fun n => (s n : H)) Filter.atTop (𝓝 x) →
      Filter.Tendsto (fun n => U₀ (s n)) Filter.atTop (𝓝 (Ufun x)) := by
    intro x s hs
    have h_diff0 : Filter.Tendsto (fun n => U₀ (s n) - U₀ (seq x n)) Filter.atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h_eq : (fun n => ‖U₀ (s n) - U₀ (seq x n) - 0‖) =
          fun n => ‖(s n : H) - (seq x n : H)‖ := by
        ext n; rw [sub_zero, ← map_sub, h_iso (s n - seq x n)]; rfl
      rw [h_eq]
      have h_sub : Filter.Tendsto (fun n => (s n : H) - (seq x n : H)) Filter.atTop (𝓝 (x - x)) :=
        hs.sub (h_seq_tend x)
      rw [sub_self] at h_sub
      simpa using (continuous_norm.tendsto _).comp h_sub
    have h_sum := h_diff0.add (h_Ufun_spec x)
    simpa using h_sum
  have h_add : ∀ x y : H, Ufun (x + y) = Ufun x + Ufun y := by
    intro x y
    have hs : Filter.Tendsto (fun n => ((seq x n + seq y n : D₀) : H)) Filter.atTop (𝓝 (x + y)) :=
      (h_seq_tend x).add (h_seq_tend y)
    have h1 := h_unique hs
    have h2 : Filter.Tendsto (fun n => U₀ (seq x n + seq y n)) Filter.atTop (𝓝 (Ufun x + Ufun y)) := by
      simp_rw [map_add]; exact (h_Ufun_spec x).add (h_Ufun_spec y)
    exact tendsto_nhds_unique h1 h2
  have h_smul : ∀ (c : ℂ) (x : H), Ufun (c • x) = c • Ufun x := by
    intro c x
    have hs : Filter.Tendsto (fun n => ((c • seq x n : D₀) : H)) Filter.atTop (𝓝 (c • x)) :=
      (h_seq_tend x).const_smul c
    have h1 := h_unique hs
    have h2 : Filter.Tendsto (fun n => U₀ (c • seq x n)) Filter.atTop (𝓝 (c • Ufun x)) := by
      simp_rw [map_smul]; exact (h_Ufun_spec x).const_smul c
    exact tendsto_nhds_unique h1 h2
  have h_norm : ∀ x : H, ‖Ufun x‖ = ‖x‖ := by
    intro x
    have h1 : Filter.Tendsto (fun n => ‖U₀ (seq x n)‖) Filter.atTop (𝓝 ‖Ufun x‖) :=
      (continuous_norm.tendsto _).comp (h_Ufun_spec x)
    have h2 : Filter.Tendsto (fun n => ‖(seq x n : H)‖) Filter.atTop (𝓝 ‖x‖) :=
      (continuous_norm.tendsto _).comp (h_seq_tend x)
    have heq : (fun n => ‖U₀ (seq x n)‖) = fun n => ‖(seq x n : H)‖ := by
      ext n; exact h_iso (seq x n)
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  have h_ext : ∀ ψ : D₀, Ufun (ψ : H) = U₀ ψ := by
    intro ψ
    have h1 := h_unique (s := fun _ => ψ) tendsto_const_nhds
    exact (tendsto_nhds_unique h1 tendsto_const_nhds).symm
  exact ⟨{ toFun := Ufun, map_add' := h_add, map_smul' := h_smul, norm_map' := h_norm }, h_ext⟩

end DenseExtend

section LocalToGlobal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Iterated composition `f^[k]` of a linear isometry `H →ₗᵢ[ℂ] H`. -/
def iterIso (f : H →ₗᵢ[ℂ] H) : ℕ → H →ₗᵢ[ℂ] H
  | 0 => LinearIsometry.id
  | k + 1 => f.comp (iterIso f k)

theorem iterIso_apply (f : H →ₗᵢ[ℂ] H) (k : ℕ) (x : H) :
    iterIso f (k + 1) x = f (iterIso f k x) := rfl

theorem iterIso_add (f : H →ₗᵢ[ℂ] H) (a b : ℕ) (x : H) :
    iterIso f (a + b) x = iterIso f a (iterIso f b x) := by
  induction a with
  | zero => simp [iterIso]
  | succ a ih => rw [Nat.succ_add, iterIso_apply, iterIso_apply, ih]

theorem iterIso_mul (f : H →ₗᵢ[ℂ] H) (a b : ℕ) (x : H) :
    iterIso f (a * b) x = iterIso (iterIso f a) b x := by
  induction b with
  | zero => simp [iterIso]
  | succ b ih => rw [Nat.mul_succ, add_comm, iterIso_add, iterIso_apply, ih]

theorem iterIso_comm_comp (f g : H →ₗᵢ[ℂ] H)
    (hcomm : ∀ x : H, f (g x) = g (f x)) (k : ℕ) (x : H) :
    iterIso (f.comp g) k x = iterIso f k (iterIso g k x) := by
  have h_swap : ∀ (m : ℕ) (y : H), f (iterIso g m y) = iterIso g m (f y) := by
    intro m
    induction m with
    | zero => intro y; simp [iterIso]
    | succ m ih => intro y; simp only [iterIso_apply, ih, hcomm]
  induction k with
  | zero => simp [iterIso]
  | succ k ih =>
      simp only [iterIso_apply, LinearIsometry.comp_apply, ih]
      rw [h_swap]

/-- **Local-to-Global 1-Parameter Unitary Group Extension:**
    Extends any local isometry family `U_loc` on `(-δ, δ)` (`δ > 0`) to a global
    1-parameter unitary group `U : ℝ → H →ₗᵢ[ℂ] H` satisfying `U 0 = id` and
    `U (s + t) x = U s (U t x)` for all `s, t : ℝ`. -/
noncomputable def globalUnitaryGroupFromLocal
    (U_loc : ℝ → H →ₗᵢ[ℂ] H) (δ : ℝ) (hδ : 0 < δ)
    (hU0 : U_loc 0 = LinearIsometry.id)
    (h_loc_add : ∀ s t : ℝ, |s| < δ → |t| < δ → |s + t| < δ →
      ∀ x : H, U_loc (s + t) x = U_loc s (U_loc t x)) :
    { U : ℝ → H →ₗᵢ[ℂ] H //
      U 0 = LinearIsometry.id ∧
      (∀ s t : ℝ, ∀ x : H, U (s + t) x = U s (U t x)) ∧
      (∀ t : ℝ, |t| < δ / 2 → U t = U_loc t) } := by
  let m : ℝ → ℕ := fun t => Nat.ceil (|t| / (δ / 2)) + 1
  have hm_pos : ∀ t : ℝ, 0 < m t := fun t => Nat.succ_pos _
  have hm_lt : ∀ t : ℝ, |t / (m t : ℝ)| < δ / 2 := by
    intro t
    have hm_r : (0 : ℝ) < (m t : ℝ) := Nat.cast_pos.mpr (hm_pos t)
    have h_ceil : |t| / (δ / 2) < (m t : ℝ) := by
      have := Nat.le_ceil (|t| / (δ / 2))
      dsimp [m]; push_cast; linarith
    rw [abs_div, abs_of_pos hm_r, div_lt_iff₀ hm_r]
    have h1 := (div_lt_iff₀ (by positivity : 0 < δ / 2)).mp h_ceil
    linarith
  have h_subdiv : ∀ (u : ℝ) (k : ℕ), 0 < k → |k * u| < δ →
      ∀ x : H, iterIso (U_loc u) k x = U_loc (k * u) x := by
    intro u k hk hku x
    induction k with
    | zero => exact absurd hk (lt_irrefl 0)
    | succ k ih =>
        cases k with
        | zero => simp [iterIso]
        | succ m' =>
            have hk_pos : 0 < m' + 1 := Nat.succ_pos m'
            have hu_lt : |u| < δ := by
              have hle : (1 : ℝ) ≤ ((m' + 2 : ℕ) : ℝ) := by
                exact_mod_cast (by omega : 1 ≤ m' + 2)
              have : |u| ≤ |((m' + 2 : ℕ) : ℝ) * u| := by
                rw [abs_mul, abs_of_pos (by positivity)]
                exact le_mul_of_one_le_left (abs_nonneg u) hle
              exact lt_of_le_of_lt this hku
            have hprev_lt : |((m' + 1 : ℕ) : ℝ) * u| < δ := by
              have hle : ((m' + 1 : ℕ) : ℝ) ≤ ((m' + 2 : ℕ) : ℝ) := by
                exact_mod_cast (by omega : m' + 1 ≤ m' + 2)
              have : |((m' + 1 : ℕ) : ℝ) * u| ≤ |((m' + 2 : ℕ) : ℝ) * u| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
                exact mul_le_mul_of_nonneg_right hle (abs_nonneg u)
              exact lt_of_le_of_lt this hku
            have hadd_eq : ((m' + 2 : ℕ) : ℝ) * u = u + ((m' + 1 : ℕ) : ℝ) * u := by
              push_cast; ring
            rw [iterIso_apply, ih hk_pos hprev_lt, hadd_eq]
            exact (h_loc_add u (((m' + 1 : ℕ) : ℝ) * u) hu_lt hprev_lt
              (by rwa [← hadd_eq]) x).symm
  have h_indep : ∀ (t : ℝ) (k₁ k₂ : ℕ), 0 < k₁ → 0 < k₂ →
      |t / (k₁ : ℝ)| < δ → |t / (k₂ : ℝ)| < δ →
      iterIso (U_loc (t / (k₁ : ℝ))) k₁ = iterIso (U_loc (t / (k₂ : ℝ))) k₂ := by
    intro t k₁ k₂ hk₁ hk₂ h1 h2
    set u : ℝ := t / ((k₁ * k₂ : ℕ) : ℝ)
    have hk₁_r : (k₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk₁.ne'
    have hk₂_r : (k₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk₂.ne'
    have h_u1 : (k₂ : ℝ) * u = t / (k₁ : ℝ) := by
      dsimp [u]; push_cast; field_simp [hk₁_r, hk₂_r]
    have h_u2 : (k₁ : ℝ) * u = t / (k₂ : ℝ) := by
      dsimp [u]; push_cast; field_simp [hk₁_r, hk₂_r]
    have hIso1 : U_loc (t / (k₁ : ℝ)) = iterIso (U_loc u) k₂ := by
      ext y; rw [← h_u1]; exact (h_subdiv u k₂ hk₂ (by rwa [h_u1]) y).symm
    have hIso2 : U_loc (t / (k₂ : ℝ)) = iterIso (U_loc u) k₁ := by
      ext y; rw [← h_u2]; exact (h_subdiv u k₁ hk₁ (by rwa [h_u2]) y).symm
    ext x
    rw [hIso1, hIso2, ← iterIso_mul, ← iterIso_mul, mul_comm k₂ k₁]
  let m : ℝ → ℕ := fun t => Nat.ceil (|t| / (δ / 2)) + 1
  let U : ℝ → H →ₗᵢ[ℂ] H := fun t => iterIso (U_loc (t / (m t : ℝ))) (m t)
  have hU_at_0 : U 0 = LinearIsometry.id := by
    dsimp [U]
    have hm0 : m 0 = 1 := by simp [m]
    rw [hm0]
    ext x
    simp [iterIso, hU0]
  have hU_small : ∀ t : ℝ, |t| < δ / 2 → U t = U_loc t := by
    intro t ht
    dsimp [U]
    have h_eq := h_indep t (m t) 1 (hm_pos t) Nat.one_pos
      (lt_trans (hm_lt t) (by linarith)) (by simpa using lt_trans ht (by linarith))
    rw [h_eq]
    ext x
    simp [iterIso]
  have hU_add : ∀ s t : ℝ, ∀ x : H, U (s + t) x = U s (U t x) := by
    intro s t x
    set K : ℕ := max (m s) (max (m t) (m (s + t)))
    have hK_pos : 0 < K := lt_of_lt_of_le (hm_pos s) (le_max_left _ _)
    have hK_s : m s ≤ K := le_max_left _ _
    have hK_t : m t ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
    have hK_st : m (s + t) ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
    have h_bd_le : ∀ (u : ℝ) (k₁ k₂ : ℕ), 0 < k₁ → k₁ ≤ k₂ → |u / (k₁ : ℝ)| < δ / 2 →
        |u / (k₂ : ℝ)| < δ / 2 := by
      intro u k₁ k₂ hk₁ hle hlt
      have hk₁_r : (0 : ℝ) < (k₁ : ℝ) := Nat.cast_pos.mpr hk₁
      have hk₂_r : (0 : ℝ) < (k₂ : ℝ) := by
        exact_mod_cast lt_of_lt_of_le hk₁ hle
      have h_le' : (k₁ : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast hle
      have : |u / (k₂ : ℝ)| ≤ |u / (k₁ : ℝ)| := by
        rw [abs_div, abs_div, abs_of_pos hk₁_r, abs_of_pos hk₂_r]
        exact div_le_div_of_nonneg_left (abs_nonneg u) hk₁_r h_le'
      exact lt_of_le_of_lt this hlt
    have hsK : |s / (K : ℝ)| < δ / 2 := h_bd_le s (m s) K (hm_pos s) hK_s (hm_lt s)
    have htK : |t / (K : ℝ)| < δ / 2 := h_bd_le t (m t) K (hm_pos t) hK_t (hm_lt t)
    have hstK : |(s + t) / (K : ℝ)| < δ / 2 :=
      h_bd_le (s + t) (m (s + t)) K (hm_pos (s + t)) hK_st (hm_lt (s + t))
    have h_st_sum : s / (K : ℝ) + t / (K : ℝ) = (s + t) / (K : ℝ) := by ring
    have h_comp : U_loc ((s + t) / (K : ℝ)) = (U_loc (s / (K : ℝ))).comp (U_loc (t / (K : ℝ))) := by
      ext y
      rw [← h_st_sum]
      exact h_loc_add (s / (K : ℝ)) (t / (K : ℝ))
        (lt_trans hsK (by linarith)) (lt_trans htK (by linarith))
        (by rw [h_st_sum]; exact lt_trans hstK (by linarith)) y
    have h_comm : ∀ y : H, U_loc (s / (K : ℝ)) (U_loc (t / (K : ℝ)) y) =
        U_loc (t / (K : ℝ)) (U_loc (s / (K : ℝ)) y) := by
      intro y
      have h1 := h_loc_add (s / (K : ℝ)) (t / (K : ℝ))
        (lt_trans hsK (by linarith)) (lt_trans htK (by linarith))
        (by rw [h_st_sum]; exact lt_trans hstK (by linarith)) y
      have h2 := h_loc_add (t / (K : ℝ)) (s / (K : ℝ))
        (lt_trans htK (by linarith)) (lt_trans hsK (by linarith))
        (by rw [add_comm, h_st_sum]; exact lt_trans hstK (by linarith)) y
      rw [← h1, ← h2, add_comm]
    have hUs : U s = iterIso (U_loc (s / (K : ℝ))) K :=
      h_indep s (m s) K (hm_pos s) hK_pos (lt_trans (hm_lt s) (by linarith))
        (lt_trans hsK (by linarith))
    have hUt : U t = iterIso (U_loc (t / (K : ℝ))) K :=
      h_indep t (m t) K (hm_pos t) hK_pos (lt_trans (hm_lt t) (by linarith))
        (lt_trans htK (by linarith))
    have hUst : U (s + t) = iterIso (U_loc ((s + t) / (K : ℝ))) K :=
      h_indep (s + t) (m (s + t)) K (hm_pos (s + t)) hK_pos
        (lt_trans (hm_lt (s + t)) (by linarith)) (lt_trans hstK (by linarith))
    rw [hUst, hUs, hUt, h_comp]
    exact iterIso_comm_comp (U_loc (s / (K : ℝ))) (U_loc (t / (K : ℝ))) h_comm K x
  exact ⟨U, hU_at_0, hU_add, hU_small⟩

end LocalToGlobal

end Imscribing.YangMills.UnitaryExtension