import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Nelson Analytic Vector Exponentiation & Unitary Isometric Flow

Proves unconditionally (`0 sorry`) on any complete complex Hilbert space `H`:
1. `iterA` and `iterA_symm` for any symmetric operator `A : D →ₗ[ℂ] H` preserving `D`.
2. `expSeries_summable`: absolute convergence of `∑' n, ((i t)^n / n!) • A^n ψ`
   for `|t| < r⁻¹` on any analytic vector `‖A^n ψ‖ ≤ M r^n n!`.
3. `expSeries_inner_eq`: exact unitary inner-product preservation
   `⟪expSeries t ψ, expSeries t φ⟫ = ⟪ψ, φ⟫` on analytic vectors via binomial
   cancellation `(it - it)^n = 0` and tail-of-geometric-series convergence.
-/

namespace Imscribing.YangMills.AnalyticVectorExp

open scoped InnerProductSpace Topology BigOperators

section NelsonExp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Iterated operator power `A^n ψ` on an invariant subspace `D`. -/
def iterA (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D) :
    ℕ → D → D
  | 0, ψ => ψ
  | n + 1, ψ => ⟨A (iterA D A hA n ψ), hA _⟩

@[simp]
theorem iterA_zero (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D) (ψ : D) :
    iterA D A hA 0 ψ = ψ := rfl

theorem iterA_succ (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D) (n : ℕ) (ψ : D) :
    (iterA D A hA (n + 1) ψ : H) = A (iterA D A hA n ψ) := rfl

theorem iterA_add (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (a b : ℕ) (ψ : D) :
    iterA D A hA (a + b) ψ = iterA D A hA a (iterA D A hA b ψ) := by
  induction a with
  | zero => simp
  | succ a ih =>
      apply Subtype.ext
      rw [Nat.succ_add, iterA_succ, iterA_succ, ih]

/-- Iterated symmetry `⟪A^j ψ, A^k φ⟫ = ⟪ψ, A^(j+k) φ⟫`. -/
theorem iterA_symm (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (h_symm : ∀ ψ φ : D, ⟪(ψ : H), A φ⟫_ℂ = ⟪A ψ, (φ : H)⟫_ℂ) :
    ∀ j k : ℕ, ∀ ψ φ : D,
      ⟪(iterA D A hA j ψ : H), (iterA D A hA k φ : H)⟫_ℂ =
        ⟪(ψ : H), (iterA D A hA (j + k) φ : H)⟫_ℂ := by
  intro j
  induction j with
  | zero => intro k ψ φ; simp
  | succ j ih =>
      intro k ψ φ
      rw [iterA_succ, ← h_symm (iterA D A hA j ψ) (iterA D A hA k φ),
          ← iterA_succ D A hA k φ, ih (k + 1) ψ φ,
          show j + (k + 1) = (j + 1) + k by omega]

/-- Analytic vector predicate: `‖A^n ψ‖ ≤ M * r^n * n!` with `r > 0`. -/
def IsAnalyticVector (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (ψ : D) (r : ℝ) : Prop :=
  0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖(iterA D A hA n ψ : H)‖ ≤ M * r ^ n * (n.factorial : ℝ)

/-- Exponential power series `∑' n, ((i t)^n / n!) • A^n ψ` for an analytic vector `ψ`. -/
noncomputable def expSeries (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (t : ℝ) (ψ : D) : H :=
  ∑' n : ℕ, ((Complex.I * (t : ℂ)) ^ n / (n.factorial : ℂ)) • (iterA D A hA n ψ : H)

/-- Absolute summability of `expSeries` on `|t| < r⁻¹`. -/
theorem expSeries_summable_norm (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    {ψ : D} {r t : ℝ} (hψ : IsAnalyticVector D A hA ψ r) (ht : r * |t| < 1) :
    Summable (fun n : ℕ =>
      ‖((Complex.I * (t : ℂ)) ^ n / (n.factorial : ℂ)) • (iterA D A hA n ψ : H)‖) := by
  rcases hψ with ⟨hr, M, hM, hbound⟩
  have h_geom : Summable (fun n : ℕ => M * (r * |t|) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) ht).mul_left M
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) h_geom
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rw [norm_smul, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Complex.norm_natCast]
  have h1 := hbound n
  calc
    (|t| ^ n / (n.factorial : ℝ)) * ‖(iterA D A hA n ψ : H)‖
        ≤ (|t| ^ n / (n.factorial : ℝ)) * (M * r ^ n * (n.factorial : ℝ)) := by
            gcongr
    _ = M * (r * |t|) ^ n := by
          rw [mul_pow]; field_simp [hfac_pos.ne']

theorem expSeries_summable (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    {ψ : D} {r t : ℝ} (hψ : IsAnalyticVector D A hA ψ r) (ht : r * |t| < 1) :
    Summable (fun n : ℕ =>
      ((Complex.I * (t : ℂ)) ^ n / (n.factorial : ℂ)) • (iterA D A hA n ψ : H)) :=
  (expSeries_summable_norm D A hA hψ ht).of_norm

private lemma inner_expSeries_partial_eq
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (h_symm : ∀ ψ φ : D, ⟪(ψ : H), A φ⟫_ℂ = ⟪A ψ, (φ : H)⟫_ℂ)
    (t : ℝ) (ψ φ : D) (N : ℕ) :
    let u : ℕ → H := fun j => ((Complex.I * (t : ℂ)) ^ j / (j.factorial : ℂ)) • (iterA D A hA j ψ : H)
    let v : ℕ → H := fun k => ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) • (iterA D A hA k φ : H)
    (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), ⟪u j, v (n - j)⟫_ℂ) =
      if N = 0 then 0 else ⟪(ψ : H), (φ : H)⟫_ℂ := by
  intro u v
  by_cases hN0 : N = 0
  · subst hN0; simp
  · simp only [hN0, ↓reduceIte]
    have h_row : ∀ n : ℕ,
        (∑ j ∈ Finset.range (n + 1), ⟪u j, v (n - j)⟫_ℂ) =
          if n = 0 then ⟪(ψ : H), (φ : H)⟫_ℂ else 0 := by
      intro n
      have h_term : ∀ j ∈ Finset.range (n + 1),
          ⟪u j, v (n - j)⟫_ℂ =
            ((n.choose j : ℂ) * (-Complex.I * (t : ℂ)) ^ j * (Complex.I * (t : ℂ)) ^ (n - j) /
              (n.factorial : ℂ)) * ⟪(ψ : H), (iterA D A hA n φ : H)⟫_ℂ := by
        intro j hj
        have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        dsimp [u, v]
        rw [inner_smul_left, inner_smul_right,
            iterA_symm D A hA h_symm j (n - j) ψ φ, Nat.add_sub_cancel' hj_le]
        have h_star : starRingEnd ℂ ((Complex.I * (t : ℂ)) ^ j / (j.factorial : ℂ)) =
            (-Complex.I * (t : ℂ)) ^ j / (j.factorial : ℂ) := by
          rw [map_div₀, map_pow, map_mul, Complex.conj_ofReal]
          have hI : starRingEnd ℂ Complex.I = -Complex.I := by simp
          have hnat : starRingEnd ℂ (j.factorial : ℂ) = (j.factorial : ℂ) := by simp
          rw [hI, hnat]
        rw [h_star]
        have h_choose : (n.factorial : ℂ) =
            (n.choose j : ℂ) * (j.factorial : ℂ) * ((n - j).factorial : ℂ) := by
          exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hj_le).symm
        have hjf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
        have hnjf : ((n - j).factorial : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - j))
        have hnf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
        have hch : (n.choose j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hj_le).ne'
        rw [h_choose]; field_simp [hjf, hnjf, hnf, hch]
      rw [Finset.sum_congr rfl h_term, ← Finset.sum_mul, ← Finset.sum_div]
      have h_binom : (∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℂ) * (-Complex.I * (t : ℂ)) ^ j * (Complex.I * (t : ℂ)) ^ (n - j)) =
          (-Complex.I * (t : ℂ) + Complex.I * (t : ℂ)) ^ n := by
        rw [add_pow]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [h_binom, show (-Complex.I * (t : ℂ) + Complex.I * (t : ℂ)) = 0 by ring]
      by_cases hn0 : n = 0
      · subst hn0; simp
      · simp [hn0, zero_pow hn0]
    rw [Finset.sum_congr rfl (fun n _ => h_row n)]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro n _ hn; simp [hn]
    · intro h0; exact absurd (Finset.mem_range.mpr (Nat.pos_of_ne_zero hN0)) h0

/-- **Unitary Inner-Product Preservation on Analytic Vectors:**
    For any symmetric `A` and analytic vectors `ψ, φ`,
    `⟪expSeries t ψ, expSeries t φ⟫ = ⟪ψ, φ⟫` on `max r₁ r₂ * |t| < 1`. -/
theorem expSeries_inner_eq
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (h_symm : ∀ ψ φ : D, ⟪(ψ : H), A φ⟫_ℂ = ⟪A ψ, (φ : H)⟫_ℂ)
    {ψ φ : D} {r₁ r₂ t : ℝ}
    (hψ : IsAnalyticVector D A hA ψ r₁) (hφ : IsAnalyticVector D A hA φ r₂)
    (ht₁ : r₁ * |t| < 1) (ht₂ : r₂ * |t| < 1) :
    ⟪expSeries D A hA t ψ, expSeries D A hA t φ⟫_ℂ = ⟪(ψ : H), (φ : H)⟫_ℂ := by
  let u : ℕ → H := fun j => ((Complex.I * (t : ℂ)) ^ j / (j.factorial : ℂ)) • (iterA D A hA j ψ : H)
  let v : ℕ → H := fun k => ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) • (iterA D A hA k φ : H)
  have hu_sum : Summable u := expSeries_summable D A hA hψ ht₁
  have hv_sum : Summable v := expSeries_summable D A hA hφ ht₂
  have hu_norm_sum : Summable (fun j => ‖u j‖) := expSeries_summable_norm D A hA hψ ht₁
  have hv_norm_sum : Summable (fun k => ‖v k‖) := expSeries_summable_norm D A hA hφ ht₂
  have h_partial_tend :
      Filter.Tendsto (fun N : ℕ => ⟪∑ j ∈ Finset.range N, u j, ∑ k ∈ Finset.range N, v k⟫_ℂ)
        Filter.atTop (𝓝 ⟪expSeries D A hA t ψ, expSeries D A hA t φ⟫_ℂ) :=
    Filter.Tendsto.inner (hu_sum.hasSum.tendsto_sum_nat) (hv_sum.hasSum.tendsto_sum_nat)
  -- Compare square partial sum with triangle sum `j + k < N`
  have h_tri_diff :
      Filter.Tendsto (fun N : ℕ =>
        ⟪∑ j ∈ Finset.range N, u j, ∑ k ∈ Finset.range N, v k⟫_ℂ -
        (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), ⟪u j, v (n - j)⟫_ℂ))
        Filter.atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h_tri_eq : ∀ N : ℕ,
        (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), ⟪u j, v (n - j)⟫_ℂ) =
        ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N),
          ⟪u p.1, v p.2⟫_ℂ := by
      intro N
      have h_sigma :
          (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), ⟪u j, v (n - j)⟫_ℂ) =
          ∑ p ∈ (Finset.range N).sigma (fun n => Finset.range (n + 1)),
            ⟪u p.2, v (p.1 - p.2)⟫_ℂ := by rw [Finset.sum_sigma]
      rw [h_sigma]
      refine Finset.sum_bij (fun p _ => (p.2, p.1 - p.2)) ?_ ?_ ?_ ?_
      · rintro ⟨n, j⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨n₁, j₁⟩ h₁ ⟨n₂, j₂⟩ h₂ heq
        simp only [Finset.mem_sigma, Finset.mem_range] at h₁ h₂
        have hj : j₁ = j₂ := congrArg Prod.fst heq
        have hd : n₁ - j₁ = n₂ - j₂ := congrArg Prod.snd heq
        have hn : n₁ = n₂ := by omega
        subst hn; subst hj; rfl
      · rintro ⟨j, k⟩ hjk
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hjk
        refine ⟨⟨j + k, j⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_range]; exact ⟨hjk.2, by omega⟩
        · ext <;> simp
      · rintro ⟨n, j⟩ _; rfl
    have h_sq_eq : ∀ N : ℕ,
        ⟪∑ j ∈ Finset.range N, u j, ∑ k ∈ Finset.range N, v k⟫_ℂ =
        ∑ p ∈ Finset.range N ×ˢ Finset.range N, ⟪u p.1, v p.2⟫_ℂ := by
      intro N
      rw [sum_inner]
      refine (Finset.sum_congr rfl fun j _ => inner_sum _ _ _).trans ?_
      rw [Finset.sum_product]
    have h_bound : ∀ N : ℕ,
        ‖(⟪∑ j ∈ Finset.range N, u j, ∑ k ∈ Finset.range N, v k⟫_ℂ -
          (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), ⟪u j, v (n - j)⟫_ℂ)) - 0‖ ≤
          (∑ j ∈ Finset.Ico (N / 2) N, ‖u j‖) * (∑' k, ‖v k‖) +
          (∑' j, ‖u j‖) * (∑ k ∈ Finset.Ico (N / 2) N, ‖v k‖) := by
      intro N
      rw [sub_zero, h_sq_eq N, h_tri_eq N,
          ← Finset.sum_sdiff_eq_sub (Finset.filter_subset _ _)]
      have h_sub_set :
          (Finset.range N ×ˢ Finset.range N \
              (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N)) ⊆
          (Finset.Ico (N / 2) N ×ˢ Finset.range N) ∪
            (Finset.range N ×ˢ Finset.Ico (N / 2) N) := by
        rintro ⟨j, k⟩ hp
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product,
          Finset.mem_range, not_and, not_lt] at hp
        rcases hp with ⟨⟨hjN, hkN⟩, hjk⟩
        have hge := hjk ⟨hjN, hkN⟩
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
        by_cases hj : N / 2 ≤ j
        · exact Or.inl ⟨⟨hj, hjN⟩, hkN⟩
        · exact Or.inr ⟨hjN, ⟨by omega, hkN⟩⟩
      have h_le1 :
          ‖∑ p ∈ (Finset.range N ×ˢ Finset.range N \
              (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N)),
              ⟪u p.1, v p.2⟫_ℂ‖ ≤
            ∑ p ∈ (Finset.range N ×ˢ Finset.range N \
              (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N)),
              ‖u p.1‖ * ‖v p.2‖ := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
        exact norm_inner_le_norm (u p.1) (v p.2)
      have h_le2 :
          (∑ p ∈ (Finset.range N ×ˢ Finset.range N \
              (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N)),
              ‖u p.1‖ * ‖v p.2‖) ≤
            (∑ p ∈ (Finset.Ico (N / 2) N ×ˢ Finset.range N), ‖u p.1‖ * ‖v p.2‖) +
            (∑ p ∈ (Finset.range N ×ˢ Finset.Ico (N / 2) N), ‖u p.1‖ * ‖v p.2‖) := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg h_sub_set
            (fun _ _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))) ?_
          exact (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (Finset.sum_union_inter (f := fun p : ℕ × ℕ => ‖u p.1‖ * ‖v p.2‖))
      have h_f1 :
          (∑ p ∈ Finset.Ico (N / 2) N ×ˢ Finset.range N, ‖u p.1‖ * ‖v p.2‖) ≤
            (∑ j ∈ Finset.Ico (N / 2) N, ‖u j‖) * (∑' k, ‖v k‖) := by
        rw [Finset.sum_product]; dsimp only
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_left
          (hv_norm_sum.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _))
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      have h_f2 :
          (∑ p ∈ Finset.range N ×ˢ Finset.Ico (N / 2) N, ‖u p.1‖ * ‖v p.2‖) ≤
            (∑' j, ‖u j‖) * (∑ k ∈ Finset.Ico (N / 2) N, ‖v k‖) := by
        rw [Finset.sum_product]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right
          (hu_norm_sum.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _))
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      exact le_trans h_le1 (le_trans h_le2 (add_le_add h_f1 h_f2))
    have h_ico_u : Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.Ico (N / 2) N, ‖u j‖)
        Filter.atTop (𝓝 0) := by
      have h_cau := hu_norm_sum.hasSum.tendsto_sum_nat
      have h_diff_t : Filter.Tendsto
          (fun N : ℕ => (∑ j ∈ Finset.range N, ‖u j‖) - (∑ j ∈ Finset.range (N / 2), ‖u j‖))
          Filter.atTop (𝓝 (∑' j, ‖u j‖ - ∑' j, ‖u j‖)) :=
        h_cau.sub (h_cau.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun n hn => by omega⟩))
      rw [sub_self] at h_diff_t
      have h_eq : (fun N : ℕ => ∑ j ∈ Finset.Ico (N / 2) N, ‖u j‖) =
          fun N : ℕ => (∑ j ∈ Finset.range N, ‖u j‖) - (∑ j ∈ Finset.range (N / 2), ‖u j‖) := by
        ext N
        simp only [Finset.range_eq_Ico]
        linarith [Finset.sum_Ico_consecutive (fun j => ‖u j‖) (Nat.zero_le (N / 2)) (Nat.div_le_self N 2)]
      rwa [h_eq]
    have h_ico_v : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ico (N / 2) N, ‖v k‖)
        Filter.atTop (𝓝 0) := by
      have h_cau := hv_norm_sum.hasSum.tendsto_sum_nat
      have h_diff_t : Filter.Tendsto
          (fun N : ℕ => (∑ k ∈ Finset.range N, ‖v k‖) - (∑ k ∈ Finset.range (N / 2), ‖v k‖))
          Filter.atTop (𝓝 (∑' k, ‖v k‖ - ∑' k, ‖v k‖)) :=
        h_cau.sub (h_cau.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun n hn => by omega⟩))
      rw [sub_self] at h_diff_t
      have h_eq : (fun N : ℕ => ∑ k ∈ Finset.Ico (N / 2) N, ‖v k‖) =
          fun N : ℕ => (∑ k ∈ Finset.range N, ‖v k‖) - (∑ k ∈ Finset.range (N / 2), ‖v k‖) := by
        ext N
        simp only [Finset.range_eq_Ico]
        linarith [Finset.sum_Ico_consecutive (fun k => ‖v k‖) (Nat.zero_le (N / 2)) (Nat.div_le_self N 2)]
      rwa [h_eq]
    have h_rhs0 : Filter.Tendsto (fun N : ℕ =>
        (∑ j ∈ Finset.Ico (N / 2) N, ‖u j‖) * (∑' k, ‖v k‖) +
        (∑' j, ‖u j‖) * (∑ k ∈ Finset.Ico (N / 2) N, ‖v k‖))
        Filter.atTop (𝓝 0) := by
      simpa using (h_ico_u.mul_const (∑' k, ‖v k‖)).add ((h_ico_v.const_mul (∑' j, ‖u j‖)))
    exact squeeze_zero (fun _ => norm_nonneg _) h_bound h_rhs0
  have h_tri_const : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), ⟪u j, v (n - j)⟫_ℂ)
      Filter.atTop (𝓝 ⟪(ψ : H), (φ : H)⟫_ℂ) := by
    have h_ev : ∀ᶠ N : ℕ in Filter.atTop,
        (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), ⟪u j, v (n - j)⟫_ℂ) =
          ⟪(ψ : H), (φ : H)⟫_ℂ := by
      rw [Filter.eventually_atTop]
      refine ⟨1, fun N hN => ?_⟩
      have h1 := inner_expSeries_partial_eq D A hA h_symm t ψ φ N
      have hne : N ≠ 0 := by omega
      simpa [hne] using h1
    exact tendsto_const_nhds.congr' (h_ev.mono fun _ h => h.symm)
  have h_diff2 := h_partial_tend.sub h_tri_const
  exact sub_eq_zero.mp (tendsto_nhds_unique h_diff2 h_tri_diff)

end NelsonExp

end Imscribing.YangMills.AnalyticVectorExp
