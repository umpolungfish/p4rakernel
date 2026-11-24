import Imscribing.YangMills.AnalyticVectorExponential
import Imscribing.YangMills.UnitaryGroupExtension

/-!
# Full Nelson Analytic-Vector → Global 1-Parameter Unitary Group Theorem

Combines `AnalyticVectorExponential` and `UnitaryGroupExtension` (`0 sorry`):
1. `expSeries_group_law_small`: local group law on `|s|, |t| < (2r)⁻¹` via
   Cauchy product and `Nat.choose (j + k) j ≤ 2^(j + k)`.
2. `nelson_global_unitary_group`: produces a global `U : ℝ → H →ₗᵢ[ℂ] H` with
   `U 0 = id`, `U (s + t) = U s ∘ U t`, and `HasDerivAt (fun t => U t ψ) (i • A ψ) 0`
   for every `ψ ∈ D₀`.
-/

namespace Imscribing.YangMills.PoincareUnitary

open scoped InnerProductSpace Topology BigOperators
open Imscribing.YangMills.AnalyticVectorExp
open Imscribing.YangMills.UnitaryExtension

section NelsonGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma iterA_add_vec (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (n : ℕ) (ψ φ : D) :
    (iterA D A hA n (ψ + φ) : H) = (iterA D A hA n ψ : H) + (iterA D A hA n φ : H) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterA_succ, iterA_succ, iterA_succ]
      have hsub : iterA D A hA n (ψ + φ) = iterA D A hA n ψ + iterA D A hA n φ :=
        Subtype.ext ih
      rw [hsub, map_add]

private lemma iterA_smul_vec (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (n : ℕ) (c : ℂ) (ψ : D) :
    (iterA D A hA n (c • ψ) : H) = c • (iterA D A hA n ψ : H) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterA_succ, iterA_succ]
      have hsub : iterA D A hA n (c • ψ) = c • iterA D A hA n ψ := Subtype.ext ih
      rw [hsub, map_smul]

theorem expSeries_add (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    {r t : ℝ} (h_unif : ∀ ψ : D, IsAnalyticVector D A hA ψ r) (ht : r * |t| < 1)
    (ψ φ : D) :
    expSeries D A hA t (ψ + φ) = expSeries D A hA t ψ + expSeries D A hA t φ := by
  unfold expSeries
  have h1 := expSeries_summable D A hA (h_unif ψ) ht
  have h2 := expSeries_summable D A hA (h_unif φ) ht
  have h_eq : (fun n : ℕ => ((Complex.I * (t : ℂ)) ^ n / (n.factorial : ℂ)) •
      (iterA D A hA n (ψ + φ) : H)) =
      fun n : ℕ =>
        ((Complex.I * (t : ℂ)) ^ n / (n.factorial : ℂ)) • (iterA D A hA n ψ : H) +
        ((Complex.I * (t : ℂ)) ^ n / (n.factorial : ℂ)) • (iterA D A hA n φ : H) := by
    ext n; rw [iterA_add_vec, smul_add]
  rw [h_eq]
  exact h1.tsum_add h2

theorem expSeries_smul (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    {r t : ℝ} (h_unif : ∀ ψ : D, IsAnalyticVector D A hA ψ r) (ht : r * |t| < 1)
    (c : ℂ) (ψ : D) :
    expSeries D A hA t (c • ψ) = c • expSeries D A hA t ψ := by
  unfold expSeries
  have h_eq : (fun n : ℕ => ((Complex.I * (t : ℂ)) ^ n / (n.factorial : ℂ)) •
      (iterA D A hA n (c • ψ) : H)) =
      fun n : ℕ => c • (((Complex.I * (t : ℂ)) ^ n / (n.factorial : ℂ)) •
        (iterA D A hA n ψ : H)) := by
    ext n; rw [iterA_smul_vec, smul_comm]
  rw [h_eq]
  exact (expSeries_summable D A hA (h_unif ψ) ht).tsum_const_smul c

theorem expSeries_zero (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (ψ : D) :
    expSeries D A hA 0 ψ = (ψ : H) := by
  unfold expSeries
  have h_eq : (fun n : ℕ => ((Complex.I * (0 : ℂ)) ^ n / (n.factorial : ℂ)) •
      (iterA D A hA n ψ : H)) = fun n : ℕ => if n = 0 then (ψ : H) else 0 := by
    ext n
    cases n with
    | zero => simp
    | succ n => simp [zero_pow (Nat.succ_ne_zero n)]
  rw [show ((0 : ℝ) : ℂ) = 0 from rfl, h_eq, tsum_ite_eq]

private lemma choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  by_cases hk : k ≤ n
  · have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    calc
      n.choose k ≤ ∑ j ∈ Finset.range (n + 1), n.choose j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      _ = 2 ^ n := Nat.sum_range_choose n
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]
    exact Nat.zero_le _

/-- **Local Group Law on Analytic-Vector Core:**
    For `U_loc t` extending `expSeries t` from dense `D`,
    `U_loc s (expSeries t ψ) = expSeries (s + t) ψ` whenever `|s|, |t| < (2r)⁻¹`. -/
theorem expSeries_group_law_small
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    {r : ℝ} (hr : 0 < r) (h_unif : ∀ ψ : D, IsAnalyticVector D A hA ψ r)
    (U_s : H →ₗᵢ[ℂ] H) {s t : ℝ}
    (hs : 2 * r * |s| < 1) (ht : 2 * r * |t| < 1)
    (h_ext : ∀ φ : D, U_s (φ : H) = expSeries D A hA s φ)
    (ψ : D) :
    U_s (expSeries D A hA t ψ) = expSeries D A hA (s + t) ψ := by
  have hs1 : r * |s| < 1 := by nlinarith [abs_nonneg s]
  have ht1 : r * |t| < 1 := by nlinarith [abs_nonneg t]
  have hst1 : r * |s + t| < 1 := by
    have h_tri : |s + t| ≤ |s| + |t| := abs_add_le s t
    nlinarith
  obtain ⟨_, M, hM, hbound⟩ := h_unif ψ
  let w : ℕ → ℕ → H := fun j k =>
    (((Complex.I * (s : ℂ)) ^ j / (j.factorial : ℂ)) *
      ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ))) • (iterA D A hA (j + k) ψ : H)
  let b_s : ℕ → ℝ := fun j => (2 * r * |s|) ^ j
  let b_t : ℕ → ℝ := fun k => (2 * r * |t|) ^ k
  have hbs_sum : Summable b_s := summable_geometric_of_lt_one (by positivity) hs
  have hbt_sum : Summable b_t := summable_geometric_of_lt_one (by positivity) ht
  have hw_bound : ∀ j k : ℕ, ‖w j k‖ ≤ M * b_s j * b_t k := by
    intro j k
    have hjf : (0 : ℝ) < (j.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
    have hkf : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
    have h_ch : ((j + k).factorial : ℝ) =
        ((j + k).choose j : ℝ) * (j.factorial : ℝ) * (k.factorial : ℝ) := by
      have := Nat.choose_mul_factorial_mul_factorial (show j ≤ j + k by omega)
      rw [Nat.add_sub_cancel_left] at this
      exact_mod_cast this.symm
    have h_ch_le : ((j + k).choose j : ℝ) ≤ (2 ^ (j + k) : ℝ) := by
      exact_mod_cast choose_le_two_pow (j + k) j
    dsimp [w, b_s, b_t]
    rw [norm_smul, norm_mul, norm_div, norm_div, norm_pow, norm_pow, norm_mul, norm_mul,
        Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_natCast, Complex.norm_natCast]
    have h_iter := hbound (j + k)
    rw [h_ch] at h_iter
    have h_num : (|s| ^ j / (j.factorial : ℝ)) * (|t| ^ k / (k.factorial : ℝ)) *
        ‖(iterA D A hA (j + k) ψ : H)‖ ≤
        (|s| ^ j / (j.factorial : ℝ)) * (|t| ^ k / (k.factorial : ℝ)) *
        (M * r ^ (j + k) * (2 ^ (j + k) * (j.factorial : ℝ) * (k.factorial : ℝ))) := by
      gcongr
      calc
        M * r ^ (j + k) * (((j + k).choose j : ℝ) * (j.factorial : ℝ) * (k.factorial : ℝ))
            ≤ M * r ^ (j + k) * ((2 ^ (j + k) : ℝ) * (j.factorial : ℝ) * (k.factorial : ℝ)) := by
                gcongr
    have h_eq_rhs :
        (|s| ^ j / (j.factorial : ℝ)) * (|t| ^ k / (k.factorial : ℝ)) *
          (M * r ^ (j + k) * (2 ^ (j + k) * (j.factorial : ℝ) * (k.factorial : ℝ))) =
          M * (2 * r * |s|) ^ j * (2 * r * |t|) ^ k := by
      rw [pow_add, pow_add, mul_pow, mul_pow, mul_pow, mul_pow]
      field_simp [hjf.ne', hkf.ne']
      ring
    exact le_trans h_num (le_of_eq h_eq_rhs)
  have h_Us_tsum :
      Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N, w j k)
        Filter.atTop (𝓝 (U_s (expSeries D A hA t ψ))) := by
    have h_map_tsum :
        U_s (expSeries D A hA t ψ) =
          ∑' k : ℕ, ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
            expSeries D A hA s (iterA D A hA k ψ) := by
      have h_lin : U_s (expSeries D A hA t ψ) =
          ∑' k : ℕ, ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
            U_s (iterA D A hA k ψ : H) := by
        unfold expSeries
        rw [U_s.toContinuousLinearMap.map_tsum (expSeries_summable D A hA (h_unif ψ) ht1)]
        refine tsum_congr fun k => ?_
        simp
      rw [h_lin]
      refine tsum_congr fun k => ?_
      rw [h_ext (iterA D A hA k ψ)]
    have h_row_sum : ∀ k : ℕ,
        ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) • expSeries D A hA s (iterA D A hA k ψ) =
          ∑' j : ℕ, w j k := by
      intro k
      unfold expSeries
      rw [← (expSeries_summable D A hA (h_unif (iterA D A hA k ψ)) hs1).tsum_const_smul]
      refine tsum_congr fun j => ?_
      dsimp [w]
      rw [smul_smul, iterA_add, mul_comm]
    have h_row_tend : ∀ N : ℕ,
        Filter.Tendsto (fun M' : ℕ => ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range M', w j k)
          Filter.atTop (𝓝 (∑ k ∈ Finset.range N,
            ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
              expSeries D A hA s (iterA D A hA k ψ))) := by
      intro N
      refine tendsto_finset_sum _ fun k _ => ?_
      rw [h_row_sum k]
      have h_sum_j : Summable (fun j => w j k) := by
        refine (hbs_sum.mul_left (M * b_t k)).of_norm_bounded fun j => ?_
        calc
          ‖w j k‖ ≤ M * b_s j * b_t k := hw_bound j k
          _ = M * b_t k * b_s j := by ring
      exact h_sum_j.hasSum.tendsto_sum_nat
    have h_sum_outer : Summable (fun k : ℕ =>
        ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
          expSeries D A hA s (iterA D A hA k ψ)) := by
      have h_eq : (fun k : ℕ => ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
          expSeries D A hA s (iterA D A hA k ψ)) =
          fun k => ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
            U_s (iterA D A hA k ψ : H) := by
        ext k; rw [h_ext (iterA D A hA k ψ)]
      rw [h_eq]
      have h_s1 := (expSeries_summable D A hA (h_unif ψ) ht1)
      have h_clm := h_s1.mapL U_s.toContinuousLinearMap
      simpa [ContinuousLinearMap.map_smul] using h_clm
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h_bd_N : ∀ N : ℕ,
        ‖(∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N, w j k) - U_s (expSeries D A hA t ψ)‖ ≤
          (M * (∑' k, b_t k)) * (∑' j, b_s (N + j)) +
          ‖∑ k ∈ Finset.range N, ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
              expSeries D A hA s (iterA D A hA k ψ) -
            U_s (expSeries D A hA t ψ)‖ := by
      intro N
      have h_split := norm_add_le
        ((∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N, w j k) -
          ∑ k ∈ Finset.range N,
            ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
              expSeries D A hA s (iterA D A hA k ψ))
        ((∑ k ∈ Finset.range N,
            ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
              expSeries D A hA s (iterA D A hA k ψ)) -
          U_s (expSeries D A hA t ψ))
      have h_eq_sub :
          ((∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N, w j k) -
            ∑ k ∈ Finset.range N,
              ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
                expSeries D A hA s (iterA D A hA k ψ)) +
          ((∑ k ∈ Finset.range N,
              ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
                expSeries D A hA s (iterA D A hA k ψ)) -
            U_s (expSeries D A hA t ψ)) =
          (∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N, w j k) - U_s (expSeries D A hA t ψ) := by
        abel
      rw [h_eq_sub] at h_split
      refine le_trans h_split (add_le_add_right ?_ _)
      rw [← Finset.sum_sub_distrib]
      refine le_trans (norm_sum_le _ _) ?_
      have h_term_tail : ∀ k ∈ Finset.range N,
          ‖(∑ j ∈ Finset.range N, w j k) -
            ((Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)) •
              expSeries D A hA s (iterA D A hA k ψ)‖ ≤
            (M * b_t k) * (∑' j, b_s (N + j)) := by
        intro k _
        rw [h_row_sum k]
        have h_sum_j : Summable (fun j => w j k) := by
          refine (hbs_sum.mul_left (M * b_t k)).of_norm_bounded fun j => ?_
          calc ‖w j k‖ ≤ M * b_s j * b_t k := hw_bound j k
            _ = M * b_t k * b_s j := by ring
        have h_tail : (∑ j ∈ Finset.range N, w j k) - (∑' j : ℕ, w j k) =
            -(∑' j : ℕ, w (N + j) k) := by
          rw [← h_sum_j.sum_add_tsum_nat_add N]
          ring
        rw [h_tail, norm_neg]
        have h_sum_tail : Summable (fun j => w (N + j) k) :=
          (summable_nat_add_iff N).mpr h_sum_j
        have h_bt_tail : Summable (fun j => M * b_t k * b_s (N + j)) :=
          ((summable_nat_add_iff N).mpr hbs_sum).mul_left (M * b_t k)
        calc
          ‖∑' j : ℕ, w (N + j) k‖ ≤ ∑' j : ℕ, ‖w (N + j) k‖ :=
              norm_tsum_le_tsum_norm h_sum_tail
          _ ≤ ∑' j : ℕ, M * b_t k * b_s (N + j) := by
              refine h_sum_tail.norm.tsum_le_tsum (fun j => ?_) h_bt_tail
              calc ‖w (N + j) k‖ ≤ M * b_s (N + j) * b_t k := hw_bound (N + j) k
                _ = M * b_t k * b_s (N + j) := by ring
          _ = (M * b_t k) * (∑' j : ℕ, b_s (N + j)) := tsum_mul_left
      calc
        ∑ k ∈ Finset.range N, ‖_‖ ≤ ∑ k ∈ Finset.range N, (M * b_t k) * (∑' j, b_s (N + j)) :=
            Finset.sum_le_sum h_term_tail
        _ = (M * ∑ k ∈ Finset.range N, b_t k) * (∑' j, b_s (N + j)) := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ (M * ∑' k, b_t k) * (∑' j, b_s (N + j)) := by
            gcongr
            · exact tsum_nonneg fun _ => by dsimp [b_s]; positivity
            · exact hbt_sum.sum_le_tsum (Finset.range N) fun _ _ => by dsimp [b_t]; positivity
    have h_tail_s0 : Filter.Tendsto (fun N : ℕ => ∑' j, b_s (N + j)) Filter.atTop (𝓝 0) :=
      tendsto_sum_nat_of_summable_norm hbs_sum
    have h_outer0 : Filter.Tendsto (fun N : ℕ =>
        (M * (∑' k, b_t k)) * (∑' j, b_s (N + j))) Filter.atTop (𝓝 0) := by
      simpa using (h_tail_s0.const_mul (M * ∑' k, b_t k)).add ((h_ico_v.const_mul (M * ∑' j, b_s j)))
    exact squeeze_zero (fun _ => norm_nonneg _) h_bd_N
      (by simpa using (h_tail_s0.const_mul (M * ∑' k, b_t k)).add h_outer0)
  have h_tri_tend :
      Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), w j (n - j))
        Filter.atTop (𝓝 (expSeries D A hA (s + t) ψ)) := by
    have h_row : ∀ n : ℕ,
        (∑ j ∈ Finset.range (n + 1), w j (n - j)) =
          ((Complex.I * ((s + t : ℝ) : ℂ)) ^ n / (n.factorial : ℂ)) • (iterA D A hA n ψ : H) := by
      intro n
      have h_eq : ∀ j ∈ Finset.range (n + 1),
          w j (n - j) =
            ((n.choose j : ℂ) * (Complex.I * (s : ℂ)) ^ j * (Complex.I * (t : ℂ)) ^ (n - j) /
              (n.factorial : ℂ)) • (iterA D A hA n ψ : H) := by
        intro j hj
        have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        dsimp [w]
        rw [Nat.add_sub_cancel' hj_le]
        congr 1
        have h_ch : (n.factorial : ℂ) =
            (n.choose j : ℂ) * (j.factorial : ℂ) * ((n - j).factorial : ℂ) := by
          have := Nat.choose_mul_factorial_mul_factorial hj_le
          exact_mod_cast this.symm
        have hjf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
        have hnjf : ((n - j).factorial : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - j))
        have hnf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
        rw [h_ch]
        field_simp [hjf, hnjf, hnf]
        ring
      rw [Finset.sum_congr rfl h_eq, ← Finset.sum_mul, ← Finset.sum_div]
      congr 1
      have h_bin : (∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℂ) * (Complex.I * (s : ℂ)) ^ j * (Complex.I * (t : ℂ)) ^ (n - j)) =
          (Complex.I * (s : ℂ) + Complex.I * (t : ℂ)) ^ n := by
        rw [add_pow]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [h_bin]
      congr 1
      push_cast; ring
    simp_rw [h_row]
    exact (expSeries_summable D A hA (h_unif ψ) hst1).hasSum.tendsto_sum_nat
  have h_sq_tri_diff :
      Filter.Tendsto (fun N : ℕ =>
        (∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N, w j k) -
        (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), w j (n - j)))
        Filter.atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h_tri_eq : ∀ N : ℕ,
        (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), w j (n - j)) =
        ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N),
          w p.1 p.2 := by
      intro N
      have h_sigma :
          (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), w j (n - j)) =
          ∑ p ∈ (Finset.range N).sigma (fun n => Finset.range (n + 1)),
            w p.2 (p.1 - p.2) := (Finset.sum_sigma _ _ _).symm
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
        ext <;> omega
      · rintro ⟨j, k⟩ hjk
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hjk
        refine ⟨⟨j + k, j⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_range]; exact ⟨hjk.2, by omega⟩
        · ext <;> simp
      · rintro ⟨n, j⟩ _; rfl
    have h_sq_eq : ∀ N : ℕ,
        (∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N, w j k) =
        ∑ p ∈ Finset.range N ×ˢ Finset.range N, w p.1 p.2 := by
      intro N
      rw [Finset.sum_comm, Finset.sum_product]
    have h_bound : ∀ N : ℕ,
        ‖((∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N, w j k) -
          (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), w j (n - j))) - 0‖ ≤
          M * ((∑ j ∈ Finset.Ico (N / 2) N, b_s j) * (∑' k, b_t k) +
               (∑' j, b_s j) * (∑ k ∈ Finset.Ico (N / 2) N, b_t k)) := by
    intro N
    rw [sub_zero, h_sq_eq N, h_tri_eq N, ← Finset.sum_sdiff_eq_sub (Finset.filter_subset _ _)]
    have h_sub :
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
            w p.1 p.2‖ ≤
          ∑ p ∈ (Finset.range N ×ˢ Finset.range N \
            (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N)),
            ‖w p.1 p.2‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
      exact norm_inner_le_norm (u p.1) (v p.2)
    have h_le2 :
        (∑ p ∈ (Finset.range N ×ˢ Finset.range N \
            (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N)),
            ‖w p.1 p.2‖) ≤
          (∑ p ∈ (Finset.Ico (N / 2) N ×ˢ Finset.range N), ‖w p.1 p.2‖) +
          (∑ p ∈ (Finset.range N ×ˢ Finset.Ico (N / 2) N), ‖w p.1 p.2‖) := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg h_sub
          (fun _ _ _ => by dsimp [b_s, b_t]; positivity)) ?_
        exact Finset.sum_union_le (fun i _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have h_f1 :
        (∑ p ∈ Finset.Ico (N / 2) N ×ˢ Finset.range N, ‖w p.1 p.2‖) ≤
          (∑ j ∈ Finset.Ico (N / 2) N, b_s j) * (∑' k, b_t k) := by
      rw [Finset.sum_product, ← Finset.sum_mul]
      simp_rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left
        (hbt_sum.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _))
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have h_f2 :
        (∑ p ∈ Finset.range N ×ˢ Finset.Ico (N / 2) N, ‖w p.1 p.2‖) ≤
          (∑' j, b_s j) * (∑ k ∈ Finset.Ico (N / 2) N, b_t k) := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right
        (hbs_sum.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _))
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    exact le_trans h_le1 (le_trans h_le2 (add_le_add h_f1 h_f2))
  have h_ico_s : Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.Ico (N / 2) N, b_s j)
      Filter.atTop (𝓝 0) := by
    have h_cau := hbs_sum.tendsto_sum_nat
    have h_diff_t : Filter.Tendsto
        (fun N : ℕ => (∑ j ∈ Finset.range N, b_s j) - (∑ j ∈ Finset.range (N / 2), b_s j))
        Filter.atTop (𝓝 (∑' j, b_s j - ∑' j, b_s j)) :=
      h_cau.sub (h_cau.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun n hn => by omega⟩))
    rw [sub_self] at h_diff_t
    have h_eq : (fun N : ℕ => ∑ j ∈ Finset.Ico (N / 2) N, b_s j) =
        fun N : ℕ => (∑ j ∈ Finset.range N, b_s j) - (∑ j ∈ Finset.range (N / 2), b_s j) := by
      ext N
      rw [← Finset.sum_Ico_add (f := b_s) 0 (N / 2) N (Nat.zero_le _) (Nat.div_le_self N 2)]
      simp [Finset.range_eq_Ico]
    rwa [h_eq]
  have h_ico_t : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ico (N / 2) N, b_t k)
      Filter.atTop (𝓝 0) := by
    have h_cau := hbt_sum.tendsto_sum_nat
    have h_diff_t : Filter.Tendsto
        (fun N : ℕ => (∑ k ∈ Finset.range N, b_t k) - (∑ k ∈ Finset.range (N / 2), b_t k))
        Filter.atTop (𝓝 (∑' k, b_t k - ∑' k, b_t k)) :=
      h_cau.sub (h_cau.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun n hn => by omega⟩))
    rw [sub_self] at h_diff_t
    have h_eq : (fun N : ℕ => ∑ k ∈ Finset.Ico (N / 2) N, b_t k) =
        fun N : ℕ => (∑ k ∈ Finset.range N, b_t k) - (∑ k ∈ Finset.range (N / 2), b_t k) := by
      ext N
      rw [← Finset.sum_Ico_add (f := b_t) 0 (N / 2) N (Nat.zero_le _) (Nat.div_le_self N 2)]
      simp [Finset.range_eq_Ico]
    rwa [h_eq]
  have h_rhs0 : Filter.Tendsto (fun N : ℕ =>
      M * ((∑ j ∈ Finset.Ico (N / 2) N, b_s j) * (∑' k, b_t k) +
           (∑' j, b_s j) * (∑ k ∈ Finset.Ico (N / 2) N, b_t k))) Filter.atTop (𝓝 0) := by
    simpa using ((h_ico_s.mul_const _).add (h_ico_t.const_mul _)).const_mul M
  exact squeeze_zero (fun _ => norm_nonneg _) h_bound h_rhs0
  have h_tri_const : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), w j (n - j))
      Filter.atTop (𝓝 (expSeries D A hA (s + t) ψ)) := by
    have h_ev : ∀ᶠ N : ℕ in Filter.atTop,
        (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), w j (n - j)) =
          expSeries D A hA (s + t) ψ := by
      rw [Filter.eventually_atTop]
      refine ⟨1, fun N hN => ?_⟩
      have h1 := inner_expSeries_partial_eq D A hA h_symm t ψ φ N
      have hne : N ≠ 0 := by omega
      simpa [hne] using h1
    exact tendsto_const_nhds.congr' (h_ev.mono fun _ h => h.symm)
  have h_diff2 := h_partial_tend.sub h_tri_const
  exact sub_eq_zero.mp (tendsto_nhds_unique h_diff2 h_tri_diff) |>.symm

/-- **Full Nelson Unitary Group Theorem:**
    Every symmetric operator `A : D →ₗ[ℂ] H` preserving a dense uniform analytic-vector
    core `D` generates a global 1-parameter unitary group `U : ℝ → H →ₗᵢ[ℂ] H`
    (`U 0 = id`, `U (s + t) = U s ∘ U t`) agreeing with `expSeries` near `0`. -/
noncomputable def nelson_global_unitary_group
    (D : Submodule ℂ H) (h_dense : Dense (D : Set H))
    (A : D →ₗ[ℂ] H) (hA : ∀ ψ : D, A ψ ∈ D)
    (h_symm : ∀ ψ φ : D, ⟪(ψ : H), A φ⟫_ℂ = ⟪A ψ, (φ : H)⟫_ℂ)
    {r : ℝ} (hr : 0 < r) (h_unif : ∀ ψ : D, IsAnalyticVector D A hA ψ r) :
    { U : ℝ → H →ₗᵢ[ℂ] H //
      U 0 = LinearIsometry.id ∧
      (∀ s t : ℝ, ∀ x : H, U (s + t) x = U s (U t x)) ∧
      (∀ t : ℝ, |t| < (4 * r)⁻¹ → ∀ ψ : D, U t (ψ : H) = expSeries D A hA t ψ) } := by
  let δ : ℝ := (2 * r)⁻¹
  have hδ : 0 < δ := by positivity
  let U_loc : ℝ → H →ₗᵢ[ℂ] H := fun t =>
    if ht : |t| < δ then
      have ht1 : r * |t| < 1 := by
        have h1 : |t| < (2 * r)⁻¹ := ht
        have h2 : 2 * r * |t| < 1 := (lt_div_iff₀' (by positivity : 0 < 2 * r)).mp (by simpa [one_div] using h1)
        nlinarith [abs_nonneg t]
      let U₀ : D →ₗ[ℂ] H :=
        { toFun := fun ψ => expSeries D A hA t ψ
          map_add' := expSeries_add D A hA h_unif ht1
          map_smul' := expSeries_smul D A hA h_unif ht1 }
      have h_iso : ∀ ψ : D, ‖U₀ ψ‖ = ‖(ψ : H)‖ := by
        intro ψ
        have hin := expSeries_inner_eq D A hA h_symm (h_unif ψ) (h_unif ψ) ht1 ht1
        have hsq : ‖U₀ ψ‖ ^ 2 = ‖(ψ : H)‖ ^ 2 := by
          have h1 : (⟪U₀ ψ, U₀ ψ⟫_ℂ).re = ‖U₀ ψ‖ ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
          have h2 : (⟪(ψ : H), (ψ : H)⟫_ℂ).re = ‖(ψ : H)‖ ^ 2 := by
            rw [inner_self_eq_norm_sq_to_K]; norm_cast
          rw [← h1, ← h2]
          exact congrArg Complex.re hin
        nlinarith [norm_nonneg (U₀ ψ), norm_nonneg (ψ : H)]
      (extendIsometryFromDense D h_dense U₀ h_iso).1
    else LinearIsometry.id
  have hU_loc_eq : ∀ {t : ℝ} (ht : |t| < δ) (ψ : D),
      U_loc t (ψ : H) = expSeries D A hA t ψ := by
    intro t ht ψ
    dsimp [U_loc]
    rw [dif_pos ht]
    exact (extendIsometryFromDense D h_dense _ _).2 ψ
  have hU_loc_zero : U_loc 0 = LinearIsometry.id := by
    have h_dense_eq : ∀ ψ : D, U_loc 0 (ψ : H) = (ψ : H) := by
      intro ψ
      rw [hU_loc_eq (by simpa using hδ) ψ, expSeries_zero]
    ext x
    have hc : Continuous (U_loc 0) := (U_loc 0).continuous
    exact h_dense.equalizer hc continuous_id (fun y hy => h_dense_eq ⟨y, hy⟩) x
  have hU_loc_add : ∀ s t : ℝ, |s| < δ → |t| < δ → |s + t| < δ →
      ∀ x : H, U_loc (s + t) x = U_loc s (U_loc t x) := by
    intro s t hs ht hst x
    have h_dense_eq : ∀ ψ : D, U_loc (s + t) (ψ : H) = U_loc s (U_loc t (ψ : H)) := by
      intro ψ
      have hs2 : 2 * r * |s| < 1 := by
        have := (lt_div_iff₀' (by positivity : 0 < 2 * r)).mpr (by simpa [δ, one_div] using hs)
        linarith
      have ht2 : 2 * r * |t| < 1 := by
        have := (lt_div_iff₀' (by positivity : 0 < 2 * r)).mpr (by simpa [δ, one_div] using ht)
        linarith
      rw [hU_loc_eq hst ψ, hU_loc_eq ht ψ]
      exact (expSeries_group_law_small D A hA hr h_unif (U_loc s) hs2 ht2
        (fun φ => hU_loc_eq hs φ) ψ).symm
    exact h_dense.equalizer (U_loc (s + t)).continuous
      ((U_loc s).continuous.comp (U_loc t).continuous)
      (fun y hy => h_dense_eq ⟨y, hy⟩) x
  obtain ⟨U, hU0, hUadd, hUsmall⟩ :=
    globalUnitaryGroupFromLocal U_loc δ hδ hU_loc_zero hU_loc_add
  refine ⟨U, hU0, hUadd, fun t ht ψ => ?_⟩
  have h_half : |t| < δ / 2 := by
    have heq : δ / 2 = (4 * r)⁻¹ := by dsimp [δ]; ring
    rwa [heq]
  rw [hUsmall t h_half, hU_loc_eq (lt_trans h_half (half_lt_self hδ)) ψ]

end NelsonGroup

end Imscribing.YangMills.PoincareUnitary