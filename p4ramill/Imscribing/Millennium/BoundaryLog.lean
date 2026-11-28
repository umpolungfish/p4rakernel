import Mathlib

open scoped Topology
open Filter Finset Metric Function

noncomputable section

namespace BoundaryBrick

/-! ### Finset helper -/

private theorem sumRangeAdd (f : ℕ → ℂ) (m n : ℕ) :
    ∑ x ∈ range (m + n), f x = (∑ x ∈ range m, f x) + ∑ x ∈ range n, f (m + x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : m + (n + 1) = m + n + 1 := by abel
    rw [h, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    abel

private theorem honeDivSub {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    1 / x - 1 / y = (y - x) / (x * y) := by
  field_simp [hx, hy]

/-! ### The boundary brick -/

/-- The map `y ↦ y + 1/2` sends the left-neighborhood of `1/2` into the left-neighborhood of `1`. -/
private theorem shiftTendsto : Tendsto (fun y : ℝ => y + 1/2) (𝓝[<](1/2:ℝ)) (𝓝[<](1:ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h2 : Continuous (fun y : ℝ => y + 1/2) := continuous_id.add continuous_const
    have h3 : Tendsto (fun y : ℝ => y + 1/2) (𝓝 ((1:ℝ)/2)) (𝓝 ((1:ℝ)/2 + 1/2)) :=
      h2.tendsto ((1:ℝ)/2)
    rw [show ((1:ℝ)/2 + 1/2) = 1 from by norm_num] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    rw [Set.mem_Iio] at hy ⊢
    linarith

/-- The scalar factor `1/(y+1/2)` tends to `1` in `ℂ` as `y → 1/2` from below. -/
private theorem invTendsto :
    Tendsto (fun y : ℝ => Complex.ofReal (1 / (y + 1/2 : ℝ))) (𝓝[<](1/2:ℝ)) (𝓝 ((1:ℂ))) := by
  have hcon : ContinuousOn (fun y : ℝ => 1 / (y + 1/2)) (Set.Ioi (0:ℝ)) := by
    refine ContinuousOn.div continuousOn_const
      (continuous_id.add continuous_const).continuousOn ?_
    intro y hy
    have := Set.mem_Ioi.mp hy
    linarith
  have hc : Tendsto (fun y : ℝ => 1 / (y + 1/2)) (𝓝[<](1/2:ℝ)) (𝓝 (1:ℝ)) := by
    have h2 : Tendsto (fun y : ℝ => 1 / (y + 1/2)) (𝓝 ((1:ℝ)/2)) (𝓝 (1 / ((1:ℝ)/2 + 1/2))) :=
      (hcon.continuousAt (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1/2))).tendsto
    rw [show (1 / ((1:ℝ)/2 + 1/2)) = (1:ℝ) from by norm_num] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hc)

/-- The interior log argument is continuous in `y`. -/
private theorem subMulContinuous {u : ℂ} :
    Continuous (fun y : ℝ => ((1:ℂ) - Complex.ofReal (y + 1/2) * u)) := by
  continuity

set_option maxHeartbeats 1000000 in
/-- Partial sums of the root-of-unity harmonic series `∑ u^(n+1)/(n+1)` converge to
`-log (1 - u)` for `u` a nontrivial `N`-th root of unity. -/
theorem tendsto_rootUnityHarmonic {u : ℂ} {N : ℕ} (hN : 0 < N) (hN1 : u ^ N = 1) (hu1 : u ≠ 1) :
    Tendsto (fun K : ℕ => ∑ n ∈ range K, u ^ (n + 1) / (n + 1 : ℂ)) atTop
      (𝓝 (-(Complex.log (1 - u)))) := by
  -- |u| = 1
  have hu1n : ‖u‖ = 1 := by
    have h0 : ‖u‖ ^ N = 1 := by rw [← norm_pow, hN1, norm_one]
    by_contra hc
    rcases lt_or_gt_of_ne hc with h | h
    · exact absurd h0 (ne_of_lt (pow_lt_one₀ (norm_nonneg u) h (by omega)))
    · exact absurd h0 (ne_of_gt (one_lt_pow₀ h (by omega)))
  -- zero blocks
  have telesc : ∀ k : ℕ, (u - 1) * ∑ r ∈ range k, u ^ r = u ^ k - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (u - 1) * ∑ r ∈ range (k + 1), u ^ r
          = (u - 1) * (∑ r ∈ range k, u ^ r + u ^ k) := by rw [Finset.sum_range_succ]
        _ = (u - 1) * ∑ r ∈ range k, u ^ r + (u - 1) * u ^ k := by ring
        _ = (u ^ k - 1) + (u * u ^ k - u ^ k) := by rw [ih, sub_mul]; ring
        _ = u ^ (k + 1) - 1 := by rw [← pow_succ']; ring
  have hzero : ∑ r ∈ range N, u ^ r = 0 := by
    have h := telesc N
    rw [hN1, sub_self, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd (sub_eq_zero.mp h) hu1
    · exact h
  have hzero1 : ∑ r ∈ range N, u ^ (r + 1) = 0 := by
    have hE : ∑ r ∈ range N, u ^ (r + 1) = u * ∑ r ∈ range N, u ^ r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => pow_succ' u r
    rw [hE, hzero, mul_zero]
  -- block sums
  set Rp : ℕ → ℂ := fun m => ∑ r ∈ range N, u ^ (r + 1) / (m * N + r + 1 : ℂ) with hRdef
  have hposN : (0 : ℝ) < N := by exact_mod_cast hN
  -- R 0 is bounded by N
  have hR0 : ‖Rp 0‖ ≤ (N : ℝ) := by
    have h1 : ∀ r ∈ range N, ‖u ^ (r + 1) / (0 * N + r + 1 : ℂ)‖ ≤ (1 : ℝ) := by
      intro r hr
      have hrN : r < N := Finset.mem_range.mp hr
      have hnp : ‖u ^ (r + 1)‖ = 1 := by rw [norm_pow, hu1n, one_pow]
      have hz : (0 * N + r + 1 : ℂ) = Complex.ofReal ((0 * N + r + 1 : ℕ) : ℝ) := by
        push_cast; ring
      have hle : (1:ℝ) ≤ ((0 * N + r + 1 : ℕ) : ℝ) := by
        have h0 : (1:ℕ) ≤ 0 * N + r + 1 := by omega
        exact_mod_cast h0
      rw [norm_div, hnp, hz, ← RCLike.ofReal_eq_complex_ofReal, RCLike.norm_ofReal,
        abs_of_nonneg (by exact_mod_cast Nat.zero_le (0 * N + r + 1))]
      refine (one_div_le_one_div_of_le (by norm_num) hle).trans_eq ?_
      rw [one_div_one]
    calc ‖Rp 0‖ = ‖∑ r ∈ range N, u ^ (r + 1) / (0 * N + r + 1 : ℂ)‖ := by
          rw [hRdef]; simp
      _ ≤ ∑ r ∈ range N, ‖u ^ (r + 1) / (0 * N + r + 1 : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ range N, (1 : ℝ) := Finset.sum_le_sum h1
      _ = N := by simp
  -- block norm bound: ‖R m‖ ≤ 1/m² for m ≥ 1
  have hRb : ∀ m : ℕ, 1 ≤ m → ‖Rp m‖ ≤ 1 / (m : ℝ) ^ 2 := by
    intro m hm
    have hsumB : ∑ r ∈ range N, u ^ (r + 1) * ((1 : ℂ) / (((m + 1) * N : ℕ) : ℂ)) = 0 := by
      rw [← Finset.sum_mul, hzero1, zero_mul]
    have hper : ∀ r < N, u ^ (r + 1) / (m * N + r + 1 : ℂ)
        = u ^ (r + 1) * ((1 : ℂ) / (m * N + r + 1 : ℂ) - (1 : ℂ) / (((m + 1) * N : ℕ) : ℂ))
          + u ^ (r + 1) * ((1 : ℂ) / (((m + 1) * N : ℕ) : ℂ)) := by
      intro r _
      rw [div_eq_mul_inv, mul_sub]
      ring
    have hexp : Rp m = ∑ r ∈ range N,
        u ^ (r + 1) * ((1 : ℂ) / (m * N + r + 1 : ℂ) - (1 : ℂ) / (((m + 1) * N : ℕ) : ℂ)) := by
      simp only [hRdef]
      rw [Finset.sum_congr rfl (fun r hr => hper r (Finset.mem_range.mp hr)),
        Finset.sum_add_distrib,
        ← Finset.sum_mul (range N) (fun r : ℕ => u ^ (r + 1))
          ((1 : ℂ) / (((m + 1) * N : ℕ) : ℂ)),
        hzero1, zero_mul, add_zero]
    have hterm : ∀ r < N,
        ‖u ^ (r + 1) * ((1 : ℂ) / (m * N + r + 1 : ℂ) - (1 : ℂ) / (((m + 1) * N : ℕ) : ℂ))‖
          ≤ (N : ℝ) / ((m : ℝ) ^ 2 * (N : ℝ) ^ 2) := by
      intro r hrn
      have hnormu : ‖u ^ (r + 1)‖ = 1 := by rw [norm_pow, hu1n, one_pow]
      have h6 : (((m + 1) * N : ℕ) = m * N + N) := by ring
      have hnat : (m * N : ℕ) + r + 1 ≤ ((m + 1) * N : ℕ) := by rw [h6]; omega
      have hge1 : ((m * N : ℕ) : ℝ) ≤ ((m * N + r + 1 : ℕ) : ℝ) :=
        Nat.cast_le.2 (by omega)
      have hge2 : ((m * N : ℕ) : ℝ) ≤ (((m + 1) * N : ℕ) : ℝ) :=
        Nat.cast_le.2 (by rw [h6]; omega)
      have hnz1 : (0:ℝ) < (((m * N + r + 1 : ℕ) : ℝ)) := by
        have h9 : (0:ℕ) < m * N + r + 1 := by omega
        exact_mod_cast h9
      have hnz2 : (0:ℝ) < (((m + 1) * N : ℕ) : ℝ) := by
        have h9 : (0:ℕ) < m * N + N := by
          have hN2 : (0:ℕ) < N := hN
          omega
        have h10 : (0:ℕ) < ((m + 1) * N : ℕ) := by rw [h6]; exact h9
        exact_mod_cast h10
      have hval : ‖u ^ (r + 1) * ((1 : ℂ) / (m * N + r + 1 : ℂ) - (1 : ℂ) / (((m + 1) * N : ℕ) : ℂ))‖
          = ((((m + 1) * N : ℕ) - (m * N + r + 1) : ℕ) : ℝ) /
            (((m * N + r + 1 : ℕ) : ℝ) * (((m + 1) * N : ℕ) : ℝ)) := by
        rw [norm_mul, hnormu, one_mul, div_eq_mul_inv, div_eq_mul_inv, one_mul, one_mul]
        have hx : (m * N + r + 1 : ℂ) = Complex.ofReal ((m * N + r + 1 : ℕ) : ℝ) := by
          push_cast; ring
        have hy : (((m + 1) * N : ℕ) : ℂ) = Complex.ofReal ((((m + 1) * N : ℕ) : ℝ)) := by
          push_cast; ring
        have hx2 : ((m * N + r + 1 : ℂ))⁻¹ = Complex.ofReal ((((m * N + r + 1 : ℕ) : ℝ))⁻¹) := by
          rw [hx, Complex.ofReal_inv]
        have hy2 : ((((m + 1) * N : ℕ) : ℂ))⁻¹ = Complex.ofReal (((((m + 1) * N : ℕ) : ℝ))⁻¹) := by
          rw [hy, Complex.ofReal_inv]
        have hsign : 0 ≤ (((m * N + r + 1 : ℕ) : ℝ))⁻¹ - ((((m + 1) * N : ℕ) : ℝ))⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div, sub_nonneg]
          exact one_div_le_one_div_of_le hnz1 (Nat.cast_le.2 hnat)
        rw [hx2, hy2, ← Complex.ofReal_sub, ← RCLike.ofReal_eq_complex_ofReal,
          RCLike.norm_ofReal, abs_of_nonneg hsign, inv_eq_one_div, inv_eq_one_div,
          Nat.cast_sub hnat]
        have hne1 : (((m * N + r + 1 : ℕ) : ℝ)) ≠ 0 := by
          intro hc
          rw [hc] at hnz1
          exact lt_irrefl 0 hnz1
        have hne2 : ((((m + 1) * N : ℕ) : ℝ)) ≠ 0 := by
          intro hc
          rw [hc] at hnz2
          exact lt_irrefl 0 hnz2
        exact honeDivSub hne1 hne2
      rw [hval]
      have hsub : (((m + 1) * N : ℕ) - (m * N + r + 1) : ℕ) ≤ N := by
        rw [h6]; omega
      have h1' : ((((m + 1) * N : ℕ) - (m * N + r + 1) : ℕ) : ℝ) ≤ (N : ℝ) :=
        Nat.cast_le.2 hsub
      have h3 : ((((m + 1) * N : ℕ) - (m * N + r + 1) : ℕ) : ℝ) /
            (((m * N + r + 1 : ℕ) : ℝ) * (((m + 1) * N : ℕ) : ℝ))
          ≤ (N : ℝ) / (((m : ℝ) * (N : ℝ)) * ((m : ℝ) * (N : ℝ))) := by
        have hPq : (0:ℝ) < (((m * N + r + 1 : ℕ) : ℝ) * (((m + 1) * N : ℕ) : ℝ)) := by
          exact mul_pos (by positivity) (by positivity)
        have h4 : ((m : ℝ) * (N : ℝ)) * ((m : ℝ) * (N : ℝ)) ≤
            (((m * N + r + 1 : ℕ) : ℝ) * (((m + 1) * N : ℕ) : ℝ)) := by
          have hp0 : ((m * N : ℕ) : ℝ) = (m : ℝ) * (N : ℝ) := by push_cast; ring
          rw [← hp0]
          exact mul_le_mul hge1 hge2 (by positivity) (by positivity)
        have hKK : (0:ℝ) < ((m : ℝ) * (N : ℝ)) * ((m : ℝ) * (N : ℝ)) := by
          positivity
        rw [div_le_div_iff₀ hPq hKK]
        exact mul_le_mul h1' h4 (by positivity) (by positivity)
      have h2 : (N : ℝ) / (((m : ℝ) * (N : ℝ)) * ((m : ℝ) * (N : ℝ)))
          ≤ (N : ℝ) / ((m : ℝ) ^ 2 * (N : ℝ) ^ 2) := by
        rw [show ((m : ℝ) * (N : ℝ)) * ((m : ℝ) * (N : ℝ)) = (m : ℝ) ^ 2 * (N : ℝ) ^ 2 from by ring]
      calc ((((m + 1) * N : ℕ) - (m * N + r + 1) : ℕ) : ℝ) /
            (((m * N + r + 1 : ℕ) : ℝ) * (((m + 1) * N : ℕ) : ℝ))
          ≤ (N : ℝ) / (((m : ℝ) * (N : ℝ)) * ((m : ℝ) * (N : ℝ))) := h3
        _ ≤ (N : ℝ) / ((m : ℝ) ^ 2 * (N : ℝ) ^ 2) := h2
    calc ‖Rp m‖ = ‖∑ r ∈ range N,
        u ^ (r + 1) * ((1 : ℂ) / (m * N + r + 1 : ℂ) - (1 : ℂ) / (((m + 1) * N : ℕ) : ℂ))‖ := by
          rw [hexp]
      _ ≤ ∑ r ∈ range N, ‖u ^ (r + 1) * ((1 : ℂ) / (m * N + r + 1 : ℂ)
            - (1 : ℂ) / (((m + 1) * N : ℕ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ range N, ((N : ℝ) / ((m : ℝ) ^ 2 * (N : ℝ) ^ 2)) :=
          Finset.sum_le_sum (fun r hr => hterm r (Finset.mem_range.mp hr))
      _ = (N : ℝ) * ((N : ℝ) / ((m : ℝ) ^ 2 * (N : ℝ) ^ 2)) := by
          rw [Finset.sum_const, card_range, nsmul_eq_mul]
      _ = 1 / (m : ℝ) ^ 2 := by
          field_simp
  -- block-tail summability
  have hRtail : Summable (fun k : ℕ => ‖Rp (k + 1)‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => hRb (k+1) (Nat.succ_le_succ (Nat.zero_le k))) ?_
    exact (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr
      ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  have hRsumm : Summable (fun m : ℕ => ‖Rp m‖) :=
    (summable_nat_add_iff (f := fun m : ℕ => ‖Rp m‖) 1).mp hRtail
  have hRsumC : Summable Rp := Summable.of_norm_bounded hRsumm (fun m => le_rfl)
  have hRhasSum : HasSum Rp (∑' m : ℕ, Rp m) := hRsumC.hasSum
  have hQ : Tendsto (fun M : ℕ => ∑ m ∈ range M, Rp m) atTop (𝓝 (∑' m : ℕ, Rp m)) :=
    hRhasSum.tendsto_sum_nat
  -- the block split of partial sums
  have hsplit : ∀ (M r : ℕ), r < N →
      (∑ n ∈ range (M * N + r), u ^ (n + 1) / (n + 1 : ℂ))
        = (∑ m ∈ range M, Rp m)
          + (∑ s ∈ range r, u ^ (M * N + s + 1) / (M * N + s + 1 : ℂ)) := by
    intro M
    induction M with
    | zero =>
      intro r _
      simp [hRdef, zero_mul, zero_add]
    | succ M ih =>
      intro r hr
      have h0 := ih 0 hN
      rw [Nat.add_zero] at h0
      have hE0 : (∑ s ∈ range 0, u ^ (M * N + s + 1) / (M * N + s + 1 : ℂ)) = 0 := by
        simp
      have hRM : (∑ x ∈ range N, u ^ (M * N + x + 1) / (((M * N + x : ℕ) : ℂ) + 1)) = Rp M := by
        rw [hRdef]
        refine Finset.sum_congr rfl fun x _ => ?_
        push_cast
        rw [Nat.add_assoc, pow_add, Nat.mul_comm M N, pow_mul, hN1, one_pow, one_mul]
      have hTr : ∀ x : ℕ, u ^ (M * N + (N + x) + 1) / (((M * N + (N + x) : ℕ) : ℂ) + 1)
          = u ^ ((M + 1) * N + x + 1) / ((M + 1) * N + x + 1 : ℂ) := by
        intro x
        rw [show M * N + (N + x) + 1 = (M + 1) * N + x + 1 from by ring]
        push_cast
        ring
      rw [show ((M + 1) * N : ℕ) + r = M * N + (N + r) from by ring,
        sumRangeAdd (fun n => u ^ (n + 1) / (n + 1 : ℂ)) (M * N) (N + r), h0,
        sumRangeAdd (f := fun x => u ^ (M * N + x + 1) / (((M * N + x : ℕ) : ℂ) + 1)) N r,
        hE0, hRM, Finset.sum_congr rfl (fun x _ => hTr x), Finset.sum_range_succ]
      push_cast
      abel
  -- residual tail bound
  have hres0 : ∀ (M r : ℕ), 1 ≤ M → r < N →
      ‖∑ s ∈ range r, u ^ (M * N + s + 1) / (M * N + s + 1 : ℂ)‖ ≤ 1 / (M:ℝ) := by
    intro M r hM hrN
    have hterm : ∀ s ∈ range r, ‖u ^ (M * N + s + 1) / (M * N + s + 1 : ℂ)‖
        ≤ 1 / ((M:ℝ) * N) := by
      intro s _
      have h1 : ‖u ^ (M * N + s + 1)‖ = 1 := by rw [norm_pow, hu1n, one_pow]
      have h3 : ((M:ℝ) * (N:ℝ)) ≤ ((M * N + s + 1 : ℕ) : ℝ) := by
        have hb : ((M * N : ℕ) : ℝ) ≤ ((M * N + s + 1 : ℕ) : ℝ) :=
          Nat.cast_le.2 (by omega)
        rwa [Nat.cast_mul] at hb
      have hz : (M * N + s + 1 : ℂ) = Complex.ofReal ((M * N + s + 1 : ℕ) : ℝ) := by
        push_cast; ring
      rw [norm_div, h1, hz, ← RCLike.ofReal_eq_complex_ofReal, RCLike.norm_ofReal,
        abs_of_nonneg (by exact_mod_cast Nat.zero_le (M * N + s + 1))]
      exact one_div_le_one_div_of_le (by positivity) h3
    have hcell : (r : ℝ) ≤ N := Nat.cast_le.2 hrN.le
    calc ‖∑ s ∈ range r, u ^ (M * N + s + 1) / (M * N + s + 1 : ℂ)‖
        ≤ ∑ s ∈ range r, ‖u ^ (M * N + s + 1) / (M * N + s + 1 : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ s ∈ range r, (1 / ((M:ℝ) * N)) :=
            Finset.sum_le_sum (fun s hs => hterm s hs)
      _ = (r : ℝ) * (1 / ((M:ℝ) * N)) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (1 / ((M:ℝ) * N)) := by
            exact mul_le_mul_of_nonneg_right hcell (by positivity)
      _ = 1 / (M:ℝ) := by field_simp
  -- partial sums of the raw series converge to ∑' Rp
  have hTl : Tendsto (fun K : ℕ => ∑ n ∈ range K, u ^ (n + 1) / (n + 1 : ℂ)) atTop
      (𝓝 (∑' m : ℕ, Rp m)) := by
    refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
    obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.mp hQ (ε/2) (by linarith)
    set t : ℕ := ⌈(2:ℝ)/ε⌉₊ + 1 with ht
    have hte : ((2:ℝ)/ε) ≤ ((t:ℕ):ℝ) := by
      have h1 := Nat.le_ceil ((2:ℝ)/ε)
      have h2 : ((t:ℕ):ℝ) = (((⌈(2:ℝ)/ε⌉₊ : ℕ) : ℝ) + 1) := by rw [ht]; push_cast; ring
      linarith
    refine ⟨max (M₁ * N) (t * N), ?_⟩
    intro K hK
    have h1 : M₁ * N ≤ K := le_trans (le_max_left _ _) hK
    have h2 : t * N ≤ K := le_trans (le_max_right _ _) hK
    set M : ℕ := K / N with hMdef
    set r : ℕ := K % N with hrdef
    have hKr : M * N + r = K := Nat.div_add_mod' K N
    have hrN : r < N := Nat.mod_lt _ hN
    have hMge : M₁ ≤ M := (Nat.le_div_iff_mul_le hN).mpr h1
    have hMt : t ≤ M := (Nat.le_div_iff_mul_le hN).mpr h2
    have hM2 : ((2:ℝ)/ε) ≤ (M:ℝ) := le_trans hte (by exact_mod_cast hMt)
    have hMre : 0 < (M:ℝ) := lt_of_lt_of_le (by positivity) hM2
    have hMge1 : 1 ≤ M := le_trans (Nat.succ_le_succ (Nat.zero_le _)) hMt
    have hb1n : ‖(∑ m ∈ range M, Rp m) - (∑' m : ℕ, Rp m)‖ < ε/2 := by
      simpa [dist_eq_norm] using hM₁ M hMge
    have hb2 : ‖∑ s ∈ range r, u ^ (M * N + s + 1) / (M * N + s + 1 : ℂ)‖ ≤ ε/2 := by
      have h5 := hres0 M r hMge1 hrN
      have h6 : 1/(M:ℝ) ≤ ε/2 := by
        rw [one_div_le hMre (by linarith), one_div_div]
        linarith
      linarith [h5, h6]
    have hKeq : ∑ n ∈ range K, u ^ (n + 1) / (n + 1 : ℂ)
        = (∑ m ∈ range M, Rp m)
          + (∑ s ∈ range r, u ^ (M * N + s + 1) / (M * N + s + 1 : ℂ)) := by
      rw [show K = M * N + r from hKr.symm]
      exact hsplit M r hrN
    calc dist ((∑ n ∈ range K, u ^ (n + 1) / (n + 1 : ℂ))) ((∑' m : ℕ, Rp m))
        _ = ‖(∑ n ∈ range K, u ^ (n + 1) / (n + 1 : ℂ)) - ∑' m : ℕ, Rp m‖ := dist_eq_norm _ _
        _ = ‖((∑ m ∈ range M, Rp m) - ∑' m : ℕ, Rp m)
              + (∑ s ∈ range r, u ^ (M * N + s + 1) / (M * N + s + 1 : ℂ))‖ := by
            rw [hKeq]
            congr 1
            abel
        _ ≤ ‖(∑ m ∈ range M, Rp m) - ∑' m : ℕ, Rp m‖
              + ‖∑ s ∈ range r, u ^ (M * N + s + 1) / (M * N + s + 1 : ℂ)‖ := norm_add_le _ _
        _ < ε := by linarith
  -- Abel's limit theorem
  set fAb : ℕ → ℂ := fun n => u ^ (n + 1) / (n + 1 : ℂ) with hfAb
  have hTl2 : Tendsto (fun K : ℕ => ∑ n ∈ range K, fAb n) atTop
      (𝓝 (∑' m : ℕ, Rp m)) := hTl
  have hAmb := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt (f := fAb)
      (l := (∑' m : ℕ, Rp m)) hTl2
  have hAmt : Tendsto (fun x : ℝ => ∑' n : ℕ, fAb n * ((x : ℂ) ^ n))
      (𝓝[<](1:ℝ)) (𝓝 (∑' m : ℕ, Rp m)) :=
    hAmb.comp Filter.tendsto_map
  -- shift the variable into (0,1)
  have hShift := shiftTendsto
  have hAmt2 : Tendsto (fun y : ℝ => ∑' n : ℕ, fAb n * (((y + 1/2 : ℝ) : ℂ) ^ n))
      (𝓝[<](1/2:ℝ)) (𝓝 (∑' m : ℕ, Rp m)) := hAmt.comp hShift
  -- interior evaluation for y < 1/2
  have hval : ∀ y : ℝ, 0 < y → y < 1/2 →
      (∑' n : ℕ, fAb n * (((y + 1/2 : ℝ) : ℂ) ^ n))
        = Complex.ofReal (1 / (y + 1/2 : ℝ))
            * (-(Complex.log ((1:ℂ) - Complex.ofReal (y + 1/2 : ℝ) * u))) := by
    intro y hy0 hy
    have hx₀p : 0 < y + 1/2 := by linarith
    have huN : ‖(Complex.ofReal (y + 1/2)) * u‖ = y + 1/2 := by
      have hnorm : ‖(Complex.ofReal (y + 1/2) : ℂ)‖ = |y + 1/2| := RCLike.norm_ofReal _
      rw [norm_mul, hnorm, abs_of_pos hx₀p, hu1n, mul_one]
    have hTay := Complex.hasSum_taylorSeries_neg_log
      (z := Complex.ofReal (y + 1/2) * u) (by rw [huN]; linarith)
    have hTayS : Summable (fun m : ℕ => (Complex.ofReal (y + 1/2) * u) ^ m / m) := hTay.summable
    -- the m = 0 term of the Taylor series vanishes
    have hzero0 : (∑ i ∈ range 1, ((fun m : ℕ => (Complex.ofReal (y + 1/2) * u) ^ m / m) i)) = 0 := by
      simp
    -- ∑' of the shifted series equals the Taylor value
    have hshT : ∑' i : ℕ, ((Complex.ofReal (y + 1/2) * u) ^ (i + 1) / (i + 1 : ℂ))
        = -(Complex.log ((1:ℂ) - Complex.ofReal (y + 1/2) * u)) := by
      have h1 := hTayS.sum_add_tsum_nat_add 1
      rw [hzero0, zero_add] at h1
      simp only [Nat.cast_add, Nat.cast_one] at h1
      rw [h1]
      exact hTay.tsum_eq
    -- per-term equality and scalar pull-out
    have hte : ∀ n : ℕ, u ^ (n + 1) / (n + 1 : ℂ) * ((Complex.ofReal (y + 1/2)) ^ n)
        = Complex.ofReal (1 / (y + 1/2 : ℝ))
            * ((Complex.ofReal (y + 1/2) * u) ^ (n + 1) / (n + 1 : ℂ)) := by
      intro n
      have hcj : Complex.ofReal (1 / (y + 1/2 : ℝ)) * Complex.ofReal (y + 1/2) = 1 := by
        rw [← Complex.ofReal_mul, one_div,
          inv_mul_cancel₀ (by linarith : (y + 1/2 : ℝ) ≠ 0), Complex.ofReal_one]
      have hscal : Complex.ofReal (1 / (y + 1/2 : ℝ)) * Complex.ofReal (y + 1/2) ^ (n + 1)
          = Complex.ofReal (y + 1/2) ^ n := by
        rw [pow_succ, mul_comm (Complex.ofReal (y + 1/2) ^ n) (Complex.ofReal (y + 1/2)),
          ← mul_assoc, hcj, one_mul]
      have hmain : Complex.ofReal (1 / (y + 1/2 : ℝ)) * ((Complex.ofReal (y + 1/2) * u) ^ (n + 1))
          = Complex.ofReal (y + 1/2) ^ n * u ^ (n + 1) := by
        rw [mul_pow, ← mul_assoc, hscal]
      rw [div_mul_eq_mul_div, mul_div_assoc', hmain]
      ring
    have hSS : Summable (fun i : ℕ => (Complex.ofReal (y + 1/2) * u) ^ (i + 1) / (i + 1 : ℂ)) := by
      have h2 := (summable_nat_add_iff
        (f := fun m : ℕ => (Complex.ofReal (y + 1/2) * u) ^ m / m) 1).mpr hTayS
      push_cast at h2 ⊢
      exact h2
    have hSep : (∑' n : ℕ, fAb n * ((Complex.ofReal (y + 1/2)) ^ n))
        = ∑' n : ℕ, (Complex.ofReal (1 / (y + 1/2 : ℝ))
            * ((Complex.ofReal (y + 1/2) * u) ^ (n + 1) / (n + 1 : ℂ))) :=
      tsum_congr hte
    rw [hSep, hSS.tsum_mul_left (Complex.ofReal (1 / (y + 1/2 : ℝ))), hshT]
  -- convergence of the scalar factor and of the log on the shifted neighbourhood
  have hI := invTendsto
  have huRe : u.re < 1 := by
    have habs := Complex.abs_re_le_norm u
    rw [hu1n] at habs
    have h3 : u.re ≤ 1 := by
      obtain ⟨_, h5⟩ := abs_le.mp habs
      exact h5
    by_contra hc
    push_neg at hc
    have hru : u.re = 1 := by linarith
    have hns : u.re * u.re + u.im * u.im = (1:ℝ) := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hu1n]
      norm_num
    rw [hru] at hns
    norm_num at hns
    exact hu1 (Complex.ext_iff.2 ⟨hru, hns⟩)
  have hlogc : ContinuousAt Complex.log ((1:ℂ) - u) :=
    (Complex.differentiableAt_log (by
      refine Or.inl ?_
      simp only [Complex.sub_re, Complex.one_re]
      linarith)).continuousAt
  have hinn : ContinuousAt (fun y : ℝ => ((1:ℂ) - Complex.ofReal (y + 1/2) * u)) ((1:ℝ)/2) :=
    (subMulContinuous (u := u)).continuousAt
  have hL : Tendsto (fun y : ℝ => Complex.log ((1:ℂ) - Complex.ofReal (y + 1/2) * u))
      (𝓝[<](1/2:ℝ)) (𝓝 (Complex.log (1 - u))) := by
    have hpt : ((1:ℂ) - Complex.ofReal ((1:ℝ)/2 + 1/2) * u) = 1 - u := by
      have hpt2 : (((1:ℝ)/2 + 1/2 : ℝ)) = 1 := by norm_num
      rw [hpt2, Complex.ofReal_one, one_mul]
    have hcomp : ContinuousAt Complex.log
        ((1:ℂ) - Complex.ofReal ((1:ℝ)/2 + 1/2) * u) := by
      rw [hpt]
      exact hlogc
    have hT2 := hcomp.tendsto.comp hinn.tendsto
    rw [hpt] at hT2
    exact hT2.mono_left nhdsWithin_le_nhds
  have hD2 : Tendsto (fun y : ℝ => Complex.ofReal (1 / (y + 1/2 : ℝ))
      * (-(Complex.log ((1:ℂ) - Complex.ofReal (y + 1/2 : ℝ) * u))))
      (𝓝[<](1/2:ℝ)) (𝓝 (-(Complex.log (1 - u)))) := by
    have h5 : Tendsto (fun y : ℝ => Complex.ofReal (1 / (y + 1/2 : ℝ))
        * (-(Complex.log ((1:ℂ) - Complex.ofReal (y + 1/2 : ℝ) * u))))
        (𝓝[<](1/2:ℝ)) (𝓝 ((1:ℂ) * -(Complex.log (1 - u)))) := hI.mul (hL.neg)
    simpa using h5
  -- uniqueness: the shifted Abel limit equals the log value
  have hIoi : (Set.Ioi (0:ℝ)) ∈ 𝓝[<](1/2:ℝ) :=
    mem_nhdsWithin.2 ⟨Set.Ioi (0:ℝ), isOpen_Ioi, Set.mem_Ioi.mpr (by norm_num : (0:ℝ) < (1:ℝ)/2),
      Set.inter_subset_left⟩
  have hposE : ∀ᶠ y : ℝ in 𝓝[<](1/2:ℝ), 0 < y := Filter.eventually_iff.2 hIoi
  have hCon : (fun y : ℝ => ∑' n : ℕ, fAb n * (((y + 1/2 : ℝ) : ℂ) ^ n))
      =ᶠ[𝓝[<](1/2:ℝ)] (fun y : ℝ => Complex.ofReal (1 / (y + 1/2 : ℝ))
        * (-(Complex.log ((1:ℂ) - Complex.ofReal (y + 1/2 : ℝ) * u)))) := by
    filter_upwards [self_mem_nhdsWithin, hposE] with y hy hy0
    exact hval y hy0 hy
  have hGi : Tendsto (fun y : ℝ => Complex.ofReal (1 / (y + 1/2 : ℝ))
      * (-(Complex.log ((1:ℂ) - Complex.ofReal (y + 1/2 : ℝ) * u))))
      (𝓝[<](1/2:ℝ)) (𝓝 (∑' m : ℕ, Rp m)) := Tendsto.congr' hCon hAmt2
  have hUni : (∑' m : ℕ, Rp m) = -(Complex.log (1 - u)) :=
    tendsto_nhds_unique hGi hD2
  rw [← hUni]
  exact hTl

end BoundaryBrick
