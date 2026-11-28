import Mathlib

/-!
# LSeriesConv: the Dirichlet/Abel bridge for congruence L-functions

Three-layer brick: (1) Abel tail bound (telescoping by parts); (2) residue-block
boundedness — partial sums of a `ZMod N`-periodic sequence with total sum zero
are bounded by the total variation `∑ ‖ψ j‖`; (3) Dirichlet test — bounded partial
sums against an antitone nonnegative null sequence converge. Application: for
`ψ : ZMod N → ℂ` with `∑ ψ = 0`, the partial sums of `ψ(n)/(n+1)` converge.
-/

open Complex Real Filter Finset Topology
open scoped LSeries

noncomputable section

namespace LSeriesConv

/-! ## Abel tail bound -/

/-- Telescoping over an `Ico`. -/
theorem telescope (d : ℕ → ℝ) (K M : ℕ) (hKM : K ≤ M) :
    ∑ i ∈ Finset.Ico K M, (d i - d (i + 1)) = d K - d M := by
  induction M with
  | zero =>
    have hK0 : K = 0 := le_antisymm hKM (Nat.zero_le _)
    subst hK0
    rw [Finset.sum_Ico_eq_sub _ (le_refl 0), sub_self]
    ring
  | succ m ih =>
    by_cases hKm : K ≤ m
    · have hsplit : ∑ i ∈ Finset.Ico K (m + 1), (d i - d (i + 1))
        = (∑ i ∈ Finset.Ico K m, (d i - d (i + 1))) + (d m - d (m + 1)) := by
        rw [Finset.sum_Ico_eq_sub _ (by omega : K ≤ m + 1), Finset.sum_range_succ,
          Finset.sum_Ico_eq_sub _ hKm]
        abel
      rw [hsplit, ih hKm]
      ring
    · push_neg at hKm
      have hK : K = m + 1 := by omega
      subst hK
      rw [Finset.sum_Ico_eq_sub _ (le_refl (m + 1)), sub_self]
      ring

/-- Abel tail estimate: if the partial sums of `z` are bounded by `B` and `d` is
antitone and nonnegative, then every block sum of `d n • z n` is at most `2·B·d K`. -/
theorem abel_tail_bound (z : ℕ → ℂ) (B : ℝ) (hB : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B)
    (d : ℕ → ℝ) (hd : Antitone d) (hdnn : ∀ n, 0 ≤ d n) {K M : ℕ} (hKM : K ≤ M) :
    ‖∑ i ∈ Finset.Ico K M, (d i : ℝ) • z i‖ ≤ 2 * B * d K := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  rcases lt_or_ge K M with hlt | hge
  · -- rewrite the block sum into by-parts form
    have key : ∑ i ∈ Finset.Ico K M, (d i : ℝ) • z i
        = (d (M - 1) : ℝ) • (∑ i ∈ Finset.range M, z i)
          - (d K : ℝ) • (∑ i ∈ Finset.range K, z i)
          - ∑ i ∈ Finset.Ico K (M - 1), (d (i + 1) - d i : ℝ)
              • (∑ j ∈ Finset.range (i + 1), z j) :=
      Finset.sum_Ico_by_parts (f := (d : ℕ → ℝ)) (g := z) hlt
    -- norm estimates for the three pieces
    have h1 : ‖(d (M - 1) : ℝ) • (∑ i ∈ Finset.range M, z i)‖ ≤ d (M - 1) * B := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hdnn _)]
      exact mul_le_mul_of_nonneg_left (hB M) (hdnn _)
    have h2 : ‖(d K : ℝ) • (∑ i ∈ Finset.range K, z i)‖ ≤ d K * B := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hdnn _)]
      exact mul_le_mul_of_nonneg_left (hB K) (hdnn _)
    have hdif : ∀ i ∈ Finset.Ico K (M - 1),
        ‖(d (i + 1) - d i : ℝ) • (∑ j ∈ Finset.range (i + 1), z j)‖
          ≤ (d i - d (i + 1)) * B := by
      intro i _
      have hle : d (i + 1) ≤ d i := hd (Nat.le_succ i)
      rw [norm_smul, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
      exact mul_le_mul_of_nonneg_left (hB (i + 1)) (sub_nonneg.mpr hle)
    have hmid : ‖∑ i ∈ Finset.Ico K (M - 1), (d (i + 1) - d i : ℝ)
        • (∑ j ∈ Finset.range (i + 1), z j)‖ ≤ (d K - d (M - 1)) * B := by
      have hS : ∑ i ∈ Finset.Ico K (M - 1), (d i - d (i + 1)) = d K - d (M - 1) :=
        telescope d K (M - 1) (by omega)
      calc ‖∑ i ∈ Finset.Ico K (M - 1), (d (i + 1) - d i : ℝ)
            • (∑ j ∈ Finset.range (i + 1), z j)‖
          ≤ ∑ i ∈ Finset.Ico K (M - 1), ‖(d (i + 1) - d i : ℝ)
              • (∑ j ∈ Finset.range (i + 1), z j)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.Ico K (M - 1), (d i - d (i + 1)) * B := Finset.sum_le_sum hdif
        _ = (∑ i ∈ Finset.Ico K (M - 1), (d i - d (i + 1))) * B := by
            rw [Finset.sum_mul]
        _ = (d K - d (M - 1)) * B := by rw [hS]
    have hcomb : ‖(d (M - 1) : ℝ) • (∑ i ∈ Finset.range M, z i)
        - (d K : ℝ) • (∑ i ∈ Finset.range K, z i)
        - ∑ i ∈ Finset.Ico K (M - 1), (d (i + 1) - d i : ℝ)
            • (∑ j ∈ Finset.range (i + 1), z j)‖
        ≤ d (M - 1) * B + d K * B + (d K - d (M - 1)) * B := by
      have htri : ∀ (A B' C : ℂ), ‖A - B' - C‖ ≤ ‖A‖ + ‖B'‖ + ‖C‖ := by
        intro A B' C
        have e1 := norm_sub_le (A - B') C
        have e2 := norm_sub_le A B'
        linarith
      simpa using (htri _ _ _).trans (add_le_add (add_le_add h1 h2) hmid)
    calc ‖∑ i ∈ Finset.Ico K M, (d i : ℝ) • z i‖
        ≤ d (M - 1) * B + d K * B + (d K - d (M - 1)) * B := by rw [key]; exact hcomb
      _ ≤ 2 * B * d K := by nlinarith
  · have hKM' : K = M := le_antisymm hKM hge
    subst hKM'
    rw [Finset.sum_Ico_eq_sub _ (le_refl K), sub_self, norm_zero]
    nlinarith [hB0, hdnn K]

/-! ## Residue-block bound -/

/-- Reindex a Fintype sum over `ZMod N` as a sum over `range N`. -/
theorem sum_rangeN {N : ℕ} [NeZero N] {M : Type*} [AddCommMonoid M] (ψ : ZMod N → M) :
    ∑ i ∈ Finset.range N, ψ ((i : ZMod N)) = ∑ j, ψ j := by
  refine Finset.sum_bij (fun i _ => (i : ZMod N)) ?_ ?_ ?_ ?_ <;> intro x hx
  · exact Finset.mem_univ _
  · intro y hy hxy
    have hv : ((x : ZMod N)).val = ((y : ZMod N)).val := congrArg ZMod.val hxy
    rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hx),
      ZMod.val_cast_of_lt (Finset.mem_range.mp hy)] at hv
    exact hv
  · refine ⟨x.val, Finset.mem_range.mpr x.val_lt, ?_⟩
    dsimp only
    exact ZMod.natCast_zmod_val x
  · rfl

/-- Full blocks of `N` consecutive integers sum to zero when `∑ ψ = 0`. -/
theorem range_mul_sum {N : ℕ} [NeZero N] {M : Type*} [AddCommGroup M]
    (ψ : ZMod N → M) (hpsi : ∑ j, ψ j = 0) (q : ℕ) :
    ∑ n ∈ Finset.range (N * q), ψ ((n : ZMod N)) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hstep : N * (q + 1) = N * q + N := by ring
    rw [hstep, Finset.sum_range_add]
    rw [ih, zero_add]
    have hzero : ∀ k : ℕ, ((N * q + k : ℕ) : ZMod N) = ((k : ZMod N)) := by
      intro k
      have h0 : (((N * q : ℕ) : ZMod N)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact Nat.dvd_mul_right N q
      calc ((N * q + k : ℕ) : ZMod N)
          = (((N * q : ℕ) : ZMod N) + ((k : ℕ) : ZMod N) : ZMod N) := by rw [Nat.cast_add]
        _ = (((0 : ZMod N) + ((k : ℕ) : ZMod N) : ZMod N)) := by rw [h0]
        _ = ((k : ZMod N)) := by simp
    rw [Finset.sum_congr rfl (fun k _ => by rw [hzero k])]
    rw [sum_rangeN, hpsi]

/-- Boundedness of partial sums of a residue-class sequence with zero total sum. -/
theorem resSum_bound {N : ℕ} [NeZero N] (ψ : ZMod N → ℂ) (hpsi : ∑ j, ψ j = 0) :
    ∀ K : ℕ, ‖∑ n ∈ Finset.range K, ψ ((n : ZMod N))‖ ≤ ∑ j, ‖ψ j‖ := by
  intro K
  obtain ⟨q, r, hrfl, hrlt⟩ : ∃ q r, K = N * q + r ∧ r < N :=
    ⟨K / N, K % N, (Nat.div_add_mod K N).symm, Nat.mod_lt K (NeZero.pos N)⟩
  rw [hrfl, Finset.sum_range_add, range_mul_sum ψ hpsi q, zero_add]
  have hzero : ∀ k : ℕ, ((N * q + k : ℕ) : ZMod N) = ((k : ZMod N)) := by
    intro k
    have h0 : (((N * q : ℕ) : ZMod N)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_mul_right N q
    calc ((N * q + k : ℕ) : ZMod N)
        = (((N * q : ℕ) : ZMod N) + ((k : ℕ) : ZMod N) : ZMod N) := by rw [Nat.cast_add]
      _ = (((0 : ZMod N) + ((k : ℕ) : ZMod N) : ZMod N)) := by rw [h0]
      _ = ((k : ZMod N)) := by simp
  have hnorm : ‖∑ k ∈ Finset.range r, ψ (((N * q + k : ℕ) : ZMod N))‖
      ≤ ∑ k ∈ Finset.range r, ‖ψ ((k : ZMod N))‖ := by
    have heq : ∑ k ∈ Finset.range r, ψ (((N * q + k : ℕ) : ZMod N))
        = ∑ k ∈ Finset.range r, ψ ((k : ZMod N)) :=
      Finset.sum_congr rfl (fun k _ => by rw [hzero k])
    rw [heq]
    exact norm_sum_le _ _
  refine hnorm.trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hi) (le_of_lt hrlt)))
    (fun i _ _ => norm_nonneg _)).trans ?_
  rw [← sum_rangeN (fun j => ‖ψ j‖)]

/-! ## Dirichlet test -/

/-- Dirichlet test: bounded partial sums against an antitone null sequence of
nonnegative reals give a convergent series. -/
theorem dirichlet_exists (d : ℕ → ℝ) (hd : Antitone d) (hdnn : ∀ n, 0 ≤ d n)
    (h0 : Tendsto d atTop (𝓝 0)) (z : ℕ → ℂ) (B : ℝ)
    (hB : ∀ K, ‖∑ n ∈ Finset.range K, z n‖ ≤ B) :
    ∃ L : ℂ, Tendsto (fun K => ∑ n ∈ Finset.range K, (d n : ℝ) • z n) atTop (𝓝 L) := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  have hD : (2:ℝ) * B + 1 ≠ 0 := ne_of_gt (by linarith)
  have hbb : ∀ ε : ℝ, 0 < ε → 2 * B * (ε / (2 * B + 1)) < ε := by
    intro ε hε
    have hlt : (0:ℝ) ≤ 2 * B + 1 := by linarith
    refine lt_of_mul_lt_mul_right ?_ hlt
    have key : (2 * B * (ε / (2 * B + 1))) * (2 * B + 1) < ε * (2 * B + 1) := by
      field_simp
      nlinarith
    exact key
  have htail : ∀ {K M : ℕ}, K ≤ M → ‖(∑ n ∈ Finset.range M, (d n : ℝ) • z n)
      - ∑ n ∈ Finset.range K, (d n : ℝ) • z n‖ ≤ 2 * B * d K := by
    intro K M hKM
    rw [← Finset.sum_Ico_eq_sub (fun i => (d i : ℝ) • z i) hKM]
    exact abel_tail_bound z B hB d hd hdnn hKM
  have hcauchy : CauchySeq (fun K => ∑ n ∈ Finset.range K, (d n : ℝ) • z n) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨K0, hK0⟩ := Metric.tendsto_atTop.mp h0 (ε / (2 * B + 1)) (div_pos hε (by linarith))
    refine ⟨K0, fun i hi => ?_⟩
    have hbound := htail hi
    have hdK : d K0 < ε / (2 * B + 1) := by
      have h1 := hK0 K0 (le_refl K0)
      rwa [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hdnn K0)] at h1
    refine lt_of_le_of_lt ?_ (hbb ε hε)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_of_lt hdK) (by linarith))
    rw [dist_eq_norm]
    exact hbound
  exact cauchySeq_tendsto_of_complete hcauchy

/-- The congruence L-series over residues converges when `∑ ψ = 0`:
the partial sums of `ψ(n) / (n+1)` converge. -/
theorem lsconv_conv_exists {N : ℕ} [NeZero N] (ψ : ZMod N → ℂ) (hpsi : ∑ j, ψ j = 0) :
    ∃ L : ℂ, Tendsto (fun K => ∑ n ∈ Finset.range K,
      (1 / (((n : ℝ) + 1)) : ℝ) • ψ ((n : ZMod N))) atTop (𝓝 L) :=
  dirichlet_exists (fun n => 1 / ((n : ℝ) + 1))
    (fun a b hab => one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hab))
    (fun n => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n => ψ ((n : ZMod N))) (∑ j, ‖ψ j‖) (resSum_bound ψ hpsi)

end LSeriesConv

end
