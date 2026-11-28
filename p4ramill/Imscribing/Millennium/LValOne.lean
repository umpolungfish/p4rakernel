import Mathlib
import Imscribing.Millennium.LSeriesConv

/-!
# LValOne: value identification `L(1, Ψ) = lim ∑ Ψ(n)/n` at the boundary

For `Ψ : ZMod N → ℂ` with `∑ Ψ = 0`, the congruence L-function at `s = 1`
equals the limit of the classical partial sums `∑_{1 ≤ n ≤ K} Ψ(n)/n`
(the Dirichlet/Abel conditional limit from `LSeriesConv`).

Route: for real `s ≥ 1` the partial sums `∑_{n<K} (n+1)^{-s}•Ψ(n+1)` converge
(`LSeriesConv.dirichlet_exists`), with tails bounded by `2·B/(K+1)` UNIFORMLY
in `s ≥ 1` (Abel + `dcoef s ≤ dcoef 1`). The limit function `Slim` is
right-continuous at `s = 1`; for `s > 1` it coincides with `ZMod.LFunction Ψ s`
(which agrees with the `LSeries` there); both sides are right-continuous
limits of functions agreeing on `(1, ∞)`, so they agree at `1`.
-/

open Complex Real Filter Finset Topology
open scoped LSeries

noncomputable section

namespace LValOne

variable {N : ℕ} [NeZero N]

/-- The numerator sequence in `LSeries` alignment: `zseq Ψ n = Ψ(n+1)`. -/
def zseq (Ψ : ZMod N → ℂ) : ℕ → ℂ := fun n => Ψ ((n : ZMod N) + 1)

/-- The `ℕ`-indexed version of `Ψ`. -/
def zfun (Ψ : ZMod N → ℂ) : ℕ → ℂ := fun n => Ψ ((n : ℕ) : ZMod N)

/-- The Dirichlet coefficient at exponent `s`: `(n+1)^{-s}`. -/
def dcoef (s : ℝ) : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-s)

theorem dcoef_nonneg (s : ℝ) : ∀ n, 0 ≤ dcoef s n := by
  intro n
  show 0 ≤ ((n : ℝ) + 1) ^ (-s)
  exact Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1) (-s)

theorem dcoef_antitone (s : ℝ) (hs : 0 ≤ s) : Antitone (dcoef s) := by
  intro a b hab
  show ((b : ℝ) + 1) ^ (-s) ≤ ((a : ℝ) + 1) ^ (-s)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.succ_le_succ hab)
    (by linarith)

theorem dcoef_le_one (s : ℝ) (hs : 1 ≤ s) (n : ℕ) :
    dcoef s n ≤ dcoef 1 n := by
  show ((n : ℝ) + 1) ^ (-s) ≤ ((n : ℝ) + 1) ^ (-(1:ℝ))
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    (by linarith)

theorem dcoef_tendsto (s : ℝ) (hs : 1 ≤ s) : Tendsto (dcoef s) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_eq_one_div] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hlow : (fun n : ℕ => (0:ℝ)) ≤ dcoef s := fun n => dcoef_nonneg s n
  have hhigh : dcoef s ≤ (fun n : ℕ => ((n : ℝ) + 1)⁻¹) := by
    intro n
    have hx1 : (1:ℝ) ≤ (n:ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have h2 : ((n : ℝ) + 1) ^ (-s) ≤ ((n : ℝ) + 1) ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rwa [Real.rpow_neg_one] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 hlow hhigh

/-- The `s`-partial sums in `LSeries` alignment. -/
def Upartial (Ψ : ZMod N → ℂ) (s : ℝ) (K : ℕ) : ℂ :=
  ∑ n ∈ Finset.range K, (dcoef s n : ℝ) • zseq Ψ n

/-- The boundedness input: partial sums of `zseq` are bounded by the total
variation of `Ψ`. -/
theorem zseq_bound (Ψ : ZMod N → ℂ) (hsum : ∑ j, Ψ j = 0) (K : ℕ) :
    ‖∑ n ∈ Finset.range K, zseq Ψ n‖ ≤ ∑ j, ‖Ψ j‖ := by
  have hψ0 : ∑ j : ZMod N, Ψ (j + 1) = 0 :=
    (Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) (fun j => Ψ (j + 1)) (fun j => Ψ j)
      (fun _ => rfl)).trans hsum
  have hnorm : ∑ j : ZMod N, ‖Ψ (j + 1)‖ = ∑ j : ZMod N, ‖Ψ j‖ :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) (fun j => ‖Ψ (j + 1)‖) (fun j => ‖Ψ j‖)
      (fun _ => rfl)
  refine le_trans (LSeriesConv.resSum_bound (fun x : ZMod N => Ψ (x + 1)) hψ0 K) ?_
  rw [hnorm]

/-- Existence of the `s`-limit for `s ≥ 1` (Dirichlet test). -/
theorem exists_lim (Ψ : ZMod N → ℂ) (hsum : ∑ j, Ψ j = 0) (s : ℝ) (hs : 1 ≤ s) :
    ∃ S : ℂ, Tendsto (Upartial Ψ s) atTop (𝓝 S) :=
  LSeriesConv.dirichlet_exists (dcoef s) (dcoef_antitone s (zero_le_one.trans hs))
    (dcoef_nonneg s) (dcoef_tendsto s hs) (zseq Ψ) (∑ j, ‖Ψ j‖) (zseq_bound Ψ hsum)

/-- The limit value at exponent `s` (for `s < 1` it is set to `0`). -/
noncomputable def Slim (Ψ : ZMod N → ℂ) (hsum : ∑ j, Ψ j = 0) (s : ℝ) : ℂ :=
  if hs : 1 ≤ s then (exists_lim Ψ hsum s hs).choose else 0

theorem Slim_spec (Ψ : ZMod N → ℂ) (hsum : ∑ j, Ψ j = 0) (s : ℝ) (hs : 1 ≤ s) :
    Tendsto (Upartial Ψ s) atTop (𝓝 (Slim Ψ hsum s)) := by
  rw [Slim, dif_pos hs]
  exact (exists_lim Ψ hsum s hs).choose_spec

/-- Uniform tail bound: `‖S(s) − U(s,K)‖ ≤ 2·B/(K+1)` for `s ≥ 1`. -/
theorem Slim_tail (Ψ : ZMod N → ℂ) (hsum : ∑ j, Ψ j = 0) (s : ℝ) (hs : 1 ≤ s) (K : ℕ) :
    ‖Slim Ψ hsum s - Upartial Ψ s K‖ ≤ 2 * (∑ j, ‖Ψ j‖) * ((K : ℝ) + 1)⁻¹ := by
  have hB0 : 0 ≤ ∑ j, ‖Ψ j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hsub : Tendsto (fun M => Upartial Ψ s M - Upartial Ψ s K) atTop
      (𝓝 (Slim Ψ hsum s - Upartial Ψ s K)) := (Slim_spec Ψ hsum s hs).sub tendsto_const_nhds
  have hnorm : Tendsto (fun M => ‖Upartial Ψ s M - Upartial Ψ s K‖) atTop
      (𝓝 ‖Slim Ψ hsum s - Upartial Ψ s K‖) := hsub.norm
  have htail : ∀ M : ℕ, K ≤ M → ‖Upartial Ψ s M - Upartial Ψ s K‖
      ≤ 2 * (∑ j, ‖Ψ j‖) * dcoef s K := by
    intro M hKM
    rw [Upartial, Upartial, ← Finset.sum_Ico_eq_sub (fun i => (dcoef s i : ℝ) • zseq Ψ i) hKM]
    exact LSeriesConv.abel_tail_bound (zseq Ψ) (∑ j, ‖Ψ j‖) (zseq_bound Ψ hsum)
      (dcoef s) (dcoef_antitone s (zero_le_one.trans hs)) (dcoef_nonneg s) hKM
  refine le_trans (le_of_tendsto hnorm
    (Filter.eventually_atTop.mpr ⟨K, fun M hM => htail M hM⟩)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (dcoef_le_one s hs K) (by linarith)) ?_
  rw [show dcoef 1 K = ((K : ℝ) + 1) ^ (-1 : ℝ) from rfl, Real.rpow_neg_one, inv_eq_one_div]

/-- Existence of a block length making the doubled tail smaller than `ε/2`. -/
theorem exists_K₀ (B : ℝ) (hB : 0 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℕ, 4 * B * ((K₀ : ℝ) + 1)⁻¹ < ε / 2 := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (8 * B / ε : ℝ) < (K : ℝ) := exists_nat_gt _
  have hK1 : (8 * B / ε : ℝ) < (K : ℝ) + 1 := by linarith
  have h8 : 8 * B < ((K : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hK1
  refine ⟨K, ?_⟩
  have h1 : (0:ℝ) < (K : ℝ) + 1 := by positivity
  rw [show (4 * B * ((K : ℝ) + 1)⁻¹ : ℝ) = 4 * B / ((K : ℝ) + 1) from by ring,
    div_lt_iff₀ h1]
  linarith

/-- Right-continuity of the limit function at `s = 1`. -/
theorem Slim_right_cont (Ψ : ZMod N → ℂ) (hsum : ∑ j, Ψ j = 0) :
    Tendsto (Slim Ψ hsum) (𝓝[≥] (1 : ℝ)) (𝓝 (Slim Ψ hsum 1)) := by
  have hB0 : 0 ≤ ∑ j, ‖Ψ j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hdcoefcont : ∀ n : ℕ, Continuous (fun s : ℝ => dcoef s n) := by
    intro n
    show Continuous (fun s : ℝ => ((n : ℝ) + 1) ^ (-s))
    have hf : Continuous (fun _ : ℝ => ((n : ℝ) + 1)) := continuous_const
    have hg : Continuous (fun s : ℝ => -s) := continuous_neg
    exact hf.rpow hg fun _ => Or.inl (by positivity : ((n : ℝ) + 1) ≠ 0)
  have hUpcont : ∀ K : ℕ, Continuous (fun s : ℝ => Upartial Ψ s K) := by
    intro K
    simp only [Upartial]
    exact continuous_finset_sum _ fun n _ => (hdcoefcont n).smul continuous_const
  have hmid : ∀ K : ℕ, Tendsto (fun s : ℝ => Upartial Ψ s K) (𝓝[≥] (1 : ℝ))
      (𝓝 (Upartial Ψ 1 K)) :=
    fun K => (hUpcont K).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds)
  have hmidK₀ : ∀ K₀ : ℕ, Tendsto
      (fun s : ℝ => ‖Upartial Ψ s K₀ - Upartial Ψ 1 K₀‖) (𝓝[≥] (1 : ℝ)) (𝓝 0) := by
    intro K₀
    have hsub1 : Tendsto (fun s : ℝ => Upartial Ψ s K₀ - Upartial Ψ 1 K₀) (𝓝[≥] (1 : ℝ))
        (𝓝 (Upartial Ψ 1 K₀ - Upartial Ψ 1 K₀)) :=
      (hmid K₀).sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => Upartial Ψ 1 K₀)
        (𝓝[≥] (1 : ℝ)) (𝓝 (Upartial Ψ 1 K₀)))
    simpa only [sub_self, norm_zero] using hsub1.norm
  refine Metric.tendsto_nhdsWithin_nhds.mpr ?_
  intro ε hε
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, 4 * (∑ j, ‖Ψ j‖) * ((K₀ : ℝ) + 1)⁻¹ < ε / 2 :=
    exists_K₀ _ hB0 hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hmidK₀ K₀) (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro s hs hdist
  have hUp := hclose hs hdist
  rw [dist_eq_norm, sub_zero, norm_norm] at hUp
  rw [dist_eq_norm]
  calc ‖Slim Ψ hsum s - Slim Ψ hsum 1‖
      ≤ 4 * (∑ j, ‖Ψ j‖) * ((K₀ : ℝ) + 1)⁻¹ + ‖Upartial Ψ s K₀ - Upartial Ψ 1 K₀‖ := by
        have h1 := Slim_tail Ψ hsum s (Set.mem_Ici.mp hs) K₀
        have h2 := Slim_tail Ψ hsum 1 le_rfl K₀
        have h3 : Slim Ψ hsum s - Slim Ψ hsum 1 =
            (Slim Ψ hsum s - Upartial Ψ s K₀) + (Upartial Ψ s K₀ - Upartial Ψ 1 K₀)
              - (Slim Ψ hsum 1 - Upartial Ψ 1 K₀) := by ring
        rw [h3]
        have h4 : ‖(Slim Ψ hsum s - Upartial Ψ s K₀) + (Upartial Ψ s K₀ - Upartial Ψ 1 K₀)
              - (Slim Ψ hsum 1 - Upartial Ψ 1 K₀)‖ ≤
            ‖Slim Ψ hsum s - Upartial Ψ s K₀‖ + ‖Upartial Ψ s K₀ - Upartial Ψ 1 K₀‖
              + ‖Slim Ψ hsum 1 - Upartial Ψ 1 K₀‖ :=
          le_trans (norm_sub_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
        linarith [h1, h2, h4]
    _ < ε := by linarith [hK₀, hUp]

/-! ## Alignment with the `LSeries` for `s > 1` -/

/-- The `ℂ`-power of a shifted natural, in real-`rpow` form. -/
theorem natCast_cpow_real {n : ℕ} (s : ℝ) :
    ((n + 1 : ℕ) : ℂ) ^ (s : ℂ) = Complex.ofReal (((n : ℝ) + 1) ^ s) := by
  rw [← Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one,
    Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (n:ℝ) + 1) s]

/-- Termwise: the `Upartial` summand is the shifted `LSeries` term. -/
theorem up_summand (Ψ : ZMod N → ℂ) (s : ℝ) (n : ℕ) :
    (dcoef s n : ℝ) • zseq Ψ n = LSeries.term (zfun Ψ) (s : ℂ) (n + 1) := by
  have hne : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
  rw [LSeries.term_of_ne_zero hne]
  rw [show (dcoef s n : ℝ) • zseq Ψ n = Complex.ofReal (dcoef s n) * zseq Ψ n from by rfl]
  simp only [zseq, zfun, dcoef]
  rw [show ((n : ZMod N) + 1) = ((n + 1 : ℕ) : ZMod N) from by rw [Nat.cast_add, Nat.cast_one],
    show ((n + 1 : ℕ) : ℂ) = Complex.ofReal (((n : ℝ) + 1)) from by
      rw [← Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one],
    Real.rpow_neg (by positivity) s, Complex.ofReal_inv, div_eq_inv_mul,
    Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (n:ℝ) + 1) s]

/-- Shifting a zero-starting sequence inside a range sum (off by one). -/
theorem range_shift (g : ℕ → ℂ) (hg0 : g 0 = 0) (K : ℕ) :
    ∑ n ∈ Finset.range K, g (n + 1) = ∑ m ∈ Finset.range (K + 1), g m := by
  induction K with
  | zero => simp [hg0]
  | succ K ih =>
      rw [Finset.sum_range_succ (fun m => g m) (K + 1), Finset.sum_range_succ, ih]

theorem lSeries_eq_Slim (Ψ : ZMod N → ℂ) (hsum : ∑ j, Ψ j = 0) (s : ℝ) (hs : 1 < s) :
    LSeries (zfun Ψ) (s : ℂ) = Slim Ψ hsum s := by
  have hg0 : LSeries.term (zfun Ψ) (s : ℂ) 0 = 0 := by
    rw [LSeries.term_def, if_pos rfl]
  have hsum' : Summable (LSeries.term (zfun Ψ) (s : ℂ)) :=
    ZMod.LSeriesSummable_of_one_lt_re Ψ (by rwa [Complex.ofReal_re])
  have hUeq : ∀ K : ℕ,
      Upartial Ψ s K = ∑ m ∈ Finset.range (K + 1), LSeries.term (zfun Ψ) (s : ℂ) m := by
    intro K
    calc Upartial Ψ s K = ∑ n ∈ Finset.range K, (dcoef s n : ℝ) • zseq Ψ n := rfl
      _ = ∑ n ∈ Finset.range K, LSeries.term (zfun Ψ) (s : ℂ) (n + 1) :=
          Finset.sum_congr rfl fun n _ => up_summand Ψ s n
      _ = ∑ m ∈ Finset.range (K + 1), LSeries.term (zfun Ψ) (s : ℂ) m :=
          range_shift _ hg0 K
  have hlimD : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, LSeries.term (zfun Ψ) (s : ℂ) n)
      atTop (𝓝 (∑' n : ℕ, LSeries.term (zfun Ψ) (s : ℂ) n)) :=
    hsum'.hasSum.tendsto_sum_nat
  have hlimD2 := hlimD.comp (tendsto_add_atTop_nat 1)
  have hcomb : Tendsto (fun K : ℕ => Upartial Ψ s K)
      atTop (𝓝 (∑' n : ℕ, LSeries.term (zfun Ψ) (s : ℂ) n)) :=
    Tendsto.congr' (Filter.Eventually.of_forall fun K => (hUeq K).symm) hlimD2
  show ∑' n : ℕ, LSeries.term (zfun Ψ) (s : ℂ) n = Slim Ψ hsum s
  exact tendsto_nhds_unique hcomb (Slim_spec Ψ hsum s (le_of_lt hs))

theorem lFunction_alignment (Ψ : ZMod N → ℂ) (hsum : ∑ j, Ψ j = 0) (s : ℝ) (hs : 1 < s) :
    ZMod.LFunction Ψ (s : ℂ) = Slim Ψ hsum s := by
  rw [ZMod.LFunction_eq_LSeries Ψ (by rwa [Complex.ofReal_re])]
  exact lSeries_eq_Slim Ψ hsum s hs

/-! ## The boundary value -/

/-- **Brick V.** For `∑ Ψ = 0`, the congruence L-function at `s = 1` equals the
Dirichlet/Abel conditional limit of `∑ Ψ(n)/n`. -/
theorem lFunction_one_eq (Ψ : ZMod N → ℂ) (hsum : ∑ j, Ψ j = 0) :
    ZMod.LFunction Ψ 1 = Slim Ψ hsum 1 := by
  have hdiff : DifferentiableAt ℂ (ZMod.LFunction Ψ) 1 :=
    ZMod.differentiableAt_LFunction Ψ 1 (Or.inr hsum)
  have hcontL : Tendsto (fun s : ℝ => ZMod.LFunction Ψ (s : ℂ)) (𝓝[≥] (1 : ℝ))
      (𝓝 (ZMod.LFunction Ψ 1)) :=
    (ContinuousAt.comp (g := ZMod.LFunction Ψ) (f := fun s : ℝ => (s : ℂ))
      hdiff.continuousAt continuous_ofReal.continuousAt).tendsto.mono_left
      (nhdsWithin_le_nhds)
  have hcontS := Slim_right_cont Ψ hsum
  have hIoi : (Set.Ioi (1 : ℝ)) ∈ 𝓝[Set.Ioi (1 : ℝ)] (1 : ℝ) :=
    mem_nhdsWithin.mpr ⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo,
      (by norm_num : (1:ℝ) ∈ Set.Ioo 0 2), Set.inter_subset_right⟩
  have hev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[Set.Ioi (1 : ℝ)] (1 : ℝ)]
      (fun s : ℝ => ZMod.LFunction Ψ (s : ℂ) - Slim Ψ hsum s) := by
    refine Filter.eventually_of_mem hIoi fun s hs => ?_
    show (0:ℂ) = ZMod.LFunction Ψ (s : ℂ) - Slim Ψ hsum s
    rw [lFunction_alignment Ψ hsum s (Set.mem_Ioi.mp hs)]
    exact (sub_self _).symm
  have hzero : Tendsto (fun s : ℝ => ZMod.LFunction Ψ (s : ℂ) - Slim Ψ hsum s)
      (𝓝[Set.Ioi (1 : ℝ)] (1 : ℝ)) (𝓝 0) :=
    Tendsto.congr' hev tendsto_const_nhds
  have hcontD : Tendsto (fun s : ℝ => ZMod.LFunction Ψ (s : ℂ) - Slim Ψ hsum s)
      (𝓝[Set.Ioi (1 : ℝ)] (1 : ℝ)) (𝓝 (ZMod.LFunction Ψ 1 - Slim Ψ hsum 1)) :=
    (hcontL.sub hcontS).mono_left (nhdsWithin_mono (1 : ℝ) (Set.Ioi_subset_Ici le_rfl))
  haveI := nhdsWithin_Ioi_neBot (le_refl (1 : ℝ))
  exact sub_eq_zero.mp (tendsto_nhds_unique hzero hcontD).symm

end LValOne
