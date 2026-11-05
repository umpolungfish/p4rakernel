import Imscribing.Millennium.Erdos.CollatzDepthSplit

/-! The endpoint cocycle returned by MoDoT's direct `gm collatz birkhoff`
instrument, interpreted on the canonical retained predecessor counts.
The native measurement cuts the root-cycle edge; these theorems use the
uncut recursion in CollatzDepthSplit and retain both endpoint counts.
-/
namespace CollatzDepthSplit
open Filter
open scoped BigOperators Topology

lemma subtreeCount_positive (v d : ℕ) : 0 < subtreeCount v d := by
  cases d with
  | zero => simp [subtreeCount]
  | succ d => rw [subtreeCount_succ]; omega

lemma subtreeCount_uniform_bound (v d : ℕ) :
    subtreeCount v d ≤ (classBound d).2 := by
  have h := subtreeCount_le_classBound d v
  have hm := classBound_mono d
  split_ifs at h <;> omega

/-- The actual ratio weight used by the finite-depth Birkhoff instrument. -/
noncomputable def amplitudeCocycle (v d : ℕ) : ℝ :=
  (3 / 4) * (subtreeCount v d : ℝ) / (subtreeCount (col v) d : ℝ)

lemma amplitudeCocycle_pos (v d : ℕ) : 0 < amplitudeCocycle v d := by
  have h₁ : (0 : ℝ) < subtreeCount v d := by exact_mod_cast subtreeCount_positive v d
  have h₂ : (0 : ℝ) < subtreeCount (col v) d := by exact_mod_cast subtreeCount_positive (col v) d
  unfold amplitudeCocycle
  positivity

/-- Every interior count cancels; only the source and returned endpoint remain. -/
theorem amplitudeCocycle_product (v d N : ℕ) :
    (∏ i ∈ Finset.range N, amplitudeCocycle (col^[i] v) d) =
      (3 / 4 : ℝ) ^ N * (subtreeCount v d : ℝ) /
        (subtreeCount (col^[N] v) d : ℝ) := by
  induction N with
  | zero =>
    have h : (subtreeCount v d : ℝ) ≠ 0 := by
      exact_mod_cast (subtreeCount_positive v d).ne'
    simp [h]
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, amplitudeCocycle,
      Function.iterate_succ_apply', pow_succ]
    have h : (subtreeCount (col^[N] v) d : ℝ) ≠ 0 := by
      exact_mod_cast (subtreeCount_positive (col^[N] v) d).ne'
    field_simp

/-- The bounded endpoint correction is exact at every finite length. -/
theorem amplitudeCocycle_log_product (v d N : ℕ) :
    Real.log (∏ i ∈ Finset.range N, amplitudeCocycle (col^[i] v) d) =
      (N : ℝ) * Real.log (3 / 4) +
        Real.log (subtreeCount v d : ℝ) -
        Real.log (subtreeCount (col^[N] v) d : ℝ) := by
  have h₁ : (subtreeCount v d : ℝ) ≠ 0 := by
    exact_mod_cast (subtreeCount_positive v d).ne'
  have h₂ : (subtreeCount (col^[N] v) d : ℝ) ≠ 0 := by
    exact_mod_cast (subtreeCount_positive (col^[N] v) d).ne'
  rw [amplitudeCocycle_product,
    Real.log_div (mul_ne_zero (by positivity) h₁) h₂,
    Real.log_mul (by positivity : (3 / 4 : ℝ) ^ N ≠ 0) h₁, Real.log_pow]

lemma subtreeCount_log_bounds (v d : ℕ) :
    0 ≤ Real.log (subtreeCount v d : ℝ) ∧
      Real.log (subtreeCount v d : ℝ) ≤ Real.log ((classBound d).2 : ℝ) := by
  have hp : (0 : ℝ) < subtreeCount v d := by exact_mod_cast subtreeCount_positive v d
  constructor
  · apply Real.log_nonneg
    exact_mod_cast subtreeCount_positive v d
  · apply Real.log_le_log hp
    exact_mod_cast subtreeCount_uniform_bound v d

/-- A fixed-depth cocycle has a uniformly bounded log defect for every seed. -/
theorem amplitudeCocycle_log_defect_bound (v d N : ℕ) :
    |Real.log (∏ i ∈ Finset.range N, amplitudeCocycle (col^[i] v) d) -
      (N : ℝ) * Real.log (3 / 4)| ≤ Real.log ((classBound d).2 : ℝ) := by
  rw [amplitudeCocycle_log_product]
  have h₁ := subtreeCount_log_bounds v d
  have h₂ := subtreeCount_log_bounds (col^[N] v) d
  apply abs_le.mpr
  constructor <;> linarith

/-- Uniform fixed-depth boundedness of the actual cocycle, with an explicit
constant and no zero-placeholder mean fields. -/
theorem cocycle_bounded (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v N : ℕ,
      |Real.log (∏ i ∈ Finset.range N, amplitudeCocycle (col^[i] v) d) -
        (N : ℝ) * Real.log (3 / 4)| ≤ C := by
  refine ⟨Real.log ((classBound d).2 : ℝ), ?_, ?_⟩
  · have h := subtreeCount_log_bounds 0 d
    linarith
  · exact fun v N => amplitudeCocycle_log_defect_bound v d N

/-- For fixed predecessor depth the endpoint correction per step tends to zero. -/
theorem amplitudeCocycle_mean_log_limit (v d : ℕ) :
    Tendsto (fun N : ℕ =>
      Real.log (∏ i ∈ Finset.range N, amplitudeCocycle (col^[i] v) d) / (N : ℝ))
      atTop (𝓝 (Real.log (3 / 4))) := by
  let M : ℝ := Real.log ((classBound d).2 : ℝ)
  let E := fun N : ℕ =>
    (Real.log (subtreeCount v d : ℝ) -
      Real.log (subtreeCount (col^[N] v) d : ℝ)) / (N : ℝ)
  have hM : Tendsto (fun N : ℕ => M / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hE : Tendsto E atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hM.neg) hM
    · intro N
      have h₁ := subtreeCount_log_bounds v d
      have h₂ := subtreeCount_log_bounds (col^[N] v) d
      dsimp [E]
      have h : -M ≤ Real.log (subtreeCount v d : ℝ) -
          Real.log (subtreeCount (col^[N] v) d : ℝ) := by dsimp [M]; linarith
      simpa only [neg_div] using div_le_div_of_nonneg_right h (Nat.cast_nonneg N)
    · intro N
      have h₁ := subtreeCount_log_bounds v d
      have h₂ := subtreeCount_log_bounds (col^[N] v) d
      dsimp [E]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      dsimp [M]
      linarith
  have hl := (tendsto_const_nhds (x := Real.log (3 / 4))).add hE
  apply (show Tendsto (fun N => Real.log (3 / 4) + E N) atTop
    (𝓝 (Real.log (3 / 4))) by simpa using hl).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [amplitudeCocycle_log_product]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp [E]
  field_simp
  <;> ring

/-- The corrected geometric-mean claim holds for every seed and fixed depth,
without assuming that depth-normalized subtree amplitudes converge. -/
theorem amplitudeCocycle_geometric_mean_limit (v d : ℕ) :
    Tendsto (fun N : ℕ =>
      (∏ i ∈ Finset.range N, amplitudeCocycle (col^[i] v) d) ^ (1 / (N : ℝ)))
      atTop (𝓝 (3 / 4 : ℝ)) := by
  have hl := Real.continuous_exp.continuousAt.tendsto.comp (amplitudeCocycle_mean_log_limit v d)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 4)] at hl
  apply hl.congr'
  filter_upwards [] with N
  rw [Real.rpow_def_of_pos (Finset.prod_pos (fun i hi => amplitudeCocycle_pos _ _))]
  simp only [Function.comp_apply, div_eq_mul_inv, one_mul]

end CollatzDepthSplit
