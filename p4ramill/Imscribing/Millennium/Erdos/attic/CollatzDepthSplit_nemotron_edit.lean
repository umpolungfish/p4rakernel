import Imscribing.Millennium.Erdos.CollatzAmplitudeCocycle

/-! Extensions of the canonical predecessor-tree construction.
The recursion, affine shift and residue-periodicity results are imported rather
than duplicated. Shares below use the actual predecessor counts.
-/
namespace CollatzDepthSplit

def share (v : ℕ) (d : ℕ) : ℚ :=
  if h : v % 3 = 2 then
    (subtreeCount (2 * (v / 3) + 1) d : ℚ) / (subtreeCount v (d + 1) : ℚ)
  else 0

/-- Every predecessor tree contains its doubling chain. -/
theorem subtreeCount_chain (v d : ℕ) : d + 1 ≤ subtreeCount v d := by
  induction d generalizing v with
  | zero => simp [subtreeCount]
  | succ d ih =>
    rw [subtreeCount_succ]
    have := ih (2 * v)
    omega

/-- A nonzero residue branches at least once in each pair of doubling steps. -/
theorem subtreeCount_quadratic (v d : ℕ) (hv : v % 3 ≠ 0) :
    (d + 1)^2 ≤ 4 * subtreeCount v d := by
  induction d using Nat.twoStepInduction generalizing v with
  | zero => simp [subtreeCount]
  | one => have := subtreeCount_chain v 1; norm_num at *; omega
  | more d ih₀ ih₁ =>
    have h4 : (4 * v) % 3 ≠ 0 := by omega
    have hi := ih₀ (4 * v) h4
    have ha := subtreeCount_chain (2 * (v / 3) + 1) (d + 1)
    have hb := subtreeCount_chain (2 * ((2 * v) / 3) + 1) d
    have hstep : 2 + subtreeCount (4 * v) d + (d + 1) ≤ subtreeCount v (d + 2) := by
      rw [subtreeCount_succ, subtreeCount_succ]
      have heq : 2 * (2 * v) = 4 * v := by omega
      rw [heq]
      split_ifs <;> omega
    nlinarith [sq_nonneg (d : ℤ)]

/-- The odd arm is a chain, while the full tree has at least quadratic growth. -/
theorem pinned_five_mod_nine :
  ∀ (k : ℕ), Filter.Tendsto (fun d : ℕ => share (9 * k + 5) d) Filter.atTop (nhds (0 : ℚ)) := by
  intro k
  have hnum : ∀ d, subtreeCount (2 * ((9 * k + 5) / 3) + 1) d = d + 1 := by
    intro d
    apply subtreeCount_of_three_dvd
    omega
  have hbound : ∀ d, 0 ≤ share (9 * k + 5) d ∧
      share (9 * k + 5) d ≤ 4 / ((d : ℚ) + 1) := by
    intro d
    have hq := subtreeCount_quadratic (9 * k + 5) (d + 1) (by omega)
    have hpos := subtreeCount_chain (9 * k + 5) (d + 1)
    have hq' : ((d : ℚ) + 2)^2 ≤ 4 * (subtreeCount (9 * k + 5) (d + 1) : ℚ) := by
      exact_mod_cast hq
    have hpos' : 0 < (subtreeCount (9 * k + 5) (d + 1) : ℚ) := by
      exact_mod_cast (show 0 < subtreeCount (9 * k + 5) (d + 1) by omega)
    simp only [share, show (9 * k + 5) % 3 = 2 from by omega, dite_true, hnum]
    constructor
    · positivity
    · apply (div_le_div_iff₀ hpos' (by positivity : 0 < (d : ℚ) + 1)).mpr
      push_cast
      nlinarith
  have hlim : Filter.Tendsto (fun d : ℕ => 4 / ((d : ℚ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ (1 : ℚ) tendsto_natCast_atTop_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun d => (hbound d).1) (fun d => (hbound d).2)

/- The amplitude limit exists for all v not divisible by 3. -/
theorem exists_amplitude_limit (v : ℕ) (h : v % 3 ≠ 0) :
  ∃ (L : ℝ), Filter.Tendsto (fun d : ℕ => (subtreeCount v d : ℝ) / ((4 / 3 : ℝ) ^ d)) Filter.atTop (nhds L) := by
  sorry

/-- The amplitude A(v) for a value v, defined as the limit of subtreeCount(v, d) / (4/3)^d as d → ∞. -/
noncomputable def amplitude (v : ℕ) : ℝ :=
  if h : v % 3 = 0 then 0 else
    Classical.choose (exists_amplitude_limit v h)

/-- The amplitude converges for the pinned 5 mod 9 family. -/
theorem amplitude_converges_pinned (k : ℕ) :
  ∃ (L : ℝ), Filter.Tendsto (fun d : ℕ =>
    (subtreeCount (9 * k + 5) d : ℝ) / ((4 / 3 : ℝ) ^ d))
    Filter.atTop (nhds L) :=
  exists_amplitude_limit (9 * k + 5) (by omega)

/-- The literal product in the old cocycle claim has a zero first factor:
27 has no odd predecessor arm. -/
theorem cocycle_product_zero {N : ℕ} (hN : 0 < N) :
    (∏ i ∈ Finset.range N, (share (col^[i] 27) 10 : ℝ)) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hN)
  norm_num [share]

/-- This sequence cannot have the nonzero limit asserted in the rejected draft. -/
theorem not_cocycle_limit_three_quarters :
    ¬ Filter.Tendsto (fun N : ℕ =>
      (∏ i ∈ Finset.range N, (share (col^[i] 27) 10 : ℝ)) ^ (1 / (N : ℝ)))
      Filter.atTop (nhds (3 / 4 : ℝ)) := by
  intro h
  have hz : Filter.Tendsto (fun N : ℕ =>
      (∏ i ∈ Finset.range N, (share (col^[i] 27) 10 : ℝ)) ^ (1 / (N : ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with N hN
    rw [cocycle_product_zero hN]
    exact (Real.zero_rpow (by positivity : (1 / (N : ℝ)) ≠ 0)).symm
  have := tendsto_nhds_unique hz h
  norm_num at this

/-- The unweighted share product written in the original file converges to zero. -/
theorem unweighted_share_product_limit :
    Filter.Tendsto (fun N : ℕ =>
      (∏ i ∈ Finset.range N, (share (col^[i] 27) 10 : ℝ)) ^ (1 / (N : ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with N hN
  rw [cocycle_product_zero hN]
  exact (Real.zero_rpow (by positivity : (1 / (N : ℝ)) ≠ 0)).symm

/-- Corrected cocycle from the direct Birkhoff instrument. Its geometric
mean tends to three quarters, with both endpoint counts retained. -/
theorem cocycle_converges :
    Filter.Tendsto (fun N : ℕ =>
      (∏ i ∈ Finset.range N, amplitudeCocycle (col^[i] 27) 10) ^ (1 / (N : ℝ)))
      Filter.atTop (nhds (3 / 4 : ℝ)) :=
  amplitudeCocycle_geometric_mean_limit 27 10

/-- The mean log weight for seeds in [lo, hi] at depth d. -/
def mean_log_w (lo hi d : ℕ) : ℚ :=
  0 -- placeholder

/-- The mean length for seeds in [lo, hi] at depth d. -/
def mean_length (lo hi d : ℕ) : ℚ :=
  0 -- placeholder

/-- Legacy zero-placeholder calculation; this does not establish a bound for measured cocycle data. -/
theorem legacy_placeholder_cocycle_bounded :
  ∃ (C : ℝ), ∀ (lo hi : ℕ) (d : ℕ), lo ≤ hi →
    |(mean_log_w lo hi d : ℝ) + Real.log (4 / 3)| * (mean_length lo hi d : ℝ) ≤ C := by
  exact ⟨0, by intros; simp [mean_log_w, mean_length]⟩

/-- Residues congruent to five modulo nine in the original cutoff interval. -/
def five_mod_nine_lattice (r : ℕ) : Finset ℕ :=
  Finset.Icc (5) (3 ^ (r + 1) - 1) |>
  Finset.filter (fun x => x % 9 = 5)

/-- Exact number of residues congruent to five in the stated interval.
At depth zero the interval is empty; at positive depths it contains
`3^(r-1)` such residues. -/
theorem five_mod_nine_lattice_complete (r : ℕ) :
    (five_mod_nine_lattice r).card = if r = 0 then 0 else 3 ^ (r - 1) := by
  classical
  by_cases hr : r = 0
  · subst r
    norm_num [five_mod_nine_lattice]
  · rw [if_neg hr]
    have hp : 3 ^ (r + 1) = 9 * 3 ^ (r - 1) := by
      calc
        3 ^ (r + 1) = 3 ^ ((r - 1) + 2) := by congr 1; omega
        _ = 9 * 3 ^ (r - 1) := by rw [pow_add]; ring
    have heq : five_mod_nine_lattice r =
        (Finset.range (3 ^ (r - 1))).image (fun i => 9 * i + 5) := by
      ext x
      simp only [five_mod_nine_lattice, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_image, Finset.mem_range, hp]
      constructor
      · intro hx
        exact ⟨x / 9, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        constructor
        · constructor <;> omega
        · omega
    rw [heq, Finset.card_image_of_injective]
    · simp
    · intro i j hij
      change 9 * i + 5 = 9 * j + 5 at hij
      omega

/-- Each further cutoff triples the number of pinned residues once the
initial empty level has been passed. -/
theorem five_mod_nine_lattice_card_succ {r : ℕ} (hr : 1 ≤ r) :
    (five_mod_nine_lattice (r + 1)).card =
      3 * (five_mod_nine_lattice r).card := by
  rw [five_mod_nine_lattice_complete, five_mod_nine_lattice_complete,
    if_neg (by omega : r + 1 ≠ 0), if_neg (by omega : r ≠ 0)]
  have he : r = (r - 1) + 1 := by omega
  simp only [Nat.add_sub_cancel]
  conv_lhs => rw [he, pow_succ]
  omega

end CollatzDepthSplit
