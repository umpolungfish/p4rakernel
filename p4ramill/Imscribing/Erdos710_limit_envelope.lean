import Imscribing.Erdos710_unconditional

open scoped BigOperators Topology
open Filter Asymptotics

noncomputable section

namespace Erdos710

/-!
# Erdős 710 — unconditional asymptotic envelope

Original open interval: `(n, n + f n)`.
Imscription: ⟨𐑦𐑸𐑑𐑿𐑐𐑧𐑲𐑝⊙𐑖𐑳𐑴⟩
IMASM: ⊢∈≻⋈∋⊡⊣ ; evidence carrier SIXTEEN₃.

All mathematical proofs below use the previously compiled
`right_endpoint_dilate` / `global_pattern_bound` theorem.  The
Shavian/IMASM inscriptions are retained as structural annotations.

There are no custom axioms, sieve estimates, placeholders, or
proof-by-contradiction tactics in this module.

This file establishes the exact finite-witness criterion for divergence
of `f(n)/n`.  It does NOT claim the witnesses grow without bound;
that arithmetic fact is an additional theorem to establish.
-/

/-- The maximum selected integer in an optimal open interval is at most
`endpoint n = n + f n - 1`. -/
def endpoint (n : ℕ) : ℕ := n + f n - 1

/-- For positive `n`, the endpoint is exactly one less than `n + f n`. -/
theorem endpoint_add_one (n : ℕ) (hn : 0 < n) :
    endpoint n + 1 = n + f n := by
  unfold endpoint
  omega

/-- An exact identity, important for tracking the open right endpoint. -/
theorem ratio_eq_endpoint_slope (n : ℕ) (hn : 0 < n) :
    (f n : ℝ) / (n : ℝ) =
      ((endpoint n : ℝ) / (n : ℝ) - 1) + 1 / (n : ℝ) := by
  have hcast : (endpoint n : ℝ) + 1 = (n : ℝ) + (f n : ℝ) := by
    exact_mod_cast endpoint_add_one n hn
  have hnum : (f n : ℝ) = (endpoint n : ℝ) + 1 - (n : ℝ) := by
    linarith
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (f n : ℝ) / (n : ℝ) =
        ((endpoint n : ℝ) + 1 - (n : ℝ)) / (n : ℝ) := by rw [hnum]
    _ = ((endpoint n : ℝ) / (n : ℝ) - 1) + 1 / (n : ℝ) := by
      field_simp [hn0]
      <;> ring

/-- Each **fixed finite instance** provides an unconditional eventual
lower bound for ALL later instances, with an arbitrarily small error.
This is a quantified asymptotic statement, not a conjectured estimate. -/
theorem eventually_ratio_ge_finite_slope_sub
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((endpoint m : ℝ) / (m : ℝ) - 1) - ε ≤
        (f n : ℝ) / (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((endpoint m : ℝ) / ε)
  filter_upwards [eventually_ge_atTop (max m (max 1 N))] with n hn
  have hmn : m ≤ n := by omega
  have hnN : N ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hNε : (endpoint m : ℝ) < ε * (N : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hN
  have hNreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
  have herr : (endpoint m : ℝ) ≤ ε * (n : ℝ) :=
    (le_of_lt hNε).trans
      (mul_le_mul_of_nonneg_left hNreal (le_of_lt hε))
  have hnat : n * endpoint m ≤
      m * endpoint n + m * endpoint m := by
    simpa only [endpoint] using global_pattern_bound m n hm hmn
  have hbase : (n : ℝ) * (endpoint m : ℝ) ≤
      (m : ℝ) * (endpoint n : ℝ) +
        (m : ℝ) * (endpoint m : ℝ) := by
    exact_mod_cast hnat
  have hcast : (endpoint n : ℝ) + 1 =
      (n : ℝ) + (f n : ℝ) := by
    exact_mod_cast endpoint_add_one n hnpos
  have hRmul : (m : ℝ) * (endpoint n : ℝ) + (m : ℝ) =
      (m : ℝ) * (n : ℝ) + (m : ℝ) * (f n : ℝ) := by
    calc
      (m : ℝ) * (endpoint n : ℝ) + (m : ℝ) =
          (m : ℝ) * ((endpoint n : ℝ) + 1) := by ring
      _ = (m : ℝ) * ((n : ℝ) + (f n : ℝ)) := by rw [hcast]
      _ = (m : ℝ) * (n : ℝ) + (m : ℝ) * (f n : ℝ) := by ring
  have hcross :
      (m : ℝ) * (((endpoint m : ℝ) / (m : ℝ)) * (n : ℝ)) =
        (n : ℝ) * (endpoint m : ℝ) := by
    field_simp [ne_of_gt hmreal]
    <;> ring
  have herrmul : (m : ℝ) * (endpoint m : ℝ) ≤
      ε * (m : ℝ) * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left herr (le_of_lt hmreal)
    nlinarith
  have hpoly :
      (m : ℝ) *
          ((((endpoint m : ℝ) / (m : ℝ)) - 1 - ε) * (n : ℝ)) ≤
        (m : ℝ) * (f n : ℝ) := by
    nlinarith [hbase, hRmul, hcross, herrmul]
  have hscaled :
      ((((endpoint m : ℝ) / (m : ℝ)) - 1 - ε) * (n : ℝ)) ≤
        (f n : ℝ) := (mul_le_mul_iff_of_pos_left hmreal).mp hpoly
  exact (le_div_iff₀ hnreal).2 hscaled

/-- A concrete finite slope above `c` forces the ratio eventually above
`c`, uniformly over all sufficiently large indices. -/
theorem finite_witness_forces_eventual_bound
    (m : ℕ) (hm : 0 < m) (c : ℝ)
    (hc : c < (endpoint m : ℝ) / (m : ℝ) - 1) :
    ∀ᶠ n : ℕ in atTop, c ≤ (f n : ℝ) / (n : ℝ) := by
  let ε : ℝ := (((endpoint m : ℝ) / (m : ℝ) - 1) - c) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  filter_upwards [eventually_ratio_ge_finite_slope_sub m hm ε hε]
    with n hn
  dsimp [ε] at hn
  linarith

/-- The exact **unconditional equivalence** between divergence of the
normalized sequence and arbitrarily large finite matching obstructions.
Neither side is postulated as an axiom. -/
theorem ratio_tendsto_atTop_iff_finite_witnesses :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop atTop ↔
      ∀ B : ℝ, ∃ m : ℕ, 0 < m ∧
        B < (endpoint m : ℝ) / (m : ℝ) - 1 := by
  constructor
  · intro h B
    have hev : ∀ᶠ n : ℕ in atTop,
        B + 2 ≤ (f n : ℝ) / (n : ℝ) :=
      (tendsto_atTop.1 h) (B + 2)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    let m : ℕ := max 1 N
    have hm : 0 < m := by dsimp [m]; omega
    have hNm : N ≤ m := by dsimp [m]; omega
    have hhigh : B + 2 ≤ (f m : ℝ) / (m : ℝ) := hN m hNm
    have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmone : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (show 1 ≤ m by omega)
    have hinv : 1 / (m : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hmreal).2
      nlinarith
    have hratio := ratio_eq_endpoint_slope m hm
    exact ⟨m, hm, by linarith⟩
  · intro hw
    apply tendsto_atTop.2
    intro B
    obtain ⟨m, hm, hB⟩ := hw (B + 1)
    filter_upwards
      [eventually_ratio_ge_finite_slope_sub m hm 1 (by norm_num)]
      with n hn
    linarith

/-- Set of all finite normalized endpoint slopes. -/
def finiteSlopeSet : Set ℝ :=
  { x | ∃ m : ℕ, 0 < m ∧ x = (endpoint m : ℝ) / (m : ℝ) - 1 }

/-- If the finite slopes have a real upper bound, the ratio converges
unconditionally to their least upper bound. This is a theorem from that
arithmetical *case*, not an assumption of a sharp sieve formula. -/
theorem ratio_tendsto_sup_of_bounded_slopes
    (B : ℝ)
    (hB : ∀ m : ℕ, 0 < m →
      (endpoint m : ℝ) / (m : ℝ) - 1 ≤ B) :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (𝓝 (sSup finiteSlopeSet)) := by
  have hne : finiteSlopeSet.Nonempty := by
    refine ⟨(endpoint 1 : ℝ) / (1 : ℝ) - 1, ?_⟩
    refine ⟨1, by omega, ?_⟩
    simp only [Nat.cast_one]
  have hbd : BddAbove finiteSlopeSet := by
    refine ⟨B, ?_⟩
    intro x hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact hB m hm
  have hsup (m : ℕ) (hm : 0 < m) :
      (endpoint m : ℝ) / (m : ℝ) - 1 ≤ sSup finiteSlopeSet := by
    apply le_csSup hbd
    exact ⟨m, hm, rfl⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨x, hx, hbelow⟩ :=
    exists_lt_of_lt_csSup hne
      (show sSup finiteSlopeSet - ε / 2 < sSup finiteSlopeSet by linarith)
  obtain ⟨m, hm, rfl⟩ := hx
  have hloev := eventually_ratio_ge_finite_slope_sub m hm (ε / 2) hhalf
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 : ℝ) / ε)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hloev
  refine ⟨max N₁ (max 1 N), ?_⟩
  intro n hn
  have hnN₁ : N₁ ≤ n := by omega
  have hlo := hN₁ n hnN₁
  have hnpos : 0 < n := by omega
  have hnN : N ≤ n := by omega
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnNreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
  have hlarge : (2 : ℝ) / ε < (n : ℝ) := lt_of_lt_of_le hN hnNreal
  have hεn : (2 : ℝ) < ε * (n : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlarge
  have hsmall : 1 / (n : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hnreal).2
    nlinarith
  have hratio := ratio_eq_endpoint_slope n hnpos
  have hupper := hsup n hnpos
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

/-- A fully unconditional extended-limit existence theorem: the ratio
has a finite real limit or tends to +infinity. No asymptotic hypotheses
are taken as parameters. -/
theorem normalized_ratio_finite_limit_or_atTop :
    (∃ ℓ : ℝ,
      Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop (𝓝 ℓ)) ∨
      Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop atTop := by
  by_cases hb : ∃ B : ℝ, ∀ m : ℕ, 0 < m →
      (endpoint m : ℝ) / (m : ℝ) - 1 ≤ B
  · obtain ⟨B, hB⟩ := hb
    exact Or.inl ⟨sSup finiteSlopeSet,
      ratio_tendsto_sup_of_bounded_slopes B hB⟩
  · right
    apply ratio_tendsto_atTop_iff_finite_witnesses.mpr
    push_neg at hb
    exact hb

#print axioms endpoint_add_one
#print axioms ratio_eq_endpoint_slope
#print axioms eventually_ratio_ge_finite_slope_sub
#print axioms finite_witness_forces_eventual_bound
#print axioms ratio_tendsto_atTop_iff_finite_witnesses
#print axioms ratio_tendsto_sup_of_bounded_slopes
#print axioms normalized_ratio_finite_limit_or_atTop

end Erdos710
