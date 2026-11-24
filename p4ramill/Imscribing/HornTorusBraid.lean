import Mathlib

/-!
# Horn-torus braid: the CRT strand permutation j ↦ q·j on ℤ/p

Claims formalized (all for p prime):
  1. 0 is a fixed point of every strand map, and the only one when q ≠ 1.
  2. Dirichlet characters are eigenmodes of the braid, with eigenvalue χ(q).
  3. The return time of any nonzero strand is exactly orderOf q.
  4. (Pre-registered, NOT derived) the pinch-crossing regularization gives ζ(0) = -1/2.

Not compiled by the author of this file; check with `lake build`.
-/

namespace Imscribing.HornTorusBraid

/-- The strand map of the CRT knot at prime p: multiplication by q. -/
def braid {p : ℕ} (q : ZMod p) : ZMod p → ZMod p := fun j => q * j

/-! ## 1. Zero is the fixed-point operator -/

theorem zero_fixed {p : ℕ} (q : ZMod p) : braid q 0 = 0 := by
  simp [braid]

theorem unique_fixed_point (p : ℕ) [Fact p.Prime] (q : ZMod p) (hq : q ≠ 1)
    (j : ZMod p) : braid q j = j ↔ j = 0 := by
  unfold braid
  constructor
  · intro h
    have h' : (q - 1) * j = 0 := by rw [sub_mul, one_mul, h, sub_self]
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hq
    · exact h1
  · rintro rfl; simp

/-! ## 2. Characters are eigenmodes of the braid -/

/-- For every Dirichlet character χ mod p, the function j ↦ χ(j) is an eigenvector
    of the strand map (as a precomposition operator), with eigenvalue χ(q).
    Holds on all of ℤ/p, including the fixed point 0. -/
theorem character_eigenmode {p : ℕ} (χ : DirichletCharacter ℂ p) (q : ZMod p) :
    ∀ j : ZMod p, χ (braid q j) = χ q * χ j := by
  intro j
  exact map_mul χ q j

/-! ## 3. Return time of a strand is the multiplicative order -/

theorem return_time_iff (p : ℕ) [Fact p.Prime] (q j : ZMod p) (hj : j ≠ 0) (k : ℕ) :
    (braid q)^[k] j = j ↔ orderOf q ∣ k := by
  have hiter : ∀ n : ℕ, (braid q)^[n] j = q ^ n * j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [braid]
      ring
  rw [hiter, orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    have h' : (q ^ k - 1) * j = 0 := by rw [sub_mul, one_mul, h, sub_self]
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hj
  · intro h; rw [h, one_mul]

/-! ## 4. Pre-registered claim: crossing-count regularization -/

/-- The pinch is crossed p times per prime-p circuit, so the total crossing count
    is the divergent sum 1 + 1 + 1 + ⋯. Abel regularization of Σ_{n≥1} e^{-εn}
    is 1/(e^ε - 1) = 1/ε - 1/2 + O(ε).
    CLAIM (open): the constant term -1/2 is the torus's ζ(0). -/
theorem abel_constant_term :
    Filter.Tendsto (fun ε : ℝ => 1 / (Real.exp ε - 1) - 1 / ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1 / 2)) := by
  -- Quantitative bound: |1/(eˣ-1) - 1/x + 1/2| ≤ 2x on (0,1].
  have key : ∀ x : ℝ, 0 < x → x ≤ 1 →
      |(1 / (Real.exp x - 1) - 1 / x) - (-1 / 2)| ≤ 2 * x := by
    intro x hx0 hx1
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp x - 1 := ⟨_, rfl⟩
    have hEx : x ≤ E := by
      have := Real.add_one_le_exp x
      linarith
    have hEpos : 0 < E := lt_of_lt_of_le hx0 hEx
    have hEne : E ≠ 0 := hEpos.ne'
    have hxne : x ≠ 0 := hx0.ne'
    -- third-order Taylor remainder
    have hb := Real.exp_bound (x := x) (by rw [abs_of_pos hx0]; exact hx1) (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, Nat.factorial] <;> ring
    rw [hsum, abs_of_pos hx0] at hb
    have hr : |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ x ^ 3 := by
      refine le_trans hb ?_
      norm_num [Nat.factorial] <;> nlinarith [pow_pos hx0 3]
    obtain ⟨r, hr1, hr2⟩ : ∃ r : ℝ, Real.exp x = 1 + x + x ^ 2 / 2 + r ∧ |r| ≤ x ^ 3 :=
      ⟨Real.exp x - (1 + x + x ^ 2 / 2), by ring, hr⟩
    have hEr : E = x + x ^ 2 / 2 + r := by rw [hE, hr1]; ring
    obtain ⟨hrlow, hrup⟩ := abs_le.mp hr2
    have hden : 0 < 2 * x * E := by positivity
    have hid : (1 / E - 1 / x) - (-1 / 2) = (x ^ 3 / 2 - 2 * r + x * r) / (2 * x * E) := by
      field_simp
      rw [hEr]
      ring
    rw [← hE, hid, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have h1 : x * x ^ 3 ≤ x ^ 3 := by nlinarith [pow_pos hx0 3]
    have h2 : 0 ≤ x ^ 2 * (E - x) := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hEx)
    have h3 : x * r ≤ x * x ^ 3 := mul_le_mul_of_nonneg_left hrup hx0.le
    have h4 : x * (-x ^ 3) ≤ x * r := mul_le_mul_of_nonneg_left hrlow hx0.le
    have h5 : 0 < x ^ 3 := pow_pos hx0 3
    apply abs_le.mpr
    constructor <;> nlinarith
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min 1 (ε / 2), lt_min one_pos (half_pos hε), ?_⟩
  intro x hx hd
  have hx0 : 0 < x := hx
  rw [Real.dist_eq, sub_zero, abs_of_pos hx0] at hd
  have h1 : x < 1 := lt_of_lt_of_le hd (min_le_left _ _)
  have h2 : x < ε / 2 := lt_of_lt_of_le hd (min_le_right _ _)
  show dist (1 / (Real.exp x - 1) - 1 / x) (-1 / 2) < ε
  rw [Real.dist_eq]
  have := key x hx0 h1.le
  linarith

/-- The target value, from Mathlib. -/
example : riemannZeta 0 = -1 / 2 := riemannZeta_zero

/- What remains unconstructed: a map from the torus's crossing structure to the
   Abel-regularized sum above. Until that map is defined from the knot itself
   (not chosen after the fact), the ζ(0) match is an observation, not a theorem.
   The standard route that would make it a derivation is the Mellin transform
   ∫₀^∞ ε^(s-1) / (e^ε - 1) dε = Γ(s) ζ(s): the -1/2 term above produces the
   residue of Γ(s)ζ(s) at s = 0, forcing ζ(0) = -1/2. -/

end Imscribing.HornTorusBraid
