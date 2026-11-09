import Imscribing.Erdos710_smooth_unconditional

open scoped BigOperators Topology
open Filter

noncomputable section

namespace Erdos710

/-!
# Erdős #710: constructive geometric-growth obstruction

Imscription: ⟨𐑦𐑸𐑑𐑿𐑐𐑧𐑲𐑝⊙𐑖𐑳𐑴⟩
IMASM: ⊢∈≻⋈∋⊡⊣
Carrier: SIXTEEN₃.

This module adds the finite-growth alternative needed for the smooth-shell
argument. No `sorry`, admitted asymptotics, custom axioms, 
`by_contra`, or `False.elim`.
-/

/-- A *finite constructive alternative*: starting from one positive shell,
within `2*k` steps either a local capacity gap has been identified,
or the shell count has grown by at least `2^k`.

This is proved by inspecting each pair of subsequent recurrence steps,
not by invoking a global contradiction principle. -/
theorem finite_gap_or_doubling (H : ℕ → ℕ) (J k : ℕ)
    (hstart : 0 < H (J + 1)) :
    (∃ j : ℕ, J + 1 ≤ j ∧ j ≤ J + 2 * k ∧
        H (j + 1) < H j + H (j - 1)) ∨
      2 ^ k ≤ H (J + 2 * k + 1) := by
  induction k with
  | zero =>
      right
      simpa using hstart
  | succ k ih =>
      rcases ih with ⟨j, hjlo, hjhi, hgap⟩ | hgrowth
      · left
        exact ⟨j, hjlo, by omega, hgap⟩
      · let u : ℕ := J + 2 * k + 1
        have hlarge : 2 ^ k ≤ H u := by
          simpa [u] using hgrowth
        by_cases hfirst : H (u + 1) < H u + H (u - 1)
        · left
          refine ⟨u, ?_, ?_, hfirst⟩
          · dsimp [u]; omega
          · dsimp [u]; omega
        · by_cases hsecond : H (u + 2) < H (u + 1) + H u
          · left
            refine ⟨u + 1, ?_, ?_, ?_⟩
            · dsimp [u]; omega
            · dsimp [u]; omega
            · simpa using hsecond
          · right
            have hstep1 : H u + H (u - 1) ≤ H (u + 1) := by omega
            have hstep2 : H (u + 1) + H u ≤ H (u + 2) := by omega
            have htwice : 2 * H u ≤ H (u + 2) := by omega
            have hindex : J + 2 * (k + 1) + 1 = u + 2 := by
              dsimp [u]
              omega
            rw [hindex]
            calc
              2 ^ (k + 1) = 2 * 2 ^ k := by
                simp [pow_succ, Nat.mul_comm]
              _ ≤ 2 * H u := Nat.mul_le_mul_left 2 hlarge
              _ ≤ H (u + 2) := htwice

/-- A finite bound strictly below doubling growth produces an *actual
index* where the capacity gap occurs. -/
theorem finite_gap_of_doubling_barrier (H : ℕ → ℕ) (J k : ℕ)
    (hstart : 0 < H (J + 1))
    (hbarrier : H (J + 2 * k + 1) < 2 ^ k) :
    ∃ j : ℕ, J + 1 ≤ j ∧ j ≤ J + 2 * k ∧
      H (j + 1) < H j + H (j - 1) := by
  rcases finite_gap_or_doubling H J k hstart with hgap | hgrowth
  · exact hgap
  · omega

/-- The precise finite smooth-capacity condition, with powers rather
than general endpoints. The cutoff `r^3+1` keeps every selected small
multiplier inside the same smooth-number carrier. -/
def geometricSmoothGap (r j : ℕ) : Prop :=
  (smoothSupply (r ^ j) (r ^ (j + 1)) (r ^ 3 + 1)).card <
    (smoothDemand (r ^ j) (r ^ (j - 2)) (r ^ 3 + 1)).card

/-- The elementary multiplicative cutoff, including the `j-2` boundary. -/
theorem geometric_smooth_cut (r j : ℕ) (hj : 2 ≤ j) :
    r ^ (j + 1) ≤ r ^ (j - 2) * (r ^ 3 + 1) := by
  have he : j + 1 = (j - 2) + 3 := by omega
  calc
    r ^ (j + 1) = r ^ ((j - 2) + 3) := by rw [he]
    _ = r ^ (j - 2) * r ^ 3 := by rw [pow_add]
    _ ≤ r ^ (j - 2) * (r ^ 3 + 1) :=
      Nat.mul_le_mul_left (r ^ (j - 2)) (by omega)

/-- A genuine unconditional Mathlib counting bound for the geometric
smooth supply. It is a first quantitative sparsity estimate and uses no
unverified arithmetic claim. -/
theorem geometric_supply_sqrt_bound (r y j : ℕ) :
    (smoothSupply (r ^ j) (r ^ (j + 1)) y).card ≤
      2 ^ y.primesBelow.card * (r ^ (j + 1)).sqrt := by
  have hsub :
      smoothSupply (r ^ j) (r ^ (j + 1)) y ⊆
        (r ^ (j + 1)).smoothNumbersUpTo y := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hle : b ≤ r ^ (j + 1) :=
      (Finset.mem_Ioc.mp hb'.1).2
    exact Nat.mem_smoothNumbersUpTo.mpr ⟨hle, hb'.2⟩
  exact (Finset.card_le_card hsub).trans
    (Nat.smoothNumbersUpTo_card_le (r ^ (j + 1)) y)

/-- Every geometric smooth-number gap gives an explicit lower bound for the
minimum **closed right endpoint** `endpoint (r^j)`. -/
theorem geometric_gap_forces_endpoint (r j : ℕ)
    (hr : 2 ≤ r) (hj : 2 ≤ j)
    (hgap : geometricSmoothGap r j) :
    r ^ (j + 1) ≤ endpoint (r ^ j) := by
  have hrpos : 0 < r := by omega
  have hnpos : 0 < r ^ j := pow_pos hrpos _
  exact smooth_gap_forces_endpoint
    (r ^ j) (r ^ (j - 2)) (r ^ (j + 1)) (r ^ 3 + 1)
    hnpos (geometric_smooth_cut r j hj) hgap

/-- An explicit *length*, not merely a right-endpoint, lower bound. -/
theorem geometric_gap_forces_length (r j : ℕ)
    (hr : 2 ≤ r) (hj : 2 ≤ j)
    (hgap : geometricSmoothGap r j) :
    (r - 1) * r ^ j + 1 ≤ f (r ^ j) := by
  have hR := geometric_gap_forces_endpoint r j hr hj hgap
  have hn : 0 < r ^ j := pow_pos (by omega : 0 < r) j
  have hRplus := endpoint_add_one (r ^ j) hn
  have hpow : r ^ (j + 1) = r * r ^ j := by
    rw [pow_succ]
    ring
  have hmult : (r - 1) * r ^ j + r ^ j = r * r ^ j := by
    calc
      (r - 1) * r ^ j + r ^ j = ((r - 1) + 1) * r ^ j := by ring
      _ = r * r ^ j := by
        congr 1
        omega
  omega

/-- Propagate any finite geometric gap to an eventual quantitative
asymptotic lower bound. The only witness required is a decidable finite
capacity inequality; no analytic upper or lower estimate is postulated. -/
theorem geometric_gap_forces_eventual_slope (r j : ℕ)
    (hr : 2 ≤ r) (hj : 2 ≤ j)
    (hgap : geometricSmoothGap r j)
    (c : ℝ) (hc : c < (r : ℝ) - 1) :
    ∀ᶠ n : ℕ in atTop, c ≤ (f n : ℝ) / (n : ℝ) := by
  have hR := geometric_gap_forces_endpoint r j hr hj hgap
  have hn : 0 < r ^ j := pow_pos (by omega : 0 < r) j
  have hnreal : (0 : ℝ) < ((r ^ j : ℕ) : ℝ) := by
    exact_mod_cast hn
  have hpow : r ^ (j + 1) = r * r ^ j := by
    rw [pow_succ]
    ring
  have hreal : (r : ℝ) * ((r ^ j : ℕ) : ℝ) ≤ (endpoint (r ^ j) : ℝ) := by
    rw [hpow] at hR
    exact_mod_cast hR
  have hdiv : (r : ℝ) ≤
      (endpoint (r ^ j) : ℝ) / ((r ^ j : ℕ) : ℝ) := by
    exact (le_div_iff₀ hnreal).2 hreal
  apply finite_witness_forces_eventual_bound (r ^ j) hn c
  linarith

#print axioms finite_gap_or_doubling
#print axioms finite_gap_of_doubling_barrier
#print axioms geometric_supply_sqrt_bound
#print axioms geometric_smooth_cut
#print axioms geometric_gap_forces_endpoint
#print axioms geometric_gap_forces_length
#print axioms geometric_gap_forces_eventual_slope

end Erdos710
