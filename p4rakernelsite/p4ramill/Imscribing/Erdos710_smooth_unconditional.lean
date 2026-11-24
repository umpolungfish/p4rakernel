import Imscribing.Erdos710_limit_envelope

open scoped BigOperators Topology
open Filter

noncomputable section

namespace Erdos710

/-!
# Erdős #710 — unified smooth-number capacity certificates

Imscription: ⟨𐑦𐑸𐑑𐑿𐑐𐑧𐑲𐑝⊙𐑖𐑳𐑴⟩
IMASM protocol: ⊢∈≻⋈∋⊡⊣
Full evidence carrier: SIXTEEN₃ = 𝒫({T,F,t,f}).

This file extends the kernel-checked `Erdos710_limit_envelope`.  The objects
below are *proof-carrying arithmetic capacity certificates*: each witness
is a finite set of y-smooth indices, and each candidate is an integer in
the right-hand interval.  The split and fusion are realized by an actual
injective image/cardinality inequality
-/

/-- The indices which are `y`-smooth and lie strictly above `lo`. -/
def smoothDemand (n lo y : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    lo < i.val + 1 ∧ i.val + 1 ∈ Nat.smoothNumbers y)

/-- The available `y`-smooth integers in the closed-right interval `(n,hi]`. -/
def smoothSupply (n hi y : ℕ) : Finset ℕ :=
  (Finset.Ioc n hi).filter (fun b => b ∈ Nat.smoothNumbers y)

/-- Direct injection from smooth demand into smooth capacity.

If every chosen multiple is at most `hi ≤ lo*y` and its index is above
`lo`, its multiplier is strictly smaller than `y`.  Hence the multiple
itself is `y`-smooth.  This gives a genuine finite injection, with no
analytic hypothesis or sieve axiom. -/
theorem smooth_capacity_of_tuple
    (n L lo hi y : ℕ)
    (hhi : n + L ≤ hi)
    (hcut : hi ≤ lo * y)
    (h : HasDivisibleDistinctTuple n n L) :
    (smoothDemand n lo y).card ≤ (smoothSupply n hi y).card := by
  obtain ⟨a, hinj, hrange⟩ := h
  have hsub : Finset.image a (smoothDemand n lo y) ⊆
      smoothSupply n hi y := by
    intro b hb
    obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hb
    have hsi : lo < i.val + 1 ∧
        i.val + 1 ∈ Nat.smoothNumbers y :=
      (Finset.mem_filter.mp hiS).2
    have habove : n < a i := (hrange i).1
    have hbelow : a i ≤ hi :=
      (le_of_lt (hrange i).2.1).trans hhi
    obtain ⟨q, hq⟩ := (hrange i).2.2
    have hqpos : 0 < q := by
      cases q with
      | zero =>
          simp at hq
          omega
      | succ _ => omega
    have hqsmall : q < y := by
      rcases lt_or_ge q y with hsmall | hlarge
      · exact hsmall
      · have hlow : lo * y ≤ lo * q :=
          Nat.mul_le_mul_left lo hlarge
        have hstrict : lo * q < (i.val + 1) * q :=
          Nat.mul_lt_mul_of_pos_right hsi.1 hqpos
        have hqhi : (i.val + 1) * q ≤ hi := by
          rw [← hq]
          exact hbelow
        omega
    have hqsmooth : q ∈ Nat.smoothNumbers y :=
      Nat.mem_smoothNumbers_of_lt hqpos hqsmall
    have hbsmooth : a i ∈ Nat.smoothNumbers y := by
      rw [hq]
      exact Nat.mul_mem_smoothNumbers hsi.2 hqsmooth
    change a i ∈ (Finset.Ioc n hi).filter
      (fun b => b ∈ Nat.smoothNumbers y)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨habove, hbelow⟩, hbsmooth⟩
  calc
    (smoothDemand n lo y).card =
        (Finset.image a (smoothDemand n lo y)).card :=
          (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (smoothSupply n hi y).card := Finset.card_le_card hsub

/-- Every finite smooth-number overcrowding certificate forces an actual
    *positive endpoint bound*.  The bound has no asymptotic hypothesis. -/
theorem smooth_gap_forces_endpoint
    (n lo hi y : ℕ) (hn : 0 < n)
    (hcut : hi ≤ lo * y)
    (hgap : (smoothSupply n hi y).card < (smoothDemand n lo y).card) :
    hi ≤ endpoint n := by
  rcases lt_or_ge hi (n + f n) with hshort | hlong
  · have heq := endpoint_add_one n hn
    omega
  · have hcapacity := smooth_capacity_of_tuple
        n (f n) lo hi y hlong hcut (f_admissible n)
    omega

/-- The finite smooth-number certificate also propagates to an *eventual*
    quantitative bound using the already-verified endpoint dilation law. -/
theorem smooth_gap_forces_eventual_ratio
    (n lo hi y : ℕ) (hn : 0 < n)
    (hcut : hi ≤ lo * y)
    (hgap : (smoothSupply n hi y).card < (smoothDemand n lo y).card)
    (c : ℝ) (hc : c < (hi : ℝ) / (n : ℝ) - 1) :
    ∀ᶠ m : ℕ in atTop, c ≤ (f m : ℝ) / (m : ℝ) := by
  have hendpoint : hi ≤ endpoint n :=
    smooth_gap_forces_endpoint n lo hi y hn hcut hgap
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hreal : (hi : ℝ) ≤ (endpoint n : ℝ) := by
    exact_mod_cast hendpoint
  have hdiv : (hi : ℝ) / (n : ℝ) ≤
      (endpoint n : ℝ) / (n : ℝ) :=
    div_le_div_of_nonneg_right hreal (le_of_lt hnreal)
  apply finite_witness_forces_eventual_bound n hn c
  linarith

/-!
For an unconditional numerical illustration we reuse the previously
kernel-checked three-index obstruction: `f_four_mul_gt` at `t = 4` gives
the stronger bound `21 ≤ f 16` and hence `36 ≤ endpoint 16`.
-/

/-- A concrete lower bound from the already checked direct obstruction. -/
theorem f_sixteen_ge_twentyone : 21 ≤ f 16 := by
  have h := f_four_mul_gt 4 (by norm_num)
  norm_num at h
  omega

/-- The right endpoint is at least 36, hence certainly at least 32. -/
theorem endpoint_sixteen_ge_thirtysix : 36 ≤ endpoint 16 := by
  have h := f_sixteen_ge_twentyone
  have heq := endpoint_add_one 16 (by norm_num)
  omega

/-- estimate follows immediately. -/
theorem f_sixteen_ge_seventeen : 17 ≤ f 16 := by
  have h := f_sixteen_ge_twentyone
  omega

#print axioms smooth_capacity_of_tuple
#print axioms smooth_gap_forces_endpoint
#print axioms smooth_gap_forces_eventual_ratio
#print axioms f_sixteen_ge_twentyone
#print axioms endpoint_sixteen_ge_thirtysix
#print axioms f_sixteen_ge_seventeen

end Erdos710
