import Mathlib

open scoped BigOperators Topology
open Filter Asymptotics

noncomputable section

namespace Erdos710

/-!
Erdos #710 — direct arithmetic core, unified imscription.

Imscription address: ⟨𐑦𐑸𐑑𐑿𐑐𐑧𐑲𐑝⊙𐑖𐑳𐑴⟩
IMASM protocol: ⊢∈≻⋈∋⊡⊣
Underlying evidence register: SIXTEEN₃ = 𝒫({T,F,t,f}).

The addresses/protocol above record the user's unified structural interpretation.
The propositions below are ordinary Lean arithmetic propositions, not an
unimplemented assertion about four-valued kernel semantics.

No external sieve assumptions or unfinished proofs. The established theorem is an unconditional
quantitative lower bound, *not* a sharp asymptotic equivalent for f(n).
-/

/-- The exact open-interval, distinct-divisible-representatives predicate. -/
def HasDivisibleDistinctTuple (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ,
    Function.Injective a ∧
      ∀ i : Fin n, m < a i ∧ a i < m + L ∧ (i.val + 1) ∣ a i

/-- The least admissible *length*, not the least right endpoint. -/
def f (n : ℕ) : ℕ :=
  sInf {L : ℕ | HasDivisibleDistinctTuple n n L}

/-- Direct construction of a legal tuple. -/
theorem admissible_exists (n : ℕ) :
    {L : ℕ | HasDivisibleDistinctTuple n n L}.Nonempty := by
  refine ⟨n * (n + 1), ?_⟩
  refine ⟨fun i => (i.val + 1) * (n + 1), ?_, ?_⟩
  · intro i j h
    have h_eq : i.val + 1 = j.val + 1 := by
      apply Nat.mul_right_cancel (by omega : 0 < n + 1)
      exact h
    exact Fin.ext (by omega)
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · have h1 : 1 ≤ i.val + 1 := by omega
      calc
        n < n + 1 := by omega
        _ ≤ (i.val + 1) * (n + 1) :=
          Nat.le_mul_of_pos_left (n + 1) h1
    · have h2 : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
      have h3 : (i.val + 1) * (n + 1) ≤ n * (n + 1) :=
        Nat.mul_le_mul_right (n + 1) h2
      have hn : 0 < n := by omega
      calc
        (i.val + 1) * (n + 1) ≤ n * (n + 1) := h3
        _ < n + n * (n + 1) := by omega
    · exact dvd_mul_right (i.val + 1) (n + 1)

/-- The infimum in `f` is attained. -/
theorem f_admissible (n : ℕ) : HasDivisibleDistinctTuple n n (f n) := by
  exact Nat.sInf_mem (admissible_exists n)

/-- The divisor-capacity bound: every selected collection of indices has
    at least as many permissible distinct multiples in the open interval.
    This is the directly checkable half of the finite matching criterion. -/
theorem capacity_of_tuple (n L : ℕ)
    (h : HasDivisibleDistinctTuple n n L) (S : Finset (Fin n)) :
    S.card ≤
      ((Finset.Ioo n (n + L)).filter
        (fun b => ∃ i ∈ S, (i.val + 1) ∣ b)).card := by
  rcases h with ⟨a, hinj, hrange⟩
  have hsub : Finset.image a S ⊆
      (Finset.Ioo n (n + L)).filter
        (fun b => ∃ i ∈ S, (i.val + 1) ∣ b) := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Ioo.mpr ⟨(hrange i).1, (hrange i).2.1⟩
    · exact ⟨i, hi, (hrange i).2.2⟩
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective S hinj] using hcard

/-- A multiple of `2*t` above `4*t` is `6*t`, `8*t`, or at least `9*t`. -/
private theorem multiple_two_or_large (t x : ℕ) (ht : 0 < t)
    (hlo : 4 * t < x) (hdvd : 2 * t ∣ x) :
    x = 6 * t ∨ x = 8 * t ∨ 9 * t ≤ x := by
  obtain ⟨q, rfl⟩ := hdvd
  have hq : 3 ≤ q := by
    rcases lt_or_ge q 3 with h | h
    · have hm := Nat.mul_le_mul_left (2 * t) (show q ≤ 2 by omega)
      omega
    · exact h
  rcases lt_or_ge q 4 with h | h
  · left
    have heq : q = 3 := by omega
    rw [heq]
    omega
  · rcases lt_or_ge q 5 with h' | h'
    · right; left
      have heq : q = 4 := by omega
      rw [heq]
      omega
    · right; right
      have hm := Nat.mul_le_mul_left (2 * t) h'
      omega

/-- A multiple of `3*t` above `4*t` is `6*t` or at least `9*t`. -/
private theorem multiple_three_or_large (t x : ℕ) (ht : 0 < t)
    (hlo : 4 * t < x) (hdvd : 3 * t ∣ x) :
    x = 6 * t ∨ 9 * t ≤ x := by
  obtain ⟨q, rfl⟩ := hdvd
  have hq : 2 ≤ q := by
    rcases lt_or_ge q 2 with h | h
    · have hm := Nat.mul_le_mul_left (3 * t) (show q ≤ 1 by omega)
      omega
    · exact h
  rcases lt_or_ge q 3 with h | h
  · left
    have heq : q = 2 := by omega
    rw [heq]
    omega
  · right
    have hm := Nat.mul_le_mul_left (3 * t) h
    omega

/-- A multiple of `4*t` above `4*t` is `8*t` or at least `9*t`. -/
private theorem multiple_four_or_large (t x : ℕ) (ht : 0 < t)
    (hlo : 4 * t < x) (hdvd : 4 * t ∣ x) :
    x = 8 * t ∨ 9 * t ≤ x := by
  obtain ⟨q, rfl⟩ := hdvd
  have hq : 2 ≤ q := by
    rcases lt_or_ge q 2 with h | h
    · have hm := Nat.mul_le_mul_left (4 * t) (show q ≤ 1 by omega)
      omega
    · exact h
  rcases lt_or_ge q 3 with h | h
  · left
    have heq : q = 2 := by omega
    rw [heq]
    omega
  · right
    have hm := Nat.mul_le_mul_left (4 * t) h
    omega

/-- Positive interval-capacity certificate: every admissible tuple for
    `n ≥ 4*t` contains a selected value at least `9*t`; hence its
    right endpoint exceeds `9*t`. -/
theorem interval_endpoint_gt (n t L : ℕ) (ht : 0 < t)
    (hnt : 4 * t ≤ n) (h : HasDivisibleDistinctTuple n n L) :
    9 * t < n + L := by
  rcases h with ⟨a, hinj, hrange⟩
  let i2 : Fin n := ⟨2 * t - 1, by omega⟩
  let i3 : Fin n := ⟨3 * t - 1, by omega⟩
  let i4 : Fin n := ⟨4 * t - 1, by omega⟩
  have hv2 : i2.val + 1 = 2 * t := by dsimp [i2]; omega
  have hv3 : i3.val + 1 = 3 * t := by dsimp [i3]; omega
  have hv4 : i4.val + 1 = 4 * t := by dsimp [i4]; omega
  have hd2 : 2 * t ∣ a i2 := by simpa only [hv2] using (hrange i2).2.2
  have hd3 : 3 * t ∣ a i3 := by simpa only [hv3] using (hrange i3).2.2
  have hd4 : 4 * t ∣ a i4 := by simpa only [hv4] using (hrange i4).2.2
  have hlo2 : 4 * t < a i2 := lt_of_le_of_lt hnt (hrange i2).1
  have hlo3 : 4 * t < a i3 := lt_of_le_of_lt hnt (hrange i3).1
  have hlo4 : 4 * t < a i4 := lt_of_le_of_lt hnt (hrange i4).1
  have hb2 := multiple_two_or_large t (a i2) ht hlo2 hd2
  have hb3 := multiple_three_or_large t (a i3) ht hlo3 hd3
  have hb4 := multiple_four_or_large t (a i4) ht hlo4 hd4
  rcases hb2 with h26 | h28 | h2big
  · rcases hb3 with h36 | h3big
    · have heq : i2 = i3 := hinj (h26.trans h36.symm)
      have hval := congrArg (fun i : Fin n => i.val) heq
      dsimp [i2, i3] at hval
      omega
    · exact lt_of_le_of_lt h3big (hrange i3).2.1
  · rcases hb4 with h48 | h4big
    · have heq : i2 = i4 := hinj (h28.trans h48.symm)
      have hval := congrArg (fun i : Fin n => i.val) heq
      dsimp [i2, i4] at hval
      omega
    · exact lt_of_le_of_lt h4big (hrange i4).2.1
  · exact lt_of_le_of_lt h2big (hrange i2).2.1

/-- Direct, unconditional, uniform linear lower bound. -/
theorem linear_lower_bound (n : ℕ) : 5 * n ≤ 4 * f n + 23 := by
  by_cases hn : n < 4
  · omega
  · have hn4 : 4 ≤ n := by omega
    have ht : 0 < n / 4 := by omega
    have hnt : 4 * (n / 4) ≤ n := by omega
    have hrem : n < 4 * (n / 4) + 4 := by omega
    have hlarge := interval_endpoint_gt n (n / 4) (f n)
      ht hnt (f_admissible n)
    omega

/-- A scalable finite obstruction with no contradiction tactic. -/
theorem f_four_mul_gt (t : ℕ) (ht : 0 < t) :
    5 * t < f (4 * t) := by
  have h := interval_endpoint_gt (4 * t) t (f (4 * t))
    ht (by omega) (f_admissible (4 * t))
  omega

/-- A fixed quantitative separation for *every* n ≥ 46. -/
theorem ratio_lower_bound (n : ℕ) (hn : 46 ≤ n) :
    (9 / 8 : ℝ) ≤ (f n : ℝ) / (n : ℝ) := by
  have hnat := linear_lower_bound n
  have hnreal : (46 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hreal : (5 : ℝ) * (n : ℝ) ≤
      (4 : ℝ) * (f n : ℝ) + 23 := by exact_mod_cast hnat
  apply (le_div_iff₀ hpos).2
  linarith

/-- The direct asymptotic certificate has no imported sieve axiom. -/
theorem eventually_ratio_ge_nine_eighths :
    ∀ᶠ (n : ℕ) in atTop, (9 / 8 : ℝ) ≤ (f n : ℝ) / (n : ℝ) := by
  filter_upwards [eventually_ge_atTop 46] with n hn
  exact ratio_lower_bound n hn

#print axioms capacity_of_tuple
#print axioms f_four_mul_gt
#print axioms eventually_ratio_ge_nine_eighths

end Erdos710
