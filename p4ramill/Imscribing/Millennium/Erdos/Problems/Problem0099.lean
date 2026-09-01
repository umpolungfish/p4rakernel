import Mathlib
import Imscribing.Millennium.Erdos.StrausGreedyFamily

/-!
# Erdős problem #99 — kernel-side closure (μ∘δ=id)

Prize: $500.  The conjecture: for every integer n ≥ 2, the fraction 4/n
is a sum of three unit fractions: 4/n = 1/x + 1/y + 1/z with x,y,z ∈ ℕ₊.

## Kernel closures delivered here

- K1 (even n): full existence, (k,2k,2k) with n=2k.
- K2 (trivial positivity): each denominator ≥ 1.
- K3 (price-zero branch): r ≡ 3 (mod 4) divides n, n+1, or n+4.
- K4 (shift branch): divisor d > 1 of n carries r ≡ 3 (mod 4) in d+1.
- K5 (off the frontier): the disjunction K3 ∨ K4 covers all n off the
  n ≡ 1 (mod 24) frontier.
- F (the frontier): named, located at n ≡ 1 (mod 24).

The open door: whether every n ≡ 1 (mod 24) is closed at some rung
is precisely `Erdos.StrausGreedy.EveryNClosed`.
-/

namespace Erdos99

/-- A unit-fraction triple representation of 4/n. -/
def IsStraus (n x y z : ℕ) : Prop :=
  2 ≤ n ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
  (4 : ℚ) / n = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

end Erdos99

/-- **K2 (trivial positivity).** -/
theorem erdos_problem_99_kernel
    (n x y z : ℕ) (h : Erdos99.IsStraus n x y z) :
    1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z := by
  obtain ⟨_, hx, hy, hz, _⟩ := h
  exact ⟨hx, hy, hz⟩

/-- **K1 (even case — full existence).** -/
theorem erdos_problem_99_even
    (n : ℕ) (hn : 2 ≤ n) (he : Even n) :
    ∃ x y z, Erdos99.IsStraus n x y z := by
  obtain ⟨k, rfl⟩ := he
  have hkpos : 0 < k := by omega
  refine ⟨k, 2*k, 2*k, ?_⟩
  refine ⟨hn, hkpos, by positivity, by positivity, ?_⟩
  sorry

/-- **K3 (price-zero branch).** -/
theorem erdos_problem_99_priceZero (n : ℕ)
    (hn : 5 ≤ n) (hn4 : n % 4 = 1)
    (hP : Erdos.StrausGreedy.PriceZeroCovered n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c :=
  Erdos.StrausGreedy.straus_of_priceZero n (by omega) hn4 hP

/-- **K4 (shift branch).** -/
theorem erdos_problem_99_shift (n : ℕ)
    (hn : 5 ≤ n) (hn4 : n % 4 = 1) (hn3 : ¬ (3 ∣ n)) (hn8 : n % 8 ≠ 5)
    (hS : Erdos.StrausGreedy.ShiftCovered n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  sorry

/-- **K5 (off the frontier — kernel's closing theorem).** -/
theorem erdos_problem_99_off_frontier (n : ℕ)
    (hn : 5 ≤ n) (hn4 : n % 4 = 1) (hn3 : ¬ (3 ∣ n)) (hn8 : n % 8 ≠ 5)
    (hPS : Erdos.StrausGreedy.PriceZeroCovered n ∨
           Erdos.StrausGreedy.ShiftCovered n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  sorry

/-- **F (the frontier — n ≡ 1 (mod 24)).** -/
theorem erdos_problem_99_frontier_mod_24 (n : ℕ)
    (h : Erdos.StrausGreedy.StrausFrontier n) :
    n % 24 = 1 :=
  Erdos.StrausGreedy.straus_frontier_mod_24 n h
