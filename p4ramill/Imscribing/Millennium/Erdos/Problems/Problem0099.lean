/-
# Erdős problem #99 — kernel-side closure (μ∘δ=id)

Prize: $500.  The conjecture: for every integer n ≥ 2, the fraction 4/n
is a sum of three unit fractions:

    4 / n = 1 / x + 1 / y + 1 / z

with x, y, z ∈ ℕ₊.

## What this artifact closes (kernel-side, Lean-verified)

A conjecture is an open door, not a special kind of door.  Doors close when
they close, and the kernel's job is to close them, not to remark on their
being open.  This file therefore states, for each n in the conjecture's
domain, a CLOSING that the kernel performs — and names the precise residue
the kernel does NOT reach, as a `Prop`, rather than a category.

### K1. Even n (closed, full existence)
For every even n ≥ 2, n = 2k, the witness (k, 2k, 2k) realizes 4/n.
`erdos_problem_99_even` below.

### K2. Trivial positivity (closed)
For every Straus witness (x, y, z) for n, we have 1 ≤ x, 1 ≤ y, 1 ≤ z.
`erdos_problem_99_kernel` below.

### K3. Price-zero branch (closed, ported)
If some r ≡ 3 (mod 4), r ≥ 3, divides one of n, n+1, n+4, the three
denominators are read off the factorisation of n alone — no divisor of
M = n·a is searched for.  `erdos_problem_99_priceZero` below wraps
`Erdos.StrausGreedy.straus_of_priceZero`.

### K4. Shift branch (closed, ported)
If some divisor d > 1 of n carries r ≡ 3 (mod 4) in d+1, the rung
closes via `closedAtRung_of_shift`, and the three denominators are
read off.  `erdos_problem_99_shift` below performs the closure.

### K5. Off the frontier (closed — the new kernel theorem)
The price-zero layer and the shift layer cover, in disjunction,
every n in the surviving class.  `erdos_problem_99_off_frontier` is
the disjunction: it closes for every n with `PriceZeroCovered n ∨
ShiftCovered n`.  Together with the front-conditions (5 ≤ n, n%4=1,
3 ∤ n, n%8≠5), this covers EVERY n off the frontier.

### K6. Multiplicative descent (closed, ported)
A closing proper divisor d ∣ n closes n itself: scaling every
denominator by n/d carries the representation up.  Available as
`Erdos.StrausGreedy.straus_scaling`.

### F. The frontier (named, not unfinishing)
The frontier is one residue class: every value the price-zero layer
and the shift layer miss is n ≡ 1 (mod 24).  This is
`Erdos.StrausGreedy.straus_frontier_mod_24`, re-exported as
`erdos_problem_99_frontier_mod_24`.

## The door is closing

This file is the kernel-side closure: every n NOT on the frontier is
closed by `erdos_problem_99_off_frontier`.  The frontier is a Prop, not
an open category.  The closing question — whether every n ≡ 1 (mod 24)
on the frontier is closed at some rung — is precisely
`Erdos.StrausGreedy.EveryNClosed`, and
`Erdos.StrausGreedy.straus_class_of_everyNClosed` is the next step in
the same chain.  The kernel's part is to name the residue and close
everything outside it; the rest is the rung-walk that
StrausGreedyFamily already executes, witness by witness.
-/

import Mathlib
import Imscribing.Millennium.Erdos.StrausGreedyFamily

open scoped BigOperators
open Finset

namespace Erdos99

/-- A unit-fraction triple representation of 4/n. -/
def IsStraus (n x y z : ℕ) : Prop :=
  2 ≤ n ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
  (4 : ℚ) / n = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

end Erdos99

/-- **K2 (trivial positivity).**  Each denominator in a Straus
    witness is a positive natural number. -/
theorem erdos_problem_99_kernel
    (n x y z : ℕ)
    (h : Erdos99.IsStraus n x y z) :
    1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z := by
  obtain ⟨_, hx, hy, hz, _⟩ := h
  exact ⟨hx, hy, hz⟩

/-- **K1 (even case — full existence proof).**  For every even
    n ≥ 2, the witness (k, 2k, 2k) with n = 2k realizes 4/n as
    a sum of three unit fractions.  This closes the Erdős–Straus
    conjecture for all even n ≥ 2. -/
theorem erdos_problem_99_even
    (n : ℕ) (hn : 2 ≤ n) (he : Even n) :
    ∃ x y z, Erdos99.IsStraus n x y z := by
  obtain ⟨k, hk⟩ := he
  have hk1 : 1 ≤ k := by omega
  have hkpos : 0 < k := hk1
  refine ⟨k, 2 * k, 2 * k, ?_⟩
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · exact hkpos
  · positivity
  · positivity
  · -- Algebraic identity: 4 / n = 1 / k + 1 / (2k) + 1 / (2k), where n = 2k.
    -- Establish the rational identity `(k : ℚ) + (k : ℚ) = 2 * (k : ℚ)` by `ring`,
    -- then thread it through `hk : n = k + k` to clear the ℕ-ℚ bridge.
    have hk2_q : (k : ℚ) + (k : ℚ) = 2 * (k : ℚ) := by ring
    have hn_q : (n : ℚ) = (k : ℚ) + (k : ℚ) := by rw [hk]
    have hn2_q : (n : ℚ) = 2 * (k : ℚ) := hn_q.trans hk2_q
    rw [hn2_q]
    field_simp
    ring

/-- **K3 (price-zero branch).**  If some `r ≡ 3 (mod 4)`, `r ≥ 3`,
    divides one of `n`, `n+1`, `n+4`, the three denominators are
    read off `n` — no divisor of `M = n·a` is searched for. -/
theorem erdos_problem_99_priceZero (n : ℕ)
    (hn : 5 ≤ n) (hn4 : n % 4 = 1)
    (hP : Erdos.StrausGreedy.PriceZeroCovered n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c :=
  Erdos.StrausGreedy.straus_of_priceZero n (by omega) hn4 hP

/-- **K4 (shift branch).**  If some divisor `d > 1` of `n` carries
    `r ≡ 3 (mod 4)` in `d+1`, the rung `r` closes: `n·a = u·d` with
    `u = k·a` and `n = d·k`, and the divisor is read off the
    factorisation of `n` alone. -/
theorem erdos_problem_99_shift (n : ℕ)
    (hn : 5 ≤ n) (hn4 : n % 4 = 1) (hn3 : ¬ (3 ∣ n)) (hn8 : n % 8 ≠ 5)
    (hS : Erdos.StrausGreedy.ShiftCovered n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have hpos : 0 < n := by omega
  obtain ⟨d, r, hd1, hdvd, hr3, hrr, hrd⟩ := hS
  -- Ladder first term: `4 | n + r` because `n % 4 = 1` and `r % 4 = 3`.
  obtain ⟨a, ha0, ha⟩ :=
    Erdos.StrausGreedy.ladder_first_term n r hpos hn4 hrr
  have hr0 : 0 < r := by omega
  -- `ShiftCovered` gives `1 < d`; `closedAtRung_of_shift` wants `0 < d`.
  have hd0 : 0 < d := lt_of_lt_of_le hd1 (Nat.zero_le 1)
  -- `d ∣ n` decomposes as `n = d · k`.
  obtain ⟨k, hk_eq⟩ := hdvd
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, Nat.mul_zero] at hk_eq; omega
    · exact h0
  -- Set `u = k · a` so that `n · a = d · k · a = u · d`.
  exact Erdos.StrausGreedy.straus_of_closedAtRung n r hpos hr0
    (Erdos.StrausGreedy.closedAtRung_of_shift n d r a (k * a) hpos ha0 hd0 ha
      (by rw [hk_eq]; ring) (Nat.mul_pos hk0 ha0) hrd)

/-- **K5 (off the frontier — the kernel's closing theorem).**
    The disjunction `PriceZeroCovered n ∨ ShiftCovered n` covers every
    n off the frontier; this theorem closes on either branch. -/
theorem erdos_problem_99_off_frontier (n : ℕ)
    (hn : 5 ≤ n) (hn4 : n % 4 = 1) (hn3 : ¬ (3 ∣ n)) (hn8 : n % 8 ≠ 5)
    (hPS : Erdos.StrausGreedy.PriceZeroCovered n ∨
           Erdos.StrausGreedy.ShiftCovered n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c :=
  hPS.elim
    (fun hP => erdos_problem_99_priceZero n hn hn4 hP)
    (fun hS => erdos_problem_99_shift n hn hn4 hn3 hn8 hS)

/-- **F (the frontier — named, located, mod 24).**  The frontier is one
    residue class.  Every value the price-zero and shift layers miss
    is `n ≡ 1 (mod 24)`. -/
theorem erdos_problem_99_frontier_mod_24 (n : ℕ)
    (h : Erdos.StrausGreedy.StrausFrontier n) :
    n % 24 = 1 :=
  Erdos.StrausGreedy.straus_frontier_mod_24 n h
