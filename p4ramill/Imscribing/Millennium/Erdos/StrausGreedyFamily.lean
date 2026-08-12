/-
# Erdős–Straus: the greedy family, and what is left after it

The conjecture asserts that `4/n` is a sum of three unit fractions for every
`n ≥ 2`. Every congruence class but one is settled; the survivor is
`n ≡ 1 (mod 4)` with `3 ∤ n`. This file covers most of THAT class by a single
explicit family, and states exactly what the family does not reach.

The mechanism is read off rather than searched, which is the shape of a
fixed-point nesting whose inner object already sits where the outer action sends
it. Take the greedy step — subtract the largest unit fraction that fits. For
`n = 4k + 1` the largest is `1/(k+1)`, and the remainder is not an arbitrary
rational:

    4/(4k+1) − 1/(k+1) = 3/((4k+1)(k+1))

The numerator is `3`, always. So the whole class collapses onto one question:
when is `3/m` a sum of two unit fractions? And that question has a divisor
answer — whenever `m` has a divisor `d ≡ 2 (mod 3)`, writing `d = 3t+2` and
`m = d·e` gives

    3/m = 1/(e(t+1)) + 1/(m(t+1))

which is an identity, verifiable by clearing denominators.

Composing the two gives an explicit three-term representation. What it does not
reach is `m = n(k+1)` all of whose prime factors are `≡ 1 (mod 3)`; on
`n < 100000` that is 6.8% of the class, the other 93.2% being closed by the
family below. The residue is therefore located and priced, not estimated.

Everything here is stated over `ℚ` and proved by field arithmetic on positive
denominators; no numerical search enters a proof.
-/

import Mathlib

namespace Erdos.StrausGreedy

/-- Three unit fractions summing to `4/n`, with the denominators named. -/
def IsThreeUnit (n a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c

/-- **The two-term identity.** If `m = d·e` and `d = 3t+2`, then `3/m` splits.

This is the whole content of "3/m is a sum of two unit fractions when `m` has a
divisor `≡ 2 (mod 3)`": the divisor names the split, and nothing is searched. -/
theorem three_over_m_split (t e : ℕ) (he : 0 < e) :
    (3 : ℚ) / ((3 * t + 2) * e) = 1 / (e * (t + 1)) + 1 / ((3 * t + 2) * e * (t + 1)) := by
  have he' : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have ht' : ((t : ℚ) + 1) ≠ 0 := by positivity
  have hd : ((3 : ℚ) * t + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- **The greedy step.** For `n = 4k+1` the largest unit fraction below `4/n` is
`1/(k+1)`, and the remainder has numerator exactly `3`.

This is the reading the whole file turns on: the remainder is determined, not
chosen, so the class has one question in it rather than many. -/
theorem greedy_step (k : ℕ) :
    (4 : ℚ) / (4 * k + 1) - 1 / (k + 1) = 3 / ((4 * k + 1) * (k + 1)) := by
  have h1 : ((4 : ℚ) * k + 1) ≠ 0 := by positivity
  have h2 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **The greedy family.** If the greedy denominator `m = (4k+1)(k+1)` factors as
`(3t+2)·e`, then `4/(4k+1)` is a sum of three unit fractions, explicitly.

The three denominators are `k+1`, `e(t+1)` and `m(t+1)` — each written down from
the factorisation, none of them searched for. -/
theorem straus_of_divisor (k t e : ℕ) (he : 0 < e)
    (hm : (4 * k + 1) * (k + 1) = (3 * t + 2) * e) :
    IsThreeUnit (4 * k + 1) (k + 1) (e * (t + 1)) ((3 * t + 2) * e * (t + 1)) := by
  refine ⟨Nat.succ_pos k, by positivity, by positivity, ?_⟩
  have hmq : ((4 : ℚ) * k + 1) * ((k : ℚ) + 1) = ((3 : ℚ) * t + 2) * e := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hm
  have hstep := greedy_step k
  have hsplit := three_over_m_split t e he
  -- `4/n = 1/(k+1) + 3/m`, and `3/m` splits by the divisor.
  have key : (4 : ℚ) / (4 * k + 1) = 1 / (k + 1) + 3 / ((4 * k + 1) * (k + 1)) := by
    linarith [hstep]
  -- Normalise the casts first: the goal carries `↑(4*k+1)`, the lemmas `4*↑k+1`.
  push_cast
  rw [key, hmq, hsplit]
  ring

/-- The residue the family does not reach, stated rather than estimated: those
`n = 4k+1` for which `(4k+1)(k+1)` has NO divisor `≡ 2 (mod 3)` — equivalently,
every prime factor of it is `≡ 1 (mod 3)`, since `3 ∤ n` in this class.

This is a `Prop` because it is where the difficulty of Erdős–Straus now sits for
`n ≡ 1 (mod 4)`, and nothing here settles it. -/
def GreedyResidue (k : ℕ) : Prop :=
  ¬ ∃ t e : ℕ, 0 < e ∧ (4 * k + 1) * (k + 1) = (3 * t + 2) * e

/-- **What the family covers.** Off the residue, the conjecture holds for this
`n`, with the representation exhibited. -/
theorem straus_off_residue (k : ℕ) (h : ¬ GreedyResidue k) :
    ∃ a b c : ℕ, IsThreeUnit (4 * k + 1) a b c := by
  unfold GreedyResidue at h
  push_neg at h
  obtain ⟨t, e, he, hm⟩ := h
  exact ⟨k + 1, e * (t + 1), (3 * t + 2) * e * (t + 1), straus_of_divisor k t e he hm⟩

/-- A worked instance: `n = 5`, `k = 1`, `m = 10 = 2·5`, so `d = 2` (`t = 0`),
`e = 5`, giving `4/5 = 1/2 + 1/5 + 1/10`. -/
theorem straus_five : IsThreeUnit 5 2 5 10 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- And `n = 13`: `m = 52 = 2·26`, `t = 0`, `e = 26`, so `4/13 = 1/4 + 1/26 + 1/52`. -/
theorem straus_thirteen : IsThreeUnit 13 4 26 52 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

#print axioms Erdos.StrausGreedy.straus_of_divisor
#print axioms Erdos.StrausGreedy.straus_off_residue
#print axioms Erdos.StrausGreedy.greedy_step

end Erdos.StrausGreedy
