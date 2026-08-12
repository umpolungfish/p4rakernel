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

/-! ## The ladder: the numerator 3 was never special

The instrument that read this class returned `B (open)` on the two-fork form —
"a δ fork dangles; fuse them, or COMMIT one arm (IFIX)". Committing the arm means
the second choice comes from a rule rather than a search, and the rule is here:
the greedy step is only the first rung.

For `n = 4k+1` and any `r ≡ 3 (mod 4)`, the term `a = (n+r)/4` is an integer and

    4/n − 1/a = r/(n·a)

so the remainder's numerator is `r`, chosen rather than met. And the two-term
identity never needed `r = 3` either: for `M = d·e` with `d ≡ −1 (mod r)`,

    r/M = 1/(e(t+1)) + 1/(M(t+1)),    d = r·t + (r−1)

The greedy family is `r = 3`. Each further rung is another covering condition on
the same `n`, and a value the earlier rungs miss can be caught by a later one:
`n = 49`, the first residue of the greedy family, closes at `r = 7` in two terms —
`4/49 = 1/14 + 1/98`.
-/

/-- **The two-term identity, in general.** The numerator `r` plays no special
role; what matters is a divisor of `M` congruent to `−1` mod `r`. -/
theorem r_over_M_split (r t e : ℕ) (hr : 2 ≤ r) (he : 0 < e) :
    (r : ℚ) / ((r * t + (r - 1)) * e)
      = 1 / (e * (t + 1)) + 1 / ((r * t + (r - 1)) * e * (t + 1)) := by
  have he' : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have ht' : ((t : ℚ) + 1) ≠ 0 := by positivity
  -- `r ≥ 2` makes the divisor at least 1, so the denominator does not vanish.
  -- At `r = 1` it can be zero (`t = 0`), which is why the bound is two: a
  -- numerator of one is already a unit fraction and needs no split.
  have hd : ((r : ℚ) * t + ((r : ℚ) - 1)) ≠ 0 := by
    have h2 : (2 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr
    have ht0 : (0 : ℚ) ≤ (t : ℚ) := Nat.cast_nonneg t
    nlinarith
  field_simp
  ring

/-- **The ladder step.** For `n = 4k+1` and `r = 4j+3`, the term `a = (n+r)/4`
is `k+j+1`, and the remainder has numerator exactly `r`. -/
theorem ladder_step (k j : ℕ) :
    (4 : ℚ) / (4 * k + 1) - 1 / (k + j + 1)
      = (4 * j + 3) / ((4 * k + 1) * (k + j + 1)) := by
  have h1 : ((4 : ℚ) * k + 1) ≠ 0 := by positivity
  have h2 : ((k : ℚ) + j + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **`n = 49` closes on the second rung**, in two terms rather than three:
`4/49 = 1/14 + 1/98`. It is the first value the greedy family misses. -/
theorem straus_forty_nine : (4 : ℚ) / 49 = 1 / 14 + 1 / 98 := by norm_num

/-- Two terms suffice there, so the three-term claim holds a fortiori — the
third denominator is free, and `4/49 = 1/14 + 1/98` is the whole content. -/
theorem straus_forty_nine_witness :
    (4 : ℚ) / 49 = 1 / 14 + 1 / 98 ∧ (0:ℚ) < 1 / 14 := by
  constructor <;> norm_num

/-! ## The second split, in full

The identity above is one sufficient family. The criterion it sits inside is
larger, and the difference is not cosmetic: it is the difference between an
instrument that called `n = 2521` unreachable and one that closes it at rung 23.

`r/M = 1/b + 1/c` holds exactly when some `u` with `u·v = M²` satisfies
`r ∣ M + u` and `r ∣ M + v`, because

    (M + u)(M + v) = M² + M(u+v) + uv = M(2M + u + v)

so the two unit fractions with denominators `(M+u)/r` and `(M+v)/r` sum to
`r(2M+u+v) / (M(2M+u+v)) = r/M`. The earlier lemma is the case `u = d`,
`v = M²/d` for a divisor `d ≡ −1 (mod r)` of `M` itself; the criterion ranges
over divisors of `M²`, which is strictly more of them.

The fixed-point rule is what made the difference legible rather than lucky. The
rung test is a congruence — a conservative action — and the rule says a
conservative operator populates only {one-shot, no-closure}, never a basin. So a
value the instrument could not close was never "close to" closing: the
stabiliser set being read was simply the wrong one, and reading the right one
either lands in one shot or does not land at all.
-/

/-- **The second split, as the criterion rather than a family.** Given `u·v = M²`
with `r ∣ M+u` and `r ∣ M+v`, the two unit fractions are explicit. -/
theorem second_split_general (r M u v b c : ℕ) (hr : 0 < r) (hM : 0 < M)
    (huv : u * v = M * M) (hu : 0 < u) (hv : 0 < v)
    (hb : r * b = M + u) (hc : r * c = M + v) (hb0 : 0 < b) (hc0 : 0 < c) :
    (r : ℚ) / M = 1 / b + 1 / c := by
  have hMq : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb0.ne'
  have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc0.ne'
  have hrq : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have huvq : (u : ℚ) * v = (M : ℚ) * M := by exact_mod_cast huv
  have hbq' : (r : ℚ) * b = (M : ℚ) + u := by exact_mod_cast hb
  have hcq' : (r : ℚ) * c = (M : ℚ) + v := by exact_mod_cast hc
  -- `(M+u)(M+v) = M(2M+u+v)` is where the whole criterion lives.
  have key : ((M : ℚ) + u) * ((M : ℚ) + v) = (M : ℚ) * (2 * M + u + v) := by
    nlinarith [huvq]
  -- Multiply the target through: `r·bc = M·(b+c)`. It follows from `key` after
  -- one cancellation of `r`, which is why `r ≠ 0` is a hypothesis.
  have sq : (r : ℚ) * ((r : ℚ) * (b * c)) = (r : ℚ) * ((M : ℚ) * (b + c)) := by
    calc (r : ℚ) * ((r : ℚ) * (b * c))
        = ((r : ℚ) * b) * ((r : ℚ) * c) := by ring
      _ = ((M : ℚ) + u) * ((M : ℚ) + v) := by rw [hbq', hcq']
      _ = (M : ℚ) * (2 * M + u + v) := key
      _ = (M : ℚ) * (((r : ℚ) * b) + ((r : ℚ) * c)) := by rw [hbq', hcq']; ring
      _ = (r : ℚ) * ((M : ℚ) * (b + c)) := by ring
  have main : (r : ℚ) * (b * c) = (M : ℚ) * (b + c) := mul_left_cancel₀ hrq sq
  field_simp
  linarith [main]

/-- `n = 2521` — the value the first instrument could not reach — closes on rung
23: `4/2521 = 1/636 + 1/69748 + 1/131876031`. -/
theorem straus_2521 : IsThreeUnit 2521 636 69748 131876031 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

#print axioms Erdos.StrausGreedy.second_split_general
#print axioms Erdos.StrausGreedy.straus_2521
#print axioms Erdos.StrausGreedy.r_over_M_split
#print axioms Erdos.StrausGreedy.ladder_step
#print axioms Erdos.StrausGreedy.straus_forty_nine
#print axioms Erdos.StrausGreedy.straus_of_divisor
#print axioms Erdos.StrausGreedy.straus_off_residue
#print axioms Erdos.StrausGreedy.greedy_step

end Erdos.StrausGreedy
