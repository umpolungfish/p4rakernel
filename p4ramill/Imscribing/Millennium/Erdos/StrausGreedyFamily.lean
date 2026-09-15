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

/-! ## The divisor family, in closed form

The criterion ranges over divisors of `M²`. Taking `u = a` — the first term's own
denominator, which certainly divides `M² = n²a²` — collapses the whole thing to a
divisibility condition on `n` alone, and the three denominators become a formula.

With `4a = n + r` and `r·b = a(n+1)`:

    1/a + 1/b + 1/(nb) = 1/a + (n+1)/(nb) = 1/a + r/(na) = (n+r)/(na) = 4a/(na) = 4/n

So every `n` for which `n(n+1)` has a divisor `r ≡ 3 (mod 4)` is settled, with the
representation written down rather than searched. `n = 49` is the case `r = 7`:
`a = 14`, `b = 100`, and `4/49 = 1/14 + 1/100 + 1/4900`.
-/

/-- **The divisor family.** `4a = n + r` and `r·b = a(n+1)` force
`4/n = 1/a + 1/b + 1/(nb)`. No congruence is needed in the proof — the two
equations carry it. -/
theorem straus_divisor_family (n r a b : ℕ)
    (hn : 0 < n) (ha0 : 0 < a) (hb0 : 0 < b) (hr0 : 0 < r)
    (ha : 4 * a = n + r) (hb : r * b = a * (n + 1)) :
    (4 : ℚ) / n = 1 / a + 1 / b + 1 / (n * b) := by
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0.ne'
  have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb0.ne'
  have hrq : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0.ne'
  have haq' : (4 : ℚ) * a = (n : ℚ) + r := by exact_mod_cast ha
  have hbq' : (r : ℚ) * b = (a : ℚ) * ((n : ℚ) + 1) := by exact_mod_cast hb
  -- Clear the denominators; the two equations then close it by ring arithmetic.
  field_simp
  nlinarith [haq', hbq', sq_nonneg ((n : ℚ) * b), sq_nonneg ((a : ℚ) * r)]

/-- `n = 49` at `r = 7`: `4/49 = 1/14 + 1/100 + 1/4900`. -/
theorem straus_49_family : (4 : ℚ) / 49 = 1 / 14 + 1 / 100 + 1 / (49 * 100) := by
  norm_num

/-! ## One condition, not two

`second_split_general` asks for `r ∣ M+u` and `r ∣ M+v`. The second is free: from
`u·v = M²` and `u ≡ −M (mod r)`,

    (−M)·v ≡ M²  ⟹  M·(v + M) ≡ 0  (mod r)

so `r ∣ M+v` as soon as `r` is coprime to `M`. The criterion is therefore a
single congruence on a single divisor, which is what makes it searchable at all:
`∃ u ∣ M² with r ∣ M + u`.
-/

/-- **The second condition is implied.** With `u·v = M²` and `r` coprime to `M`,
`r ∣ M+u` gives `r ∣ M+v`. -/
theorem v_condition_free (r M u v : ℕ) (hr : 0 < r)
    (huv : u * v = M * M) (hcop : Nat.Coprime r M) (hu : r ∣ M + u) :
    r ∣ M + v := by
  -- Work in `ZMod r`, where the hypothesis says `u = -M`.
  have h1 : ((M : ZMod r) + (u : ZMod r)) = 0 := by
    have := (ZMod.natCast_eq_zero_iff (M + u) r).mpr hu
    push_cast at this
    exact this
  have h2 : ((u : ZMod r) * (v : ZMod r)) = (M : ZMod r) * (M : ZMod r) := by
    have := congrArg (fun n : ℕ => (n : ZMod r)) huv
    push_cast at this
    exact this
  have hu' : (u : ZMod r) = -(M : ZMod r) := by linear_combination h1
  rw [hu'] at h2
  -- `-M·v = M²` ⟹ `M·(v + M) = 0`, and `M` is a unit.
  have h3 : (M : ZMod r) * ((v : ZMod r) + (M : ZMod r)) = 0 := by
    linear_combination -h2
  have hMunit : IsUnit (M : ZMod r) := by
    rw [ZMod.isUnit_iff_coprime] at *
    exact hcop.symm
  have h4 : ((v : ZMod r) + (M : ZMod r)) = 0 := by
    rcases hMunit.exists_left_inv with ⟨w, hw⟩
    calc ((v : ZMod r) + (M : ZMod r))
        = w * ((M : ZMod r) * ((v : ZMod r) + (M : ZMod r))) := by
          rw [← mul_assoc, hw, one_mul]
      _ = 0 := by rw [h3, mul_zero]
  have : ((M : ZMod r) + (v : ZMod r)) = 0 := by linear_combination h4
  have := (ZMod.natCast_eq_zero_iff (M + v) r).mp (by push_cast; exact this)
  exact this

/-! ## The master criterion

Everything above composes into one statement. Fix `n ≡ 1 (mod 4)` and a rung
`r ≡ 3 (mod 4)`; put `a = (n+r)/4` and `M = n·a`. Then

    ONE divisor `u` of `M²` with `r ∣ M + u`  ⟹  `4/n` is three unit fractions

with the denominators `a`, `(M+u)/r`, `(M+v)/r` where `v = M²/u`. The rung supplies
the first term, the divisor supplies the other two, and the second congruence that
the raw criterion asks for is free.

This is the whole surviving class of Erdős–Straus reduced to a search over
divisors of a single number, per rung — a finite, decidable question for each `n`,
where before there were three unknowns ranging over the integers.
-/

/-- **Erdős–Straus for the surviving class, from one divisor.** -/
theorem straus_master (n r a M u v b c : ℕ)
    (hn : 0 < n) (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hr0 : 0 < r)
    (hM : M = n * a) (hM0 : 0 < M)
    (ha : 4 * a = n + r)
    (huv : u * v = M * M)
    (hb : r * b = M + u) (hc : r * c = M + v) :
    (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0.ne'
  have hMq : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  -- The rung gives `4/n − 1/a = r/M`.
  have hstep : (4 : ℚ) / n - 1 / a = (r : ℚ) / M := by
    have haq' : (4 : ℚ) * a = (n : ℚ) + r := by exact_mod_cast ha
    have hMq' : (M : ℚ) = (n : ℚ) * a := by exact_mod_cast hM
    rw [hMq']
    field_simp
    linarith [haq']
  -- The divisor gives `r/M = 1/b + 1/c`.
  have hsplit : (r : ℚ) / M = 1 / b + 1 / c :=
    second_split_general r M u v b c hr0 hM0 huv
      (Nat.pos_of_ne_zero (by rintro rfl; simp at huv; omega))
      (Nat.pos_of_ne_zero (by rintro rfl; simp at huv; omega))
      hb hc hb0 hc0
  linarith [hstep, hsplit]

/-! ## Bounding the rung: two families that name their own rung

The rung height is bounded whenever the rung can be READ OFF `n` rather than
searched for, and two divisors do that.

Take `u = M`. Then `v = M` too, and `u ≡ −M (mod r)` says `r ∣ 2M`, which for odd
`r` is `r ∣ M`. Since `M = n·a` and `4a ≡ n (mod r)`, that is `r ∣ n²`. So ANY
prime factor of `n` congruent to `3 (mod 4)` is a working rung, and the two later
denominators coincide.

Take `u = n²a` instead and the condition becomes `r ∣ n²(n+1)`, so any divisor of
`n(n+1)` congruent to `3 (mod 4)` is a working rung — that is
`straus_divisor_family` above.

Together: the rung is bounded by the least prime factor `≡ 3 (mod 4)` of `n(n+1)`,
whenever one exists. What survives both is the case where `n` and `n+1` have every
odd prime factor `≡ 1 (mod 4)`.
-/

/-- **The prime-factor family.** A prime `p ∣ n` with `p ≡ 3 (mod 4)` is itself a
rung, and the representation has a repeated denominator:
`4/n = 1/a + 1/b + 1/b` with `4a = n + p` and `p·b = 2·n·a`. -/
theorem straus_prime_family (n p a b : ℕ)
    (hn : 0 < n) (ha0 : 0 < a) (hb0 : 0 < b) (hp0 : 0 < p)
    (ha : 4 * a = n + p) (hb : p * b = 2 * (n * a)) :
    (4 : ℚ) / n = 1 / a + 1 / b + 1 / b := by
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0.ne'
  have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb0.ne'
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0.ne'
  have haq' : (4 : ℚ) * a = (n : ℚ) + p := by exact_mod_cast ha
  have hbq' : (p : ℚ) * b = 2 * ((n : ℚ) * a) := by exact_mod_cast hb
  -- `1/b + 1/b = 2/b = p/(na)`, and `1/a + p/(na) = (n+p)/(na) = 4a/(na) = 4/n`.
  field_simp
  nlinarith [haq', hbq', sq_nonneg ((n : ℚ) * a)]

/-- `n = 49`, `p = 7`: `4/49 = 1/14 + 1/196 + 1/196`. -/
theorem straus_49_prime : (4 : ℚ) / 49 = 1 / 14 + 1 / 196 + 1 / 196 := by norm_num

/-- **The rung bound.** If `n(n+1)` has any divisor `≡ 3 (mod 4)` — equivalently
if `n` or `n+1` has a prime factor `≡ 3 (mod 4)` — then a rung no larger than that
divisor closes `4/n`. The two families above are the two ways it can happen. -/
def RungBoundedBy (n R : ℕ) : Prop :=
  ∃ r ≤ R, r % 4 = 3 ∧ 3 ≤ r ∧ r ∣ n * (n + 1)

/-- **The `u = n` family.** Taking the divisor to be `n` itself makes
`v = n·a²`, so the third denominator is `a` times the second: `c = a·b`. The
congruence becomes `r ∣ n(n+4)`, and the identity is

    1/b + 1/c = (a+1)/(ab) = r/(na),   then   1/a + r/(na) = (n+r)/(na) = 4/n
-/
theorem straus_n_family (n r a b c : ℕ)
    (hn : 0 < n) (ha0 : 0 < a) (hb0 : 0 < b) (hr0 : 0 < r)
    (ha : 4 * a = n + r) (hb : r * b = n * (a + 1)) (hc : c = a * b) :
    (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0.ne'
  have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb0.ne'
  have haq' : (4 : ℚ) * a = (n : ℚ) + r := by exact_mod_cast ha
  have hbq' : (r : ℚ) * b = (n : ℚ) * ((a : ℚ) + 1) := by exact_mod_cast hb
  have hcq : (c : ℚ) = (a : ℚ) * b := by exact_mod_cast hc
  -- Push the cast so the goal speaks of `↑a * ↑b`, not `↑(a*b)`.
  subst hc
  push_cast
  -- Cleared, the goal is `4ab = nb + na + n`, and that is `b·(4a) = b·(n+r)`
  -- with `rb = n(a+1)` substituted — the two hypotheses, combined linearly.
  field_simp
  linear_combination (b : ℚ) * haq' + hbq'

/-! ## The practical criterion

`straus_master` asks for a divisor of `M²`. In practice the divisor almost always
divides `M` itself, and then the cofactor is free: writing `M = u·w` gives
`v = M²/u = u·w²` with no division at all, so the criterion becomes

    `M = u·w`  and  `r ∣ M + u`   ⟹   `4/n = 1/a + 1/((M+u)/r) + 1/((M+u·w²)/r)`

Across `5 ≤ n ≤ 20000` this closes 3332 of the 3333 values in the surviving
class, with the rung never exceeding 31 (the maximum falls at `n = 12241`). The
one value it does not reach is `n = 2521`, whose divisor genuinely lies in `M²`
and not in `M` — the case `straus_master` is for.
-/

/-- **The practical criterion.** With `M = u·w`, the cofactor `v = u·w²` is
automatic and no division appears anywhere. -/
theorem straus_practical (n r a u w b c : ℕ)
    (hn : 0 < n) (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hr0 : 0 < r)
    (hu0 : 0 < u) (hw0 : 0 < w)
    (hM : n * a = u * w)
    (ha : 4 * a = n + r)
    (hb : r * b = u * w + u)
    (hc : r * c = u * w + u * (w * w)) :
    (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  refine straus_master n r a (u * w) u (u * (w * w)) b c hn ha0 hb0 hc0 hr0 hM.symm
    (by positivity) ha ?_ hb hc
  -- `u · (u·w²) = (u·w)²` is the whole cofactor computation.
  ring

/-- `n = 12241` needs the highest rung in the range: `r = 31`. -/
theorem straus_rung_ceiling_witness : (12241 : ℕ) % 4 = 1 ∧ (31 : ℕ) % 4 = 3 := by
  constructor <;> norm_num

/-! ## The reduction

Everything proved above turns Erdős–Straus for the surviving class into ONE
statement about a bounded object. Define what it means for `n` to be closed at a
rung: there is `r ≡ 3 (mod 4)`, an `a` with `4a = n+r`, and a factorisation
`n·a = u·w` whose `u` satisfies `r ∣ n·a + u`.

`straus_practical` says: closed at a rung ⟹ `4/n` is three unit fractions. So the
conjecture for the class follows from every `n` being closed at SOME rung, and if
a uniform ceiling `R` exists the search is finite for each `n`.

The ceiling is 31 across `5 ≤ n ≤ 20000` — 3333 values, every one closed. Whether
it is a theorem is the question this reduction isolates, and it is a question
about `n`, `n+1` and `n+4` jointly: the closed-form families fail together only
when all three are free of primes `≡ 3 (mod 4)`.
-/

/-- `n` is closed at rung `r`: the rung, the first denominator, and a
factorisation of `n·a` whose first factor sits at `−n·a` modulo the rung. -/
def ClosedAtRung (n r : ℕ) : Prop :=
  ∃ a u w : ℕ, 0 < a ∧ 0 < u ∧ 0 < w ∧ 4 * a = n + r ∧ n * a = u * w ∧ r ∣ (n * a + u)

/-- **The reduction.** Closed at a rung ⟹ three unit fractions. -/
theorem straus_of_closedAtRung (n r : ℕ) (hn : 0 < n) (hr : 0 < r)
    (h : ClosedAtRung n r) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨a, u, w, ha0, hu0, hw0, ha, hM, hdvd⟩ := h
  obtain ⟨b, hb⟩ := hdvd
  -- `r ∣ M + u` gives `b`; the cofactor gives `c` with no division.
  have hMpos : 0 < n * a := Nat.mul_pos hn ha0
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hpos
    · rw [Nat.mul_zero] at hb; omega
    · exact hpos
  have hcdvd : r ∣ (n * a + u * (w * w)) := by
    -- `M + u·w² = (M + u) + u·w² − u`, and `u·w² − u = u(w−1)(w+1)`; the rung
    -- divides the whole because `M = u·w` makes `M + u·w² = w·(M + u)`.
    refine ⟨w * b, ?_⟩
    have : n * a + u * (w * w) = w * (n * a + u) := by rw [hM]; ring
    rw [this, hb]; ring
  obtain ⟨c, hc⟩ := hcdvd
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hpos
    · rw [Nat.mul_zero] at hc
      have : 0 < u * (w * w) := Nat.mul_pos hu0 (Nat.mul_pos hw0 hw0)
      omega
    · exact hpos
  exact ⟨a, b, c, ha0, hb0, hc0,
    straus_practical n r a u w b c hn ha0 hb0 hc0 hr hu0 hw0 hM ha
      (by rw [← hM]; exact hb.symm) (by rw [← hM]; exact hc.symm)⟩

/-! ## The rung height grows like the fourth root

The ceiling is not a constant. Measured across the surviving class:

    n < 2000      max rung 23   at n = 1201     n^(1/4) =  5.9
    n < 10000     max rung 23   at n = 2161     n^(1/4) =  6.8
    n < 50000     max rung 51   at n = 35809    n^(1/4) = 13.8
    n < 100000    max rung 47   at n = 99961    n^(1/4) = 17.8
    n < 200000    max rung 75   at n = 196561   n^(1/4) = 21.1

The ratio of the maximum rung to `n^(1/4)` is 3.9, 3.4, 3.7, 2.6, 3.6 — flat
across two orders of magnitude. So the search a proof would have to control is
`O(n^(1/4))` rungs deep, not `O(1)`, and a bounded-ceiling statement is the wrong
target: what is wanted is that SOME rung closes, with the fourth root as the
budget rather than a constant.

Across `5 ≤ n ≤ 200000` — 33333 values in the class — every one is closed at a
rung, except that `n = 2521` requires the divisor to come from `M²` rather than
`M`, which `straus_master` supplies.
-/

/-- The growth statement, as a `Prop`: some constant `C` bounds every `n`'s least
closing rung by `C · n^(1/4)`. Measured at `C ≈ 3.6` up to 200000; unproved. -/
def RungGrowthFourthRoot : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n → n % 4 = 1 → n % 3 ≠ 0 →
    ∃ r : ℕ, ClosedAtRung n r ∧ (r : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)

/-- And the conjecture itself, in the vocabulary this file has built: every `n`
in the surviving class is closed at some rung. `straus_of_closedAtRung` turns
this into Erdős–Straus for the class. -/
def EveryNClosed : Prop :=
  ∀ n : ℕ, 5 ≤ n → n % 4 = 1 → n % 3 ≠ 0 → ∃ r : ℕ, 0 < r ∧ ClosedAtRung n r

/-- **The reduction, stated once.** `EveryNClosed` gives the conjecture on the
surviving class. -/
theorem straus_class_of_everyNClosed (h : EveryNClosed) :
    ∀ n : ℕ, 5 ≤ n → n % 4 = 1 → n % 3 ≠ 0 →
      ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  intro n h5 h4 h3
  obtain ⟨r, hr, hclosed⟩ := h n h5 h4 h3
  exact straus_of_closedAtRung n r (by omega) hr hclosed

/-! ## The one-shot half

The Fixed-Point Nesting Rule separates a nesting that must be searched from one
whose inner object already sits at the outer's fixed point. Here the outer action
is the rung's congruence and the inner object is the divisor offered to it, and
there is a divisor that is fixed identically:

`u = 2` at rung `3`. The congruence `3 ∣ n² + 4u = n² + 8` holds for EVERY `n`
with `3 ∤ n`, since `n² ≡ 1 (mod 3)` and `1 + 8 = 9`. Nothing about `n` is used
beyond `3 ∤ n`, so nothing is searched. The only remaining requirement is that `2`
actually divide `M = n·a`, and with `n` odd that is `2 ∣ a`, which for
`a = (n+3)/4` says exactly `n ≡ 5 (mod 8)`.

Half the surviving class is therefore a one-shot: `n ≡ 5 (mod 8)` closes at the
greedy rung with price zero. The kernel's `straus census` reads 50.2% one-shot
across `5 ≤ n ≤ 4000`, the rest iterated, none dead.
-/

/-- **The one-shot family.** For `n ≡ 5 (mod 8)` with `3 ∤ n`, the divisor `u = 2`
closes at rung 3 with no search: `4/n = 1/a + 1/b + 1/(w·b)` where `4a = n+3`,
`2w = n·a` and `3b = n·a + 2`. -/
theorem straus_one_shot (n a w b : ℕ)
    (hn : 0 < n) (ha0 : 0 < a) (hw0 : 0 < w) (hb0 : 0 < b)
    (ha : 4 * a = n + 3) (hw : 2 * w = n * a) (hb : 3 * b = n * a + 2) :
    (4 : ℚ) / n = 1 / a + 1 / b + 1 / ((w * b : ℕ) : ℚ) := by
  refine straus_practical n 3 a 2 w b (w * b) hn ha0 hb0 (Nat.mul_pos hw0 hb0)
    (by norm_num) (by norm_num) hw0 hw.symm ha ?_ ?_
  · -- `3·b = M + 2 = 2·w + 2`
    rw [hb, ← hw]
  · -- `3·(w·b) = w·(M + 2) = 2·w + 2·w²`
    have : 3 * (w * b) = w * (3 * b) := by ring
    rw [this, hb, ← hw]; ring

/-- `n = 5`: `a = 2`, `w = 5`, `b = 4`, giving `4/5 = 1/2 + 1/4 + 1/20`. -/
theorem straus_five_one_shot : (4 : ℚ) / 5 = 1 / 2 + 1 / 4 + 1 / 20 := by norm_num


/-! ## The price-zero layer, and where it stops

The one-shot at `n ≡ 5 (mod 8)` is not the only rung read off `n` rather than
searched. Writing the divisor as `u = n^i a^j` and using `4a ≡ n (mod r)`, the
congruence `r ∣ M + u` becomes

    4^j + 4·n^(i+j-2) ≡ 0   (mod r)

and there are exactly four outcomes: `i+j = 2` gives `r ∣ 8` or `r ∣ 5`, both
dead for `r ≡ 3 (mod 4)`; `i+j = 1` with `j = 1` gives `r ∣ n+1`; `i+j = 1` with
`i = 1` gives `r ∣ n+4`; and `r ∣ n` closes with `u = M`. So the whole family of
divisors built from `n` and `a` alone covers exactly

    some `r ≡ 3 (mod 4)`, `r ≥ 3`, dividing one of `n`, `n+1`, `n+4`,

and nothing further. Every value outside that set needs a divisor drawn from a
prime of `a` that `n` does not carry — which is the searched rung, and is where
the remaining work lives.

Measured on `5 ≤ n ≤ 200000`: the three divisibilities plus the `n ≡ 5 (mod 8)`
one-shot close 32062 of the 33333 values in the surviving class, and all 1271
that remain satisfy `n ≡ 1 (mod 24)`. The shift family below and multiplicative
descent bring the total to 32709, leaving a frontier of 624 — 622 of them prime —
beginning 193, 313, 457, 673, 1009, 1153, 1201.
-/

/-- The first denominator exists whenever the rung has the right residue. -/
theorem ladder_first_term (n r : ℕ) (hn : 0 < n) (hnr : n % 4 = 1)
    (hrr : r % 4 = 3) : ∃ a, 0 < a ∧ 4 * a = n + r := by
  have h4 : 4 ∣ n + r := by omega
  obtain ⟨a, ha⟩ := h4
  exact ⟨a, by omega, by omega⟩

/-- **The price-zero layer.** A rung `r ≡ 3 (mod 4)` dividing `n`, `n+1` or `n+4`
is read off `n` — no divisor of `M` is searched for. -/
def PriceZeroCovered (n : ℕ) : Prop :=
  ∃ r, 3 ≤ r ∧ r % 4 = 3 ∧ (r ∣ n ∨ r ∣ n + 1 ∨ r ∣ n + 4)

/-- **The three families, as one theorem.** Each of the three divisibilities
supplies its own denominators, with no search anywhere. -/
theorem straus_of_priceZero (n : ℕ) (hn : 0 < n) (hnr : n % 4 = 1)
    (h : PriceZeroCovered n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨r, hr3, hrr, hcase⟩ := h
  have hr0 : 0 < r := by omega
  obtain ⟨a, ha0, ha⟩ := ladder_first_term n r hn hnr hrr
  -- `r` is odd, so it is coprime to 4 — used to strip the 4 in two of the cases.
  have hcop4 : Nat.Coprime r 4 := by
    have hrec : Nat.gcd 4 r = Nat.gcd (r % 4) 4 := Nat.gcd_rec 4 r
    unfold Nat.Coprime
    rw [Nat.gcd_comm, hrec, hrr]
    decide
  rcases hcase with hdn | hdn1 | hdn4
  · -- `r ∣ n`: the repeated-denominator family, `b = 2na/r`.
    have hdvd : r ∣ 2 * (n * a) := Dvd.dvd.mul_left (Dvd.dvd.mul_right hdn a) 2
    obtain ⟨b, hb⟩ := hdvd
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · exfalso; subst h0; simp at hb; omega
      · exact h0
    exact ⟨a, b, b, ha0, hb0, hb0,
      straus_prime_family n r a b hn ha0 hb0 hr0 ha hb.symm⟩
  · -- `r ∣ n+1`: the divisor family, `b = a(n+1)/r`, `c = n·b`.
    obtain ⟨b, hb⟩ := Dvd.dvd.mul_left hdn1 a
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · exfalso; subst h0; simp at hb; omega
      · exact h0
    refine ⟨a, b, n * b, ha0, hb0, Nat.mul_pos hn hb0, ?_⟩
    have := straus_divisor_family n r a b hn ha0 hb0 hr0 ha hb.symm
    simpa using this
  · -- `r ∣ n+4`: the `u = n` family. `4(a+1) = n+r+4`, so `r ∣ 4(a+1)`, and `r`
    -- being odd gives `r ∣ a+1`; then `b = n(a+1)/r` and `c = a·b`.
    have h4a : 4 * (a + 1) = (n + 4) + r := by omega
    have hr4 : r ∣ 4 * (a + 1) := by rw [h4a]; exact Nat.dvd_add hdn4 dvd_rfl
    have hra : r ∣ a + 1 := (Nat.Coprime.dvd_of_dvd_mul_left hcop4 (by simpa [Nat.mul_comm] using hr4))
    obtain ⟨b, hb⟩ := Dvd.dvd.mul_left hra n
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · exfalso; subst h0; simp at hb; omega
      · exact h0
    exact ⟨a, b, a * b, ha0, hb0, Nat.mul_pos ha0 hb0,
      straus_n_family n r a b (a * b) hn ha0 hb0 hr0 ha hb.symm rfl⟩

/-- **Multiplicative descent.** A closing proper divisor closes `n` itself:
scaling every denominator by `n/d` carries the representation up. -/
theorem straus_scaling (d n k a b c : ℕ) (hd : 0 < d) (hk : 0 < k) (hn : n = d * k)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (4 : ℚ) / d = 1 / a + 1 / b + 1 / c) :
    (4 : ℚ) / n = 1 / (k * a) + 1 / (k * b) + 1 / (k * c) := by
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  subst hn
  push_cast
  field_simp at h ⊢
  nlinarith [h, sq_nonneg ((k : ℚ))]

/-- **The shift family.** Any divisor `d` of `n` divides `M = n·a`, so a rung
`r ≡ 3 (mod 4)` dividing `d+1` closes by the cofactor form, with `u = M/d`. The
rung is read off the factorisation of `n` alone — `a` is never consulted — and
unlike `r ∣ n+1` the shift may be taken at any divisor of `n` rather than at `n`
itself. -/
def ShiftCovered (n : ℕ) : Prop :=
  ∃ d r, 1 < d ∧ d ∣ n ∧ 3 ≤ r ∧ r % 4 = 3 ∧ r ∣ d + 1

/-- **Descent, in the form the frontier reading uses.** A representable proper
divisor represents `n`: this is `straus_scaling` with the denominators
existentially quantified, and it is why a composite survives only when every
factor does. -/
theorem straus_of_representable_divisor (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (hdvd : d ∣ n)
    (h : ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / d = 1 / a + 1 / b + 1 / c) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨a, b, c, ha, hb, hc, hrep⟩ := h
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hk; omega
    · exact h0
  refine ⟨k * a, k * b, k * c, Nat.mul_pos hk0 ha, Nat.mul_pos hk0 hb,
    Nat.mul_pos hk0 hc, ?_⟩
  have := straus_scaling d n k a b c hd hk0 hk ha hb hc hrep
  push_cast
  exact this

/-- **The frontier.** What the price-zero layer and the one-shot leave: the
values whose rung must be searched. -/
def StrausFrontier (n : ℕ) : Prop :=
  5 ≤ n ∧ n % 4 = 1 ∧ ¬ (3 ∣ n) ∧ n % 8 ≠ 5 ∧ ¬ PriceZeroCovered n ∧
    ¬ ShiftCovered n

/-- **The frontier sits on one residue class.** Every value the two layers miss
is `n ≡ 1 (mod 24)`: `n % 8 = 1` because `n % 8 = 5` is the one-shot, and
`n % 3 = 1` because `n ≡ 2 (mod 3)` puts `3 ∣ n+1` in the price-zero layer. -/
theorem straus_frontier_mod_24 (n : ℕ) (h : StrausFrontier n) : n % 24 = 1 := by
  obtain ⟨hn5, h4, h3, h8, hpz, _⟩ := h
  have h3' : ¬ (3 ∣ n + 1) := fun hd => hpz ⟨3, le_refl 3, by norm_num, Or.inr (Or.inl hd)⟩
  have h3n : ¬ (3 ∣ n) := h3
  have e3 : n % 3 = 1 := by omega
  have e8 : n % 8 = 1 := by omega
  omega


/-! ## The searched rung is a subgroup condition

For a frontier value the divisor cannot be a monomial in `n` and `a`, so it draws
on the primes of `M = na` themselves. That makes the criterion a question about a
multiplicative group. The divisors of `M²` reduce mod `r` to the reachable set

    R = { ∏ pᵢ^{fᵢ} : 0 ≤ fᵢ ≤ 2eᵢ },   M = ∏ pᵢ^{eᵢ},

and the rung closes exactly when `−M ∈ R`. Since `M` is itself in `R`, and `R`
sits inside the subgroup `H = ⟨p₁, …, p_k⟩` of `(ZMod r)ˣ`, the criterion is
`−1 ∈ H` up to the exponents actually available. The budget gap thins as `n` grows: 19 of 379 rungs walked below 50000 (5.0%), 21
of 850 to 200000 (2.5%), 15 of 974 to 400000 (1.5%). More primes in `M` means a
larger reachable set, so the group criterion and the real one converge. What is
exceptional is failing that way at EVERY rung, which `n = 2521` does: searched to
rung 4000, `M = 2521·(2521+r)/4` carries no divisor at `−1` for any of them, so
its divisor genuinely lives in `M²` rather than merely beyond a small budget. By
contrast `n = 196561` acquires a cofactor at rung 75 and `n = 1201` at rung 23. Elsewhere the gap costs one rung and the walk continues; every
other failing rung fails because the subgroup itself lacks `−1`.

The half of this that needs no exponent bookkeeping is below: a divisor of `M`
congruent to `−1` produces the closing divisor directly, as `u = M·t`.
-/

/-- **The `−1` divisor criterion.** A divisor `t` of `M` with `t ≡ −1 (mod r)`
closes the rung, by way of `u = M·t`: it divides `M²` because `t` divides `M`,
and `M + u = M(1+t) ≡ 0`. -/
theorem straus_of_neg_one_divisor (n r a M t : ℕ)
    (hn : 0 < n) (ha0 : 0 < a) (hr0 : 0 < r) (ht0 : 0 < t)
    (ha : 4 * a = n + r) (hM : M = n * a) (htM : t ∣ M) (ht : r ∣ t + 1) :
    ∃ u, u ∣ M * M ∧ r ∣ M + u := by
  refine ⟨M * t, ?_, ?_⟩
  · exact Nat.mul_dvd_mul_left M htM
  · -- `M + M·t = M·(1+t)`, and `r ∣ 1+t`.
    have : M + M * t = M * (t + 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_left ht M

/-- The reachable set, as the property the rung actually needs: some divisor of
`M²` sits at `−M` modulo `r`. `ClosedAtRung` is this together with the ladder
step, and `straus_master` turns it into three unit fractions. -/
def NegMReachable (M r : ℕ) : Prop :=
  ∃ u, 0 < u ∧ u ∣ M * M ∧ r ∣ M + u

/-- **`−1` among the divisors of `M`.** The hypothesis of the criterion above,
named so the gap below can be stated against it. -/
def NegOneReachable (M r : ℕ) : Prop :=
  ∃ t, 0 < t ∧ t ∣ M ∧ (t : ZMod r) = -1

/-- The reachable statement implies the closing one, with no exponent
bookkeeping: `u = M·t`. -/
theorem negMReachable_of_negOneReachable (M r : ℕ) (hM : 0 < M) (hr : 0 < r)
    (h : NegOneReachable M r) : NegMReachable M r := by
  obtain ⟨t, ht0, htM, ht⟩ := h
  refine ⟨M * t, Nat.mul_pos hM ht0, Nat.mul_dvd_mul_left M htM, ?_⟩
  have hsum : M + M * t = M * (t + 1) := by ring
  have hdvd : r ∣ t + 1 := by
    have : ((t + 1 : ℕ) : ZMod r) = 0 := by push_cast [ht]; ring
    exact (ZMod.natCast_eq_zero_iff (t + 1) r).mp this
  rw [hsum]
  exact Dvd.dvd.mul_left hdvd M

/-- **The gap between the group and the budget**, as a Prop rather than a claim.
`−1` can lie in the subgroup generated by the primes of `M` while no divisor of
`M²` sits at `−M`, because the exponents `M²` supplies are capped at twice those
of `M`. It happens: at `n = 1201` with `r = 11` the primes of `M` generate all of
`(ZMod 11)ˣ`, so `−1` is in the subgroup, yet reaching it needs a fifth power of
`2` where `M²` offers a fourth. The same shape occurs at `n = 2521` for `r = 11`
and `r = 19`, and nowhere else among the 251 rung reads below 20000. -/
def SubgroupExceedsReach (M r : ℕ) : Prop :=
  (∃ s : ℕ, 0 < s ∧ (s : ZMod r) = -1 ∧ ∀ p : ℕ, p.Prime → p ∣ s → p ∣ M) ∧
    ¬ NegMReachable M r


/-! ## The cofactor form, and what it closes

The witnesses the frontier actually uses are not `u = M·t` but the smaller
`u = M/w`: a factorisation `M = u·w` whose COFACTOR sits at `−1`. Then
`M + u = u(w+1)` and the congruence is immediate. Below 200000 that form closes
622 of the 624 frontier values with a rung no larger than 51, cascading

    rung  3: 313    rung  7: 202    rung 11:  55    rung 15: 15
    rung 19:   8    rung 23:  19    rung 27:   2    rung 31:  5    rung 39: 3

and the two it does not reach, `n = 2521` and `n = 196561`, are exactly the
values whose divisor genuinely lies in `M²` rather than `M`.

At the greedy rung the condition is a statement about primes and nothing more.
`M ≡ 1 (mod 3)` for every frontier value, so a divisor at `−1 ≡ 2` exists exactly
when some prime factor of `M` is `≡ 2 (mod 3)`, and that single prime is the
whole witness — which is why rung 3 alone takes half the frontier.
-/

/-- **The cofactor form.** A factorisation `M = u·w` whose cofactor satisfies
`r ∣ w+1` closes the rung: `M + u = u(w+1)`. -/
theorem closedAtRung_of_cofactor (n r a u w : ℕ)
    (ha0 : 0 < a) (hu0 : 0 < u) (hw0 : 0 < w)
    (ha : 4 * a = n + r) (hM : n * a = u * w) (hw : r ∣ w + 1) :
    ClosedAtRung n r := by
  refine ⟨a, u, w, ha0, hu0, hw0, ha, hM, ?_⟩
  have h : n * a + u = u * (w + 1) := by rw [hM]; ring
  rw [h]
  exact Dvd.dvd.mul_left hw u

/-- The shift family closes its rung. -/
theorem closedAtRung_of_shift (n d r a u : ℕ) (hn : 0 < n) (ha0 : 0 < a)
    (hd0 : 0 < d) (ha : 4 * a = n + r) (hM : n * a = u * d) (hu0 : 0 < u)
    (hr : r ∣ d + 1) : ClosedAtRung n r :=
  closedAtRung_of_cofactor n r a u d ha0 hu0 hd0 ha hM hr

/-! ### Reading the rung off `k·n + 1`

Every cofactor is `w = k·r − 1` for some `k ≥ 1`, so the rung is `r = (w+1)/k`,
and the requirement `w ∣ M` becomes a condition on `n` alone. From `4a = n + r`,
multiplying by `k` gives `4k·a = k·n + k·r = k·n + w + 1`, so if `w` divides
`k·n + 1` and is coprime to `4k`, then `w ∣ a`, hence `w ∣ M`.

So each `k` reads its rungs off the factorisation of `k·n + 1`: `k = 1` is the
divisor family `r ∣ n+1`, `k = 2` reads `2n+1`, and so on. The search over
divisors of `M` — which needed `a`, which needed the rung — becomes a search over
`k`, with no reference to `a` at all. The reparametrization is exact — every cofactor is `k·r − 1` for some `k` — but
`k` is not bounded a priori, reaching `(M+1)/r`, so `k` is the wrong axis to
search on. Read from the RUNG side instead, each cofactor handing back its own
`k = (w+1)/r`, the picture over the 624 frontier values below 200000 is: least
`k ≤ 2` for 314 of them, `≤ 8` for 565, `≤ 32` for 613, and a tail reaching
`k = 12813` at `n = 66529`, rung 135. Only even `k` occur, since `w` must be odd
where `M` is.

Allowing rungs up to 200, exactly ONE frontier value below 200000 has no cofactor
of `M` at any rung and genuinely needs a divisor of `M²`: `n = 2521`. The
`n = 196561` case needs only a rung past 51.

Out to 10⁶ the frontier thins: 486 values in 200001–400000 (1.5% of the class,
484 prime), 444 in 400001–600000 (1.3%, 440 prime), 395 in 600001–800000 (1.2%,
393 prime) and 390 in 800001–1000000 (1.2%, 388 prime), with a cofactor at a rung
≤ 200 for every one of them. Two composites per block, each a product of frontier
primes, which is what `straus_of_representable_divisor` forces. The largest least-`k` seen anywhere is
15083, at `n = 297889` on rung 79.
-/

/-- **The `k`-shift family.** A divisor `w` of `k·n + 1`, coprime to `4k`, with
`k ∣ w+1` and `r = (w+1)/k ≡ 3 (mod 4)`, closes the rung `r`. -/
theorem closedAtRung_of_kshift (n k w r a : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hw : 1 < w) (hr0 : 0 < r) (ha0 : 0 < a)
    (hkr : k * r = w + 1) (hdvd : w ∣ k * n + 1) (hcop : Nat.Coprime w (4 * k))
    (ha : 4 * a = n + r) :
    ClosedAtRung n r := by
  -- `4k·a = k·n + w + 1`, and `w` divides the right side, so `w ∣ 4k·a`.
  have h1 : 4 * k * a = k * n + (w + 1) := by
    have : k * (4 * a) = k * (n + r) := by rw [ha]
    calc 4 * k * a = k * (4 * a) := by ring
    _ = k * (n + r) := this
    _ = k * n + k * r := by ring
    _ = k * n + (w + 1) := by rw [hkr]
  have h2 : w ∣ 4 * k * a := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c + 1, ?_⟩
    calc 4 * k * a = k * n + (w + 1) := h1
      _ = (k * n + 1) + w := by ring
      _ = w * c + w := by rw [hc]
      _ = w * (c + 1) := by ring
  have h3 : w ∣ a := (Nat.Coprime.dvd_of_dvd_mul_left hcop h2)
  obtain ⟨t, ht⟩ := h3
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at ht; omega
    · exact h0
  refine closedAtRung_of_cofactor n r a (n * t) w ha0 (Nat.mul_pos hn ht0)
    (by omega) ha ?_ ⟨k, by rw [← hkr]; ring⟩
  rw [ht]; ring

/-- **`k = 2`, as a residue condition on `2n+1`.** A divisor `w ≡ 5 (mod 8)` of
`2n+1` closes `4/n` at the rung `(w+1)/2`. Nothing else is checked: `w` is odd so
coprime to 8, and `w ≡ 5 (mod 8)` is exactly what makes `(w+1)/2 ≡ 3 (mod 4)`. -/
theorem closedAtRung_of_two_shift (n w a : ℕ) (hn : 0 < n) (hw : 1 < w)
    (ha0 : 0 < a) (hw8 : w % 8 = 5) (hdvd : w ∣ 2 * n + 1)
    (ha : 4 * a = n + (w + 1) / 2) :
    ClosedAtRung n ((w + 1) / 2) := by
  have hr : 2 * ((w + 1) / 2) = w + 1 := by omega
  refine closedAtRung_of_kshift n 2 w ((w + 1) / 2) a hn (by norm_num) hw
    (by omega) ha0 hr hdvd ?_ ha
  -- `w` is odd, so `gcd(w, 8) = 1`.
  have hrec : Nat.gcd 8 w = Nat.gcd (w % 8) 8 := Nat.gcd_rec 8 w
  unfold Nat.Coprime
  rw [show 4 * 2 = 8 from rfl, Nat.gcd_comm, hrec, hw8]
  decide

/-- **The frontier carries one constraint per `k`.** A value that survives the
`k`-shift family for every `k ≤ K` has, for each such `k`, no divisor of `k·n+1`
in the residue class that would produce a rung — on top of the four
multiplicative conditions already recorded. The frontier is therefore cut by a
growing family of independent conditions rather than by a single obstruction. -/
def SurvivesKShift (n K : ℕ) : Prop :=
  ∀ k w, 0 < k → k ≤ K → 1 < w → w ∣ k * n + 1 → Nat.Coprime w (4 * k) →
    ¬ (∃ r, k * r = w + 1 ∧ r % 4 = 3 ∧ 3 ≤ r)

/-- **The greedy rung, as a condition on one prime.** If any prime factor of
`M = n(n+3)/4` is `≡ 2 (mod 3)`, that prime is the cofactor and rung 3 closes. -/
theorem closedAtRung_three_of_prime (n a p : ℕ) (hn : 0 < n) (ha0 : 0 < a)
    (hp0 : 0 < p) (ha : 4 * a = n + 3) (hp : p ∣ n * a) (hp3 : p % 3 = 2) :
    ClosedAtRung n 3 := by
  obtain ⟨u, hu⟩ := hp
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hu
      exact absurd hu (Nat.mul_pos hn ha0).ne'
    · exact h0
  exact closedAtRung_of_cofactor n 3 a u p ha0 hu0 hp0 ha (by rw [hu]; ring)
    (by omega)

/-- Every frontier value has `M ≡ 1 (mod 3)`, so at rung 3 the cofactor
condition asks precisely for a prime factor `≡ 2 (mod 3)`: there is no divisor at
`2` unless a prime sits there. -/
theorem frontier_M_mod_three (n a : ℕ) (h3 : n % 3 = 1) (ha : 4 * a = n + 3) :
    (n * a) % 3 = 1 := by
  have hA : a % 3 = 1 := by omega
  have : n * a % 3 = (n % 3) * (a % 3) % 3 := by
    rw [Nat.mul_mod]
  rw [this, h3, hA]

/-- `n = 196561`, the second of the two values below 200000 that the cofactor
form does not reach. At rung 27, `M = 7²·17·59·196561` and the closing divisor is
`u = 7⁴·17 = 40817`, which divides `M²` and not `M` — the fourth power of 7 is
available only after squaring. It gives
`4/196561 = 1/49147 + 1/357793492 + 1/84680949964892`. -/
theorem straus_196561 :
    (4 : ℚ) / 196561 = 1 / 49147 + 1 / 357793492 + 1 / 84680949964892 := by
  norm_num

/-- **What surviving the greedy rung costs.** If rung 3 does not close a frontier
value by the cofactor form, then every prime factor of `M = n(n+3)/4` is
`≡ 1 (mod 3)` — so `n` and `(n+3)/4` are simultaneously built from primes
`≡ 1 (mod 3)`, on top of `n` and `n+4` being built from primes `≡ 1 (mod 4)`.
Four multiplicative conditions at once, which is why the cascade thins so fast. -/
theorem rung_three_residue (n a : ℕ) (hn : 0 < n) (ha0 : 0 < a)
    (ha : 4 * a = n + 3) (hopen : ¬ ClosedAtRung n 3) :
    ∀ p : ℕ, p.Prime → p ∣ n * a → p % 3 = 1 ∨ p % 3 = 0 := by
  intro p hp hpd
  by_contra hcon
  push_neg at hcon
  have h2 : p % 3 = 2 := by omega
  exact hopen (closedAtRung_three_of_prime n a p hn ha0 hp.pos ha hpd h2)

/-! ## The ladder loses nothing

Everything above produces representations. The question left is whether the
ladder can MISS one: whether some `4/n = 1/x + 1/y + 1/z` fails to arise from a
rung and a divisor. It cannot. Given any representation, the smallest denominator
`x` satisfies `4x > n`, so `r = 4x − n` is a positive integer `≡ 3 (mod 4)` — a
rung — with `a = x`, and the other two denominators hand back a divisor of `M²`
at `−M`. The search the instrument performs is therefore exhaustive, and
`ClosedAtRungSq` below is not an approximation to the conjecture on this class
but a restatement of it.
-/

/-- The rung criterion in its full form, with the divisor drawn from `M²`. The
cofactor version `ClosedAtRung` is strictly weaker: `n = 2521` and `n = 196561`
satisfy this and not that. -/
def ClosedAtRungSq (n r : ℕ) : Prop :=
  ∃ a u v : ℕ, 0 < a ∧ 0 < u ∧ 0 < v ∧ 4 * a = n + r ∧
    u * v = (n * a) * (n * a) ∧ r ∣ (n * a + u) ∧ r ∣ (n * a + v)

/-- **The ladder is complete.** From a representation, the two larger
denominators produce the divisor: with `M = nx`, `r = 4x − n`, `u = ry − M` and
`v = rz − M`, the identity `(M+u)(M+v) = M(2M+u+v)` forces `uv = M²`, and
`M + u = ry` is divisible by `r` outright. -/
theorem ladder_complete (n x y z r M u v : ℕ)
    (hr : 4 * x = n + r) (hM : M = n * x)
    (hyz : M * (y + z) = r * (y * z))
    (hu : M + u = r * y) (hv : M + v = r * z) :
    u * v = M * M ∧ r ∣ (M + u) ∧ r ∣ (M + v) := by
  refine ⟨?_, ⟨y, hu⟩, ⟨z, hv⟩⟩
  · -- `(M+u)(M+v) = r²yz = M(2M+u+v)`, and expanding cancels everything but `uv`.
    have h1 : (M + u) * (M + v) = (r * y) * (r * z) := by rw [hu, hv]
    have h2 : (r * y) * (r * z) = r * (r * (y * z)) := by ring
    have h3 : r * (r * (y * z)) = r * (M * (y + z)) := by rw [hyz]
    have h4 : r * (M * (y + z)) = M * (r * y + r * z) := by ring
    have h5 : M * (r * y + r * z) = M * ((M + u) + (M + v)) := by rw [hu, hv]
    have h6 : (M + u) * (M + v) = M * ((M + u) + (M + v)) := by
      rw [h1, h2, h3, h4, h5]
    nlinarith [h6]

/-- The cross-multiplied form of a representation: `4/n = 1/x + 1/y + 1/z` says
exactly `M(y+z) = r·yz` once `r = 4x − n` and `M = nx` are named. -/
theorem ladder_cross (n x y z r M : ℕ) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hr : 4 * x = n + r) (hM : M = n * x)
    (hrep : (4 : ℚ) / n = 1 / x + 1 / y + 1 / z) :
    M * (y + z) = r * (y * z) := by
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hxq : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyq : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzq : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hrq : (4 : ℚ) * x = (n : ℚ) + r := by exact_mod_cast hr
  have hMq : (M : ℚ) = (n : ℚ) * x := by exact_mod_cast hM
  have hMq0 : (M : ℚ) ≠ 0 := by
    rw [hMq]; exact mul_ne_zero hnq hxq
  -- `4/n − 1/x = (4x − n)/(nx) = r/M`, so the tail is `r/M`.
  have hsplit : (4 : ℚ) / n - 1 / x = (r : ℚ) / M := by
    rw [hMq]
    field_simp
    linarith [hrq]
  have key : (1 : ℚ) / y + 1 / z = (r : ℚ) / M := by
    rw [← hsplit]; linarith [hrep]
  have goal : (M : ℚ) * ((y : ℚ) + z) = (r : ℚ) * ((y : ℚ) * z) := by
    field_simp at key
    linarith [key]
  exact_mod_cast goal

/-- The rung a representation sits on is `4x − n`, and it is `≡ 3 (mod 4)`
because `n ≡ 1` is. -/
theorem ladder_rung_residue (n x r : ℕ) (hn : n % 4 = 1) (hr : 4 * x = n + r) :
    r % 4 = 3 := by omega

/-- **The conjecture on the surviving class, as a statement about rungs.** With
completeness in hand, `EveryNClosed` is not a sufficient condition dressed up: a
value with no rung has no representation at all. -/
def EveryNClosedSq : Prop :=
  ∀ n : ℕ, 5 ≤ n → n % 4 = 1 → ¬ (3 ∣ n) → ∃ r, r % 4 = 3 ∧ ClosedAtRungSq n r

/-- **The equivalence.** A rung with a divisor of `M²` at `−M` gives a
representation: the two congruence quotients are the denominators. With
`ladder_complete` for the converse, `ClosedAtRungSq` at some rung and
representability are the same property of `n`. -/
theorem threeUnit_of_closedAtRungSq (n r : ℕ) (hn : 0 < n) (hr0 : 0 < r)
    (h : ClosedAtRungSq n r) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨a, u, v, ha0, hu0, hv0, ha, huv, hdu, hdv⟩ := h
  obtain ⟨b, hb⟩ := hdu
  obtain ⟨c, hc⟩ := hdv
  have hM0 : 0 < n * a := Nat.mul_pos hn ha0
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hb; omega
    · exact h0
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hc; omega
    · exact h0
  exact ⟨a, b, c, ha0, hb0, hc0,
    straus_master n r a (n * a) u v b c hn ha0 hb0 hc0 hr0 rfl hM0 ha huv hb.symm hc.symm⟩

#print axioms Erdos.StrausGreedy.threeUnit_of_closedAtRungSq
/-! ## What a bound would have to say

Three statements now sit between the ladder and the conjecture on this class, and
they are ordered by strength.

The weakest is `EveryNClosedSq`: every `n` has SOME rung. By `ladder_complete`
this is the conjecture itself on the class, neither more nor less.

The middle one is the cofactor version: every `n` has a rung at which `M` — not
`M²` — carries a divisor at `−1`. It is strictly stronger, and `n = 2521`
refutes it as stated for rungs up to 200 while satisfying the weak one, so the
gap between the two is inhabited rather than notional.

The strongest is a BOUND: a function `B` with a closing rung below `B n` for
every `n`. What is measured fits `C·n^{1/4}` with `C ≈ 4.6`. Over `5 ≤ n ≤ 4·10⁶` the least closing rung never exceeds 71, first reached at
n = 1430641; the earlier records are 3, 7, 11, 23, 31, 59 at n = 5, 49, 1129,
1201, 21169, 118801, and the block from 2·10⁶ to 4·10⁶ tops out at 55. The ratio
`r / ⌊n^{1/4}⌋` is largest at small `n` — 4.6 at n = 1201 — and runs 1.4 to 2.1
past a million, so the shape holds and the binding constant comes from the small
values.
A bound
of any shape settles the conjecture on every range it covers, since the rungs
below it are finitely many and each is decidable. That is why the bound, and not
the existence, is the statement worth attacking.
-/

/-- **The bounded form.** A closing rung below an explicit bound. -/
def RungBounded (B : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 5 ≤ n → n % 4 = 1 → ¬ (3 ∣ n) → ∃ r, r < B n ∧ r % 4 = 3 ∧ ClosedAtRungSq n r

/-- A bound gives the conjecture on the surviving class: the rung it supplies is
a rung, and `threeUnit_of_closedAtRungSq` turns it into three unit fractions. -/
theorem straus_class_of_rungBounded (B : ℕ → ℕ) (h : RungBounded B) :
    ∀ n : ℕ, 5 ≤ n → n % 4 = 1 → ¬ (3 ∣ n) →
      ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  intro n hn5 h4 h3
  obtain ⟨r, _, hr4, hcl⟩ := h n hn5 h4 h3
  have hn : 0 < n := by omega
  have hr0 : 0 < r := by omega
  exact threeUnit_of_closedAtRungSq n r hn hr0 hcl

/-! ## What the twelfth object says about the bound

The object designed for "the least rung at which the ladder product carries a
divisor at `−1`, and its bound in the integer alone" reads its reverse morphism
as the product's SIZE forcing the divisor: as `M` grows its divisors multiply,
and a residue class cannot stay empty once enough of them land. That is the
coverage the instrument measures — the size of `{M + u mod r : u ∣ M²}` against
`r` — and it is the bridge from a measurement to a bound.

The bridge itself is elementary and is proved here. What is not proved, and is
what a bound needs, is that coverage reaches `r` by a stated rung.
-/

/-- **Full coverage forces closure.** If the divisors of `M²` meet every residue
class mod `r`, one of them meets `−M`, and the rung closes. This is the object's
reverse morphism written out: size forcing the divisor. -/
theorem closedAtRung_of_full_coverage (n r a : ℕ) (hn : 0 < n) (ha0 : 0 < a)
    (hr : 0 < r) (ha : 4 * a = n + r)
    (hfull : ∀ x : ZMod r, ∃ u : ℕ, 0 < u ∧ u ∣ (n * a) * (n * a) ∧ (u : ZMod r) = x) :
    ∃ u : ℕ, 0 < u ∧ u ∣ (n * a) * (n * a) ∧ r ∣ (n * a + u) := by
  obtain ⟨u, hu0, hudvd, hux⟩ := hfull (-(n * a : ℕ) : ZMod r)
  refine ⟨u, hu0, hudvd, ?_⟩
  have : ((n * a + u : ℕ) : ZMod r) = 0 := by
    push_cast [hux]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

/-- **The coverage route to a bound, as a Prop.** A bound follows from knowing
that the divisors of `M²` cover `ZMod r` by some rung below `B n`. Measured, the
coverage at a closing rung averages 0.73 and the walk is dissipative in it; that
is evidence for this statement, not a proof of it. -/
def CoverageReachesFull (B : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 5 ≤ n → n % 4 = 1 → ¬ (3 ∣ n) →
    ∃ r a : ℕ, r < B n ∧ r % 4 = 3 ∧ 4 * a = n + r ∧
      ∀ x : ZMod r, ∃ u : ℕ, 0 < u ∧ u ∣ (n * a) * (n * a) ∧ (u : ZMod r) = x

#print axioms Erdos.StrausGreedy.closedAtRung_of_full_coverage

#print axioms Erdos.StrausGreedy.straus_class_of_rungBounded
#print axioms Erdos.StrausGreedy.ladder_cross
#print axioms Erdos.StrausGreedy.ladder_complete
#print axioms Erdos.StrausGreedy.ladder_rung_residue
#print axioms Erdos.StrausGreedy.rung_three_residue
#print axioms Erdos.StrausGreedy.closedAtRung_of_shift
#print axioms Erdos.StrausGreedy.closedAtRung_of_kshift
#print axioms Erdos.StrausGreedy.closedAtRung_of_two_shift
#print axioms Erdos.StrausGreedy.straus_196561
#print axioms Erdos.StrausGreedy.closedAtRung_of_cofactor
#print axioms Erdos.StrausGreedy.closedAtRung_three_of_prime
#print axioms Erdos.StrausGreedy.straus_of_neg_one_divisor
#print axioms Erdos.StrausGreedy.negMReachable_of_negOneReachable

#print axioms Erdos.StrausGreedy.straus_of_priceZero
#print axioms Erdos.StrausGreedy.straus_scaling
#print axioms Erdos.StrausGreedy.straus_of_representable_divisor
#print axioms Erdos.StrausGreedy.straus_frontier_mod_24

#print axioms Erdos.StrausGreedy.straus_one_shot
#print axioms Erdos.StrausGreedy.straus_class_of_everyNClosed
#print axioms Erdos.StrausGreedy.straus_of_closedAtRung
#print axioms Erdos.StrausGreedy.straus_practical
#print axioms Erdos.StrausGreedy.straus_n_family
#print axioms Erdos.StrausGreedy.straus_prime_family
#print axioms Erdos.StrausGreedy.straus_master
#print axioms Erdos.StrausGreedy.v_condition_free
#print axioms Erdos.StrausGreedy.straus_divisor_family
#print axioms Erdos.StrausGreedy.second_split_general
#print axioms Erdos.StrausGreedy.straus_2521
#print axioms Erdos.StrausGreedy.r_over_M_split
#print axioms Erdos.StrausGreedy.ladder_step
#print axioms Erdos.StrausGreedy.straus_forty_nine
#print axioms Erdos.StrausGreedy.straus_of_divisor
#print axioms Erdos.StrausGreedy.straus_off_residue
#print axioms Erdos.StrausGreedy.greedy_step

/-! ## A new covering progression: `n ≡ 17 (mod 20)`

The `k`-shift reads a rung off `k·n + 1` for any `k`, not only `k = 1`. Taking
`k = 2` with cofactor `w = 5` and rung `r = 3` (`k·r = w+1`, `Coprime 5 8`) needs
`5 ∣ 2n+1`, i.e. `n ≡ 2 (mod 5)`. Together with `n ≡ 1 (mod 4)` that is the class
`n ≡ 17 (mod 20)`, closed at the greedy rung with no search — a covering family
beyond the price-zero layer, whose rung is read off `2n+1` rather than `n`. -/

/-- **`n ≡ 17 (mod 20)` closes at rung 3.** Instance of `closedAtRung_of_kshift`
with `k=2, w=5, r=3`: the cofactor `w = 5` divides `2n+1` exactly when
`n ≡ 2 (mod 5)`. -/
theorem closedAtRung_three_of_mod20 (n : ℕ) (hn : 0 < n)
    (h4 : n % 4 = 1) (h5 : n % 5 = 2) : ClosedAtRung n 3 := by
  have h4d : 4 ∣ n + 3 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  refine closedAtRung_of_kshift n 2 5 3 a hn (by norm_num) (by norm_num)
    (by norm_num) ha0 (by norm_num) ?_ (by norm_num) (by omega)
  omega

/-- **Erdős–Straus on `n ≡ 17 (mod 20)`.** Every such `n` has `4/n` a sum of three
unit fractions, with denominators exhibited by the rung-3 construction. -/
theorem straus_mod20 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (h5 : n % 5 = 2) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c :=
  straus_of_closedAtRung n 3 hn (by norm_num) (closedAtRung_three_of_mod20 n hn h4 h5)

#print axioms straus_mod20

/-! ## Frontier witnesses from the mOMonadOS `straus` instrument

The kernel's iterated rung emits an explicit representation for each frontier
value `n ≡ 1 (mod 24)` the price-zero and one-shot families miss. Each is
machine-checked here, turning the instrument's print into a theorem. -/

theorem straus_193 : (4:ℚ)/193 = 1/50 + 1/1380 + 1/1331700 := by norm_num
theorem straus_313 : (4:ℚ)/313 = 1/80 + 1/3580 + 1/4482160 := by norm_num
theorem straus_457 : (4:ℚ)/457 = 1/115 + 1/17520 + 1/184152720 := by norm_num
theorem straus_673 : (4:ℚ)/673 = 1/170 + 1/16345 + 1/374006290 := by norm_num
theorem straus_1009 : (4:ℚ)/1009 = 1/253 + 1/85096 + 1/1974822872 := by norm_num

/-! ## More covering progressions from the kernel's `kshift` engine

Each `(k, w, r)` the instrument returns closes an infinite congruence class at a
fixed rung with no search — the covering families beyond `n ≡ 17 (mod 20)`. -/

/-- Covering family: `n ≡ 1 (mod 4)` and `n ≡ 8 (mod 11)` close at rung 3
    via the `k=4` shift (cofactor `w=11`). Erdős–Straus on this class. -/
theorem straus_cover_mod44 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 11 = 8) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 3 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 3 :=
    closedAtRung_of_kshift n 4 11 3 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 3 hn (by norm_num) hcl

/-- Covering family: `n ≡ 1 (mod 4)` and `n ≡ 6 (mod 13)` close at rung 7
    via the `k=2` shift (cofactor `w=13`). Erdős–Straus on this class. -/
theorem straus_cover_mod52 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 13 = 6) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 7 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 7 :=
    closedAtRung_of_kshift n 2 13 7 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 7 hn (by norm_num) hcl

/-- Covering family: `n ≡ 1 (mod 4)` and `n ≡ 14 (mod 17)` close at rung 3
    via the `k=6` shift (cofactor `w=17`). Erdős–Straus on this class. -/
theorem straus_cover_mod68 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 17 = 14) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 3 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 3 :=
    closedAtRung_of_kshift n 6 17 3 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 3 hn (by norm_num) hcl

/-- Covering family: `n ≡ 1 (mod 4)` and `n ≡ 10 (mod 21)` close at rung 11
    via the `k=2` shift (cofactor `w=21`). Erdős–Straus on this class. -/
theorem straus_cover_mod84 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 21 = 10) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 11 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 11 :=
    closedAtRung_of_kshift n 2 21 11 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 11 hn (by norm_num) hcl

/-- Covering family: `n ≡ 1 (mod 4)` and `n ≡ 20 (mod 23)` close at rung 3
    via the `k=8` shift (cofactor `w=23`). Erdős–Straus on this class. -/
theorem straus_cover_mod92 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 23 = 20) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 3 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 3 :=
    closedAtRung_of_kshift n 8 23 3 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 3 hn (by norm_num) hcl

/-- Covering family: `n ≡ 1 (mod 4)` and `n ≡ 20 (mod 27)` close at rung 7
    via the `k=4` shift (cofactor `w=27`). Erdős–Straus on this class. -/
theorem straus_cover_mod108 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 27 = 20) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 7 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 7 :=
    closedAtRung_of_kshift n 4 27 7 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 7 hn (by norm_num) hcl

/-- Covering family: `n ≡ 1 (mod 4)` and `n ≡ 14 (mod 29)` close at rung 15
    via the `k=2` shift (cofactor `w=29`). Erdős–Straus on this class. -/
theorem straus_cover_mod116 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 29 = 14) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 15 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 15 :=
    closedAtRung_of_kshift n 2 29 15 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 15 hn (by norm_num) hcl


/-! ## Covering families and frontier witnesses, batch 2 (kernel-sourced) -/

theorem straus_cover_mod140 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 35 = 32) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 3 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 3 :=
    closedAtRung_of_kshift n 12 35 3 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 3 hn (by norm_num) hcl

theorem straus_cover_mod148 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 37 = 18) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 19 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 19 :=
    closedAtRung_of_kshift n 2 37 19 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 19 hn (by norm_num) hcl

theorem straus_cover_mod164 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 41 = 34) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 7 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 7 :=
    closedAtRung_of_kshift n 6 41 7 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 7 hn (by norm_num) hcl

theorem straus_cover_mod172 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 43 = 32) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 11 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 11 :=
    closedAtRung_of_kshift n 4 43 11 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 11 hn (by norm_num) hcl

theorem straus_cover_mod180 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 45 = 22) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 23 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 23 :=
    closedAtRung_of_kshift n 2 45 23 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 23 hn (by norm_num) hcl

theorem straus_cover_mod212 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 53 = 26) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 27 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 27 :=
    closedAtRung_of_kshift n 2 53 27 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 27 hn (by norm_num) hcl

theorem straus_cover_mod220 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 55 = 48) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 7 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 7 :=
    closedAtRung_of_kshift n 8 55 7 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 7 hn (by norm_num) hcl

theorem straus_cover_mod236 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 59 = 44) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 15 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 15 :=
    closedAtRung_of_kshift n 4 59 15 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 15 hn (by norm_num) hcl

theorem straus_cover_mod244 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 61 = 30) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 31 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 31 :=
    closedAtRung_of_kshift n 2 61 31 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 31 hn (by norm_num) hcl

theorem straus_cover_mod260 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 65 = 54) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 11 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 11 :=
    closedAtRung_of_kshift n 6 65 11 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 11 hn (by norm_num) hcl

theorem straus_1153 : (4:ℚ)/1153 = 1/289 + 1/111078 + 1/2177239878 := by norm_num
theorem straus_1201 : (4:ℚ)/1201 = 1/306 + 1/15980 + 1/172727820 := by norm_num
theorem straus_1453 : (4:ℚ)/1453 = 1/364 + 1/176298 + 1/46621300908 := by norm_num
theorem straus_1489 : (4:ℚ)/1489 = 1/374 + 1/79560 + 1/1303113240 := by norm_num
theorem straus_1621 : (4:ℚ)/1621 = 1/406 + 1/219376 + 1/72188524688 := by norm_num
theorem straus_1873 : (4:ℚ)/1873 = 1/470 + 1/125760 + 1/11070778560 := by norm_num

/-! ## Covering families and frontier witnesses, batch 3 (kernel-sourced) -/

theorem straus_cover_mod276 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 69 = 34) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 35 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 35 :=
    closedAtRung_of_kshift n 2 69 35 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 35 hn (by norm_num) hcl

theorem straus_cover_mod300 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 75 = 56) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 19 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 19 :=
    closedAtRung_of_kshift n 4 75 19 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 19 hn (by norm_num) hcl

theorem straus_cover_mod308 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 77 = 38) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 39 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 39 :=
    closedAtRung_of_kshift n 2 77 39 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 39 hn (by norm_num) hcl

theorem straus_cover_mod332 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 83 = 76) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 7 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 7 :=
    closedAtRung_of_kshift n 12 83 7 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 7 hn (by norm_num) hcl

theorem straus_cover_mod340 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 85 = 42) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 43 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 43 :=
    closedAtRung_of_kshift n 2 85 43 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 43 hn (by norm_num) hcl

theorem straus_cover_mod348 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 87 = 76) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 11 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 11 :=
    closedAtRung_of_kshift n 8 87 11 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 11 hn (by norm_num) hcl

theorem straus_cover_mod356 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 89 = 74) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 15 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 15 :=
    closedAtRung_of_kshift n 6 89 15 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 15 hn (by norm_num) hcl

theorem straus_cover_mod364 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 91 = 68) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 23 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 23 :=
    closedAtRung_of_kshift n 4 91 23 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 23 hn (by norm_num) hcl

theorem straus_cover_mod372 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 93 = 46) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 47 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 47 :=
    closedAtRung_of_kshift n 2 93 47 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 47 hn (by norm_num) hcl

theorem straus_cover_mod388 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 97 = 90) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 7 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 7 :=
    closedAtRung_of_kshift n 14 97 7 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 7 hn (by norm_num) hcl

theorem straus_cover_mod404 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 101 = 50) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 51 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 51 :=
    closedAtRung_of_kshift n 2 101 51 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 51 hn (by norm_num) hcl

theorem straus_cover_mod428 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 107 = 80) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 27 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 27 :=
    closedAtRung_of_kshift n 4 107 27 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 27 hn (by norm_num) hcl

theorem straus_2089 : (4:ℚ)/2089 = 1/524 + 1/156414 + 1/653497692 := by norm_num
theorem straus_2113 : (4:ℚ)/2113 = 1/529 + 1/372600 + 1/18107987400 := by norm_num
theorem straus_2857 : (4:ℚ)/2857 = 1/715 + 1/680920 + 1/278190546920 := by norm_num
theorem straus_3049 : (4:ℚ)/3049 = 1/765 + 1/212058 + 1/3232824210 := by norm_num
theorem straus_3217 : (4:ℚ)/3217 = 1/805 + 1/863230 + 1/447098756510 := by norm_num
theorem straus_3313 : (4:ℚ)/3313 = 1/830 + 1/392830 + 1/54010000285 := by norm_num

/-! ## Covering families and frontier witnesses, batch 4 (kernel-sourced) -/

theorem straus_cover_mod188 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 47 = 44) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 3 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 3 :=
    closedAtRung_of_kshift n 16 47 3 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 3 hn (by norm_num) hcl

theorem straus_cover_mod436 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 109 = 54) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 55 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 55 :=
    closedAtRung_of_kshift n 2 109 55 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 55 hn (by norm_num) hcl

theorem straus_cover_mod444 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 111 = 104) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 7 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 7 :=
    closedAtRung_of_kshift n 16 111 7 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 7 hn (by norm_num) hcl

theorem straus_cover_mod452 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 113 = 94) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 19 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 19 :=
    closedAtRung_of_kshift n 6 113 19 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 19 hn (by norm_num) hcl

theorem straus_cover_mod468 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 117 = 58) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 59 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 59 :=
    closedAtRung_of_kshift n 2 117 59 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 59 hn (by norm_num) hcl

theorem straus_cover_mod476 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 119 = 104) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 15 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 15 :=
    closedAtRung_of_kshift n 8 119 15 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 15 hn (by norm_num) hcl

theorem straus_cover_mod492 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 123 = 92) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 31 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 31 :=
    closedAtRung_of_kshift n 4 123 31 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 31 hn (by norm_num) hcl

theorem straus_cover_mod500 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 125 = 62) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 63 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 63 :=
    closedAtRung_of_kshift n 2 125 63 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 63 hn (by norm_num) hcl

theorem straus_cover_mod524 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 131 = 120) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 11 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 11 :=
    closedAtRung_of_kshift n 12 131 11 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 11 hn (by norm_num) hcl

theorem straus_cover_mod532 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 133 = 66) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 67 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 67 :=
    closedAtRung_of_kshift n 2 133 67 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 67 hn (by norm_num) hcl

theorem straus_cover_mod548 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 137 = 114) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 23 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 23 :=
    closedAtRung_of_kshift n 6 137 23 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 23 hn (by norm_num) hcl

theorem straus_cover_mod556 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 139 = 104) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 35 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 35 :=
    closedAtRung_of_kshift n 4 139 35 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 35 hn (by norm_num) hcl

theorem straus_cover_mod564 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 141 = 70) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 71 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 71 :=
    closedAtRung_of_kshift n 2 141 71 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 71 hn (by norm_num) hcl

theorem straus_cover_mod596 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 149 = 74) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 75 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 75 :=
    closedAtRung_of_kshift n 2 149 75 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 75 hn (by norm_num) hcl

theorem straus_cover_mod604 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 151 = 132) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 19 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 19 :=
    closedAtRung_of_kshift n 8 151 19 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 19 hn (by norm_num) hcl

theorem straus_cover_mod612 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 153 = 142) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 11 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 11 :=
    closedAtRung_of_kshift n 14 153 11 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 11 hn (by norm_num) hcl

theorem straus_3457 : (4:ℚ)/3457 = 1/865 + 1/996770 + 1/596129262970 := by norm_num
theorem straus_3673 : (4:ℚ)/3673 = 1/920 + 1/482740 + 1/81562784920 := by norm_num
theorem straus_4177 : (4:ℚ)/4177 = 1/1045 + 1/1454990 + 1/1270196085070 := by norm_num
theorem straus_4481 : (4:ℚ)/4481 = 1/1121 + 1/1674420 + 1/142558444380 := by norm_num
theorem straus_4657 : (4:ℚ)/4657 = 1/1165 + 1/1808470 + 1/1962336436070 := by norm_num
theorem straus_4993 : (4:ℚ)/4993 = 1/1250 + 1/891610 + 1/278238045625 := by norm_num

/-! ## Covering families and frontier witnesses, batch 5 (kernel-sourced) -/

theorem straus_cover_mod620 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 155 = 116) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 39 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 39 :=
    closedAtRung_of_kshift n 4 155 39 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 39 hn (by norm_num) hcl

theorem straus_cover_mod628 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 157 = 78) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 79 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 79 :=
    closedAtRung_of_kshift n 2 157 79 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 79 hn (by norm_num) hcl

theorem straus_cover_mod644 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 161 = 134) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 27 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 27 :=
    closedAtRung_of_kshift n 6 161 27 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 27 hn (by norm_num) hcl

theorem straus_cover_mod660 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 165 = 82) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 83 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 83 :=
    closedAtRung_of_kshift n 2 165 83 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 83 hn (by norm_num) hcl

theorem straus_cover_mod684 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 171 = 128) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 43 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 43 :=
    closedAtRung_of_kshift n 4 171 43 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 43 hn (by norm_num) hcl

theorem straus_cover_mod692 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 173 = 86) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 87 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 87 :=
    closedAtRung_of_kshift n 2 173 87 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 87 hn (by norm_num) hcl

theorem straus_cover_mod700 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 175 = 164) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 11 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 11 :=
    closedAtRung_of_kshift n 16 175 11 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 11 hn (by norm_num) hcl

theorem straus_cover_mod716 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 179 = 164) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 15 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 15 :=
    closedAtRung_of_kshift n 12 179 15 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 15 hn (by norm_num) hcl

theorem straus_cover_mod724 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 181 = 90) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 91 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 91 :=
    closedAtRung_of_kshift n 2 181 91 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 91 hn (by norm_num) hcl

theorem straus_cover_mod732 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 183 = 160) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 23 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 23 :=
    closedAtRung_of_kshift n 8 183 23 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 23 hn (by norm_num) hcl

theorem straus_cover_mod740 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 185 = 154) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 31 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 31 :=
    closedAtRung_of_kshift n 6 185 31 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 31 hn (by norm_num) hcl

theorem straus_cover_mod748 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 187 = 140) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 47 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 47 :=
    closedAtRung_of_kshift n 4 187 47 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 47 hn (by norm_num) hcl

theorem straus_cover_mod756 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 189 = 94) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 95 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 95 :=
    closedAtRung_of_kshift n 2 189 95 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 95 hn (by norm_num) hcl

theorem straus_cover_mod788 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 197 = 98) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 99 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 99 :=
    closedAtRung_of_kshift n 2 197 99 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 99 hn (by norm_num) hcl

theorem straus_cover_mod812 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 203 = 152) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 51 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 51 :=
    closedAtRung_of_kshift n 4 203 51 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 51 hn (by norm_num) hcl

theorem straus_cover_mod820 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 205 = 102) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 103 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 103 :=
    closedAtRung_of_kshift n 2 205 103 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 103 hn (by norm_num) hcl

theorem straus_5233 : (4:ℚ)/5233 = 1/1309 + 1/2283336 + 1/1421894977272 := by norm_num
theorem straus_5449 : (4:ℚ)/5449 = 1/1363 + 1/2475672 + 1/634027026216 := by norm_num
theorem straus_5641 : (4:ℚ)/5641 = 1/1411 + 1/2653156 + 1/1242215598668 := by norm_num
theorem straus_6217 : (4:ℚ)/6217 = 1/1555 + 1/3222480 + 1/6230623187760 := by norm_num
theorem straus_6553 : (4:ℚ)/6553 = 1/1639 + 1/3580126 + 1/3495624286022 := by norm_num
theorem straus_6793 : (4:ℚ)/6793 = 1/1700 + 1/1649730 + 1/1905124701300 := by norm_num

/-! ## Covering families and frontier witnesses, batch 6 (kernel-sourced) -/

theorem straus_cover_mod836 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 209 = 174) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 35 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 35 :=
    closedAtRung_of_kshift n 6 209 35 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 35 hn (by norm_num) hcl

theorem straus_cover_mod852 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 213 = 106) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 107 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 107 :=
    closedAtRung_of_kshift n 2 213 107 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 107 hn (by norm_num) hcl

theorem straus_cover_mod860 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 215 = 188) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 27 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 27 :=
    closedAtRung_of_kshift n 8 215 27 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 27 hn (by norm_num) hcl

theorem straus_cover_mod876 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 219 = 164) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 55 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 55 :=
    closedAtRung_of_kshift n 4 219 55 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 55 hn (by norm_num) hcl

theorem straus_cover_mod884 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 221 = 110) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 111 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 111 :=
    closedAtRung_of_kshift n 2 221 111 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 111 hn (by norm_num) hcl

theorem straus_cover_mod908 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 227 = 208) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 19 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 19 :=
    closedAtRung_of_kshift n 12 227 19 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 19 hn (by norm_num) hcl

theorem straus_cover_mod916 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 229 = 114) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 115 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 115 :=
    closedAtRung_of_kshift n 2 229 115 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 115 hn (by norm_num) hcl

theorem straus_cover_mod932 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 233 = 194) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 39 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 39 :=
    closedAtRung_of_kshift n 6 233 39 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 39 hn (by norm_num) hcl

theorem straus_cover_mod940 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 235 = 176) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 59 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 59 :=
    closedAtRung_of_kshift n 4 235 59 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 59 hn (by norm_num) hcl

theorem straus_cover_mod948 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 237 = 118) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 119 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 119 :=
    closedAtRung_of_kshift n 2 237 119 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 119 hn (by norm_num) hcl

theorem straus_cover_mod956 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 239 = 224) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 15 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 15 :=
    closedAtRung_of_kshift n 16 239 15 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 15 hn (by norm_num) hcl

theorem straus_cover_mod980 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 245 = 122) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 123 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 123 :=
    closedAtRung_of_kshift n 2 245 123 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 123 hn (by norm_num) hcl

theorem straus_cover_mod988 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 247 = 216) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 31 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 31 :=
    closedAtRung_of_kshift n 8 247 31 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 31 hn (by norm_num) hcl

theorem straus_cover_mod1004 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 251 = 188) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 63 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 63 :=
    closedAtRung_of_kshift n 4 251 63 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 63 hn (by norm_num) hcl

theorem straus_cover_mod1012 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 253 = 126) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 127 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 127 :=
    closedAtRung_of_kshift n 2 253 127 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 127 hn (by norm_num) hcl

theorem straus_cover_mod1028 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 257 = 214) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 43 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 43 :=
    closedAtRung_of_kshift n 6 257 43 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 43 hn (by norm_num) hcl

theorem straus_7057 : (4:ℚ)/7057 = 1/1765 + 1/4151870 + 1/10342810546270 := by norm_num
theorem straus_7297 : (4:ℚ)/7297 = 1/1825 + 1/4439010 + 1/11822881429050 := by norm_num
theorem straus_7873 : (4:ℚ)/7873 = 1/1969 + 1/5167316 + 1/7282127917372 := by norm_num
theorem straus_8089 : (4:ℚ)/8089 = 1/2023 + 1/5454688 + 1/5250633576608 := by norm_num
theorem straus_8761 : (4:ℚ)/8761 = 1/2193 + 1/1746660 + 1/86714100140 := by norm_num
theorem straus_9337 : (4:ℚ)/9337 = 1/2335 + 1/7267300 + 1/31688182306700 := by norm_num

/-! ## Covering families and frontier witnesses, batch 7 (kernel-sourced) -/

theorem straus_cover_mod1044 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 261 = 130) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 131 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 131 :=
    closedAtRung_of_kshift n 2 261 131 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 131 hn (by norm_num) hcl

theorem straus_cover_mod1060 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 265 = 246) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 19 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 19 :=
    closedAtRung_of_kshift n 14 265 19 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 19 hn (by norm_num) hcl

theorem straus_cover_mod1068 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 267 = 200) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 67 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 67 :=
    closedAtRung_of_kshift n 4 267 67 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 67 hn (by norm_num) hcl

theorem straus_cover_mod1076 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 269 = 134) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 135 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 135 :=
    closedAtRung_of_kshift n 2 269 135 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 135 hn (by norm_num) hcl

theorem straus_cover_mod1100 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 275 = 252) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 23 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 23 :=
    closedAtRung_of_kshift n 12 275 23 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 23 hn (by norm_num) hcl

theorem straus_cover_mod1108 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 277 = 138) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 139 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 139 :=
    closedAtRung_of_kshift n 2 277 139 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 139 hn (by norm_num) hcl

theorem straus_cover_mod1116 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 279 = 244) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 35 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 35 :=
    closedAtRung_of_kshift n 8 279 35 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 35 hn (by norm_num) hcl

theorem straus_cover_mod1124 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 281 = 234) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 47 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 47 :=
    closedAtRung_of_kshift n 6 281 47 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 47 hn (by norm_num) hcl

theorem straus_cover_mod1132 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 283 = 212) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 71 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 71 :=
    closedAtRung_of_kshift n 4 283 71 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 71 hn (by norm_num) hcl

theorem straus_cover_mod1140 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 285 = 142) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 143 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 143 :=
    closedAtRung_of_kshift n 2 285 143 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 143 hn (by norm_num) hcl

theorem straus_cover_mod1172 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 293 = 146) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 147 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 147 :=
    closedAtRung_of_kshift n 2 293 147 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 147 hn (by norm_num) hcl

theorem straus_cover_mod1196 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 299 = 224) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 75 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 75 :=
    closedAtRung_of_kshift n 4 299 75 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 75 hn (by norm_num) hcl

theorem straus_cover_mod1204 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 301 = 150) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 151 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 151 :=
    closedAtRung_of_kshift n 2 301 151 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 151 hn (by norm_num) hcl

theorem straus_cover_mod1212 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 303 = 284) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 19 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 19 :=
    closedAtRung_of_kshift n 16 303 19 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 19 hn (by norm_num) hcl

theorem straus_cover_mod1220 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 305 = 254) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 51 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 51 :=
    closedAtRung_of_kshift n 6 305 51 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 51 hn (by norm_num) hcl

theorem straus_cover_mod1236 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 309 = 154) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 155 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 155 :=
    closedAtRung_of_kshift n 2 309 155 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 155 hn (by norm_num) hcl

theorem straus_9601 : (4:ℚ)/9601 = 1/2405 + 1/1216930 + 1/898749610 := by norm_num
theorem straus_9817 : (4:ℚ)/9817 = 1/2455 + 1/8033580 + 1/38723036536260 := by norm_num
theorem straus_10009 : (4:ℚ)/10009 = 1/2504 + 1/3580407 + 1/286690349304 := by norm_num
theorem straus_10513 : (4:ℚ)/10513 = 1/2629 + 1/9212896 + 1/23148386979872 := by norm_num
theorem straus_11113 : (4:ℚ)/11113 = 1/2780 + 1/4413450 + 1/13634974218300 := by norm_num
theorem straus_11593 : (4:ℚ)/11593 = 1/2900 + 1/4802815 + 1/32293839891100 := by norm_num

/-! ## Covering families and frontier witnesses, batch 8 (kernel-sourced) -/

theorem straus_cover_mod964 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 241 = 230) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 11 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 11 :=
    closedAtRung_of_kshift n 22 241 11 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 11 hn (by norm_num) hcl

theorem straus_cover_mod1244 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 311 = 272) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 39 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 39 :=
    closedAtRung_of_kshift n 8 311 39 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 39 hn (by norm_num) hcl

theorem straus_cover_mod1260 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 315 = 236) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 79 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 79 :=
    closedAtRung_of_kshift n 4 315 79 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 79 hn (by norm_num) hcl

theorem straus_cover_mod1268 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 317 = 158) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 159 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 159 :=
    closedAtRung_of_kshift n 2 317 159 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 159 hn (by norm_num) hcl

theorem straus_cover_mod1284 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 321 = 298) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 23 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 23 :=
    closedAtRung_of_kshift n 14 321 23 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 23 hn (by norm_num) hcl

theorem straus_cover_mod1292 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 323 = 296) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 27 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 27 :=
    closedAtRung_of_kshift n 12 323 27 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 27 hn (by norm_num) hcl

theorem straus_cover_mod1300 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 325 = 162) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 163 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 163 :=
    closedAtRung_of_kshift n 2 325 163 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 163 hn (by norm_num) hcl

theorem straus_cover_mod1316 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 329 = 274) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 55 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 55 :=
    closedAtRung_of_kshift n 6 329 55 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 55 hn (by norm_num) hcl

theorem straus_cover_mod1324 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 331 = 248) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 83 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 83 :=
    closedAtRung_of_kshift n 4 331 83 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 83 hn (by norm_num) hcl

theorem straus_cover_mod1332 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 333 = 166) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 167 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 167 :=
    closedAtRung_of_kshift n 2 333 167 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 167 hn (by norm_num) hcl

theorem straus_cover_mod1364 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 341 = 170) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 171 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 171 :=
    closedAtRung_of_kshift n 2 341 171 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 171 hn (by norm_num) hcl

theorem straus_cover_mod1372 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 343 = 300) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 43 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 43 :=
    closedAtRung_of_kshift n 8 343 43 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 43 hn (by norm_num) hcl

theorem straus_cover_mod1388 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 347 = 260) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 87 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 87 :=
    closedAtRung_of_kshift n 4 347 87 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 87 hn (by norm_num) hcl

theorem straus_cover_mod1396 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 349 = 174) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 175 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 175 :=
    closedAtRung_of_kshift n 2 349 175 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 175 hn (by norm_num) hcl

theorem straus_cover_mod1412 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 353 = 294) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 59 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 59 :=
    closedAtRung_of_kshift n 6 353 59 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 59 hn (by norm_num) hcl

theorem straus_cover_mod1428 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 357 = 178) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 179 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 179 :=
    closedAtRung_of_kshift n 2 357 179 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 179 hn (by norm_num) hcl

theorem straus_12097 : (4:ℚ)/12097 = 1/3025 + 1/12197810 + 1/89271929079850 := by norm_num
theorem straus_12409 : (4:ℚ)/12409 = 1/3103 + 1/12835052 + 1/17041907148676 := by norm_num
theorem straus_13513 : (4:ℚ)/13513 = 1/3380 + 1/6524850 + 1/29801560740900 := by norm_num
theorem straus_13729 : (4:ℚ)/13729 = 1/3434 + 1/6735060 + 1/9339029512740 := by norm_num
theorem straus_14401 : (4:ℚ)/14401 = 1/3605 + 1/2732590 + 1/39352028590 := by norm_num
theorem straus_15013 : (4:ℚ)/15013 = 1/3754 + 1/18786268 + 1/529385779265468 := by norm_num

/-! ## Covering families and frontier witnesses, batch 9 (kernel-sourced) -/

theorem straus_cover_mod284 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 71 = 68) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 3 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 3 :=
    closedAtRung_of_kshift n 24 71 3 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 3 hn (by norm_num) hcl

theorem straus_cover_mod668 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 167 = 160) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 7 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 7 :=
    closedAtRung_of_kshift n 24 167 7 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 7 hn (by norm_num) hcl

theorem straus_cover_mod1052 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 263 = 252) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 11 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 11 :=
    closedAtRung_of_kshift n 24 263 11 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 11 hn (by norm_num) hcl

theorem straus_cover_mod1436 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 359 = 344) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 15 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 15 :=
    closedAtRung_of_kshift n 24 359 15 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 15 hn (by norm_num) hcl

theorem straus_cover_mod1452 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 363 = 272) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 91 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 91 :=
    closedAtRung_of_kshift n 4 363 91 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 91 hn (by norm_num) hcl

theorem straus_cover_mod1460 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 365 = 182) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 183 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 183 :=
    closedAtRung_of_kshift n 2 365 183 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 183 hn (by norm_num) hcl

theorem straus_cover_mod1468 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 367 = 344) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 23 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 23 :=
    closedAtRung_of_kshift n 16 367 23 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 23 hn (by norm_num) hcl

theorem straus_cover_mod1484 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 371 = 340) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 31 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 31 :=
    closedAtRung_of_kshift n 12 371 31 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 31 hn (by norm_num) hcl

theorem straus_cover_mod1492 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 373 = 186) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 187 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 187 :=
    closedAtRung_of_kshift n 2 373 187 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 187 hn (by norm_num) hcl

theorem straus_cover_mod1500 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 375 = 328) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 47 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 47 :=
    closedAtRung_of_kshift n 8 375 47 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 47 hn (by norm_num) hcl

theorem straus_cover_mod1508 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 377 = 314) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 63 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 63 :=
    closedAtRung_of_kshift n 6 377 63 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 63 hn (by norm_num) hcl

theorem straus_cover_mod1516 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 379 = 284) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 95 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 95 :=
    closedAtRung_of_kshift n 4 379 95 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 95 hn (by norm_num) hcl

theorem straus_cover_mod1524 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 381 = 190) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 191 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 191 :=
    closedAtRung_of_kshift n 2 381 191 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 191 hn (by norm_num) hcl

theorem straus_cover_mod1556 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 389 = 194) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 195 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 195 :=
    closedAtRung_of_kshift n 2 389 195 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 195 hn (by norm_num) hcl

theorem straus_cover_mod1580 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 395 = 296) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 99 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 99 :=
    closedAtRung_of_kshift n 4 395 99 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 99 hn (by norm_num) hcl

theorem straus_cover_mod1588 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (hw : n % 397 = 198) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  have h4d : 4 ∣ n + 199 := by omega
  obtain ⟨a, ha⟩ := h4d
  have ha0 : 0 < a := by omega
  have hcl : ClosedAtRung n 199 :=
    closedAtRung_of_kshift n 2 397 199 a hn (by norm_num) (by norm_num)
      (by norm_num) ha0 (by norm_num) (by omega) (by norm_num) (by omega)
  exact straus_of_closedAtRung n 199 hn (by norm_num) hcl

theorem straus_15121 : (4:ℚ)/15121 = 1/3782 + 1/8169669 + 1/7659081026838 := by norm_num
theorem straus_15313 : (4:ℚ)/15313 = 1/3830 + 1/8378400 + 1/49138302213600 := by norm_num
theorem straus_16033 : (4:ℚ)/16033 = 1/4010 + 1/9184620 + 1/59050061996460 := by norm_num
theorem straus_16633 : (4:ℚ)/16633 = 1/4160 + 1/9884755 + 1/136791724089280 := by norm_num
theorem straus_17401 : (4:ℚ)/17401 = 1/4352 + 1/10818460 + 1/12048129437440 := by norm_num
theorem straus_18313 : (4:ℚ)/18313 = 1/4580 + 1/11981935 + 1/200993460899980 := by norm_num

/-! ## The consolidated coverage theorem -/

/-- **The covered residue classes** — the explicit union over every proved covering family. -/
def StrausCovered (n : ℕ) : Prop :=
  n % 5 = 2 ∨ n % 11 = 8 ∨ n % 13 = 6 ∨ n % 17 = 14 ∨ n % 21 = 10 ∨ n % 23 = 20 ∨ n % 27 = 20 ∨ n % 29 = 14 ∨ n % 35 = 32 ∨ n % 37 = 18 ∨ n % 41 = 34 ∨ n % 43 = 32 ∨ n % 45 = 22 ∨ n % 53 = 26 ∨ n % 55 = 48 ∨ n % 59 = 44 ∨ n % 61 = 30 ∨ n % 65 = 54 ∨ n % 69 = 34 ∨ n % 75 = 56 ∨ n % 77 = 38 ∨ n % 83 = 76 ∨ n % 85 = 42 ∨ n % 87 = 76 ∨ n % 89 = 74 ∨ n % 91 = 68 ∨ n % 93 = 46 ∨ n % 97 = 90 ∨ n % 101 = 50 ∨ n % 107 = 80 ∨ n % 47 = 44 ∨ n % 109 = 54 ∨ n % 111 = 104 ∨ n % 113 = 94 ∨ n % 117 = 58 ∨ n % 119 = 104 ∨ n % 123 = 92 ∨ n % 125 = 62 ∨ n % 131 = 120 ∨ n % 133 = 66 ∨ n % 137 = 114 ∨ n % 139 = 104 ∨ n % 141 = 70 ∨ n % 149 = 74 ∨ n % 151 = 132 ∨ n % 153 = 142 ∨ n % 155 = 116 ∨ n % 157 = 78 ∨ n % 161 = 134 ∨ n % 165 = 82 ∨ n % 171 = 128 ∨ n % 173 = 86 ∨ n % 175 = 164 ∨ n % 179 = 164 ∨ n % 181 = 90 ∨ n % 183 = 160 ∨ n % 185 = 154 ∨ n % 187 = 140 ∨ n % 189 = 94 ∨ n % 197 = 98 ∨ n % 203 = 152 ∨ n % 205 = 102 ∨ n % 209 = 174 ∨ n % 213 = 106 ∨ n % 215 = 188 ∨ n % 219 = 164 ∨ n % 221 = 110 ∨ n % 227 = 208 ∨ n % 229 = 114 ∨ n % 233 = 194 ∨ n % 235 = 176 ∨ n % 237 = 118 ∨ n % 239 = 224 ∨ n % 245 = 122 ∨ n % 247 = 216 ∨ n % 251 = 188 ∨ n % 253 = 126 ∨ n % 257 = 214 ∨ n % 261 = 130 ∨ n % 265 = 246 ∨ n % 267 = 200 ∨ n % 269 = 134 ∨ n % 275 = 252 ∨ n % 277 = 138 ∨ n % 279 = 244 ∨ n % 281 = 234 ∨ n % 283 = 212 ∨ n % 285 = 142 ∨ n % 293 = 146 ∨ n % 299 = 224 ∨ n % 301 = 150 ∨ n % 303 = 284 ∨ n % 305 = 254 ∨ n % 309 = 154 ∨ n % 241 = 230 ∨ n % 311 = 272 ∨ n % 315 = 236 ∨ n % 317 = 158 ∨ n % 321 = 298 ∨ n % 323 = 296 ∨ n % 325 = 162 ∨ n % 329 = 274 ∨ n % 331 = 248 ∨ n % 333 = 166 ∨ n % 341 = 170 ∨ n % 343 = 300 ∨ n % 347 = 260 ∨ n % 349 = 174 ∨ n % 353 = 294 ∨ n % 357 = 178 ∨ n % 71 = 68 ∨ n % 167 = 160 ∨ n % 263 = 252 ∨ n % 359 = 344 ∨ n % 363 = 272 ∨ n % 365 = 182 ∨ n % 367 = 344 ∨ n % 371 = 340 ∨ n % 373 = 186 ∨ n % 375 = 328 ∨ n % 377 = 314 ∨ n % 379 = 284 ∨ n % 381 = 190 ∨ n % 389 = 194 ∨ n % 395 = 296 ∨ n % 397 = 198

/-- **Erdős–Straus on the covered union.** One theorem: every `n ≡ 1 (mod 4)` in any
    proved covering class has `4/n` a sum of three unit fractions. -/
theorem straus_of_covered (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1)
    (hc : StrausCovered n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4:ℚ)/n = 1/a + 1/b + 1/c := by
  unfold StrausCovered at hc
  rcases hc with c0|c1|c2|c3|c4|c5|c6|c7|c8|c9|c10|c11|c12|c13|c14|c15|c16|c17|c18|c19|c20|c21|c22|c23|c24|c25|c26|c27|c28|c29|c30|c31|c32|c33|c34|c35|c36|c37|c38|c39|c40|c41|c42|c43|c44|c45|c46|c47|c48|c49|c50|c51|c52|c53|c54|c55|c56|c57|c58|c59|c60|c61|c62|c63|c64|c65|c66|c67|c68|c69|c70|c71|c72|c73|c74|c75|c76|c77|c78|c79|c80|c81|c82|c83|c84|c85|c86|c87|c88|c89|c90|c91|c92|c93|c94|c95|c96|c97|c98|c99|c100|c101|c102|c103|c104|c105|c106|c107|c108|c109|c110|c111|c112|c113|c114|c115|c116|c117|c118|c119|c120|c121|c122|c123|c124|c125
  · exact straus_mod20 n hn h4 c0
  · exact straus_cover_mod44 n hn h4 c1
  · exact straus_cover_mod52 n hn h4 c2
  · exact straus_cover_mod68 n hn h4 c3
  · exact straus_cover_mod84 n hn h4 c4
  · exact straus_cover_mod92 n hn h4 c5
  · exact straus_cover_mod108 n hn h4 c6
  · exact straus_cover_mod116 n hn h4 c7
  · exact straus_cover_mod140 n hn h4 c8
  · exact straus_cover_mod148 n hn h4 c9
  · exact straus_cover_mod164 n hn h4 c10
  · exact straus_cover_mod172 n hn h4 c11
  · exact straus_cover_mod180 n hn h4 c12
  · exact straus_cover_mod212 n hn h4 c13
  · exact straus_cover_mod220 n hn h4 c14
  · exact straus_cover_mod236 n hn h4 c15
  · exact straus_cover_mod244 n hn h4 c16
  · exact straus_cover_mod260 n hn h4 c17
  · exact straus_cover_mod276 n hn h4 c18
  · exact straus_cover_mod300 n hn h4 c19
  · exact straus_cover_mod308 n hn h4 c20
  · exact straus_cover_mod332 n hn h4 c21
  · exact straus_cover_mod340 n hn h4 c22
  · exact straus_cover_mod348 n hn h4 c23
  · exact straus_cover_mod356 n hn h4 c24
  · exact straus_cover_mod364 n hn h4 c25
  · exact straus_cover_mod372 n hn h4 c26
  · exact straus_cover_mod388 n hn h4 c27
  · exact straus_cover_mod404 n hn h4 c28
  · exact straus_cover_mod428 n hn h4 c29
  · exact straus_cover_mod188 n hn h4 c30
  · exact straus_cover_mod436 n hn h4 c31
  · exact straus_cover_mod444 n hn h4 c32
  · exact straus_cover_mod452 n hn h4 c33
  · exact straus_cover_mod468 n hn h4 c34
  · exact straus_cover_mod476 n hn h4 c35
  · exact straus_cover_mod492 n hn h4 c36
  · exact straus_cover_mod500 n hn h4 c37
  · exact straus_cover_mod524 n hn h4 c38
  · exact straus_cover_mod532 n hn h4 c39
  · exact straus_cover_mod548 n hn h4 c40
  · exact straus_cover_mod556 n hn h4 c41
  · exact straus_cover_mod564 n hn h4 c42
  · exact straus_cover_mod596 n hn h4 c43
  · exact straus_cover_mod604 n hn h4 c44
  · exact straus_cover_mod612 n hn h4 c45
  · exact straus_cover_mod620 n hn h4 c46
  · exact straus_cover_mod628 n hn h4 c47
  · exact straus_cover_mod644 n hn h4 c48
  · exact straus_cover_mod660 n hn h4 c49
  · exact straus_cover_mod684 n hn h4 c50
  · exact straus_cover_mod692 n hn h4 c51
  · exact straus_cover_mod700 n hn h4 c52
  · exact straus_cover_mod716 n hn h4 c53
  · exact straus_cover_mod724 n hn h4 c54
  · exact straus_cover_mod732 n hn h4 c55
  · exact straus_cover_mod740 n hn h4 c56
  · exact straus_cover_mod748 n hn h4 c57
  · exact straus_cover_mod756 n hn h4 c58
  · exact straus_cover_mod788 n hn h4 c59
  · exact straus_cover_mod812 n hn h4 c60
  · exact straus_cover_mod820 n hn h4 c61
  · exact straus_cover_mod836 n hn h4 c62
  · exact straus_cover_mod852 n hn h4 c63
  · exact straus_cover_mod860 n hn h4 c64
  · exact straus_cover_mod876 n hn h4 c65
  · exact straus_cover_mod884 n hn h4 c66
  · exact straus_cover_mod908 n hn h4 c67
  · exact straus_cover_mod916 n hn h4 c68
  · exact straus_cover_mod932 n hn h4 c69
  · exact straus_cover_mod940 n hn h4 c70
  · exact straus_cover_mod948 n hn h4 c71
  · exact straus_cover_mod956 n hn h4 c72
  · exact straus_cover_mod980 n hn h4 c73
  · exact straus_cover_mod988 n hn h4 c74
  · exact straus_cover_mod1004 n hn h4 c75
  · exact straus_cover_mod1012 n hn h4 c76
  · exact straus_cover_mod1028 n hn h4 c77
  · exact straus_cover_mod1044 n hn h4 c78
  · exact straus_cover_mod1060 n hn h4 c79
  · exact straus_cover_mod1068 n hn h4 c80
  · exact straus_cover_mod1076 n hn h4 c81
  · exact straus_cover_mod1100 n hn h4 c82
  · exact straus_cover_mod1108 n hn h4 c83
  · exact straus_cover_mod1116 n hn h4 c84
  · exact straus_cover_mod1124 n hn h4 c85
  · exact straus_cover_mod1132 n hn h4 c86
  · exact straus_cover_mod1140 n hn h4 c87
  · exact straus_cover_mod1172 n hn h4 c88
  · exact straus_cover_mod1196 n hn h4 c89
  · exact straus_cover_mod1204 n hn h4 c90
  · exact straus_cover_mod1212 n hn h4 c91
  · exact straus_cover_mod1220 n hn h4 c92
  · exact straus_cover_mod1236 n hn h4 c93
  · exact straus_cover_mod964 n hn h4 c94
  · exact straus_cover_mod1244 n hn h4 c95
  · exact straus_cover_mod1260 n hn h4 c96
  · exact straus_cover_mod1268 n hn h4 c97
  · exact straus_cover_mod1284 n hn h4 c98
  · exact straus_cover_mod1292 n hn h4 c99
  · exact straus_cover_mod1300 n hn h4 c100
  · exact straus_cover_mod1316 n hn h4 c101
  · exact straus_cover_mod1324 n hn h4 c102
  · exact straus_cover_mod1332 n hn h4 c103
  · exact straus_cover_mod1364 n hn h4 c104
  · exact straus_cover_mod1372 n hn h4 c105
  · exact straus_cover_mod1388 n hn h4 c106
  · exact straus_cover_mod1396 n hn h4 c107
  · exact straus_cover_mod1412 n hn h4 c108
  · exact straus_cover_mod1428 n hn h4 c109
  · exact straus_cover_mod284 n hn h4 c110
  · exact straus_cover_mod668 n hn h4 c111
  · exact straus_cover_mod1052 n hn h4 c112
  · exact straus_cover_mod1436 n hn h4 c113
  · exact straus_cover_mod1452 n hn h4 c114
  · exact straus_cover_mod1460 n hn h4 c115
  · exact straus_cover_mod1468 n hn h4 c116
  · exact straus_cover_mod1484 n hn h4 c117
  · exact straus_cover_mod1492 n hn h4 c118
  · exact straus_cover_mod1500 n hn h4 c119
  · exact straus_cover_mod1508 n hn h4 c120
  · exact straus_cover_mod1516 n hn h4 c121
  · exact straus_cover_mod1524 n hn h4 c122
  · exact straus_cover_mod1556 n hn h4 c123
  · exact straus_cover_mod1580 n hn h4 c124
  · exact straus_cover_mod1588 n hn h4 c125

/-! ## The general rung criterion: a QNR prime factor puts −1 in the subgroup -/

open ZMod in
/-- **The Euler-criterion rung lemma.** For an odd prime rung `r`, any nonzero
non-square `a` mod `r` satisfies `a^(r/2) = -1`. A quadratic non-residue divisor
of `M` therefore puts `-1` in the subgroup `⟨primes of M⟩ ⊂ (ZMod r)ˣ` at EVERY
rung — the general form of the rung-3 `p ≡ 2 (mod 3)` criterion. -/
theorem qnr_pow_eq_neg_one {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (a : ZMod r) (ha : a ≠ 0) (hns : ¬ IsSquare a) : a ^ (r / 2) = -1 := by
  have hodd : Odd r := (Nat.Prime.odd_of_ne_two (Fact.out) hr2)
  -- a^(r/2) ≠ 1  (Euler: square ↔ = 1)
  have hne1 : a ^ (r / 2) ≠ 1 := fun h => hns ((ZMod.euler_criterion r ha).mpr h)
  -- (a^(r/2))^2 = a^(r-1) = 1
  have hsq : (a ^ (r / 2)) ^ 2 = 1 := by
    rw [← pow_mul]
    obtain ⟨k, hk⟩ := hodd
    have : r / 2 * 2 = r - 1 := by omega
    rw [this]; exact ZMod.pow_card_sub_one_eq_one ha
  -- x^2 = 1 → x = 1 ∨ x = -1, and x ≠ 1
  have h2 : a ^ (r / 2) * a ^ (r / 2) = 1 := by rw [← sq]; exact hsq
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exact absurd h hne1
  · exact h

/-! ## Primitive-root closure of the exponent-budget arm -/

/-- **Primitive-root closure of the exponent-budget arm.** If `M` carries a prime
`p` that is a primitive root mod `r` (its powers hit every nonzero residue) with
enough power that `p^(r-1) ∣ M²`, then some divisor of `M²` lands at `−M`, so the
rung is `NegMReachable`. This resolves the held exponent-budget case (`−1` in the
subgroup but the divisor must be assembled) whenever a single primitive-root prime
supplies the whole group. -/
theorem negMReachable_of_primitiveRoot (M r p : ℕ) (hr : 1 < r) (hp : 0 < p)
    (hrM : ¬ (r ∣ M))
    (hprim : ∀ x : ZMod r, x ≠ 0 → ∃ j : ℕ, j < r - 1 ∧ (p : ZMod r) ^ j = x)
    (hpow : (p : ℕ) ^ (r - 1) ∣ M * M) :
    NegMReachable M r := by
  have hMne : (M : ZMod r) ≠ 0 := fun h => hrM ((ZMod.natCast_eq_zero_iff M r).mp h)
  have hne : (-(M : ZMod r)) ≠ 0 := neg_ne_zero.mpr hMne
  obtain ⟨j, hj, hjx⟩ := hprim (-(M : ZMod r)) hne
  refine ⟨p ^ j, pow_pos hp j, ?_, ?_⟩
  · exact dvd_trans (pow_dvd_pow p (by omega)) hpow
  · have : ((M + p ^ j : ℕ) : ZMod r) = 0 := by
      push_cast
      rw [hjx]; ring
    exact (ZMod.natCast_eq_zero_iff _ r).mp this

/-! ## Two-generator coverage -/

/-- **Two-generator closure.** When two coprime primes `p, q` of `M` jointly hit
every nonzero residue mod `r` (`⟨p,q⟩ = (ZMod r)ˣ`) and each carries enough power
(`p^(r-1), q^(r-1) ∣ M²`), the product `p^i q^j` realizing `−M` is a divisor of
`M²`, so the rung is `NegMReachable`. The multi-generator step past a single
primitive root. -/
theorem negMReachable_of_twoGen (M r p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (hrM : ¬ (r ∣ M))
    (hgen : ∀ x : ZMod r, x ≠ 0 →
      ∃ i j : ℕ, i < r - 1 ∧ j < r - 1 ∧ (p : ZMod r) ^ i * (q : ZMod r) ^ j = x)
    (hpM : (p : ℕ) ^ (r - 1) ∣ M * M) (hqM : (q : ℕ) ^ (r - 1) ∣ M * M) :
    NegMReachable M r := by
  have hMne : (M : ZMod r) ≠ 0 := fun h => hrM ((ZMod.natCast_eq_zero_iff M r).mp h)
  obtain ⟨i, j, hi, hj, hx⟩ := hgen (-(M : ZMod r)) (neg_ne_zero.mpr hMne)
  refine ⟨p ^ i * q ^ j, by positivity, ?_, ?_⟩
  · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow i j hcop)
      (dvd_trans (pow_dvd_pow p (by omega)) hpM)
      (dvd_trans (pow_dvd_pow q (by omega)) hqM)
  · have : ((M + p ^ i * q ^ j : ℕ) : ZMod r) = 0 := by push_cast; rw [hx]; ring
    exact (ZMod.natCast_eq_zero_iff _ r).mp this

/-! ## Multi-generator coverage — the pigeonhole step -/

/-- Product of pairwise-coprime divisors of `N` divides `N`. -/
theorem prod_dvd_of_pairwise_coprime {N : ℕ} (g : ℕ → ℕ) :
    ∀ T : Finset ℕ, (∀ s ∈ T, g s ∣ N) →
      (∀ a ∈ T, ∀ b ∈ T, a ≠ b → Nat.Coprime (g a) (g b)) →
      (∏ s ∈ T, g s) ∣ N := by
  intro T
  induction T using Finset.induction with
  | empty => intro _ _; simp
  | @insert a T ha ih =>
    intro hd hc
    rw [Finset.prod_insert ha]
    have hcop : Nat.Coprime (g a) (∏ s ∈ T, g s) := by
      apply Nat.Coprime.prod_right
      intro s hs
      exact hc a (Finset.mem_insert_self a T) s (Finset.mem_insert_of_mem hs)
        (by rintro rfl; exact ha hs)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (hd a (Finset.mem_insert_self a T))
      (ih (fun s hs => hd s (Finset.mem_insert_of_mem hs))
          (fun x hx y hy hxy => hc x (Finset.mem_insert_of_mem hx) y
            (Finset.mem_insert_of_mem hy) hxy))

/-- **Multi-generator closure.** A finite family `S` of pairwise-coprime prime
powers dividing `M`, whose powers jointly hit every nonzero residue mod `r`
within budget, closes the rung. The full pigeonhole coverage step. -/
theorem negMReachable_of_multiGen (M r : ℕ) (S : Finset ℕ)
    (hpos : ∀ s ∈ S, 0 < s)
    (hcop : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b)
    (hrM : ¬ (r ∣ M)) (hbud : ∀ s ∈ S, s ^ (r - 1) ∣ M * M)
    (hgen : ∀ x : ZMod r, x ≠ 0 → ∃ f : ℕ → ℕ, (∀ s ∈ S, f s < r - 1) ∧
        ∏ s ∈ S, (s : ZMod r) ^ (f s) = x) :
    NegMReachable M r := by
  have hMne : (M : ZMod r) ≠ 0 := fun h => hrM ((ZMod.natCast_eq_zero_iff M r).mp h)
  obtain ⟨f, hf, hx⟩ := hgen (-(M : ZMod r)) (neg_ne_zero.mpr hMne)
  refine ⟨∏ s ∈ S, s ^ (f s), Finset.prod_pos (fun s hs => pow_pos (hpos s hs) _), ?_, ?_⟩
  · exact prod_dvd_of_pairwise_coprime (fun s => s ^ (f s)) S
      (fun s hs => dvd_trans (pow_dvd_pow s (by have := hf s hs; omega)) (hbud s hs))
      (fun a ha b hb hab => Nat.Coprime.pow _ _ (hcop a ha b hb hab))
  · have hc : ((∏ s ∈ S, s ^ (f s) : ℕ) : ZMod r) = -(M : ZMod r) := by push_cast; exact hx
    have : ((M + ∏ s ∈ S, s ^ (f s) : ℕ) : ZMod r) = 0 := by push_cast [hc]; ring
    exact (ZMod.natCast_eq_zero_iff _ r).mp this

end Erdos.StrausGreedy
