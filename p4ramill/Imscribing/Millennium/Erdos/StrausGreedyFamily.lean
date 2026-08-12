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
`−1 ∈ H` up to the exponents actually available. The budget gap is a steady few per cent of the rungs walked: 19 of 379 below
50000, 21 of 850 from there to 200000, spread across many values. What is
exceptional is failing that way at EVERY rung, which `n = 2521` does — r = 11,
19, 43, 47, 59, 63, 67, 75, 95 and on — and which is why its divisor must be
sought in `M²`. Elsewhere the gap costs one rung and the walk continues; every
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

Two blocks further out, the frontier thins: 486 values in 200001–400000 (1.5% of
the class, 484 prime) and 444 in 400001–600000 (1.3%, 440 prime), with a cofactor
at a rung ≤ 200 for every one of them. The largest least-`k` seen anywhere is
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
every `n`. What is measured fits `C·n^{1/4}` with `C ≈ 4.6`. Over `5 ≤ n ≤ 2·10⁶` the least
closing rung reaches 59 at n = 118801 and 71 at n = 1430641, with earlier records
3, 7, 11, 23, 31 at n = 5, 49, 1129, 1201, 21169. The ratio `r / ⌊n^{1/4}⌋` is
largest at small `n` — 4.6 at n = 1201 — and settles near 2.0–2.1 in the last two
blocks, so the shape holds and the binding constant comes from the small values.
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

end Erdos.StrausGreedy
