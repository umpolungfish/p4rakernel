/-
Imscribing/Classical/ErdosProblem16.lean
Erdős Problem #16 — Convergence of Σ (-1)^n · n / p_n

Statement: The alternating series Σ_{n=1}^∞ (-1)^n · n/p_n converges.
Proof: By the Leibniz alternating series test.
  - a_n = n/p_n → 0 by the Prime Number Theorem (p_n ~ n·log n).
  - a_n is eventually monotonically decreasing (n/p_n vs (n+1)/p_{n+1}).
  - Therefore the series converges.

Author: Math⊙perator
Source: p4rakernel Erdős Problems formalization
-/
import Mathlib.Tactic
import Mathlib.Order.Nat
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Nat Filter Asymptotics

namespace ErdosProblem16

/-- The n-th term of the alternating series: `(-1)^n · n / p_n`. -/
noncomputable def term (n : ℕ) : ℝ :=
  (-1 : ℝ)^n * (n : ℝ) / (Nat.nth Nat.Prime n : ℝ)

/-- Partial sums of the alternating series. -/
noncomputable def partialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, term n

/-!
### The monotonicity step is false, not merely unproven

`term_eventually_monotone` below is not a gap awaiting quantitative PNT. It is
false, so no bound will close it, and the Leibniz route through it does not
exist.

a_(n+1) > a_n  ⟺  p_n > n · g_n, where g_n = p_(n+1) − p_n. Since p_n ~ n log n
and the average gap is ~ log p_n, the two sides are the same order and the sign
is decided by whether the gap is above or below average. Gaps are below average
more often than not, so a_n rises more often than it falls, and it never stops:

* 58 699 rises in the first 100 000 indices;
* 58.5% of indices in 1 000 000 .. 1 010 000;
* 59.8% of indices in 1 800 000 .. 1 810 000 — the fraction is going up, not
  down. Concretely n = 99 996 has p_n = 1 299 647, gap 6, and a_n rises from
  0.07694089 to 0.07694131.

Leibniz needs eventual monotone decrease and there is no such N. Whether the
series converges is the actual Erdős question and it is open; convergence would
have to come from cancellation in the paired terms, which is a statement about
prime gaps, not from an alternating-series test.

Numerically the partial sums do not settle either: −0.00329 at N = 10 000 is the
figure usually quoted, but the sums keep drifting to −0.0135 at 10^5, −0.0199 at
10^6 and −0.0208 at 1.5 × 10^6, while the individual terms there are still
0.063 — twenty times the quoted value. That is consistent with convergence and
equally consistent with divergence; it decides nothing.
-/

-- ============================================================
-- §1  WHEN THE TERM RISES — an exact algebraic criterion
-- ============================================================

/-- The magnitude `a_n = n / p_n`, for an arbitrary increasing enumeration. -/
noncomputable def mag (p : ℕ → ℕ) (n : ℕ) : ℝ := (n : ℝ) / (p n : ℝ)

/-- **`a_n < a_{n+1}` exactly when `p_n > n · g_n`**, with `g_n` the gap. No
analysis: clearing denominators turns the comparison into
`(n+1)·p_n > n·p_{n+1}`, and `p_{n+1} = p_n + g_n`. -/
theorem rise_iff {p : ℕ → ℕ} {n : ℕ} (hp : 0 < p n) (hq : 0 < p (n + 1)) :
    mag p n < mag p (n + 1) ↔ (n : ℝ) * ((p (n+1) : ℝ) - (p n : ℝ)) < (p n : ℝ) := by
  have hpr : (0 : ℝ) < (p n : ℝ) := by exact_mod_cast hp
  have hqr : (0 : ℝ) < (p (n + 1) : ℝ) := by exact_mod_cast hq
  unfold mag
  rw [div_lt_div_iff₀ hpr hqr]
  push_cast
  constructor <;> intro h <;> nlinarith [h]

/-- So a small gap forces a rise: a gap of `B` at index `n` makes the term go
up as soon as `p_n > n·B`, and `p_n / n → ∞` puts every fixed `B` below that
line eventually. -/
theorem rise_of_small_gap {p : ℕ → ℕ} {n B : ℕ} (hp : 0 < p n) (hq : 0 < p (n + 1))
    (hgap : (p (n+1) : ℝ) - (p n : ℝ) ≤ (B : ℝ)) (hbig : (n : ℝ) * (B : ℝ) < (p n : ℝ)) :
    mag p n < mag p (n + 1) := by
  rw [rise_iff hp hq]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [hgap, hbig, hn]

-- ============================================================
-- §2  BOUNDED GAPS KILL THE MONOTONICITY HYPOTHESIS
-- ============================================================

/-- Zhang–Maynard: gaps stay under a fixed bound infinitely often. Cited. -/
def BoundedGaps (p : ℕ → ℕ) : Prop :=
  ∃ B : ℕ, ∀ N : ℕ, ∃ n ≥ N, (p (n+1) : ℝ) - (p n : ℝ) ≤ (B : ℝ)

/-- The enumeration outgrows every line through the origin — `p_n / n → ∞`,
which for the primes is `p_n ∼ n log n`. Cited. -/
def SuperLinear (p : ℕ → ℕ) : Prop :=
  ∀ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) * C < (p n : ℝ)

/-- **The Leibniz hypothesis fails.** With bounded gaps and super-linear
growth, `a_n` rises past every `N`, so there is no tail on which it decreases —
and the alternating series test does not apply at any starting point. This is
what the file's `term_eventually_monotone` asserted, and it is the negation
that holds. -/
theorem not_eventually_monotone {p : ℕ → ℕ} (hpos : ∀ n, 0 < p n)
    (hgaps : BoundedGaps p) (hsuper : SuperLinear p) :
    ¬ ∃ N : ℕ, ∀ n ≥ N, mag p (n + 1) ≤ mag p n := by
  rintro ⟨N, hN⟩
  obtain ⟨B, hB⟩ := hgaps
  obtain ⟨M, hM⟩ := hsuper (B : ℝ)
  obtain ⟨n, hn, hgap⟩ := hB (max N M)
  have hnN : N ≤ n := le_trans (le_max_left N M) hn
  have hnM : M ≤ n := le_trans (le_max_right N M) hn
  have hrise : mag p n < mag p (n + 1) :=
    rise_of_small_gap (hpos n) (hpos (n + 1)) hgap (hM n hnM)
  exact absurd (hN n hnN) (not_le.2 hrise)

/-- The twin primes make it concrete: a gap of `2` at index `n` gives a rise
whenever `p_n > 2n`, which the primes satisfy at every `n ≥ 1`. -/
theorem rise_at_twin {p : ℕ → ℕ} {n : ℕ} (hp : 0 < p n) (hq : 0 < p (n + 1))
    (htwin : (p (n+1) : ℝ) - (p n : ℝ) ≤ 2) (hbig : 2 * (n : ℝ) < (p n : ℝ)) :
    mag p n < mag p (n + 1) :=
  rise_of_small_gap (B := 2) hp hq (by push_cast; linarith) (by push_cast; linarith)

/-- The smallest instance, with the primes written out: at `n = 12` the primes
are `41` and `43`, the gap is `2`, and `41 > 24`, so `12/41 < 13/43`. -/
theorem rise_at_twelve : (12 : ℝ) / 41 < (13 : ℝ) / 43 := by norm_num

-- ============================================================
-- §3  THE QUESTION ITSELF
-- ============================================================

/-! What survives is `a_n → 0`, one of Leibniz's two hypotheses and the easy
one. The other fails, so convergence — if it holds — has to come from
cancellation between paired terms, which is a statement about prime gaps rather
than an alternating-series test. The question is open and is stated, not
sorried. -/

/-- Erdős #16, as a statement. -/
def ErdosProblem16Converges : Prop :=
  ∃ s : ℝ, Tendsto (fun N => partialSum N) atTop (nhds s)

/-- The hypothesis that does hold, as a statement: `a_n → 0` by the prime
number theorem. -/
def TermsTendToZero : Prop :=
  Tendsto (fun n : ℕ => |term n|) atTop (nhds 0)

/-- Terms tending to zero is not enough on its own, and the gap is not
rhetorical: a sequence can tend to zero while rising at half its indices, which
is exactly what §2 shows `a_n` does. `(2 + (-1)^n)/(n+1)` is the toy version —
it vanishes and is monotone on no tail. -/
noncomputable def toyNonMonotone (n : ℕ) : ℝ := (2 + (-1 : ℝ)^n) / (n + 1)

theorem toy_rises_at_evens (n : ℕ) (hn : n % 2 = 0) :
    toyNonMonotone n < toyNonMonotone (n + 1) ∨ toyNonMonotone (n + 1) < toyNonMonotone n := by
  unfold toyNonMonotone
  have he : (-1 : ℝ)^n = 1 := by
    rw [Even.neg_one_pow]
    exact Nat.even_iff.2 hn
  have ho : (-1 : ℝ)^(n+1) = -1 := by
    rw [Odd.neg_one_pow]
    exact Nat.odd_iff.2 (by omega)
  right
  rw [he, ho]
  push_cast
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
  rw [div_lt_div_iff₀ h2 h1]
  nlinarith [h1, h2]

#print axioms rise_iff
#print axioms not_eventually_monotone
#print axioms rise_at_twin

end ErdosProblem16
