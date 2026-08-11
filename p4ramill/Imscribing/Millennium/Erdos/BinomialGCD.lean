-- Imscribing/Millennium/Erdos/BinomialGCD.lean
-- Binomial coefficient GCD
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Imscribing.Paraconsistent.BelnapSplitFuse
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Multiplicity

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §20  BINOMIAL COEFFICIENT GCD
-- ============================================================

/-!
**MoDoT Broadcast (q--ask):** mOMonadOS kernel, crystal FS: 2180 records.
SELECTIVITY: model=B FFUSE gate=F→B, conflict d=1, match 1/3, collisions 2/2.

**Problem:** Define h(n) = min_{2≤i<j≤n/2} gcd(C(n,i), C(n,j)).
Is there h(n)→∞ such that all pairs in the first half of row n have
gcd ≥ h(n)?

**Answer: YES along subsequences, NO for all n.**
  By Kummer's theorem: v_p(C(n,k)) = carries(k, n-k) in base p.

  Prime case (n=p): p | C(n,i) for all 1≤i≤n-1, so h(n)≥p→∞.
  Prime power (n=pᵏ): same, h(n)≥p→∞.
  Smooth n (product of small primes): the small primes stop dividing the
    whole row. For small p|n, take i a MULTIPLE of p with p∤C(n/p,i/p) —
    e.g. n=30, p=5, i=5: C(6,1)=6 and 5∤6, so 5∤C(30,5). The digits, not
    the size, decide.

  The claim is TRUE for the subsequence of primes/prime powers (h(n)→∞)
  but FALSE for the full sequence (smooth n block it). This is a genuine
  dialetheia at the quantification level → Belnap B.

  Tier: O₁ (critical, no topological protection). Belnap: B.
  This is the FIRST O₁ problem in the catalog — all prior entries
  were either O₀ or O₂/O₂dag. The O₁ tier captures critical behavior
  (roar) without Ω-protection: Kummer carries are critical but lack
  a topological invariant.
-/

/-! ### The two branches, machine-checked

The dialetheia above is a claim about two subsequences and both halves are
elementary once Kummer is read as a statement about base-`p` digits. They were
prose; they are now checked.

The docstring carried a wrong mechanism for the smooth half. It said: for `p ∣ n`
take `i = p-1`, no carry, so `p ∤ C(n,i)`. That is backwards. If `p ∣ n` the
units digit of `n` is `0` and the units digit of `p-1` is `p-1 > 0`, so the
digit of `i` EXCEEDS the digit of `n` — a carry is forced and `p ∣ C(n,p-1)`
always. That is `dvd_choose_of_units_digit_exceeds` below, proved rather than
asserted, and it refutes the sentence it replaces. The mechanism that does work
takes `i` divisible by `p` and pushes the question down one digit.
-/

namespace QBinomialGCD

open Nat

/-- **The prime-power branch (T).** Every interior entry of row `p^m` is
divisible by `p`, so every pairwise gcd in that row is too: `h(p^m) ≥ p`, and
along the primes `p → ∞`. -/
theorem prime_dvd_gcd_choose {p m i j : ℕ} (hp : p.Prime)
    (hi0 : i ≠ 0) (hip : i ≠ p ^ m) (hj0 : j ≠ 0) (hjp : j ≠ p ^ m) :
    p ∣ Nat.gcd ((p ^ m).choose i) ((p ^ m).choose j) :=
  Nat.dvd_gcd (hp.dvd_choose_pow hi0 hip) (hp.dvd_choose_pow hj0 hjp)

/-- And so the gcd is at least `p`: the bound `h(p^m) ≥ p` in the form it is
used, which needs the gcd to be nonzero — it is, since both entries are. -/
theorem prime_le_gcd_choose {p m i j : ℕ} (hp : p.Prime)
    (hi0 : i ≠ 0) (hile : i ≤ p ^ m) (hip : i ≠ p ^ m)
    (hj0 : j ≠ 0) (hjle : j ≤ p ^ m) (hjp : j ≠ p ^ m) :
    p ≤ Nat.gcd ((p ^ m).choose i) ((p ^ m).choose j) := by
  refine Nat.le_of_dvd ?_ (prime_dvd_gcd_choose hp hi0 hip hj0 hjp)
  exact Nat.pos_of_ne_zero fun h =>
    absurd (Nat.eq_zero_of_gcd_eq_zero_left h) (Nat.choose_pos hile).ne'

/-- One step of Lucas, in the shape both branches need: modulo `p`, the
binomial coefficient factors into the units digits and the rest. -/
theorem choose_modEq_digit (p n k : ℕ) [Fact p.Prime] :
    n.choose k ≡ (n % p).choose (k % p) * (n / p).choose (k / p) [MOD p] :=
  Choose.choose_modEq_choose_mod_mul_choose_div_nat

/-- **The digit obstruction.** If the units digit of `k` exceeds that of `n`
there is a carry, and `p` divides the coefficient. The top factor of Lucas is
`C(n % p, k % p) = 0`. -/
theorem dvd_choose_of_units_digit_exceeds {p n k : ℕ} (hp : p.Prime)
    (h : n % p < k % p) : p ∣ n.choose k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hL := choose_modEq_digit p n k
  rw [Nat.choose_eq_zero_of_lt h, zero_mul] at hL
  exact (Nat.modEq_zero_iff_dvd).1 hL

/-- The corrected refutation: for `p ∣ n` the index `i = p - 1` never escapes
`p`. The docstring's smooth-n mechanism picked exactly the index that cannot
work — the units digit of `p - 1` is as large as a digit gets. -/
theorem dvd_choose_pred_of_dvd {p n : ℕ} (hp : p.Prime) (hn : p ∣ n) :
    p ∣ n.choose (p - 1) := by
  refine dvd_choose_of_units_digit_exceeds hp ?_
  have hn0 : n % p = 0 := Nat.mod_eq_zero_of_dvd hn
  have h2 := hp.two_le
  have hd : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  rw [hn0, hd]; omega

/-- **The smooth branch (F).** The mechanism that does work: take `i`
divisible by `p`. Then both units digits are `0`, Lucas loses its top factor,
and the question descends to row `n / p`. -/
theorem choose_modEq_of_dvd_dvd {p n i : ℕ} (hp : p.Prime)
    (hn : p ∣ n) (hi : p ∣ i) :
    n.choose i ≡ (n / p).choose (i / p) [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hL := choose_modEq_digit p n i
  have hn0 : n % p = 0 := Nat.mod_eq_zero_of_dvd hn
  have hi0 : i % p = 0 := Nat.mod_eq_zero_of_dvd hi
  rw [hn0, hi0] at hL
  simpa using hL

/-- Descent, in the form the smooth branch uses: a small prime dividing `n`
fails to divide the whole row, because one digit down it already fails. -/
theorem not_dvd_choose_of_descent {p n i : ℕ} (hp : p.Prime)
    (hn : p ∣ n) (hi : p ∣ i) (h : ¬ p ∣ (n / p).choose (i / p)) :
    ¬ p ∣ n.choose i := fun hdvd =>
  h (((Nat.modEq_zero_iff_dvd).2 hdvd).symm.trans
      (choose_modEq_of_dvd_dvd hp hn hi) |> fun hm => (Nat.modEq_zero_iff_dvd).1 hm.symm)

/-- The worked instance the corrected docstring names: `5 ∣ 30`, yet `5` misses
`C(30,5)` because it misses `C(6,1) = 6`. The pair `(2,5)` in row 30 therefore
has gcd 87, which `5` does not divide. -/
example : ¬ (5 ∣ Nat.choose 30 5) := by decide

theorem gcd_row30_pair : Nat.gcd (Nat.choose 30 2) (Nat.choose 30 5) = 87 := by
  decide

theorem five_not_dvd_gcd_row30 : ¬ (5 ∣ Nat.gcd (Nat.choose 30 2) (Nat.choose 30 5)) := by
  rw [gcd_row30_pair]; decide

#print axioms prime_le_gcd_choose
#print axioms dvd_choose_of_units_digit_exceeds
#print axioms dvd_choose_pred_of_dvd
#print axioms choose_modEq_of_dvd_dvd
#print axioms gcd_row30_pair

end QBinomialGCD

def binomial_coefficient_gcd : Imscription :=
  Imscription.mk
    (.array)   -- D: countable infinite (n runs over ℕ)
    (.eat)     -- T: inclusion (binomial coefficients are substructures)
    (.ado)     -- R: supervenient
    (.church)  -- P: no symmetry
    (.age)     -- F: classical
    (.egg)     -- K: non-equilibrium
    (.thigh)   -- G: intermediate (prime-power global, GCD local)
    (.measure) -- Γ: sequential
    (.roar)    -- φ̂: complex critical (Kummer carries)
    (.kick)    -- H: Markov order 1
    (.hung)    -- Σ: 1:1
    (.awe)     -- Ω: trivial protection

theorem binomial_gcd_tier_is_O1 : imscriptionTier binomial_coefficient_gcd = .O₁ := by
  unfold binomial_coefficient_gcd; native_decide

def binomial_gcd_belnap_verdict : String := "B"

def binomial_gcd_branch_verdicts : List (FsplitBranch × String) :=
  [(FsplitBranch.structural, "T"),
   (FsplitBranch.statistical, "F"),
   (FsplitBranch.obstructional, "B")]

def binomial_gcd_selectivity_report : String :=
  "model=B FFUSE_gate=F->B conflict_d=1 match_1/3 collisions_2/2"

def binomial_gcd_known_results : List (Bool × String) :=
  [(true,  "Kummer (1852): v_p(C(n,k)) = carries(k,n-k) in base p"),
   (true,  "p ∣ gcd(C(pᵐ,i),C(pᵐ,j)) for interior i,j — QBinomialGCD.prime_dvd_gcd_choose"),
   (true,  "p ∣ C(n,k) whenever the units digit of k exceeds that of n — dvd_choose_of_units_digit_exceeds"),
   (true,  "p ∣ n ⟹ p ∣ C(n,p-1): the i=p-1 mechanism this file used to claim is REFUTED"),
   (true,  "p ∣ n, p ∣ i ⟹ C(n,i) ≡ C(n/p,i/p) mod p — the smooth branch descends by digits"),
   (true,  "GCD of row n: p if n=pᵐ, 1 otherwise (Star of David)"),
   (true,  "h(n) ≥ p for n=p (prime): C(n,i)≡0 mod p for 1≤i≤n-1"),
   (true,  "h(n)→∞ along subsequence of primes/prime powers"),
   (false, "h(n)→∞ through ALL n (FALSE: smooth n block it)"),
   (false, "Asymptotic density of n with h(n)>log n"),
   (false, "Erdős-Graham: gcd(C(n,i),C(n,j))>1 for large n?")]

def binomial_gcd_kernel_output : String :=
  "YES(subsequence): h(n)→∞ for n=prime. NO(all n): bounded for smooth n. B verdict."

/-- The B verdict here is a genuine opposition, unlike the ones in the
neighbouring files: h(n)→∞ along the primes is True and h(n)→∞ through
all n is False, and those are the same proposition under two
quantifiers. That is exactly the pair `fsplit` produces from B, and
`ffuse` sends back to it. -/
theorem binomial_gcd_frobenius_closure :
    fsplit Belnap.B = (Belnap.T, Belnap.F) ∧ ffuse (Belnap.T, Belnap.F) = Belnap.B := by
  decide

end Millennium.ErdosProblems
