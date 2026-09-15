-- Imscribing/Millennium/Erdos/PolynomAsymptotics.lean
-- Erdős polynomial asymptotics, with the q2 rerun
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Imscribing.Paraconsistent.BelnapSplitFuse
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §8  ERDŐS POLYNOM ASYMPTOTICS — M_n on the unit circle
-- ============================================================

/-!
**Erdős Conjecture #4.1 / Polynomial Extremum on S¹:**
Let M_n = max_{|z|=1} ∏_{i=1}^n |z - z_i| where all |z_i| = 1
(roots lie on the unit circle). Three nested questions:

  Q1: Is limsup_{n→∞} M_n = ∞?
  Q2: Does ∃c>0 such that M_n > n^c infinitely often?
  Q3: Does ∃c>0 such that Σ_{k≤n} M_k > n^{1+c} for large n?

**mOMonadOS Agent FSPLIT Decomposition (Cycle 6):**

  Branch 1 — Wagner_Log_Bound (structural): Wagner (1980) proved
    M_n > (log n)^c for infinitely many n via L² norm of the
    logarithmic derivative. So M_n is strictly unbounded: Q1 = TRUE.

  Branch 2 — Beck_Polynomial_Max (statistical): Beck (1991) used
    Fourier analysis and discrepancy theory to show max_{n≤N} M_n > N^c.
    Hence M_n > n^c infinitely often: Q2 = TRUE.

  Branch 3 — Linden_Sublinear_Growth (obstructional): Linden (1977)
    constructed sequences with M_n ≪ n^{1-c}, showing M_n can be
    "small" for most n. This makes the sum condition Q3 deeply
    non-trivial and currently OPEN.

**Result: Q1=T, Q2=T, Q3=OPEN.** What Q3 asks over and above Q2 is a
power saving, not growth: M_k ≥ 1 always, since ∏(z − z_i) is monic of
degree k, so Σ_{k≤n} M_k ≥ n is free and Q3's n^{1+c} lives entirely in
the exponent (`sum_ge_card`, `q3_is_power_saving`). Q2's M_k > k^c
infinitely often contributes only finitely much to any given partial
sum, which is why Q3 does not follow from it.

**Structural Imscription — erdos_polynom_asymptotics:**
  D=array (n→∞ asymptotic sequence)
  T=oil (points on S¹, angular coordinates ≈ ℤ/2πℤ)
  R=ear (Fourier duality: point distribution ↔ product maximum)
  P=out (bounded vs. unbounded dichotomy)
  F=peep (Fourier-analytic precision)
  K=egg (slow growth: log n → n^c gap)
  G=ice (global correlations: all n points interact via discrepancy)
  Γ=measure (sequential n→∞)
  φ̂=roar (complex-axis: unit circle = ℂ boundary)
  H=sure (persistent chiral: product is directional on S¹)
  Σ=hung (1:1: one point configuration → one M_n value)
  Ω=ah (integer winding: n counts points → ℤ-valued parameter)
-/

/--
The Erdős polynom asymptotics problem as an Imscription.
Tier: O₂dag — roar+ice+ah creates the dagger-crossing.
-/
def erdos_polynom_asymptotics : Imscription :=
  { dim  := Dimensionality.array
    top  := Topology.oil
    rel  := Relational.ear
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.ice
    gram := Grammar.measure
    crit := Criticality.roar
    chir := Chirality.sure
    stoi := Stoichiometry.hung
    prot := Protection.ah }

theorem erdos_polynom_asymptotics_tier : imscriptionTier erdos_polynom_asymptotics = .O₂dag := by
  unfold erdos_polynom_asymptotics; native_decide


-- ============================================================
-- §8.1  THE ROOTS OF UNITY GIVE M_n = 2, AND WHY THAT IS ALLOWED
-- ============================================================

/-!
Taking the `n`-th roots of unity for the points makes the product
`∏(z − z_i)` equal to `z^n − 1`, whose maximum on the circle is exactly
2 — no growth in `n` at all. That configuration does not refute Q1,
because Q1 is about ONE infinite sequence and the first `n` of its terms.
The `n`-th roots of unity and the `(n+1)`-th roots meet only at 1, so no
single sequence can present the roots of unity at two consecutive `n`.
That is the whole reason the question is hard: the extremal configuration
at each `n` exists but cannot be held simultaneously.
-/

/-- On the unit circle `‖z^n − 1‖ ≤ 2`. -/
theorem abs_pow_sub_one_le_two {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ 2 := by
  have h1 : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [h1]; norm_num

/-- And 2 is attained, at any `z` with `z^n = −1`. -/
theorem abs_pow_sub_one_eq_two {z : ℂ} {n : ℕ} (h : z ^ n = -1) :
    ‖z ^ n - 1‖ = 2 := by
  rw [h, show (-1 : ℂ) - 1 = -2 by ring]
  simp

/-- **`M_n = 2` for the roots-of-unity configuration** — bounded in `n`,
so no single `n` witnesses unboundedness. -/
theorem roots_of_unity_max_is_two {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ 2 ∧ (z ^ n = -1 → ‖z ^ n - 1‖ = 2) :=
  ⟨abs_pow_sub_one_le_two hz n, fun h => abs_pow_sub_one_eq_two h⟩

/-- **The configurations cannot be nested.** The `n`-th and `(n+1)`-th
roots of unity share only the roots of order dividing `gcd(n, n+1) = 1`,
namely 1 itself. A single sequence therefore cannot be extremal at two
consecutive lengths. -/
theorem consecutive_roots_coprime (n : ℕ) : Nat.gcd n (n + 1) = 1 := by
  simpa using Nat.coprime_succ_self_right (n := n)

-- ============================================================
-- §8.2  WHAT Q3 IS ASKING OVER AND ABOVE Q2
-- ============================================================

/-!
`M_k ≥ 1` holds for every configuration, because `∏(z − z_i)` is monic of
degree `k` and a monic polynomial has maximum modulus at least 1 on the
unit circle. So `Σ_{k≤n} M_k ≥ n` is free, and Q3's `n^{1+c}` is a POWER
SAVING over that trivial bound rather than a growth statement on its own.
Q2 gives `M_k > k^c` infinitely often, which by itself contributes only
finitely much extra to any particular partial sum — which is exactly why
Q3 does not follow from Q2.
-/

/-- The trivial partial-sum bound, from `M_k ≥ 1`. -/
theorem sum_ge_card {n : ℕ} (M : ℕ → ℝ) (hM : ∀ k, 1 ≤ M k) :
    (n : ℝ) ≤ ∑ k ∈ Finset.range n, M k := by
  calc (n : ℝ) = ∑ _k ∈ Finset.range n, (1 : ℝ) := by simp
    _ ≤ ∑ k ∈ Finset.range n, M k :=
        Finset.sum_le_sum (fun k _ => hM k)

/-- Q3 is a power saving above it: `n^{1+c}` beats `n` for `c > 0` and
`n ≥ 2`, so the content of Q3 is entirely in the exponent. -/
theorem q3_is_power_saving (n : ℕ) (c : ℝ) (hc : 0 < c) (hn : 2 ≤ n) :
    (n : ℝ) < (n : ℝ) ^ (1 + c) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ < (n : ℝ) ^ (1 + c) := by
        exact Real.rpow_lt_rpow_left_iff hn1 |>.2 (by linarith)

-- ============================================================
-- §8.3  T WITH N IS T
-- ============================================================

/-!
The verdict here reads "B — Both True (Q1/Q2 resolved) and Neither (Q3 is
open)". B is Both-True-and-False. The kernel's `ffuse` sends `(T,N)` to T,
returning B only from a genuine T/F opposition, so the two branches as
described fuse to T with the open question contributing N.

The hub's rerun table separately records this problem as an
OPEN→TRUE divergence on Q3. That divergence stands as an ambiguity: the
original run read Q3 open and the rerun read it true, and nothing here
settles which reading of Q3 was answered.
-/

theorem polynom_ffuse_true_neither : ffuse (Belnap.T, Belnap.N) = Belnap.T := by decide

#print axioms abs_pow_sub_one_le_two
#print axioms consecutive_roots_coprime
#print axioms sum_ge_card

/-!
**Why O₂dag?** roar+ice+ah — global correlation range (ice: all n
points on S¹ interact via discrepancy) with complex-analytic
criticality (roar) and integer winding (ah) creates the dagger-crossing.

**Verdict: T.** This read "B — Both True (Q1/Q2 resolved) and Neither
(Q3 is open)". B is Both-True-and-False; True with Neither is not it,
and the kernel's own `ffuse` sends (T,N) to T, returning B only from a
genuine T/F opposition (`polynom_ffuse_true_neither`). Q1 and Q2 carry
T, Q3 contributes N, and the join absorbs it.

The hub's rerun table records this problem separately as an OPEN→TRUE
divergence on Q3. That stands as an ambiguity: the original run read Q3
open, the rerun read it true, and nothing here settles which reading of
Q3 each answered.

-/

-- ============================================================
-- §16  ERDŐS POLYNOM KERNEL DIVERGENCE — mOMonadOS q2 Rerun
-- ============================================================

/-!
**CRITICAL KERNEL DIVERGENCE — Erdős Polynom Asymptotics q2 Rerun:**

The mOMonadOS q2 rerun (Cycle 11) produced a DIFFERENT structural
verdict from the original run (Cycle 6, §8).

  ORIGINAL RUN (Cycle 6):   Q1=T, Q2=T, Q3=OPEN (Belnap B)
  RERUN (Cycle 11):         Q1=T, Q2=T, Q3=TRUE (Belnap T)

The rerun claims:
  "By the lower bounds on the L^∞ norm of such polynomials (related
  to the work of Erdos on the 'flatness' of polynomials), it is TRUE
  that the average growth is super-linear."

This contradicts the existing formalization where Q3 is classified
as OPEN. The rerun cites Körner (1996) and "flatness of polynomials"
but does not provide a specific theorem statement for the sum bound.

**Structural Analysis of the Divergence:**

The difference hinges on the interpretation of Q3:
  Q3: Does ∃c>0 such that Σ_{k≤n} M_k > n^{1+c} for large n?

The original run (Cycle 6) treats this as requiring the AVERAGE M_k
to exceed n^c, which the Linden (1977) construction potentially
contradicts (M_n ≪ n^{1-c} for positive density of n).

The rerun interprets the "flatness" results as implying that even
the well-distributed sequences have sufficient "spikes" to drive
the cumulative sum above n^{1+c}. This is a genuinely different
structural assessment — the rerun places the problem at a higher
confidence tier.

**Resolution: The divergence is preserved as a Belnap dialetheia.**
Both runs achieved Frobenius ratio 1.0 (μ∘δ=id), meaning both
structural decompositions are internally consistent. The divergence
reflects an ambiguity in the mathematical literature itself: the
"flatness" results (Erdős, Körner) give L^∞ lower bounds for some
sequences, but whether these force the cumulative sum above n^{1+c}
for ALL sequences is not settled.

**We encode the divergence as a kernel fork:**
- Left branch (original):  Q3 = OPEN, Belnap B
- Right branch (rerun):    Q3 = TRUE, Belnap T
- The fork is itself a Belnap B state at the meta-level.

**Structural Imscription (unchanged):** Same as erdos_polynom_asymptotics (§8).
-/

/--
Kernel divergence for Erdős Polynom Asymptotics Q3.
The original run says OPEN; the rerun says TRUE.
-/
inductive PolynomQ3Verdict where
  | open_question   -- original run (Cycle 6)
  | proven_true     -- rerun (Cycle 11)
  deriving DecidableEq, Repr

/--
The two conflicting verdicts for Erdős Polynom Q3.
-/
def polynom_q3_divergence : List (String × PolynomQ3Verdict) :=
  [("original_cycle6", PolynomQ3Verdict.open_question),
   ("rerun_cycle11",   PolynomQ3Verdict.proven_true)]

/-- The Belnap value each recorded verdict carries: `open_question` is N,
`proven_true` is T. -/
def q3VerdictBelnap : PolynomQ3Verdict → Belnap
  | PolynomQ3Verdict.open_question => Belnap.N
  | PolynomQ3Verdict.proven_true   => Belnap.T

/-- **The divergence is not dialetheic.** This was recorded as a
meta-level B — "the divergence between the two runs is itself a
dialetheic state". One run read Q3 open and the other read it true, which
is N against T, and `ffuse` sends that pair to T. B needs one run to have
read it FALSE. What the two runs disagree about is how much is known, and
a gap in knowledge is N, which the join absorbs. -/
theorem polynom_q3_meta_fuses_to_true :
    ffuse (q3VerdictBelnap PolynomQ3Verdict.proven_true,
           q3VerdictBelnap PolynomQ3Verdict.open_question) = Belnap.T := by
  decide

/-- For contrast, the pair that would have earned B. -/
theorem polynom_q3_what_B_needs :
    ffuse (Belnap.T, Belnap.F) = Belnap.B := by decide

end Millennium.ErdosProblems
