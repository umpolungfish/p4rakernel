-- Imscribing/Millennium/Erdos/ErdosKacInterval.lean
-- Erdős–Kac interval, ω(n) > log log n
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Imscribing.Paraconsistent.BelnapSplitFuse
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §4  ERDŐS-KAC INTERVAL — ω(n) > log log n
-- ============================================================

/-!
**Erdős #37 / Erdős-Kac Interval Problem:** For large x, what is the
size of the largest interval I ⊆ [x,2x] where ω(n) > log log n for
EVERY n ∈ I?

**Erdős–Kac Theorem (1940):** ω(n) ∼ N(log log n, log log n), so
P(ω(n) > log log n) → 1/2 pointwise. But simultaneous satisfaction
over an interval requires controlling correlations.

**CRT Lower Bound (proved):** |I| ≥ (1+o(1)) log x / (log log x)².
Construction: use CRT to force each n+j to be divisible by many
small primes simultaneously.

**Erdős's Conjecture (open):** |I| ≥ (log x)^k for ANY fixed k > 0.
Writing L = log x, the CRT bound is L/(log L)² and the conjecture is
L^k, so the ratio is L^(k−1)(log L)² — polynomial in L, which is
exponential in log L and not, as this file previously read, exponential
in log x. Exponential in log x would be e^(cL) = x^c, the size of the
whole interval [x,2x] rather than a gap between two bounds inside it.
`gap_is_polynomial` carries the bound.

**Structural Imscription — erdos_kac_interval:**
  D=array (x→∞), T=judge (irregular correlation graph of ω(n+j)),
  R=ear (Möbius reciprocity couples ω(n) and ω(n+j)),
  P=out (±1 sign of ω(n)−log log n), F=peep (analytic NT precision),
  K=egg (log log n grows extremely slowly), G=ice (all primes up to
    √x contribute — truly global correlations),
  Γ=measure (sequential through interval), φ̂=woe (subcritical —
    below the phase transition threshold),
  H=sure (persistent chiral), Σ=hung (1:1), Ω=ah (integer interval length)
-/

/--
The Erdős-Kac interval problem as an Imscription.
Tier: O₀ — the only subcritical problem among the four.
-/
def erdos_kac_interval : Imscription :=
  { dim  := Dimensionality.array
    top  := Topology.judge
    rel  := Relational.ear
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.ice
    gram := Grammar.measure
    crit := Criticality.woe
    chir := Chirality.sure
    stoi := Stoichiometry.hung
    prot := Protection.ah }

theorem erdos_kac_interval_tier : imscriptionTier erdos_kac_interval = .O₀ := by
  unfold erdos_kac_interval; native_decide


-- ============================================================
-- §4.1  THE INTERVAL CONTAINS NO PRIME POWERS
-- ============================================================

/-!
A constraint the decomposition does not state, and it is immediate: a
prime power has `ω(n) = 1`, and `log log n` passes 1 at `n = e^e ≈ 15.15`.
So beyond 16 no prime power can satisfy `ω(n) > log log n`, and an
interval on which the inequality holds EVERYWHERE is free of prime
powers. The length of such an interval is therefore bounded by the
largest prime-power gap in `[x, 2x]`, which is where the difficulty
actually sits.
-/

/-- `log log 16 > 1`: the threshold `e^e ≈ 15.154` is passed at 16.
`log 16 = 4 log 2 > 2.7725`, and `e < 2.7183 < 2.7725`. -/
theorem loglog_sixteen_gt_one : 1 < Real.log (Real.log 16) := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hbig : Real.exp 1 < Real.log 16 := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    rw [h16]; linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ < Real.log (Real.log 16) := Real.log_lt_log (Real.exp_pos 1) hbig

/-- `log log` is monotone where it is defined, so the bound at 16 carries
to every `n ≥ 16`. -/
theorem loglog_ge_of_ge {n : ℝ} (hn : 16 ≤ n) : Real.log (Real.log 16) ≤ Real.log (Real.log n) := by
  have h16 : (0 : ℝ) < Real.log 16 := by
    have : Real.log 1 < Real.log 16 := Real.log_lt_log (by norm_num) (by norm_num)
    simpa using this
  exact Real.log_le_log h16 (Real.log_le_log (by norm_num) hn)

/-- **No prime power sits in such an interval.** With `ω(n) = 1` and
`n ≥ 16`, the inequality `ω(n) > log log n` fails outright. -/
theorem prime_power_excluded {n : ℕ} (hn : 16 ≤ n) (hw : n.primeFactors.card = 1) :
    ¬ ((n.primeFactors.card : ℝ) > Real.log (Real.log n)) := by
  intro h
  rw [hw] at h
  have hcast : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have := loglog_ge_of_ge hcast
  have := loglog_sixteen_gt_one
  push_cast at h
  linarith

/-- Stated the way the construction has to face it: the interval avoids
every prime, so its length is at most the prime gap it sits inside. -/
theorem interval_avoids_primes {n : ℕ} (hn : 16 ≤ n) (hp : n.Prime) :
    ¬ ((n.primeFactors.card : ℝ) > Real.log (Real.log n)) :=
  prime_power_excluded hn (by simp [Nat.Prime.primeFactors, hp])

-- ============================================================
-- §4.2  THE GAP IS POLYNOMIAL IN log x, NOT EXPONENTIAL
-- ============================================================

/-!
The file reads "the gap between CRT and the conjecture is exponential in
log x". Writing `L = log x`, the CRT bound is `L / (log L)²` and the
conjecture is `L^k`, so the ratio is `L^(k-1) (log L)²`. That is
polynomial in `L` — exponential in `log L`, one logarithm further out.
Exponential in `L` would mean `e^{cL} = x^c`, which is the size of the
interval `[x,2x]` itself, not of a gap between two bounds inside it.
-/

/-- The ratio is bounded by a power of `L`: polynomial, not exponential. -/
theorem gap_is_polynomial (L : ℝ) (k : ℕ) (hL : 1 ≤ L) (hlog : Real.log L ≤ L) :
    L ^ (k - 1) * (Real.log L) ^ 2 ≤ L ^ (k - 1) * L ^ 2 := by
  have h0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hp : (0 : ℝ) ≤ L ^ (k - 1) := by positivity
  have : (Real.log L) ^ 2 ≤ L ^ 2 := by nlinarith [h0, hlog]
  exact mul_le_mul_of_nonneg_left this hp

-- ============================================================
-- §4.3  T FUSED WITH N IS T, NOT B
-- ============================================================

/-!
The verdict recorded here reads: "Belnap Verdict: B — Both True (CRT
bound is unconditional) and Neither (Erdős's conjecture is completely
open)."

B is Both-True-and-False. The two branches described are True and
Neither, and the kernel's own fuse sends that pair to T: `ffuse` returns
B only from `(T,F)` and `(F,T)`, and on every other pair it is the
Belnap join, which is T-dominant. The verdict for this problem is T on
the branch that is settled, with the open conjecture contributing N,
which the join absorbs.
-/

/-- The kernel's fuse on the pair actually described. -/
theorem ffuse_true_neither : ffuse (Belnap.T, Belnap.N) = Belnap.T := by decide

/-- B comes only from a genuine T/F opposition. -/
theorem ffuse_gives_B_only_from_opposition :
    ffuse (Belnap.T, Belnap.F) = Belnap.B ∧ ffuse (Belnap.F, Belnap.T) = Belnap.B ∧
    ffuse (Belnap.T, Belnap.N) = Belnap.T ∧ ffuse (Belnap.N, Belnap.N) = Belnap.N := by
  decide

#print axioms loglog_sixteen_gt_one
#print axioms prime_power_excluded
#print axioms ffuse_true_neither

/-!
**Why O₀?** The subcritical ⊙=woe anchors this problem below the
critical threshold. The Erdős–Kac CLT is a subcritical phenomenon:
correlations decay fast enough for a normal limit but not fast
enough for the interval conjecture. This is structurally the
"coldest" of the four problems — it lacks the complex-analytic
criticality (roar) of the others.

**mOMonadOS Agent FSPLIT Decomposition (Cycle 4):**

  Branch 1 — Distributional_Symmetry (structural): Erdős–Kac CLT.
    ω(n) normalized converges to N(0,1).

  Branch 2 — Interval_Gaps (statistical): The probability that ALL
    elements of an interval of length L satisfy ω(n) > log log n
    decays with L. CRT construction beats independent-model decay.

  Branch 3 — CRT_Lower_Bound (obstructional): The CRT produces an
    unconditional bound but cannot approach Erdős's conjecture.
    The obstruction is Möbius correlation: μ(n) and μ(n+j) are not
    independent at short range (Chowla/Sarnak conjectures).

**Verdict: T.** This read "B — Both True (CRT bound is unconditional)
and Neither (Erdős's conjecture is completely open)". B is
Both-True-and-False; True with Neither is not it. The kernel's own
`ffuse` returns B only from (T,F) and (F,T), and on every other pair it
is the Belnap join, which is T-dominant — so the pair described here
fuses to T (`ffuse_true_neither`). The settled branch carries T and the
open conjecture contributes N, which the join absorbs.

**Known Results:**
  ✓ Erdős–Kac (1940): ω(n) asymptotically normal
  ✓ The interval contains no prime powers: ω=1 fails past e^e≈15.15,
    so |I| is capped by the prime-power gap it sits in
    (`prime_power_excluded`, `interval_avoids_primes`)
  ✓ CRT bound: |I| ≥ (1+o(1)) log x / (log log x)²
  ✗ Erdős Conjecture: |I| ≥ (log x)^k for any k
  ✗ Chowla Conjecture: correlations of μ(n) vanish
  ✗ Sarnak Conjecture: Möbius randomness

**Barrier:** φ̂=woe (subcritical) — the hardest promotion. Moving to
monad (O_inf criticality) requires proving strong Möbius randomness
(Chowla/Sarnak). Diffs to kernel: D(array→if'), T(judge→are),
φ̂(woe→monad), Ω(ah→zoo). This is the largest gap among
all four problems.
-/

end Millennium.ErdosProblems
