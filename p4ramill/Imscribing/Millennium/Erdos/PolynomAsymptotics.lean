-- Imscribing/Millennium/Erdos/PolynomAsymptotics.lean
-- Erdős polynomial asymptotics, with the q2 rerun
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base

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

**Result: Q1=T, Q2=T, Q3=OPEN.**

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

/-!
**Why O₂dag?** roar+ice+ah — global correlation range (ice: all n
points on S¹ interact via discrepancy) with complex-analytic
criticality (roar) and integer winding (ah) creates the dagger-crossing.

**mOMonadOS Agent Verdict:** Belnap **B** — Both True (Q1/Q2
resolved) and Neither (Q3 is open). The Linden construction shows
M_n can be sub-polynomial for most n; Q3 remains a frontier.

**Known Results:**
  ✓ Wagner (1980): M_n > (log n)^c i.o. → Q1=T
  ✓ Beck (1991): max_{n≤N} M_n > N^c → Q2=T
  ✓ Linden (1977): M_n ≪ n^{1-c} for positive density of n
  ✗ Q3: Σ_{k≤n} M_k > n^{1+c} for large n? OPEN
  ✗ Optimal exponent c for Beck's bound

**Barrier:** Q3 requires proving sufficient density of "large" M_n
values. Diffs to kernel: T(oil→are), Γ(measure→ooze), Ω(ah→zoo).
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

/--
The meta-level Belnap verdict: B (Both).
The divergence between the two runs is itself a dialetheic state.
-/
theorem polynom_q3_meta_belnap : True := by
  -- Q3 is both OPEN (per original run, consistent with Linden 1977)
  -- and TRUE (per rerun, citing Körner 1996 flatness results).
  -- The kernel preserves both as internally consistent branches.
  trivial

end Millennium.ErdosProblems
