-- Imscribing/Millennium/Erdos/ErdosKacInterval.lean
-- Erdős–Kac interval, ω(n) > log log n
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
The gap between CRT and the conjecture is exponential in log x.

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

**Belnap Verdict: B** — Both True (CRT bound is unconditional) and
Neither (Erdős's (log x)^k conjecture is completely open).

**Known Results:**
  ✓ Erdős–Kac (1940): ω(n) asymptotically normal
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
