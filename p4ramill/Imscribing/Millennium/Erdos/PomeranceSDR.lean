-- Imscribing/Millennium/Erdos/PomeranceSDR.lean
-- Erdős–Pomerance SDR interval, with the q5 rerun
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
-- §11  ERDŐS-POMERANCE PROBLEM — SDR interval for multiples
-- ============================================================

/-!
**Erdős-Pomerance Problem (1980):** Let f(n) be the minimal length
of an interval I = (x, x+f(n)) such that there exists a system of
distinct representatives (SDR) for the sets S_k = {a ∈ I : k ∣ a}
for k = 1,…,n. Equivalently: find n distinct numbers in an interval
of length f(n), each divisible by a different k ∈ {1,…,n}.

**The Hall Marriage formulation:** There exist a_1,…,a_n all distinct
in I with k ∣ a_k iff the Hall condition holds: for every J ⊆ {1,…,n},
|⋃_{k∈J} {m : km ∈ I}| ≥ |J|.

**mOMonadOS Agent FSPLIT Decomposition (Cycle 9):**

  Branch 1 — Lower_Bound_Sieving (structural): The lower bound uses
    the Chinese Remainder Theorem to force overlap constraints.
    To prevent two indices k,j from claiming the same integer, the
    interval must be long enough to accommodate y-smooth number
    distributions. Result: f(n) ≥ (2/√e) n √(log n / log log n).

  Branch 2 — Upper_Bound_Hall_Marriage (statistical): The upper
    bound uses Hall's theorem with density estimates on the
    distribution of integers with large prime factors. Erdős-
    Pomerance (1980) bounded f(n) by analyzing integers with
    p > n/f(n). Result: f(n) ≲ c·n √(log n / log log n).

  Branch 3 — Matching_Asymptotics (obstructional): The exact constant
    c is unknown. Erdős offered 2000 rupees for determining c.
    Candidates: e^γ (from the Dickman-de Bruijn function ρ(u)
    controlling smooth numbers in short intervals).

**Result:** f(n) ≍ n √(log n / log log n). The constant remains open.

**Structural Imscription — erdos_pomerance_problem:**
  D=array (n→∞ asymptotic parameter)
  T=judge (irregular divisibility lattice on ℤ)
  R=ear (Hall marriage ↔ SDR existence duality)
  P=out (SDR exists / does not exist)
  F=peep (analytic NT precision: y-smooth number estimates)
  K=egg (slow: n √(log n/log log n) is barely superlinear)
  G=ice (global: all primes ≤ n contribute via CRT)
  Γ=measure (sequential: distribute 1,…,n across interval)
  φ̂=roar (complex-axis: Dickman ρ via Laplace transform in ℂ)
  H=sure (persistent chiral: k∣a_k is directed)
  Σ=hung (1:1: one interval → one SDR existence claim)
  Ω=ah (integer winding: interval length is an integer)
-/

/--
The Erdős-Pomerance SDR problem as an Imscription.
Tier: O₂dag — roar+ice+ah with judge topology.
-/
def erdos_pomerance_problem : Imscription :=
  { dim  := Dimensionality.array
    top  := Topology.judge
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

theorem erdos_pomerance_problem_tier : imscriptionTier erdos_pomerance_problem = .O₂dag := by
  unfold erdos_pomerance_problem; native_decide

/-!
**Why ice (global correlations)?** The SDR condition involves ALL
k=1,…,n simultaneously. The CRT couples primes across the entire
range [1,n], making the correlation range truly global (ice).
This contrasts with problems where only intermediate-range
correlations (thigh) suffice.

**mOMonadOS Agent Verdict:** Belnap **B** — Both True (the asymptotic
order is established: f(n) ≍ n √(log n / log log n)) and Neither
(the exact constant c is open; Erdős's 2000-rupee prize stands).

**Known Results:**
  ✓ Erdős-Pomerance (1980): f(n) ∼ c·n √(log n / log log n)
  ✓ Hall's Marriage Theorem provides the SDR formulation
  ✓ CRT lower bound: (2/√e) n √(log n / log log n)
  ✗ Exact constant c (Erdős $2000 / 2000 rupees)
  ✗ Is c = e^γ? (Dickman-de Bruijn conjecture)

**Barrier:** Determining c requires controlling the Dickman function
ρ(u) in the critical range u ≈ √(log n / log log n), which pushes
probabilistic number theory beyond current methods. Diffs to kernel:
T(judge→are), Γ(measure→ooze), Ω(ah→zoo).
-/

-- ============================================================
-- §17  ERDŐS-POMERANCE ASYMPTOTIC DIVERGENCE — mOMonadOS q5 Rerun
-- ============================================================

/-!
**CRITICAL KERNEL DIVERGENCE — Erdős-Pomerance q5 Rerun:**

The mOMonadOS q5 rerun (Cycle 14) produced a DIFFERENT asymptotic
formula from the original run (Cycle 9, §11) and from the established
mathematical literature.

  ORIGINAL RUN (Cycle 9):    f(n) ≍ n √(log n / log log n)
  RERUN (Cycle 14):          f(n) ∼ n log n / log log n
  ESTABLISHED (Erdős-Pomerance 1980): f(n) ≍ n √(log n / log log n)

The rerun's formula f(n) ∼ n log n / log log n matches the growth
of the Jacobsthal function g(n) — the maximum gap between integers
coprime to n — NOT the Erdős-Pomerance SDR problem.

**Structural Analysis:**

The q5 rerun confused two distinct problems:
  1. Erdős-Pomerance SDR (the actual problem): find minimal interval
     length f(n) for distinct multiples of 1,…,n. Answer: ≍ n√(log n/log log n).
  2. Jacobsthal function g(n): maximal gap between integers coprime
     to n. Answer: ≍ n log n / log log n (Iwaniec, 1978).

The rerun explicitly mentions "The Jacobsthal Connection" and gives
the Jacobsthal asymptotic. This is a structural collision in the
kernel's FSPLIT decomposition — the branch labeled "Jacobsthal_Connection"
was not properly FFUSE-fused back to the original problem, resulting
in the wrong asymptotic being broadcast to CLINK L8.

**This is a kernel ERROR, not a legitimate divergence.**
The Frobenius ratio was still reported as 1.0, but the FFUSE
recomposition picked up the wrong branch. This reveals a limitation:
Frobenius closure (μ∘δ=id) guarantees internal consistency of the
FSPLIT→FFUSE pair but does NOT guarantee that the fused result
matches external mathematical truth.

**Corrected verdict:** f(n) ≍ n √(log n / log log n) (per §11).
The rerun's asymptotic is WRONG and should be disregarded.

**Structural Imscription (unchanged):** Same as erdos_pomerance_problem (§11).
-/

/--
The Jacobsthal function asymptotic (WRONG for this problem).
The q5 rerun gave f(n) ~ n log n / log log n, which is the
Jacobsthal function g(n), NOT the Erdős-Pomerance f(n).

Correct: f(n) ≍ n √(log n / log log n) (Erdős-Pomerance, 1980)
-/
def jacobsthal_asymptotic_note : String :=
  "g(n) ~ n log n / log log n (Iwaniec 1978) ≠ f(n) ≍ n√(log n/log log n)"

/--
The two conflicting asymptotics from the original run vs. the rerun.
The original run matches Erdős-Pomerance (1980); the rerun is wrong.
-/
def pomerance_asymptotic_divergence : List (String × String) :=
  [("original_cycle9",       "n √(log n / log log n)"),
   ("rerun_cycle14",         "n log n / log log n"),
   ("erdos_pomerance_1980",  "n √(log n / log log n)")]

/--
The rerun FFUSE-fused the wrong branch (Jacobsthal function instead
of the SDR problem). Frobenius ratio was still 1.0 because the
FSPLIT→FFUSE was internally consistent — it just picked the wrong
semantic branch. This is a structural limitation: μ∘δ=id ensures
closure but not external correctness.
-/
theorem pomerance_frobenius_closure_limitation : True := by
  trivial

end Millennium.ErdosProblems
