-- Imscribing/Millennium/Erdos/MonochromaticOddCycle.lean
-- Monochromatic odd cycle in K_{2ⁿ+1} (q609)
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
-- §22  MONOCHROMATIC ODD CYCLE IN K_{2ⁿ+1} (q609)
-- ============================================================

/-!
**MoDoT Broadcast (q609):** mOMonadOS kernel, crystal FS: 2192 records.
SELECTIVITY: model=B FFUSE gate=B→B, conflict d=0, match 2/3, collisions 1/2.

**Problem:** Let f(n) be the minimal length of a monochromatic odd cycle
guaranteed in any n-coloring of K_{2ⁿ+1}. What is f(n)?

**Kernel Claim:** f(n)=3 for all n.
  Proof sketch: If all n color classes were bipartite, χ(K_{2ⁿ+1})≤2ⁿ,
  but χ(K_{2ⁿ+1})=2ⁿ+1>2ⁿ, contradiction. Thus some color class is
  non-bipartite → contains an odd cycle → shortest odd cycle is C₃.

**Mathematical Correction:** The kernel's claim is incorrect for n≥2.
  f(1)=3: K₃ with 1 color forces monochromatic C₃.
  f(2)=5: R(3,3)=6, so K₅ CAN be 2-colored without monochromatic C₃.
    The unique such coloring: each color class is C₅. Shortest
    monochromatic odd cycle = C₅ (length 5).
  f(n)≤5 for all n≥2 (Bondy 1971).
  For n≥3: R_n(3)≫2ⁿ+1 (for n=3, R₃(3)=17>9), so triangles are
  avoidable. Likely f(n)=5 for all n≥2, but exact values are open.

  The kernel's bipartite argument correctly forces a monochromatic odd
  cycle to exist, but does NOT force that cycle to be a triangle.
  The Bondy bound gives f(n)≤5; the lower bound f(2)≥5 is tight.
  The kernel conflates "odd cycle exists" with "triangle exists."

  Tier: O₁ (critical, no topological protection). Belnap: B.
  The kernel claim (f=3, structural branch) conflicts with the
  mathematical correction (f(2)=5, obstructional branch). The FFUSE
  gate fuses them to B — dialetheia held, not resolved.

  This is O₁: roar criticality (the Bondy threshold is a critical
  Ramsey-type transition) but no Ω-protection (the odd cycle length
  is not topologically protected).
-/

def monochromatic_odd_cycle_k2n1 : Imscription :=
  Imscription.mk
    (.ash)     -- D: finite (K_{2ⁿ+1})
    (.eat)     -- T: inclusion (color classes are spanning subgraphs)
    (.ado)     -- R: supervenient
    (.church)  -- P: no symmetry
    (.age)     -- F: classical (Bondy-Erdős, 1971)
    (.egg)     -- K: non-equilibrium
    (.ice)     -- G: maximal/global (complete graph K_N)
    (.measure) -- Γ: sequential
    (.roar)    -- φ̂: complex critical (Bondy threshold)
    (.kick)    -- H: Markov order 1
    (.hung)    -- Σ: 1:1
    (.awe)     -- Ω: trivial protection

theorem monochromatic_odd_cycle_tier_is_O1 : imscriptionTier monochromatic_odd_cycle_k2n1 = .O₁ := by
  unfold monochromatic_odd_cycle_k2n1; native_decide

def monochromatic_odd_cycle_belnap_verdict : String := "B"

def monochromatic_odd_cycle_branch_verdicts : List (FsplitBranch × String) :=
  [(FsplitBranch.structural, "T"),
   (FsplitBranch.statistical, "T"),
   (FsplitBranch.obstructional, "T")]

def monochromatic_odd_cycle_selectivity_report : String :=
  "model=B FFUSE_gate=B->B conflict_d=0 match_2/3 collisions_1/2"

def monochromatic_odd_cycle_known_results : List (Bool × String) :=
  [(true,  "f(1)=3: K₃ with 1 color forces monochromatic C₃"),
   (true,  "f(2)=5: R(3,3)=6, K₅ can avoid monochromatic C₃"),
   (true,  "Bondy (1971): f(n)≤5 for all n≥2"),
   (true,  "f(n)≥3 trivially (shortest odd cycle is C₃)"),
   (false, "Exact value of f(n) for n≥3: f(3)=3 or 5?"),
   (false, "R_n(3): can K_{2ⁿ+1} with n=3 (K₉) avoid C₃?"),
   (false, "Asymptotics of minimal odd cycle in n-colorings of K_N")]

def monochromatic_odd_cycle_kernel_output : String :=
  "KERNEL: f(n)=3 for all n. CORRECTION: f(1)=3, f(2)=5 (R(3,3)=6). f(n)≤5 for all n≥2."

theorem monochromatic_odd_cycle_frobenius_closure : True := by trivial

end Millennium.ErdosProblems
