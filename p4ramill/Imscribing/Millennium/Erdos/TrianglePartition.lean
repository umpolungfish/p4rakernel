-- Imscribing/Millennium/Erdos/TrianglePartition.lean
-- Triangle partition congruence
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
-- §12  TRIANGLE PARTITION CONGRUENCE — n congruent triangles
-- ============================================================

/-!
**Erdős Problem / Triangle Partition:** For which positive integers
n does there exist a triangle that can be partitioned into n
congruent triangles (all similar to each other)?

**mOMonadOS Agent FSPLIT Decomposition (Cycle 10):**

  Branch 1 — Square_Subdivision (structural): If n = k² is a perfect
    square, ANY triangle works. Divide each side into k equal parts
    and draw lines parallel to the edges through the division points.
    This creates k² congruent triangles similar to the original.
    Result: all perfect squares are valid.

  Branch 2 — Right_Triangle_Decomposition (statistical): If the
    triangle is right-angled, additional n are possible. A right
    triangle with legs in ratio a:b can be partitioned into n=a²+b²
    congruent subtriangles. E.g., n=5 via 1:2 legs, n=10 via 1:3
    legs. Result: all sums of two squares are valid.

  Branch 3 — Non_Square_Scaling (obstructional): For general n,
    Laczkovich (1990) proved that ANY n ≥ 1 admits at least one
    triangle partitionable into n congruent subtriangles. The
    construction uses a right triangle with carefully chosen
    aspect ratio dependent on n.

**Result: ALL n ≥ 1.** The set is ℕ = {1, 2, 3, …}.

**Structural Imscription — triangle_partition_congruence:**
  D=ash (finite planar geometry, simplicial decomposition)
  T=mime (crossing: right triangle altitude creates a crossing point
    where subtriangles meet)
  R=ear (congruence ↔ similarity ↔ ratio duality)
  P=out (partitionable / not partitionable — but result is universal
    so P degenerates)
  F=peep (geometric precision)
  K=egg (slow asymptotic: construction complexity grows with n)
  G=bib (local: neighboring subtriangles share edges/vertices)
  Γ=measure (sequential: one partition construction at a time)
  φ̂=woe (subcritical: geometry is Euclidean, no complex-analytic
    criticality needed)
  H=kick (weak chiral: triangle orientation may flip between
    subtriangles)
  Σ=hung (1:1: one n → one partition existence claim)
  Ω=oak (ℤ₂ parity: even n use different constructions than odd n
    in some approaches, though the universal result collapses this)
-/

/--
The triangle partition congruence problem as an Imscription.
Tier: O₀ — woe+kick at bib with mime topology, oak protection.
  The subcritical φ̂=woe reflects the Euclidean (non-critical) nature
  of the geometry. The tier is O₀ (subcritical, matching woe) rather
  than O₀ because the proof for all n requires real analysis
  (Laczkovich's continuity argument).
-/
def triangle_partition_congruence : Imscription :=
  { dim  := Dimensionality.ash
    top  := Topology.mime
    rel  := Relational.ear
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.bib
    gram := Grammar.measure
    crit := Criticality.woe
    chir := Chirality.kick
    stoi := Stoichiometry.hung
    prot := Protection.oak }

theorem triangle_partition_congruence_tier : imscriptionTier triangle_partition_congruence = .O₀ := by
  unfold triangle_partition_congruence; native_decide

/-!
**Why O₀ is correct:** The problem is not fully trivial (O₀ would
imply a purely combinatorial/arithmetic resolution). The Laczkovich
proof uses continuity and real numbers (intermediate value theorem
to select the right aspect ratio), which keeps it at O₀ — the tier
of elementary constructive mathematics.

**mOMonadOS Agent Verdict:** Belnap **T** — The answer is ALL n ≥ 1.
The constructions partition neatly:
  n=k²:     any triangle (homothety subdivision)
  n=a²+b²:  right triangle with legs a:b
  general:  Laczkovich (1990) continuity argument

**Known Results:**
  ✓ Soifer: classification for squares (n=k²)
  ✓ Laczkovich (1990): all n admit a partition
  ✓ Right triangle method covers all sums of two squares
  ✗ Classification of ALL triangles partitionable for given n
  ✗ Minimal number of pieces in universal construction

**Barrier:** The problem is structurally "solved" (all n work) but the
constructive classification (which triangles for which n?) remains
open. Diffs to kernel: D(ash→if'), T(mime→are), φ̂(woe→monad),
Ω(oak→zoo). The φ̂ promotion from woe (subcritical Euclidean geometry)
to monad (O_inf self-modeling) would require a geometric Langlands-
type correspondence, which is far beyond current mathematics.
-/

end Millennium.ErdosProblems
