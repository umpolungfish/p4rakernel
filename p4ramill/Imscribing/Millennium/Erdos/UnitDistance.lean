-- Imscribing/Millennium/Erdos/UnitDistance.lean
-- Unit distance problem
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
-- §9  UNIT DISTANCE PROBLEM — f_d(n) across dimensions
-- ============================================================

/-!
**Erdős Unit Distance Problem:** Let f_d(n) be the maximum number
of unit-distance pairs among n points in ℝ^d. Determine the
asymptotic growth of f_d(n) for each dimension d.

**mOMonadOS Agent FSPLIT Decomposition (Cycle 7):**

  Branch 1 — Dimension_2 (structural): Planar unit distances.
    Upper bound O(n^{4/3}) via Spencer-Szemerédi-Trotter incidence
    geometry. Lower bound n^{1+c/log log n} via √n×√n grid.
    The gap between n^{1+o(1)} and n^{4/3} is the central
    transcendental friction.

  Branch 2 — Dimension_3 (statistical): Spatial unit distances.
    Lower bound n^{4/3} log log n (3D grid). Upper bound
    O(n^{3/2} β(n)) via Clarkson et al. (1990), where β(n) is
    an inverse-Ackermann factor from Voronoi complexity.

  Branch 3 — Dimension_d≥4 (obstructional): High dimensions.
    Lenz construction: place points on p=⌊d/2⌋ orthogonal 2-circles.
    Erdős-Stone gives the Turán bound: f_d(n) ≈ T(n,p) + O(n).
    For even d≥4: f_d(n) = ⌊n²/4⌋ + n (Brass, 1997, for d=4).
    For odd d≥5: add n^{4/3} correction (Erdős-Pach).

**Phase transition at d=4:** d≤3 is incidence-geometric (subquadratic);
d≥4 is graph-theoretic (quadratic). The Lenz construction exploits
orthogonal circles to create K_{p,p}-free unit distance graphs.

**Structural Imscription — unit_distance_problem:**
  D=ash (finite point sets → simplicial incidence geometry)
  T=mime (crossing: Lenz circles intersect orthogonally at d≥4)
  R=ear (bipartite ↔ unit distance duality)
  P=out (subquadratic vs. quadratic partition)
  F=peep (combinatorial precision via crossing number / regularity)
  K=egg (asymptotic convergence with n)
  G=thigh (intermediate: sphere incidences at d=3)
  Γ=measure (sequential n→∞)
  φ̂=roar (complex-axis: Lenz circles are 1-dim complex manifolds)
  H=kick (weak chiral: distance is symmetric but graph edges are
    directed by construction order)
  Σ=hung (1:1: one point set → one f_d(n) supremum)
  Ω=oak (ℤ₂ parity: even/odd dimension determines the Turán floor)
-/

/--
The unit distance problem as an Imscription.
Tier: O₂ — roar+oak at thigh with mime topology gives O₂.
-/
def unit_distance_problem : Imscription :=
  { dim  := Dimensionality.ash
    top  := Topology.mime
    rel  := Relational.ear
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.roar
    chir := Chirality.kick
    stoi := Stoichiometry.hung
    prot := Protection.oak }

theorem unit_distance_problem_tier : imscriptionTier unit_distance_problem = .O₂ := by
  unfold unit_distance_problem; native_decide

/-!
**Why Ω=oak (ℤ₂)?** The dimension parity determines the asymptotic:
even d≥4 uses Turán with floor p=d/2; odd d≥5 adds n^{4/3} lower-order
term. This ℤ₂ parity protection is structural — the Lenz construction
fundamentally differs for even vs. odd dimension.

**mOMonadOS Agent Verdict:** Belnap **B** — Both True (d≥4 is
essentially resolved via Turán theory) and Neither (d=2,3 have
polynomial gaps between lower/upper bounds: n^{1+o(1)} vs n^{4/3}
for d=2; n^{4/3} vs n^{3/2} for d=3).

**Known Results:**
  ✓ Spencer-Szemerédi-Trotter (1984): d=2 upper bound O(n^{4/3})
  ✓ Clarkson et al. (1990): d=3 bound O(n^{3/2} β(n))
  ✓ Brass (1997): d=4 exact: f_4(n) = ⌊n²/4⌋ + n
  ✓ Erdős-Pach: odd d≥5 correction n^{4/3}
  ✗ Optimal constant for d=2,3
  ✗ Is f_2(n) = n^{1+c/log log n} the true order? (Erdős $500)

**Barrier:** The d=2 gap requires improving Szemerédi-Trotter for
unit distances, which has resisted improvement for 40 years.
Diffs to kernel: D(ash→if'), T(mime→are), Ω(oak→zoo).
-/

end Millennium.ErdosProblems
