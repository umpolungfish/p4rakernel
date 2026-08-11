-- Imscribing/Millennium/Erdos/SubgroupOrders.lean
-- Subgroup orders of S_n
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
-- §3  SUBGROUP ORDERS OF S_n — STATISTICAL ARITHMETIC
-- ============================================================

/-!
**Problem:** Describe the statistical arithmetic structure of
O_n = { |G| : G ≤ S_n }, the set of subgroup orders of S_n.

Three key results intersect:

  **Erdős–Turán Law (order of a random permutation):**
    (log X_n − (1/2)log²n) / √((1/3)log³n) → N(0,1) as n→∞

  **Landau's g(n):** Maximum element order. log g(n) ∼ √(n log n).

  **Dixon's Theorem:** Two random elements generate A_n or S_n a.a.s.

**Structural Imscription — subgroup_orders_sn:**
  D=array (n→∞), T=judge (heterogeneous subgroup lattice),
  R=tot (functorial inclusion maps), P=out (A_n/S_n dichotomy),
  F=peep (probabilistic precision), K=loll (moderate convergence),
  G=thigh (Landau-PNT coupling at intermediate scale),
  Γ=measure (sequential n→∞), φ̂=roar (Fourier-analytic methods),
  H=sure (persistent chiral), Σ=so (n:n subgroup→order mapping),
  Ω=ah (LCM of cycle lengths = integer winding)
-/

/--
The subgroup orders problem as an Imscription.
Tier: O₂dag (partial resolution: some aspects classified, lattice open).
-/
def subgroup_orders_sn : Imscription :=
  { dim  := Dimensionality.array
    top  := Topology.judge
    rel  := Relational.tot
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.loll
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.roar
    chir := Chirality.sure
    stoi := Stoichiometry.so
    prot := Protection.ah }

theorem subgroup_orders_sn_tier : imscriptionTier subgroup_orders_sn = .O₂dag := by
  unfold subgroup_orders_sn; native_decide

/-!
**mOMonadOS Agent FSPLIT Decomposition (Cycle 3):**

  Branch 1 — Landau_g(n) (structural): Maximal order. Connected to
    PNT via integer partitions: g(n) = max_{fun⊢n} lcm(fun₁,…,λ_k).

  Branch 2 — Random_Permutations (statistical): Erdős–Turán log-normal
    law. The typical order concentrates around exp((1/2)log²n).

  Branch 3 — Partition_Geometry (obstructional): The set O_n is sparse
    in [1,n!]; most integers are NOT subgroup orders. "Fractal clumping."

**Belnap Verdict: B** — Both rigid (g(n) deterministic, transitive
subgroups constrained by n| |G|) and chaotic (Dixon: random subgroups
almost always A_n/S_n). The heavy-tail property: typical order is far
smaller than maximum — gap of ~√(n log n) in the exponent.

**Known Results:**
  ✓ Landau (1903): g(n) asymptotic
  ✓ Erdős–Turán (1967): log-normal limit
  ✓ Dixon (1969): random subgroups → A_n/S_n
  ✓ Pyber (1993): bounds on |Sub(S_n)|
  ✗ Full classification of O_n for all n
  ✗ Sharp constants in Pyber's bounds

**Barrier:** Σ=so (n:n) — the many-to-many subgroup→order mapping
is irreducibly statistical. Diffs to kernel: T(judge→are),
R(tot→ian), Σ(so→up).
-/

end Millennium.ErdosProblems
