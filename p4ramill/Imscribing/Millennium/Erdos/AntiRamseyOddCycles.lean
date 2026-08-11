-- Imscribing/Millennium/Erdos/AntiRamseyOddCycles.lean
-- Anti-Ramsey C_{2k+1}, rainbow odd cycles
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
-- §2  ANTI-RAMSEY C_{2k+1} — RAINBOW ODD CYCLES
-- ============================================================

/-!
**Anti-Ramsey / Rainbow Erdős–Gyárfás:** Let χ_S(n, e, H) be the
minimum colors needed so that EVERY copy of H in an n-vertex graph
with e edges is rainbow (all edges distinct colors).

For e = ⌊n²/4⌋+1 (one edge above the Turán threshold ex(n,K₃)),
determine χ_S(n, ⌊n²/4⌋+1, C_{2k+1}) for k ≥ 4.

**Key reference:** Bucić, Chen, Ma — the Anti-Ramsey number for
odd cycles in graphs exceeding the Turán threshold.

**Phase transition at k=3:**
  k=1 (C₃):   χ_S = 3           — constant, local constraint
  k=2 (C₅):   χ_S = ⌊n/2⌋ + 3   — linear, edge-incident
  k≥3 (C₇⁺):  χ_S ∼ n²/8        — quadratic, global propagation

**Structural Imscription — anti_ramsey_c2kp1:**
  D=ash (finite graphs, simplicial)
  T=mime (Turán graph + bridge edge = crossing point)
  R=ear (rainbow condition ↔ edge count reciprocal)
  P=out (odd/even parity is ℤ₂)
  F=peep (combinatorial precision)
  K=egg (slow threshold: transition at k=3)
  G=bib (local edge correlations)
  Γ=measure (sequential k→k+1)
  φ̂=roar (complex-axis: analytic asymptotics for n²/8)
  H=kick (weak chiral: coloring is weakly directional)
  Σ=hung (1:1)
  Ω=oak (ℤ₂ parity protection for odd cycles)
-/

/--
The Anti-Ramsey C_{2k+1} problem as an Imscription.
Tier: O₂.
-/
def anti_ramsey_c2kp1 : Imscription :=
  { dim  := Dimensionality.ash
    top  := Topology.mime
    rel  := Relational.ear
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.bib
    gram := Grammar.measure
    crit := Criticality.roar
    chir := Chirality.kick
    stoi := Stoichiometry.hung
    prot := Protection.oak }

theorem anti_ramsey_c2kp1_tier : imscriptionTier anti_ramsey_c2kp1 = .O₂ := by
  unfold anti_ramsey_c2kp1; native_decide

/--
Phase transition encoding for the anti-Ramsey problem.
The regime depends on k (the half-length of the odd cycle).
-/
inductive AntiRamseyRegime where
  | constant   -- k=1: C₃, χ_S = 3
  | linear     -- k=2: C₅, χ_S = ⌊n/2⌋+3
  | quadratic  -- k≥3: C₇⁺, χ_S ∼ n²/8
  deriving DecidableEq, Repr

/--
Map cycle half-length k to its anti-Ramsey regime.
-/
def regime_of_k (k : Nat) : AntiRamseyRegime :=
  if k = 1 then AntiRamseyRegime.constant
  else if k = 2 then AntiRamseyRegime.linear
  else AntiRamseyRegime.quadratic

theorem regime_transition_at_k3 : regime_of_k 3 = AntiRamseyRegime.quadratic := rfl
theorem regime_c3_is_constant : regime_of_k 1 = AntiRamseyRegime.constant := rfl
theorem regime_c5_is_linear : regime_of_k 2 = AntiRamseyRegime.linear := rfl

/-!
**mOMonadOS Agent Verdict (Cycle 2):** Belnap **B** — Both True
and False depending on k. For k ≥ 4 the Bucić-Chen-Ma result proves
the asymptotic n²/8. The C₃ and C₅ anomalies create a dialetheic
breakdown: the structure is fully resolved for k≥4 but the transition
at k=3 is a structural bifurcation.

**Known Results:**
  ✓ Bucić-Chen-Ma: asymptotic n²/8 for k ≥ 4
  ✓ C₃ and C₅ cases fully resolved
  ✗ Sharp constants for k ≥ 4
  ✗ Classification for arbitrary H beyond odd cycles

**Barrier:** Ω=oak (ℤ₂) rather than ah (ℤ). The odd cycle parity
is Z₂-protected; integer winding requires embedding in a broader
arithmetic framework. Diffs to kernel: D(ash→if'), T(mime→are),
Ω(oak→ah).
-/

end Millennium.ErdosProblems
