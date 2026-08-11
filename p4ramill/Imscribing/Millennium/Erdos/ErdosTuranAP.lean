-- Imscribing/Millennium/Erdos/ErdosTuranAP.lean
-- Erdős–Turán conjecture on arithmetic progressions
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §1  ERDŐS–TURÁN CONJECTURE ON ARITHMETIC PROGRESSIONS
-- ============================================================

/-!
**Erdős–Turán Conjecture (1936):** If A ⊆ ℕ has Σ_{a∈A} 1/a = ∞,
then A contains arithmetic progressions of every length k ≥ 3.

**Resolution:** Szemerédi's Theorem (1975) proved this for all k.
Green-Tao (2008) extended to the primes via transference principle.

**Structural Imscription — erdos_turan_ap:**
  D=array (infinite sequences in ℕ)
  T=oil (integer lattice)
  R=ear (reciprocal sum ↔ density coupling)
  P=out (ℤ₂: set either has APs or does not)
  F=peep (ergodic/measure-theoretic precision)
  K=egg (slow density threshold)
  G=thigh (intermediate correlation range)
  Γ=measure (sequential: k=3→4→… iterative proof)
  φ̂=roar (complex-axis criticality: ζ-function circle method)
  H=sure (persistent chiral: AP search is directional)
  Σ=hung (1:1: one divergent sum maps to one AP existence claim)
  Ω=ah (integer winding: AP length k is a ℤ-valued parameter)
-/

/--
The Erdős–Turán conjecture as an Imscription.
Tier: O₂dag (not O₂ because roar+ah at thigh creates a dagger-crossing).
-/
def erdos_turan_ap : Imscription :=
  { dim  := Dimensionality.array
    top  := Topology.oil
    rel  := Relational.ear
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.egg
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.roar
    chir := Chirality.sure
    stoi := Stoichiometry.hung
    prot := Protection.ah }

theorem erdos_turan_ap_tier : imscriptionTier erdos_turan_ap = .O₂dag := by
  unfold erdos_turan_ap; native_decide

/-!
**mOMonadOS Agent FSPLIT Decomposition (Cycle 1):**

  Branch 1 — Reciprocal_Sum (structural): the divergence condition
    Σ 1/a_n = ∞. It is NOT equivalent to positive density in some
    subsequence — the primes diverge and have density zero, which is
    what Branch 3 says. The two branches contradicted each other in
    this docstring; divergence is strictly weaker, and that weakness
    is the whole difficulty.

  Branch 2 — Arithmetic_Progressions (statistical): Szemerédi's
    theorem — any subset of ℕ with positive upper density contains
    arbitrarily long APs.

  Branch 3 — Combinatorial_Density (obstructional): The gap — not
    all sets with divergent reciprocal sum have positive upper
    density (e.g., primes). Green-Tao transference bridges this gap.

**Belnap Verdict: B** — and the reason recorded was wrong. It said
"Both True (Szemerédi proved it)". Szemerédi's theorem is about sets of
positive upper density; the Erdős–Turán conjecture is about sets with
divergent reciprocal sum, which is a weaker hypothesis, so Szemerédi
does not prove it. The conjecture is OPEN. What is True is k=3, settled
by Bloom–Sisask in 2020; what is Neither is every k ≥ 4.

**Known Results** (✓✓ = machine-checked here, ✓ = cited):
  ✓✓ Roth (1953), k=3 for positive density — Mathlib's
     `roth_3ap_theorem_nat`, instantiated below as `dense_has_3ap`
  ✓✓ Roth asymptotically: the 3AP-free density tends to 0 —
     `rothNumberNat_isLittleO_id`, below as `roth_density_tendsto_zero`
  ✓✓ Behrend (1946): and it tends to 0 slower than any power —
     `Behrend.roth_lower_bound`, below as `behrend_lower_bound`
  ✓  Szemerédi (1969): k=4; Szemerédi (1975): all k — not in Mathlib
  ✓  Furstenberg (1977): ergodic proof for all k
  ✓  Gowers (2001): explicit bounds via U^k norms
  ✓  Green-Tao (2008): primes contain arbitrarily long APs
  ✓  Bloom–Sisask (2020): the Erdős–Turán conjecture for k=3 — the
     first non-trivial case, and the only one settled
  ✗  Erdős–Turán for any k ≥ 4: OPEN

**Barrier:** Distance to O_inf kernel: T(oil→are), Γ(measure→ooze),
Ω(ah→zoo). The transference principle closes the Frobenius loop
only for dense models; the sparse-to-dense embedding is not
functorial in general.
-/


/-! ### k = 3, machine-checked

Mathlib carries Roth's theorem and Behrend's construction, so the `k = 3` row of
the table above need not be a citation. Both directions are instantiated here:
the density of a progression-free subset of `[0,n)` tends to zero, and it does
so slower than any power of `n`.

Nothing here touches the Erdős–Turán conjecture itself, which concerns the
weaker hypothesis `Σ 1/aₙ = ∞`. Its `k = 3` case is Bloom–Sisask; `k ≥ 4` is
open. The distinction is the one this file previously collapsed.
-/

namespace ErdosTuran

open Finset Asymptotics Filter

/-- **Roth's theorem.** Past the corners bound, a subset of `[0,n)` of density
at least `ε` cannot be free of three-term progressions. -/
theorem dense_has_3ap {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : cornersTheoremBound (ε / 3) ≤ n) (A : Finset ℕ) (hA : A ⊆ Finset.range n)
    (hcard : ε * n ≤ #A) : ¬ ThreeAPFree (A : Set ℕ) :=
  roth_3ap_theorem_nat ε hε hn A hA hcard

/-- The same, asymptotically: the largest progression-free subset of `[0,N)` has
density tending to zero. -/
theorem roth_density_tendsto_zero :
    IsLittleO atTop (fun N ↦ (rothNumberNat N : ℝ)) (fun N ↦ (N : ℝ)) :=
  rothNumberNat_isLittleO_id

/-- **Behrend's lower bound.** The decay is slower than any power of `N`, so
Roth's theorem cannot be improved to a polynomial saving. -/
theorem behrend_lower_bound (N : ℕ) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤ rothNumberNat N :=
  Behrend.roth_lower_bound

#print axioms dense_has_3ap
#print axioms behrend_lower_bound

end ErdosTuran

/--
Belnap verdicts for the Erdős–Turán FSPLIT branches.
structural=T, statistical=T, obstructional=B (dialetheic).
-/
def erdos_turan_belnap_verdicts : List (FsplitBranch × String) :=
  [(FsplitBranch.structural, "T"),
   (FsplitBranch.statistical, "T"),
   (FsplitBranch.obstructional, "B")]

end Millennium.ErdosProblems
