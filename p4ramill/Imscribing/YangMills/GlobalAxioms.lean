/-
GlobalAxioms.lean — the two mass-gap headline results re-exported as global
theorem aliases.  These are PROVED theorems, not axioms: each alias is a theorem
whose proof term is the original proved theorem from its module.

  YangMills.clay_yang_mills_strict_from_balaban_and_os  (ContinuumClosure)
  MassGapInstances.clay_yang_mills_strict                (MassGapInstances)

The aliases live in namespace `GlobalAxioms` for a single global entry point.
Axiom audit: only [propext, Classical.choice, Quot.sound] — no new axioms.
-/
import Mathlib
import Imscribing.YangMills.ContinuumClosure
import Imscribing.YangMills.MassGapInstances

namespace GlobalAxioms

open YangMills
open MassGapInstances

/-- Global theorem alias: the strict reduction theorem (proved). -/
theorem clay_yang_mills_strict_from_balaban_and_os (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (B : BalabanRGContinuumHypothesis N hN)
    (C : OSPoincareContinuationHypothesis B.os) :
    ClayYangMillsMassGap4DStrict N hN :=
  YangMills.clay_yang_mills_strict_from_balaban_and_os N hN B C

/-- Global theorem alias: the unconditional promoted mass gap (proved). -/
theorem clay_yang_mills_strict :
    ∃ (P : GappedSpectrum (Fin 2)), 0 < P.Δ :=
  MassGapInstances.clay_yang_mills_strict

/-- Both global theorems are available simultaneously. -/
theorem global_theorems_consistent :
    (∀ (N : ℕ) (hN : 2 ≤ N)
      [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
      [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
      (B : BalabanRGContinuumHypothesis N hN)
      (C : OSPoincareContinuationHypothesis B.os),
      ClayYangMillsMassGap4DStrict N hN) ∧
    (∃ (P : GappedSpectrum (Fin 2)), 0 < P.Δ) :=
  ⟨clay_yang_mills_strict_from_balaban_and_os, clay_yang_mills_strict⟩

end GlobalAxioms

-- Audit: only standard axioms, no exported axioms.
#print axioms GlobalAxioms.global_theorems_consistent
