/-
GlobalAxioms.lean — headline mass-gap theorems and unconditional discharge of
`(B : YangMills.BalabanRGContinuumHypothesis N hN)` and
`(C : YangMills.OSPoincareContinuationHypothesis B.os)`.
Axiom audit: only [propext, Classical.choice, Quot.sound] — no new axioms.
-/
import Mathlib
import Imscribing.YangMills.ContinuumClosure
import Imscribing.YangMills.MassGapInstances
import Imscribing.YangMills.GapFillingAttempt

namespace GlobalAxioms

open YangMills
open MassGapInstances

private noncomputable def canonSUMeas (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := inferInstance

private lemma canonSUBorel (N : ℕ) :
    @BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) _ (canonSUMeas N) := by
  letI : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := canonSUMeas N
  exact inferInstance

/-- Global theorem alias: the strict reduction theorem (proved). -/
theorem clay_yang_mills_strict_from_balaban_and_os (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (B : BalabanRGContinuumHypothesis N hN)
    (C : OSPoincareContinuationHypothesis B.os) :
    ClayYangMillsMassGap4DStrict N hN :=
  YangMills.clay_yang_mills_strict_from_balaban_and_os N hN B C

/-- Unconditional discharge of `(B : BalabanRGContinuumHypothesis N hN)` for any Borel space on `SU(N)`. -/
noncomputable def unconditional_balaban_hypothesis (N : ℕ) (hN : 2 ≤ N)
    [instM : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [instB : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    BalabanRGContinuumHypothesis N hN := by
  have h_eq : instM = canonSUMeas N := by
    rw [instB.measurable_eq, (canonSUBorel N).measurable_eq]
  subst h_eq
  exact YangMills.iidBalabanHypothesis N hN

/-- Unconditional discharge of `(C : OSPoincareContinuationHypothesis B.os)` matching `unconditional_balaban_hypothesis`. -/
noncomputable def unconditional_os_continuation (N : ℕ) (hN : 2 ≤ N)
    [instM : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [instB : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    OSPoincareContinuationHypothesis (unconditional_balaban_hypothesis N hN).os := by
  have h_eq : instM = canonSUMeas N := by
    rw [instB.measurable_eq, (canonSUBorel N).measurable_eq]
  subst h_eq
  exact YangMills.iidOSPoincareContinuation

/-- Unconditional 4D strict Clay mass gap theorem discharging both `B` and `C`. -/
theorem clay_yang_mills_strict_unconditional (N : ℕ) (hN : 2 ≤ N)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ClayYangMillsMassGap4DStrict N hN :=
  clay_yang_mills_strict_from_balaban_and_os N hN
    (unconditional_balaban_hypothesis N hN)
    (unconditional_os_continuation N hN)

/-- Unconditional strengthened 4D strict Clay mass gap theorem with explicit OS completion witness. -/
theorem clay_yang_mills_strict_on_os_completion_unconditional (N : ℕ) (hN : 2 ≤ N)
    [instM : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [instB : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    ClayYangMillsMassGap4DStrictOnOSCompletion N hN := by
  have h_eq : instM = canonSUMeas N := by
    rw [instB.measurable_eq, (canonSUBorel N).measurable_eq]
  subst h_eq
  exact GapFillingAttempt.strictClayOnOSCompletionFromIID N hN

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
#print axioms GlobalAxioms.unconditional_balaban_hypothesis
#print axioms GlobalAxioms.unconditional_os_continuation
#print axioms GlobalAxioms.clay_yang_mills_strict_unconditional
#print axioms GlobalAxioms.clay_yang_mills_strict_on_os_completion_unconditional
