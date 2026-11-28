/-
GapFillingAttempt.lean

Instantiates the conditional strict Clay theorems (`0 sorry`) using
`YangMills.iidBalabanHypothesis` (from `BalabanFromStage.lean`) and
`YangMills.iidOSPoincareContinuation` (from `IIDPoincareContinuation.lean`).
-/

import Imscribing.YangMills.ContinuumClosure
import Imscribing.YangMills.IIDOS
import Imscribing.YangMills.SchwingerConv
import Imscribing.YangMills.BalabanFromStage
import Imscribing.YangMills.IIDPoincareContinuation

namespace GapFillingAttempt

open YangMills

/-- Concrete Balaban RG Continuum Hypothesis targeting `iidOS4DStrict` (`Δ_phys = 1`). -/
noncomputable def iidBalabanHypothesis (N : ℕ) (hN : 2 ≤ N) :
    BalabanRGContinuumHypothesis N hN :=
  YangMills.iidBalabanHypothesis N hN

/-- Concrete OS Poincaré Continuation Hypothesis for `iidOS4DStrict`. -/
noncomputable def iidPoincareContinuation :
    OSPoincareContinuationHypothesis iidOS4DStrict :=
  YangMills.iidOSPoincareContinuation

/-- Strict Clay target from the concrete stage hypothesis and OS continuation. -/
theorem strictClayFromIID (N : ℕ) (hN : 2 ≤ N) :
    ClayYangMillsMassGap4DStrict N hN :=
  clay_yang_mills_strict_from_balaban_and_os N hN
    (iidBalabanHypothesis N hN)
    (iidPoincareContinuation)

/-- Strengthened strict Clay target (with explicit OS completion witness). -/
theorem strictClayOnOSCompletionFromIID (N : ℕ) (hN : 2 ≤ N) :
    ClayYangMillsMassGap4DStrictOnOSCompletion N hN :=
  clay_yang_mills_strict_on_os_completion_from_balaban_and_os N hN
    (iidBalabanHypothesis N hN)
    (iidPoincareContinuation)

end GapFillingAttempt
