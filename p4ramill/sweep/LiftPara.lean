import DeMorganBooleanCentre
import Imscribing.Vox.ProofLift
/-!
Lift the standalone paraconsistent tower at the p4rakernel root — Belnap FOUR,
the Frobenius closure, the classical restriction, the De Morgan centre. These
four sit outside the lakefile, so nothing in the corpus sweep has ever reached
them; this is the first pass.

They import each other by bare module name, so the kernel root must be on
LEAN_PATH for this file to elaborate.
-/
#eval ProofLift.sweepModule "Belnap"
#eval ProofLift.sweepModule "ParaconsistentFrobeniusClosure"
#eval ProofLift.sweepModule "ClassicalRestriction"
#eval ProofLift.sweepModule "DeMorganBooleanCentre"
