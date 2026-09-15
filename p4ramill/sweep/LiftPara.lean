import Imscribing.Paraconsistent.DeMorganBooleanCentre
import Imscribing.Vox.ProofLift
/-!
Lift the paraconsistent tower now living under Imscribing.Paraconsistent —
Belnap FOUR, the Frobenius closure, the classical restriction, the De Morgan
centre. These four used to sit outside the lakefile at the p4rakernel root,
unreached by the corpus sweep; they were moved into the library and now
import each other by their qualified Imscribing.Paraconsistent module names.
-/
#eval ProofLift.sweepModule "Belnap"
#eval ProofLift.sweepModule "ParaconsistentFrobeniusClosure"
#eval ProofLift.sweepModule "ClassicalRestriction"
#eval ProofLift.sweepModule "DeMorganBooleanCentre"
