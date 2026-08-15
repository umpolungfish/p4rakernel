import Imscribing.ManuscriptSpine.QuestionsExtended
import Imscribing.MetaYonedaCollapse
import Imscribing.Millennium.A1A2CoptMacrocycle
import Imscribing.Millennium.AlchemicalHermeticUniverse
import Imscribing.Millennium.BSD
import Imscribing.Millennium.BSD_Complete_Witness
import Imscribing.Millennium.BSD_GateInhabitants
import Imscribing.Millennium.BSD_MathBridge
import Imscribing.Millennium.BSD_Resolution
import Imscribing.Millennium.BSD_Witness
import Imscribing.Millennium.BanachMeasure
import Imscribing.Millennium.Beal
import Imscribing.Millennium.BosonMassRatios
import Imscribing.Millennium.CKMFullDerivation
import Imscribing.Millennium.CMPLX_IMGN
import Imscribing.Millennium.CanonicalOrdinalFaithfulness
import Imscribing.Millennium.Chema
import Imscribing.Millennium.ClayCandidateProfile
import Imscribing.Millennium.ClayCandidateTuples
import Imscribing.Millennium.ClayCanonicalTuples
import Imscribing.Millennium.Clay_TransportedClosure
import Imscribing.Millennium.Clay_UnclosedResistance
import Imscribing.Millennium.Clay_WitnessedClosure
import Imscribing.Millennium.Collatz
import Imscribing.Millennium.CompositionRules
import Imscribing.Millennium.ContinuumMacrocycle
import Imscribing.Millennium.Cosmogeny
import Imscribing.Millennium.Cramer
import Imscribing.Millennium.CrystalBoot
import Imscribing.Millennium.DarkEnergy
import Imscribing.Millennium.DialetheicUniverse
import Imscribing.Millennium.DimensionfulEmission
import Imscribing.Millennium.Dixmier
import Imscribing.Millennium.DualLinkVessel
import Imscribing.Millennium.E8G2_Vessel
import Imscribing.Millennium.E8G2_Vessel_Witnesses
import Imscribing.Millennium.EilenbergGanea
import Imscribing.Millennium.Erdos.AntiRamseyOddCycles
import Imscribing.Millennium.Erdos.Base
import Imscribing.Millennium.Erdos.BinomialGCD
import Imscribing.Vox.ProofLift
/-!
Sweep: lift every theorem THIS repo declares and emit `name<TAB>word<TAB>axioms`
for Vox to verdict in bulk. The lifter is NOT restated here — it lives once, in
`Imscribing.Vox.ProofLift`. Every copy of it that stood in these files was a
generation behind: `isSorry` matched the spelling rather than the axiom, and
`isAssumed` did not exist at all, so a declared axiom lifted to ◻ and read as
proved.
-/
#eval ProofLift.sweepAll
