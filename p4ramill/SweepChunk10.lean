import Imscribing.Paraconsistent.NeutrinoOscillation
import Imscribing.Paraconsistent.NuclearBelnap
import Imscribing.Paraconsistent.OrbitalBelnap
import Imscribing.Paraconsistent.Paraconsistent
import Imscribing.Paraconsistent.ParaconsistentShell
import Imscribing.Paraconsistent.ParaconsistentTopos
import Imscribing.Paraconsistent.Paradice
import Imscribing.Paraconsistent.ParadoxFS
import Imscribing.Paraconsistent.Portal
import Imscribing.Paraconsistent.QCDColorFrustration
import Imscribing.Paraconsistent.QCI_FrobeniusBias
import Imscribing.Paraconsistent.QCI_PvsNP_Bridge
import Imscribing.Paraconsistent.QCI_RH_Bridge
import Imscribing.Paraconsistent.QCI_SICPOVM_Bridge
import Imscribing.Paraconsistent.QCI_Sequences
import Imscribing.Paraconsistent.QCI_YM_Bridge
import Imscribing.Paraconsistent.QCI_nRegister
import Imscribing.Paraconsistent.QuantumClassicalInterface
import Imscribing.Paraconsistent.QuantumGravityBelnap
import Imscribing.Paraconsistent.QuarkBelnap
import Imscribing.Paraconsistent.QuarkFlavor
import Imscribing.Paraconsistent.SelfVerification
import Imscribing.Paraconsistent.SelfVerifyingWASM
import Imscribing.Paraconsistent.Shor.BelnapModExp
import Imscribing.Paraconsistent.Shor.BelnapNFiducial
import Imscribing.Paraconsistent.Shor.BelnapQFT
import Imscribing.Paraconsistent.Shor.BelnapRing2048
import Imscribing.Paraconsistent.Shor.BelnapWHMultilattice
import Imscribing.Paraconsistent.Shor.DialetheicOperator
import Imscribing.Paraconsistent.Shor.FullPipeline
import Imscribing.Paraconsistent.Shor.MZIMesh
import Imscribing.Paraconsistent.Shor.SIC_Multilattice_Proof
import Imscribing.Paraconsistent.StandardModelBelnap
import Imscribing.Paraconsistent.SuperconductingPhase
import Imscribing.Paraconsistent.TenProofs
import Imscribing.Paraconsistent.TernaryTruth
import Imscribing.Paraconsistent.TupleCodec
import Imscribing.ParityIndex
import Imscribing.PhilosophicalSystem
import Imscribing.PowerMath.AbundanceTheorem
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
