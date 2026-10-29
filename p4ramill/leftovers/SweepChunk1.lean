import Imscribing.Classical.RamseyAsymptotics
import Imscribing.Classical.RepresentationParity
import Imscribing.Classical.SidonRepresentation
import Imscribing.Classical.Solitary10
import Imscribing.Classical.Szemeredi
import Imscribing.Classical.TriangleTiling
import Imscribing.Classical.UnitDistanceDiameterOne
import Imscribing.Classical.UnitDistancePhaseTransition
import Imscribing.Classical.WindowedBound
import Imscribing.Coagula.Polymer
import Imscribing.CollatzOperationalized
import Imscribing.ColoursGreatWork
import Imscribing.CompletingD2048InD12
import Imscribing.Consciousness
import Imscribing.Decomposition
import Imscribing.EudoxusSixKeys
import Imscribing.EulerInvariant
import Imscribing.FrancisBacon
import Imscribing.FrancisBaconGold
import Imscribing.Frobenius
import Imscribing.GateOrdering
import Imscribing.GeneToProtein
import Imscribing.GeneticCode
import Imscribing.HermeticVesselPolymer
import Imscribing.HowDiracEquationArise
import Imscribing.HowHilbertQMArise
import Imscribing.HowInductionArise
import Imscribing.HowNaturalNumbersArise
import Imscribing.HowProbabilityArise
import Imscribing.IGFunctor
import Imscribing.IGMorphism
import Imscribing.IGScaffold
import Imscribing.IG_Algebra
import Imscribing.IMASM.BankedWeight
import Imscribing.Isomorphisms
import Imscribing.JohnFrench
import Imscribing.LandoMills
import Imscribing.LiarIdempotent
import Imscribing.LiminalSpaces
import Imscribing.ManuscriptSpine.Questions
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
