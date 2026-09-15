import Imscribing.SixCoeffFrobenius
import Imscribing.SpectralFace
import Imscribing.TheGrammarAppliedToTheGrammar
import Imscribing.Tier2.CLU_GPM
import Imscribing.TierRefinement
import Imscribing.TimeFixedPoint
import Imscribing.TimeWithinTheStone
import Imscribing.Urbigerus
import Imscribing.UsableZeroPointEnergy
import Imscribing.VaeVitaScaffold
import Imscribing.VesselContent
import Imscribing.VitalNecrosis
import Imscribing.at_home_zpe_scaffold
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
