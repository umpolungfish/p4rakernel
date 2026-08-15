import Imscribing.PowerMath.AndrewsCurtisTheorem
import Imscribing.PowerMath.ArtinSTheoremOnPrimitiveRoots
import Imscribing.PowerMath.BarnetteSTheorem
import Imscribing.PowerMath.BerryTaborTheorem
import Imscribing.PowerMath.BorelTheorem
import Imscribing.PowerMath.BrennanTheorem
import Imscribing.PowerMath.BrocardSTheorem
import Imscribing.PowerMath.CasasAlveroTheorem
import Imscribing.PowerMath.DadeSTheorem
import Imscribing.PowerMath.EilenbergGaneaTheorem
import Imscribing.PowerMath.FarrellJonesTheorem
import Imscribing.PowerMath.FermatNumberCompositenessTheorem
import Imscribing.PowerMath.FugledeSTheorem
import Imscribing.PowerMath.HadamardSMaximalDeterminantTheorem
import Imscribing.PowerMath.HadamardTheorem
import Imscribing.PowerMath.HerzogSchNheimTheorem
import Imscribing.PowerMath.HilbertArnoldTheorem
import Imscribing.PowerMath.InscribedSquareTheoremToeplitzTheorem
import Imscribing.PowerMath.InvariantSubspaceTheorem
import Imscribing.PowerMath.JacobsonSTheorem
import Imscribing.PowerMath.KTheTheorem
import Imscribing.PowerMath.KaplanskySTheorems
import Imscribing.PowerMath.LegendreSTheorem
import Imscribing.PowerMath.LehmerSTheorem
import Imscribing.PowerMath.LonelyRunnerTheorem
import Imscribing.PowerMath.MargulisTheorem
import Imscribing.PowerMath.MckayTheorem
import Imscribing.PowerMath.MlcTheorem
import Imscribing.PowerMath.NoThreeInLineTheorem
import Imscribing.PowerMath.NovikovTheorem
import Imscribing.PowerMath.RokhlinSMultipleMixingTheorem
import Imscribing.PowerMath.RotaSBasisTheorem
import Imscribing.PowerMath.SendovSTheorem
import Imscribing.PowerMath.SerreSTheoremIi
import Imscribing.PowerMath.ShavianDefs
import Imscribing.PowerMath.SmoothFourDimensionalPoincarTheorem
import Imscribing.PowerMath.SunflowerTheorem
import Imscribing.PowerMath.The1323Theorem
import Imscribing.PowerMath.UnionClosedSetsTheorem
import Imscribing.PowerMath.WeinsteinTheorem
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
