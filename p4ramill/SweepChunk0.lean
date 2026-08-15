import Imscribing.AFDMC_MBL_Cohomology
import Imscribing.AgentSelf
import Imscribing.Agricola
import Imscribing.Algebra
import Imscribing.ArsAnimaglyphica
import Imscribing.ArsCrossDomain
import Imscribing.ArsFungiglyphica
import Imscribing.AtHomeSanguineHomunculus
import Imscribing.AutopoieticConvergence_UPDATED
import Imscribing.AxiomD_Demotion
import Imscribing.B4FactorBootstrap
import Imscribing.Barriers
import Imscribing.Basic
import Imscribing.BasilValentine
import Imscribing.BooksOfJeu
import Imscribing.BootstrapSequence
import Imscribing.BotanicalWalkthrough
import Imscribing.BoundaryOperators
import Imscribing.BruceCodex.BooksOfJeu
import Imscribing.BruceCodex.UntitledText
import Imscribing.CL9NK_Chain
import Imscribing.CLINK
import Imscribing.CLINK_L9
import Imscribing.CLU744Bridge
import Imscribing.CatalogImmutability
import Imscribing.CirculatumMinus
import Imscribing.Classical.APIntersectingFamily
import Imscribing.Classical.BoseChowla
import Imscribing.Classical.DifferenceSetSyndetic
import Imscribing.Classical.ErdosLaxDivergence
import Imscribing.Classical.ErdosProblem16
import Imscribing.Classical.ErdosPropertyP
import Imscribing.Classical.ErdosStrausDecomposition
import Imscribing.Classical.ErdosTuranBound
import Imscribing.Classical.ErdosTuranReduction
import Imscribing.Classical.ErdosTuranSmallC
import Imscribing.Classical.HajnalSpecker
import Imscribing.Classical.HeckeLandau
import Imscribing.Classical.InfiniteSidon
import Imscribing.Classical.MatchingSDR
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
