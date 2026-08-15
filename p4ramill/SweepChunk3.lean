import Imscribing.Millennium.Erdos.ChromaticOddCycle
import Imscribing.Millennium.Erdos.DifferenceSets
import Imscribing.Millennium.Erdos.ErdosKacInterval
import Imscribing.Millennium.Erdos.ErdosTuranAP
import Imscribing.Millennium.Erdos.MonochromaticOddCycle
import Imscribing.Millennium.Erdos.PolynomAsymptotics
import Imscribing.Millennium.Erdos.PomeranceSDR
import Imscribing.Millennium.Erdos.Problems.Problem0003
import Imscribing.Millennium.Erdos.RamseyAsymptotics
import Imscribing.Millennium.Erdos.RatioSetSharp
import Imscribing.Millennium.Erdos.SchutteTClose
import Imscribing.Millennium.Erdos.SchutteTournament
import Imscribing.Millennium.Erdos.SidonCounting
import Imscribing.Millennium.Erdos.SquarefreePlusPowerOfTwo
import Imscribing.Millennium.Erdos.SquarefreePlusPowerOfTwoClose
import Imscribing.Millennium.Erdos.StrausGreedyFamily
import Imscribing.Millennium.Erdos.SubgroupOrders
import Imscribing.Millennium.Erdos.SumsetAvoidingAP
import Imscribing.Millennium.Erdos.TrianglePartition
import Imscribing.Millennium.Erdos.UnitDistance
import Imscribing.Millennium.ErdosFormalize
import Imscribing.Millennium.ErdosFormalize2
import Imscribing.Millennium.ErdosFormalize3
import Imscribing.Millennium.ErdosProblems
import Imscribing.Millennium.FieldTheoreticMacrocycle
import Imscribing.Millennium.FineStructureConstant
import Imscribing.Millennium.FrobeniusStructure
import Imscribing.Millennium.FrobeniusUnification
import Imscribing.Millennium.GapCompletion
import Imscribing.Millennium.GeneralizedPipeline
import Imscribing.Millennium.GodelCompleteSentence
import Imscribing.Millennium.GodelCompleteUniverse
import Imscribing.Millennium.GodelCompletion
import Imscribing.Millennium.GodelResolvedFinal
import Imscribing.Millennium.Goldbach
import Imscribing.Millennium.GoldbachABC
import Imscribing.Millennium.GrammarBridge
import Imscribing.Millennium.GrammarMetricDerivation
import Imscribing.Millennium.GrammarSICPOVM_ZaunerBridge
import Imscribing.Millennium.GrammarStructuralAnalysis
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
