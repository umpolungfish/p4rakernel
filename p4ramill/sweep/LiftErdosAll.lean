import Imscribing.Classical.ErdosLaxDivergence
import Imscribing.Classical.ErdosProblem16
import Imscribing.Classical.ErdosPropertyP
import Imscribing.Classical.ErdosStrausDecomposition
import Imscribing.Classical.ErdosTuranBound
import Imscribing.Classical.ErdosTuranReduction
import Imscribing.Classical.ErdosTuranSmallC
import Imscribing.Millennium.Erdos.APFreeReduction
import Imscribing.Millennium.Erdos.AdditiveEnergy
import Imscribing.Millennium.Erdos.AntiRamseyOddCycles
import Imscribing.Millennium.Erdos.Base
import Imscribing.Millennium.Erdos.BinomialGCD
import Imscribing.Millennium.Erdos.ChromaticOddCycle
import Imscribing.Millennium.Erdos.CollatzDepthSplit
import Imscribing.Millennium.Erdos.Collatz_Escape_Measure
import Imscribing.Millennium.Erdos.Collatz_Proof_Skeleton
import Imscribing.Millennium.Erdos.Collatz_Unified_Closure
import Imscribing.Millennium.Erdos.DifferenceSets
import Imscribing.Millennium.Erdos.ErdosKacInterval
import Imscribing.Millennium.Erdos.ErdosTuranAP
import Imscribing.Millennium.Erdos.MonochromaticOddCycle
import Imscribing.Millennium.Erdos.PolynomAsymptotics
import Imscribing.Millennium.Erdos.PomeranceSDR
import Imscribing.Millennium.Erdos.Problems.Problem0003
import Imscribing.Millennium.Erdos.Problems.Problem0041
import Imscribing.Millennium.Erdos.Problems.Problem1135
import Imscribing.Millennium.Erdos.RamseyAsymptotics
import Imscribing.Millennium.Erdos.RatioSetSharp
import Imscribing.Millennium.Erdos.SchutteTClose
import Imscribing.Millennium.Erdos.SchutteTournament
import Imscribing.Millennium.Erdos.SidonCounting
import Imscribing.Millennium.Erdos.SquarefreePlusPowerOfTwo
import Imscribing.Millennium.Erdos.StrausGreedyFamily
import Imscribing.Millennium.Erdos.SubgroupOrders
import Imscribing.Millennium.Erdos.SumsetAvoidingAP
import Imscribing.Millennium.Erdos.TrianglePartition
import Imscribing.Millennium.Erdos.UnitDistance
import Imscribing.Millennium.ErdosFormalize
import Imscribing.Millennium.ErdosFormalize2
import Imscribing.Millennium.ErdosFormalize3
import Imscribing.Millennium.ErdosProblems
import Imscribing.Millennium.ProofModules.ErdosFuchs
import Imscribing.NumberTheory.ErdosStrausProof
import Imscribing.Vox.ProofLift
/-!
Lift the active-lakefile Erdős corpus into `name<TAB>word<TAB>axioms` for
`vox verdict --tsv`. `sweepAll`'s `ourDecl` filter checks for a
"Imscribing"/"Millennium"/"IG" NAME prefix, but these files declare into their
own short namespace (`CollatzDepthSplit.foo`, not
`Imscribing.Millennium.Erdos.CollatzDepthSplit.foo`), so it matches nothing
here — `sweepModule` is called once per actual declared namespace instead.
Problem0500, Problem0564, and Problem0593 declare with NO namespace (bare
top-level names) and Problem0564/Problem0593 collide with each other on
`Register`, so none of the three are covered by this pass — they need
individual handling, not a prefix sweep.
-/
#eval ProofLift.sweepModule "Millennium.ErdosProblems"
#eval ProofLift.sweepModule "BloomSisaskSubmitted"
#eval ProofLift.sweepModule "Erdos.RatioSet"
#eval ProofLift.sweepModule "Imscribing.Millennium.Erdos"
#eval ProofLift.sweepModule "Erdos.Sidon"
#eval ProofLift.sweepModule "Erdos.SquarefreePow2"
#eval ProofLift.sweepModule "Erdos.StrausGreedy"
#eval ProofLift.sweepModule "CollatzDepthSplit"
#eval ProofLift.sweepModule "CollatzEscapeMeasure"
#eval ProofLift.sweepModule "CollatzProofSkeleton"
#eval ProofLift.sweepModule "CollatzUnifiedClosure"
#eval ProofLift.sweepModule "Erdos1135"
#eval ProofLift.sweepModule "ErdosFormalize"
#eval ProofLift.sweepModule "Millennium.ProofModules.ErdosFuchs"
#eval ProofLift.sweepModule "ErdosStraus"
#eval ProofLift.sweepModule "Classical.ErdosLaxDivergence"
#eval ProofLift.sweepModule "ErdosProblem16"
#eval ProofLift.sweepModule "Imscribing.Classical.ErdosPropertyP"
#eval ProofLift.sweepModule "Imscribing.Classical.ErdosStrausDecomposition"
#eval ProofLift.sweepModule "Imscribing.Classical.ErdosTuranBound"
#eval ProofLift.sweepModule "Imscribing.Classical"
