import Imscribing.Millennium.OPN_PsiGraph
import Imscribing.Millennium.OPN_Witness
import Imscribing.Millennium.OmegaCorrClosure
import Imscribing.Millennium.OracleDelphi
import Imscribing.Millennium.PMNSFullDerivation
import Imscribing.Millennium.ParadoxBoot
import Imscribing.Millennium.PerfectCuboid
import Imscribing.Millennium.PerfectCuboid.Bootstrap
import Imscribing.Millennium.PerfectCuboid.CaseC
import Imscribing.Millennium.PerfectCuboid.CaseC_Attempt
import Imscribing.Millennium.PerfectCuboid.DescentOperator
import Imscribing.Millennium.PerfectCuboid.DescentTheorem
import Imscribing.Millennium.PerfectCuboid.FactorizationLemma
import Imscribing.Millennium.PerfectCuboid.PerfectCuboidWitness
import Imscribing.Millennium.PerfectCuboid.PrerequisiteLemmasL5_L7
import Imscribing.Millennium.Pkg
import Imscribing.Millennium.PrimitiveBridge
import Imscribing.Millennium.PrimitiveConventionalBridge
import Imscribing.Millennium.PrimordialOoze
import Imscribing.Millennium.ProofModules.DistinctDistances
import Imscribing.Millennium.ProofModules.ErdosFuchs
import Imscribing.Millennium.ProofModules.FurstenbergCorrespondence
import Imscribing.Millennium.ProofModules.FurstenbergSarkozy
import Imscribing.Millennium.ProofModules.HopfPannwitz
import Imscribing.Millennium.ProofModules.HypergraphRamsey
import Imscribing.Millennium.ProofModules.LCMSieve
import Imscribing.Millennium.ProofModules.RamseyGap
import Imscribing.Millennium.ProofModules.RamseyLimit
import Imscribing.Millennium.ProofModules.SumFreeSets
import Imscribing.Millennium.ProofModules.SunflowerProofModule
import Imscribing.Millennium.ProofModules.TrianglePartition
import Imscribing.Millennium.ProofModules.VerifiedConjectures
import Imscribing.Millennium.ProtonElectronMass
import Imscribing.Millennium.PvsNP
import Imscribing.Millennium.PvsNP_Certificates
import Imscribing.Millennium.PvsNP_Structural
import Imscribing.Millennium.PvsNP_Witness
import Imscribing.Millennium.QGUnifiedBridge
import Imscribing.Millennium.RH
import Imscribing.Millennium.RH_GateInhabitants
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
