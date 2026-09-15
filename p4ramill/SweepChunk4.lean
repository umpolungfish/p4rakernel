import Imscribing.Millennium.GrammarUniversalDualFrameSICPOVM
import Imscribing.Millennium.GravitationalCoupling
import Imscribing.Millennium.GrothendieckA
import Imscribing.Millennium.HadwigerNelson
import Imscribing.Millennium.Hodge
import Imscribing.Millennium.Hodge_AlgebraicCycleConstruction
import Imscribing.Millennium.Hodge_Descent
import Imscribing.Millennium.Hodge_GateInhabitants
import Imscribing.Millennium.Hodge_Grammar
import Imscribing.Millennium.Hodge_KernelCrossing
import Imscribing.Millennium.Hodge_Mathematical_Witness
import Imscribing.Millennium.Hodge_RegulatorSurjectivity
import Imscribing.Millennium.Hodge_ThresholdCrossing
import Imscribing.Millennium.Hodge_Witness
import Imscribing.Millennium.HolonomyWinding
import Imscribing.Millennium.HornTorusEmission
import Imscribing.Millennium.HornTorusModularForm
import Imscribing.Millennium.HubbleConstant
import Imscribing.Millennium.IGThresholdAnalysis
import Imscribing.Millennium.ImaginaryNumbers
import Imscribing.Millennium.InflationarySlowRoll
import Imscribing.Millennium.LeeYang_Xi_Product_Construction
import Imscribing.Millennium.Lefschetz11
import Imscribing.Millennium.Lefschetz11_Grammar
import Imscribing.Millennium.LeptonMassRatios
import Imscribing.Millennium.LonelyRunner
import Imscribing.Millennium.Macrocycle107_1135_713
import Imscribing.Millennium.MacrocyclicClosure
import Imscribing.Millennium.MajoranaPhases
import Imscribing.Millennium.Manuscript_ZFCt
import Imscribing.Millennium.Master_Witness
import Imscribing.Millennium.MathProof
import Imscribing.Millennium.NS
import Imscribing.Millennium.NS_CriticalBound
import Imscribing.Millennium.NS_Mathematical_Witness
import Imscribing.Millennium.NS_Resolution
import Imscribing.Millennium.NS_Seige
import Imscribing.Millennium.NS_Witness
import Imscribing.Millennium.NS_ZFCt_Bridge
import Imscribing.Millennium.OPN
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
