import Imscribing.Millennium.SemanticBranchVerifier
import Imscribing.Millennium.SevenFortyFourDecomposition
import Imscribing.Millennium.SpiderMachine
import Imscribing.Millennium.StandardModelFromGrammar
import Imscribing.Millennium.StrongCPClosure
import Imscribing.Millennium.Suffering
import Imscribing.Millennium.SumsetImprovedBounds
import Imscribing.Millennium.SumsetNo3AP
import Imscribing.Millennium.TetractysInit
import Imscribing.Millennium.ThresholdFrobenius
import Imscribing.Millennium.Thresholds
import Imscribing.Millennium.TwinPrime
import Imscribing.Millennium.UnificationConvergence
import Imscribing.Millennium.UnifiedForcing
import Imscribing.Millennium.UniverseRulesets
import Imscribing.Millennium.Unsolved
import Imscribing.Millennium.VAE_Vita_ManuscriptSpine
import Imscribing.Millennium.VAE_Vita_Port
import Imscribing.Millennium.VAE_Vita_SIC_POVM_Bridge
import Imscribing.Millennium.VAE_Vita_Unify
import Imscribing.Millennium.VoidConsensus
import Imscribing.Millennium.WorldReligions
import Imscribing.Millennium.WormwoodRevelation
import Imscribing.Millennium.YM
import Imscribing.Millennium.YM_Closure
import Imscribing.Millennium.YM_GateInhabitants
import Imscribing.Millennium.YM_Mathematical_Witness
import Imscribing.Millennium.YM_Witness
import Imscribing.Millennium.YM_ZFCt_Bridge
import Imscribing.Millennium.Z7StructureConstants
import Imscribing.Millennium.ZFCt_Unified_Bridge
import Imscribing.Millennium.ZaunerEmbeddingEquivalence
import Imscribing.Millennium.ZaunerTransportMap
import Imscribing.Millennium.ZaunerUnitaryConstruction
import Imscribing.Millennium.Zosimos_Stilling
import Imscribing.Millennium.truth
import Imscribing.MoDoT.ManuscriptSpine
import Imscribing.MomonadOS
import Imscribing.MomonadOS.AutopoieticConvergence
import Imscribing.MomonadOS.SheafEnrichedFrobenius
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
