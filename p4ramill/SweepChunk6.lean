import Imscribing.Millennium.RH_LeeYang_Bridge
import Imscribing.Millennium.RH_Mathematical_Witness
import Imscribing.Millennium.RH_Witness
import Imscribing.Millennium.RH_ZFCt_Bridge
import Imscribing.Millennium.Rebis
import Imscribing.Millennium.RiemannSIC
import Imscribing.Millennium.RiemannSIC_FullProof
import Imscribing.Millennium.Ring2048_Bridge
import Imscribing.Millennium.RohoncCodexBraiding
import Imscribing.Millennium.RohoncCodexJarlskog
import Imscribing.Millennium.SICFlavorPartition
import Imscribing.Millennium.SIC_D12_ComputableCyclotomic
import Imscribing.Millennium.SIC_D12_Embedding
import Imscribing.Millennium.SIC_D12_Equiangularity
import Imscribing.Millennium.SIC_D12_ExistenceRing
import Imscribing.Millennium.SIC_D12_Field288Test
import Imscribing.Millennium.SIC_D12_Field48Test
import Imscribing.Millennium.SIC_D12_MagnitudeClasses
import Imscribing.Millennium.SIC_D12_Norm
import Imscribing.Millennium.SIC_D12_NumberField
import Imscribing.Millennium.SIC_D12_QuadraticTower
import Imscribing.Millennium.SIC_D12_RayCubic
import Imscribing.Millennium.SIC_D12_RayCubicNF
import Imscribing.Millennium.SIC_D12_RayTower
import Imscribing.Millennium.SIC_D12_SymmetricModuli
import Imscribing.Millennium.SIC_D12_WitnessVessel
import Imscribing.Millennium.SIC_D16_Moduli
import Imscribing.Millennium.SIC_D2048_A0Stratum
import Imscribing.Millennium.SIC_D2048_Moduli
import Imscribing.Millennium.SIC_D2048_Unconditional
import Imscribing.Millennium.SIC_D20_Moduli
import Imscribing.Millennium.SIC_Moduli_Report
import Imscribing.Millennium.SIC_POVM_DualLinkClosure
import Imscribing.Millennium.SIC_POVM_Functor
import Imscribing.Millennium.SIC_POVM_ParityGate
import Imscribing.Millennium.SIC_POVM_Stark
import Imscribing.Millennium.SIC_POVM_Stark_Ob3ect
import Imscribing.Millennium.SIC_StarkUnit
import Imscribing.Millennium.SMUGTConsummation
import Imscribing.Millennium.SacredConvergence
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
