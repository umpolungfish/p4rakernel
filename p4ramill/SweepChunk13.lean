import Imscribing.Primitives.Types.PrimitiveTypeLoll
import Imscribing.Primitives.Types.PrimitiveTypeMeasure
import Imscribing.Primitives.Types.PrimitiveTypeMime
import Imscribing.Primitives.Types.PrimitiveTypeMonad
import Imscribing.Primitives.Types.PrimitiveTypeNun
import Imscribing.Primitives.Types.PrimitiveTypeOak
import Imscribing.Primitives.Types.PrimitiveTypeOil
import Imscribing.Primitives.Types.PrimitiveTypeOn
import Imscribing.Primitives.Types.PrimitiveTypeOoze
import Imscribing.Primitives.Types.PrimitiveTypeOr
import Imscribing.Primitives.Types.PrimitiveTypeOut
import Imscribing.Primitives.Types.PrimitiveTypePeep
import Imscribing.Primitives.Types.PrimitiveTypeRoar
import Imscribing.Primitives.Types.PrimitiveTypeSo
import Imscribing.Primitives.Types.PrimitiveTypeSure
import Imscribing.Primitives.Types.PrimitiveTypeThey
import Imscribing.Primitives.Types.PrimitiveTypeThigh
import Imscribing.Primitives.Types.PrimitiveTypeTot
import Imscribing.Primitives.Types.PrimitiveTypeUp
import Imscribing.Primitives.Types.PrimitiveTypeVow
import Imscribing.Primitives.Types.PrimitiveTypeWoe
import Imscribing.Primitives.Types.PrimitiveTypeWool
import Imscribing.Primitives.Types.PrimitiveTypeYea
import Imscribing.Primitives.Types.PrimitiveTypeYew
import Imscribing.Primitives.Types.PrimitiveTypeZoo
import Imscribing.ProofTheory
import Imscribing.Quantum.ExcitedStates
import Imscribing.Quantum.FibonacciAnyon
import Imscribing.Quantum.FrobeniusDualPOVM
import Imscribing.Quantum.GateObstruction
import Imscribing.Quantum.GrammarPOVM
import Imscribing.Quantum.OVM
import Imscribing.Quantum.PeriodReadout
import Imscribing.Quantum.WindingLattice
import Imscribing.Quersitanus
import Imscribing.RotatOpOpcode
import Imscribing.Scratch.ProverScratch
import Imscribing.Scratch.ProverScratchB
import Imscribing.Seals
import Imscribing.SerpentRod
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
