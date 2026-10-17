import Imscribing.PowerMath.ZariskiLipmanTheorem
import Imscribing.PrimitiveMismatch
import Imscribing.Primitives.AlchemicalIdentity
import Imscribing.Primitives.BSD_2adic
import Imscribing.Primitives.CLU
import Imscribing.Primitives.Catalog
import Imscribing.Primitives.Core
import Imscribing.Primitives.Crystal
import Imscribing.Primitives.EML
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Lattice
import Imscribing.Primitives.LinearOrder
import Imscribing.Primitives.OPN_2adic
import Imscribing.Primitives.SacredVessel
import Imscribing.Primitives.ScrollInvariant
import Imscribing.Primitives.TierCrossing
import Imscribing.Primitives.Types.PrimitiveTypeAdo
import Imscribing.Primitives.Types.PrimitiveTypeAge
import Imscribing.Primitives.Types.PrimitiveTypeAh
import Imscribing.Primitives.Types.PrimitiveTypeAir
import Imscribing.Primitives.Types.PrimitiveTypeAre
import Imscribing.Primitives.Types.PrimitiveTypeArray
import Imscribing.Primitives.Types.PrimitiveTypeAsh
import Imscribing.Primitives.Types.PrimitiveTypeAwe
import Imscribing.Primitives.Types.PrimitiveTypeBib
import Imscribing.Primitives.Types.PrimitiveTypeChurch
import Imscribing.Primitives.Types.PrimitiveTypeDead
import Imscribing.Primitives.Types.PrimitiveTypeEar
import Imscribing.Primitives.Types.PrimitiveTypeEat
import Imscribing.Primitives.Types.PrimitiveTypeEgg
import Imscribing.Primitives.Types.PrimitiveTypeErr
import Imscribing.Primitives.Types.PrimitiveTypeFee
import Imscribing.Primitives.Types.PrimitiveTypeGag
import Imscribing.Primitives.Types.PrimitiveTypeHaHa
import Imscribing.Primitives.Types.PrimitiveTypeHung
import Imscribing.Primitives.Types.PrimitiveTypeIan
import Imscribing.Primitives.Types.PrimitiveTypeIce
import Imscribing.Primitives.Types.PrimitiveTypeIf
import Imscribing.Primitives.Types.PrimitiveTypeJudge
import Imscribing.Primitives.Types.PrimitiveTypeKick
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
