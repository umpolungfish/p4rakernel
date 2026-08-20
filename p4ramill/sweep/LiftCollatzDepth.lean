import Imscribing.Millennium.Erdos.CollatzDepthSplit
import Imscribing.Vox.ProofLift
/-!
Lift CollatzDepthSplit into `name<TAB>word<TAB>axioms` for `vox verdict --tsv`.
-/
#eval ProofLift.sweepModule "CollatzDepthSplit"
