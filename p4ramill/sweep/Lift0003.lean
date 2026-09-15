import Imscribing.Millennium.Erdos.Problems.Problem0003
import Imscribing.Vox.ProofLift
/-!
Lift Problem0003, one module, into `name<TAB>word<TAB>axioms` for `vox verdict --tsv`.

Per module, not per corpus: importing everything into one environment is blocked
by name collisions, and the lift never needed it. The lifter is not restated here.
-/
#eval ProofLift.sweepModule "Millennium.ErdosProblems"
