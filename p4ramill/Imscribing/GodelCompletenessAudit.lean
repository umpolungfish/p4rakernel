/-
  Imscribing/GodelCompletenessAudit.lean
  Vox proof-lift audit of GodelCompleteness: emit each proof term's IMASM word so
  `vox verdict` can read whether the proof closes, and list the assumed axioms.
-/

import Imscribing.GodelCompleteness
import Imscribing.Vox.ProofLift

open Imscribing.GodelCompleteness

#lift grammar_godel_complete
#lift godel_fixed_point_in_ambient
#lift godel_absent_from_classical
#lift no_ex_falso
#lift boolean_impossibility
#lift grammar_self_imscribes
#lift godel_gate_reaches_O_inf
#lift crystal_cardinality
#lift grammar_godel_complete_typed

-- CONTROL (run once, recorded here so the library carries no live `sorry`):
--   theorem control_holed : ∃ n, n = n + 1 := by sorry
--   #lift control_holed   ⟶   ⊢∈⊣   ⟶   vox verdict  B  (open: the fork never rejoins)
-- The holed proof reads B; the real theorems below read T (fork closes) or N
-- (forkless direct term). None reads B or F. Corroborated by the kernel:
#print axioms grammar_godel_complete
#print axioms grammar_godel_complete_typed
