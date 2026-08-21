-- Imscribing/Millennium/Erdos/CollatzItem1Meet.lean
--
-- Item 1' carries crit = err.  `absorption_rule_general` says tensoring it with any
-- monad-critical object leaves it at err -- composition cannot move that slot --
-- while `absorption_rule_meet` says the meet does move it.  So this computes the
-- meet, rather than reasoning about it.
--
--   item 1'   ⊢⊙∈≻⊤≺⊥∋⋈⊞◻⊣   ⟨𐑦𐑶𐑾𐑹𐑐𐑘𐑔𐑠𐑻𐑫𐑳𐑭⟩  crystal 16404190
--   canonical I_Dialetheic_Bootstrap  ⟨𐑼𐑸𐑾𐑹𐑐𐑘𐑔𐑠⊙𐑫𐑳𐑭⟩
--
-- They differ in exactly three slots: dim, top, crit.

import Imscribing.Decomposition

namespace Imscribing.Decomposition

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

/-- Item 1' as the instrument derives it. -/
def item1 : Imscription :=
  { dim := if', top := oil, rel := ian, pol := or', fid := peep, kin := yea,
    gran := thigh, gram := measure, crit := err, chir := wool, stoi := up, prot := ah }

/-- The canonical the classifier reports nearest, at distance 3. -/
def bootstrapCanonical : Imscription :=
  { dim := array, top := are, rel := ian, pol := or', fid := peep, kin := yea,
    gran := thigh, gram := measure, crit := monad, chir := wool, stoi := up, prot := ah }

#eval compute_meet item1 bootstrapCanonical
#eval compute_join item1 bootstrapCanonical
#eval (tensorProduct item1 bootstrapCanonical).crit
#eval (compute_meet item1 bootstrapCanonical).crit

/-- The meet moves the criticality slot to monad; the tensor does not. -/
theorem item1_meet_crit : (compute_meet item1 bootstrapCanonical).crit = .monad := by decide

theorem item1_tensor_crit : (tensorProduct item1 bootstrapCanonical).crit = .err := by decide

-- item1 carries wool with yea, so InfiniteMemoryNeedsSlowKinetics refuses it.  That
-- is `wool_yea_refused` in CollatzWordImscription.lean, stated on the two slots the
-- predicate reads; it is not restated here.

end Imscribing.Decomposition
