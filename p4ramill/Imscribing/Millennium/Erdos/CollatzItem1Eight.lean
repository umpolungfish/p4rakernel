import Imscribing.Decomposition
namespace Imscribing.Decomposition
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

/-- Item 1' carried on eight IFIX marks: ⊢⊙∈≻⊤≺⊥∋⋈⊞◻◻◻◻◻◻◻◻⊣
    derives ⟨𐑛𐑶𐑾𐑹𐑐𐑪𐑲𐑠𐑻𐑫𐑳𐑭⟩, crystal 3450910.  `dim` is `dead` because the word
    carries exactly one FSPLIT/FFUSE pair -- a point-like fork, which is CLINK L9's
    own ⊢ value. -/
def item1_eight : Imscription :=
  { dim := dead, top := oil, rel := ian, pol := or', fid := peep, kin := on,
    gran := ice, gram := measure, crit := err, chir := wool, stoi := up, prot := ah }

/-- The memory bound ADMITS it: wool with `on` is one of the two the predicate allows,
    where wool with `yea` was refused (`wool_yea_refused`). -/
theorem item1_eight_admitted : InfiniteMemoryNeedsSlowKinetics item1_eight := by decide

/-- And the decomposition bound it feeds: with wool, the predicate is exactly
    kin ∈ {egg, on}. -/
theorem item1_eight_kin : item1_eight.kin = .on := rfl

end Imscribing.Decomposition
