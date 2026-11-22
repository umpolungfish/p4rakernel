-- Re-entry of the Schwinger subject's Type assignment.
-- The framework's own checked predicates force two coordinate corrections.
import Imscribing.Primitives.Imscription

open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

namespace SchwingerReentry

/-- Prior assignment: ⟨𐑦𐑸𐑽𐑗𐑐𐑧𐑲𐑵⊙𐑓𐑙𐑟⟩. -/
def prior : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .church,
    fid := .peep, kin := .egg, gran := .ice, gram := .ooze,
    crit := .monad, chir := .fee, stoi := .hung, prot := .zoo }

/-- Re-entered assignment: ⟨𐑦𐑸𐑽𐑹𐑐𐑧𐑲𐑵⊙𐑖𐑙𐑟⟩.
pol 𐑗 → 𐑹 (church → or'), chir 𐑓 → 𐑖 (fee → sure). -/
def corrected : Imscription :=
  { dim := .if', top := .are, rel := .ear, pol := .or',
    fid := .peep, kin := .egg, gran := .ice, gram := .ooze,
    crit := .monad, chir := .sure, stoi := .hung, prot := .zoo }

theorem corrected_topology : ImscriptiveTopology corrected := by
  intro h
  rfl

theorem corrected_closure : ImscriptiveClosure corrected := by
  intro h₁ h₂ h₃
  rfl

theorem corrected_chirality : WindingNeedsChirality corrected := by
  intro h
  decide

theorem prior_violates_closure : ¬ ImscriptiveClosure prior := by
  intro h
  have hp := h rfl rfl (by decide)
  contradiction

theorem prior_violates_chirality : ¬ WindingNeedsChirality prior := by
  intro h
  have hc := h (by decide)
  contradiction

#print axioms corrected_closure
#print axioms corrected_chirality

end SchwingerReentry
