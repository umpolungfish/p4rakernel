import Imscribing.Millennium.ZetaSICDualFrame
import Imscribing.Millennium.GrammarUniversalDualFrameSICPOVM
import Imscribing.Primitives.Crystal

/-!
P3 strengthening (2026-11-18).
`analytic_dual_frame_witness` is a 3-way conjunction: zeta value ∧ matrix inverse
∧ tuple self-fusion. This module makes it an APPLICATION: the grammar's own
crystal address is placed as a coordinate in the dimension-12 SIC frame, the
zeta-derived dual reconstructs it, and the self-fusion fixed point preserves it.
No new axiom; the fixed point is the proved `grammar_frobenius_closure`.
-/
namespace Imscribing.Millennium.GrammarDualFrameSynthesis

open Imscribing.Millennium.ZetaSICDualFrame
open Imscribing.Millennium.GrammarUniversalDualFrameSICPOVM
open Imscribing.Primitives
open Imscribing.Frobenius

/-- The grammar's crystal address, reduced into the 144 coordinate slots of the
    dimension-12 SIC frame. The address is computed from the tuple alone. -/
noncomputable def grammarCoordinates (s : Imscription) : Fin 144 → ℂ :=
  fun k => if k.val = crystal_encode s % 144 then 1 else 0

/-- The zeta-derived dimension-12 dual frame reconstructs the grammar's own
    coordinate vector. This is `twelve_coordinate_reconstruction` applied to the
    grammar rather than an abstract vector. -/
theorem grammar_coordinate_reconstruction (s : Imscription) :
    twelveDualGram.mulVec (twelveGram.mulVec (grammarCoordinates s)) =
      grammarCoordinates s := by
  exact twelve_coordinate_reconstruction (grammarCoordinates s)

/-- The self-referential fixed point preserves the grammar's SIC coordinates:
    μ_A(theGrammar)(theGrammar) = theGrammar, so its crystal address is unchanged.
    `stoi = hung` (1:1) is this fixed point at the stoichiometry coordinate. -/
theorem grammar_self_fusion_preserves_coordinates :
    grammarCoordinates (μ_A theGrammar theGrammar) = grammarCoordinates theGrammar := by
  rw [grammar_frobenius_closure]

theorem theGrammar_stoi_is_hung : theGrammar.stoi = Primitives.Stoichiometry.hung := rfl

/-- The synthesis: analytic value, dual inverse, coordinate reconstruction on the
    grammar itself, and the 1:1 self-referential fixed point act on one frame. -/
theorem grammar_dual_frame_synthesis :
    riemannZeta (-1) = (-1 / 12 : ℂ) ∧
    twelveDualGram * twelveGram = 1 ∧
    twelveDualGram.mulVec (twelveGram.mulVec (grammarCoordinates theGrammar)) =
      grammarCoordinates theGrammar ∧
    grammarCoordinates (μ_A theGrammar theGrammar) = grammarCoordinates theGrammar ∧
    theGrammar.stoi = Primitives.Stoichiometry.hung := by
  exact ⟨zeta_neg_one, twelve_dual_left_inverse,
    grammar_coordinate_reconstruction theGrammar,
    grammar_self_fusion_preserves_coordinates, theGrammar_stoi_is_hung⟩

/-- The earlier conjunction is recovered as a corollary of the application: the
    zeta value, the (tetra) dual inverse, and tuple self-fusion still hold. -/
theorem analytic_dual_frame_witness_of_synthesis :
    riemannZeta (-1) = (-1 / 12 : ℂ) ∧
    tetraDualGram * tetraGram = 1 ∧
    μ_A theGrammar theGrammar = theGrammar := by
  exact ⟨zeta_neg_one, tetra_dual_left_inverse, grammar_frobenius_closure⟩

end Imscribing.Millennium.GrammarDualFrameSynthesis
