import Imscribing.BCReentryBounded

/-!
Native adapter TEMPLATE for the fork; requires src/Lean/Sixteen3.lean.
This is not compiled here. Inspect the fork API and adjust membership syntax.
-/

namespace BCReentry

/-- Minimal Sixteen3 structure for compilation; replace with fork's actual type. -/
structure Sixteen3 : Type where
  hasN : Bool
  hasT : Bool
  hasF : Bool
  hasB : Bool

/-- Provisional mapping of native fields to four binary selections. -/
def nativeMembership (v : Sixteen3) : Fin 4 → Bool
  | ⟨0, _⟩ => v.hasN
  | ⟨1, _⟩ => v.hasT
  | ⟨2, _⟩ => v.hasF
  | _ => v.hasB

/-- The exact native transport theorem to discharge against the fork. -/
theorem ofMask_transport (n : Fin 16) (i : Fin 4) :
    nativeMembership (⟨false, false, false, false⟩ : Sixteen3) i = selected n.val i := by
  -- Supply a proof after validating `ofMask` and field signatures.
  -- Deliberately leave the integration obligation unproved, rather than
  -- admitting an axiom or presenting a fictitious certificate.
  sorry

end BCReentry