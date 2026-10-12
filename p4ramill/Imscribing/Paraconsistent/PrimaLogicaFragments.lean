import Imscribing.Paraconsistent.PrimaLogicaWinding

/-!
# Prima Logica: L3 Kleen, L4 FDE, L5 LP

C. Lando Mills — supplementary formalization.

The author's terminology is retained exactly:
  L3 = Kleen: {N,T,F}.
  L4 = FDE: {N,T,F,B}.
  L5 = LP: BNTF + Inclosure.

The L5 LP structure is the native SIXTEEN_3 register space together with the
ordered Inclosure operation `lpInclosure` in PrimaLogicaWinding. L5 LP is the
full process, not a renaming of an auxiliary three-value subtype.

The auxiliary (T,F,B) and definite (T,F) value subtypes below are included
only for carrier-level comparison. They do not rename L5 LP. The fork's
existing restriction and Boolean-centre proofs remain in force.
-/

namespace Imscribing.PrimaLogica

open Lean Imscribing.NSReentry Imscribing.Paraconsistent

/-- L3 Kleen: the N,T,F carrier. -/
abbrev ThreeGapCarrier := {v : Belnap // v ≠ Belnap.B}

/-- Auxiliary T,F,B carrier; not the L5 LP construction. -/
abbrev ThreeGlutCarrier := {v : Belnap // v ≠ Belnap.N}

/-- The two definite values. -/
abbrev TwoDefiniteCarrier := {v : Belnap // v = Belnap.T ∨ v = Belnap.F}

/-- L4 FDE: the four-value BNTF carrier is the existing Belnap type. -/
abbrev FourCarrier := Belnap

/-- L3 = Kleen, expressed as the existing N,T,F carrier. -/
abbrev L3_Kleen := ThreeGapCarrier

/-- L4 = FDE, expressed as the full N,T,F,B carrier. -/
abbrev L4_FDE := FourCarrier

/-- L5 = LP is defined by `L5_LP` + `lpInclosure` in PrimaLogicaWinding.
    Its terminal register is `unifiedB`, and its five stages are `stage 0` to `stage 4`. -/
theorem L5_LP_terminal_is_unifiedB : stage 4 = unifiedB := rfl

/-- Each three-valued carrier is literally included in FOUR. -/
def gapIntoFour (v : ThreeGapCarrier) : FourCarrier := v.1
def glutIntoFour (v : ThreeGlutCarrier) : FourCarrier := v.1

/-- Their carrier inclusions are injective. -/
theorem gapIntoFour_injective : Function.Injective gapIntoFour := by
  intro x y h
  exact Subtype.ext h

theorem glutIntoFour_injective : Function.Injective glutIntoFour := by
  intro x y h
  exact Subtype.ext h

/-- The definite fragment embeds into both three-valued carriers. -/
def definiteIntoGap (v : TwoDefiniteCarrier) : ThreeGapCarrier :=
  ⟨v.1, by
    rcases v.2 with h | h
    · simp [h]
    · simp [h]⟩

def definiteIntoGlut (v : TwoDefiniteCarrier) : ThreeGlutCarrier :=
  ⟨v.1, by
    rcases v.2 with h | h
    · simp [h]
    · simp [h]⟩

theorem definite_agrees_in_four (v : TwoDefiniteCarrier) :
    gapIntoFour (definiteIntoGap v) = glutIntoFour (definiteIntoGlut v) := rfl

/-- A value in the gap-carrier is necessarily N, T, or F. -/
theorem gap_values_exhaustive (v : ThreeGapCarrier) :
    v.1 = Belnap.N ∨ v.1 = Belnap.T ∨ v.1 = Belnap.F := by
  rcases v with ⟨x, hx⟩
  cases x <;> simp_all <;> exact hx rfl

/-- A value in the glut-carrier is necessarily T, F, or B. -/
theorem glut_values_exhaustive (v : ThreeGlutCarrier) :
    v.1 = Belnap.T ∨ v.1 = Belnap.F ∨ v.1 = Belnap.B := by
  rcases v with ⟨x, hx⟩
  cases x <;> simp_all <;> exact hx rfl

/-- Every Belnap value's native singleton is included in full Inclosure. -/
theorem every_singleton_below_complete (v : Belnap) :
    Sixteen3.le_i (kernelSingleton v) complete = true := by
  cases v <;> rfl

/-- The three-member stage contains exactly the named carrier memberships. -/
theorem three_member_stage :
    (stage 3).hasN = true ∧ (stage 3).hasT = true ∧
    (stage 3).hasF = true ∧ (stage 3).hasB = false := by
  decide

/-- The terminal stage retains every membership. -/
theorem four_member_stage :
    (stage 4).hasN = true ∧ (stage 4).hasT = true ∧
    (stage 4).hasF = true ∧ (stage 4).hasB = true := by
  decide

end Imscribing.PrimaLogica
