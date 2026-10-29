import Mathlib
import Imscribing.Biochem.PrimaLogicaMechanicalGlut

/-!
# Residue-level encoding of B-supported secondary structure (SCAFFOLD, NOT COMPILED)

Proposal. For a residue whose evidence for a class is B, the two retained supports
become two quadratic wells over one collective coordinate q, here the Calpha(i)-Calpha(i+2)
distance in angstroms. Typical ideal values are about 5.4 for helix and about 6.5 for strand.
These reference values and the stiffness rule are modelling inputs. They are
assumptions, not results.

  well 1 (affirming support):  rest a = helixRef,  stiffness k1 = 1 + (contacts agreeing)
  well 2 (denying support):    rest b = strandRef, stiffness k2 = 1 + (contacts disagreeing)

epsilon then measures the residual held frustration of that residue. Support does not
verdict on realness: epsilon says how strongly two retained evidence sources pull on
the same coordinate, not that the residue is or is not helical.

Compile in the Imscribing project before relying on it.
-/

namespace Imscribing.PrimaLogica.MechanicalGlut

open Lean Imscribing.PrimaLogica

/-- Reference Calpha(i)-Calpha(i+2) distances (angstroms), modelling inputs. -/
noncomputable def helixRef : ℝ := 5.4
noncomputable def strandRef : ℝ := 6.5

theorem helixRef_ne_strandRef : helixRef ≠ strandRef := by
  unfold helixRef strandRef
  norm_num

/-- Encoding of any Sixteen3 state using contact counts as stiffness weights.
    faithfulBoth holds because the two references differ by construction. -/
noncomputable def residueEncoding (s : Sixteen3) (nAgree nDisagree : ℕ) :
    MechanicalEncoding s where
  k1 := 1 + (nAgree : ℝ)
  k2 := 1 + (nDisagree : ℝ)
  a := helixRef
  b := strandRef
  k1_pos := by positivity
  k2_pos := by positivity
  faithfulBoth := fun _ => helixRef_ne_strandRef

/-- Per-residue frustration is strictly positive whenever the state is Both. -/
theorem residue_frustration_pos (s : Sixteen3) (nA nD : ℕ) (hB : IsBoth s) :
    0 < ((residueEncoding s nA nD).realize hB).epsilon :=
  B_realizes_positive_energy s (residueEncoding s nA nD) hB

/-- Closed form: epsilon = (k1*k2 / (2*(k1+k2))) * (strandRef - helixRef)^2. -/
theorem residue_frustration_formula (s : Sixteen3) (nA nD : ℕ) (hB : IsBoth s) :
    ((residueEncoding s nA nD).realize hB).epsilon =
      ((1 + (nA : ℝ)) * (1 + (nD : ℝ)) /
        (2 * ((1 + (nA : ℝ)) + (1 + (nD : ℝ))))) * (helixRef - strandRef)^2 := by
  rfl

end Imscribing.PrimaLogica.MechanicalGlut
