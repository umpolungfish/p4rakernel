import Mathlib
import Imscribing.Millennium.ZetaSICDualFrame
import Imscribing.Millennium.SourceBraidSICContraction

/-!
Stage 5: transport of ordered source operators through the **existing** SIC
coordinate reconstruction. No new SIC existence claim is made here.

The 144-coordinate map is the Gram-coordinate map already established by
ZetaSICDualFrame.lean. The executable Python tool uses its real rational
restriction, scaled by 1/12 when interpreting reference-projector mixtures
as SIC probabilities. Its domain is carefully narrower than arbitrary
continuum- or physically realizable channel claims.

This file must be compiled inside G-mOMonadOS, where the imported project
modules and the user's Gram/SIC existence foundations are available.
-/

namespace Imscribing.Millennium.WhorlSICTransport

open Matrix
open Imscribing.Millennium.ZetaSICDualFrame
open Imscribing.SourceBraidSICContraction

abbrev Coords144 := Fin 144 → ℂ

/-- Encode coordinate coefficients in the established 144-coordinate Gram frame. -/
noncomputable def analyze144 (c : Coords144) : Coords144 :=
  twelveGram.mulVec c

/-- Synthesize coefficients using the established exact dual Gram frame. -/
noncomputable def synthesize144 (p : Coords144) : Coords144 :=
  twelveDualGram.mulVec p

/-- Reuse the user's existing left-inverse theorem. -/
theorem synthesize_analyze144 (c : Coords144) :
    synthesize144 (analyze144 c) = c := by
  exact twelve_coordinate_reconstruction c

theorem analyze144_injective : Function.Injective analyze144 := by
  intro a b h
  have h' := congrArg synthesize144 h
  simpa only [synthesize_analyze144] using h'

/-- An arbitrary source transformation transported through the SIC analysis. -/
noncomputable def transport144 (f : Coords144 → Coords144)
    (p : Coords144) : Coords144 :=
  analyze144 (f (synthesize144 p))

/-- Every source transformation commutes with its transported version on valid
    analyzed states, without asserting the map is a quantum channel. -/
theorem transport144_on_image (f : Coords144 → Coords144) (c : Coords144) :
    transport144 f (analyze144 c) = analyze144 (f c) := by
  simp only [transport144, synthesize_analyze144]

/-- Sequential source operations remain sequential when transported. -/
theorem transport144_comp_on_image (f g : Coords144 → Coords144)
    (c : Coords144) :
    transport144 f (transport144 g (analyze144 c)) =
      transport144 (f ∘ g) (analyze144 c) := by
  rw [transport144_on_image]
  rw [transport144_on_image]
  rw [transport144_on_image]
  rfl

/-- If two operations disagree before SIC analysis, their analyzed results
    disagree as well. This preserves *operational order*, not just state. -/
theorem transport144_detects_order (f g : Coords144 → Coords144)
    (c : Coords144) (h : f c ≠ g c) :
    transport144 f (analyze144 c) ≠ transport144 g (analyze144 c) := by
  intro he
  apply h
  apply analyze144_injective
  simpa only [transport144_on_image] using he

/-- Base-12 SIC label format: one lane digit is the row, the other the column.
    This is *ordered*, so swapping the lanes changes the label in general. -/
def laneSwapLabel (i : Fin 144) : Fin 144 :=
  ⟨12 * (i.val % 12) + i.val / 12, by
    have hi := i.isLt
    omega⟩

theorem laneSwapLabel_involution (i : Fin 144) :
    laneSwapLabel (laneSwapLabel i) = i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [laneSwapLabel, Fin.val_mk]
  omega

/-- Contravariant permutation of coordinate vectors by ordered lane swap. -/
def swapCoords (c : Coords144) : Coords144 := fun i => c (laneSwapLabel i)

theorem swapCoords_involution (c : Coords144) :
    swapCoords (swapCoords c) = c := by
  funext i
  change c (laneSwapLabel (laneSwapLabel i)) = c i
  rw [laneSwapLabel_involution]

/-- M16 reduced mod 12, indexed by ordered lane digits (a,b):
    [-47,256;-9,49] == [1,4;3,1] modulo 12. -/
def m16Label (i : Fin 144) : Fin 144 :=
  ⟨12 * ((i.val / 12 + 4 * (i.val % 12)) % 12) +
        ((3 * (i.val / 12) + (i.val % 12)) % 12), by
    omega⟩

/-- M13 reduced mod 12: [-38,169;-9,40] == [10,1;3,4]. -/
def m13Label (i : Fin 144) : Fin 144 :=
  ⟨12 * ((10 * (i.val / 12) + (i.val % 12)) % 12) +
        ((3 * (i.val / 12) + 4 * (i.val % 12)) % 12), by
    omega⟩

/-- The source-index actions are distinct at the ordered pair (3,11).
    These are 12-ary digit operations, not the 4-bit modulo-16 example. -/
theorem swap_m16_label_order_witness :
    laneSwapLabel (m16Label ⟨47, by decide⟩) = ⟨107, by decide⟩ ∧
    m16Label (laneSwapLabel ⟨47, by decide⟩) = ⟨132, by decide⟩ := by
  constructor <;> decide

/-- Inverse M16 reduced mod 12: [49,-256;9,-47] == [1,8;9,1]. -/
def m16InverseLabel (i : Fin 144) : Fin 144 :=
  ⟨12 * ((i.val / 12 + 8 * (i.val % 12)) % 12) +
        ((9 * (i.val / 12) + (i.val % 12)) % 12), by omega⟩

/-- Inverse M13 reduced mod 12: [40,-169;9,-38] == [4,11;9,10]. -/
def m13InverseLabel (i : Fin 144) : Fin 144 :=
  ⟨12 * ((4 * (i.val / 12) + 11 * (i.val % 12)) % 12) +
        ((9 * (i.val / 12) + 10 * (i.val % 12)) % 12), by omega⟩

/-- Pushforward of coefficient vectors under each ordered-label permutation.
    Pulling coefficients from the inverse label is essential: it agrees with
    the executable Python transport convention. -/
def m16Coords (c : Coords144) : Coords144 := fun i => c (m16InverseLabel i)
def m13Coords (c : Coords144) : Coords144 := fun i => c (m13InverseLabel i)

/-- Concretely usable transported SIC-coordinate operators. -/
noncomputable def sicSwap : Coords144 → Coords144 := transport144 swapCoords
noncomputable def sicM16 : Coords144 → Coords144 := transport144 m16Coords
noncomputable def sicM13 : Coords144 → Coords144 := transport144 m13Coords

theorem sicSwap_correct (c : Coords144) :
    sicSwap (analyze144 c) = analyze144 (swapCoords c) := by
  exact transport144_on_image swapCoords c

theorem sicM16_correct (c : Coords144) :
    sicM16 (analyze144 c) = analyze144 (m16Coords c) := by
  exact transport144_on_image m16Coords c

/-- The exact joint 16-coordinate construction provides the same transport law
    for k correlated labels, not an independent product of marginalized labels. -/
abbrev JointCoords (k : ℕ) := JointLabel k → ℂ

noncomputable def analyzeJoint (k : ℕ) (c : JointCoords k) : JointCoords k :=
  (jointGram k).mulVec c

noncomputable def synthesizeJoint (k : ℕ) (p : JointCoords k) : JointCoords k :=
  (jointDual k).mulVec p

theorem synthesize_analyze_joint (k : ℕ) (c : JointCoords k) :
    synthesizeJoint k (analyzeJoint k c) = c := by
  exact joint_coordinate_return k c

noncomputable def transportJoint (k : ℕ)
    (f : JointCoords k → JointCoords k) (p : JointCoords k) : JointCoords k :=
  analyzeJoint k (f (synthesizeJoint k p))

theorem transport_joint_on_image (k : ℕ)
    (f : JointCoords k → JointCoords k) (c : JointCoords k) :
    transportJoint k f (analyzeJoint k c) = analyzeJoint k (f c) := by
  simp only [transportJoint, synthesize_analyze_joint]

#print axioms synthesize_analyze144
#print axioms transport144_comp_on_image
#print axioms transport144_detects_order
#print axioms swap_m16_label_order_witness
#print axioms transport_joint_on_image

end Imscribing.Millennium.WhorlSICTransport
