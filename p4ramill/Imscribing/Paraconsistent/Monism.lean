import Mathlib

namespace Imscribing.Paraconsistent.Monism

/-!
# Monistic Boundary Conditions on the Spindle Manifold

The spindle geometry, throat-fiber identification, and Belnap FOUR
monistic valuation are formulated within one structure.

The two spindle throat fibers preserve their logical valuations
under toroidal coordinate identification.
-/

/-! ## 1. Belnap FOUR -/

inductive Belnap4
  | N
  | T
  | F
  | B
  deriving DecidableEq, Repr

/-- Monistic states retain truth or a truth-value glut. -/
def Monistic (q : Belnap4) : Prop :=
  q = Belnap4.T ∨ q = Belnap4.B

/-! ## 2. Spindle Geometry -/

/-- Radial spindle factor. -/
noncomputable def spindleA (R φ : ℝ) : ℝ :=
  R + Real.cos (2 * Real.pi * φ)

/-- Angular location of the spindle throat. -/
noncomputable def spindleAlpha (R : ℝ) : ℝ :=
  Real.arccos (-R)

/-- Positive spindle throat coordinate. -/
noncomputable def spindlePhiPlus (R : ℝ) : ℝ :=
  spindleAlpha R / (2 * Real.pi)

/-- Negative spindle throat coordinate. -/
noncomputable def spindlePhiMinus (R : ℝ) : ℝ :=
  1 - spindlePhiPlus R

/-! ## 3. Monistic Field -/

/-- The field valuation over the spindle parameter space. -/
abbrev MonisticField := ℝ → ℝ → Belnap4

/-- Every point retains either truth or a glut. -/
def monisticField (Q : MonisticField) : Prop :=
  ∀ φ θ, Monistic (Q φ θ)

/-! ## 4. Throat-Fiber Compatibility -/

/--
All toroidal approaches to either spindle throat have
identical logical valuations.
-/
def throatCompatible
    (Q : MonisticField) (R : ℝ) : Prop :=
  (∀ θ₁ θ₂,
    Q (spindlePhiPlus R) θ₁ =
      Q (spindlePhiPlus R) θ₂) ∧
  (∀ θ₁ θ₂,
    Q (spindlePhiMinus R) θ₁ =
      Q (spindlePhiMinus R) θ₂)

/-! ## 5. Monistic Throat Preservation -/

/--
Both spindle throat fibers preserve their valuations and
their monistic truth states.
-/
theorem monistic_throat_preservation
    (Q : MonisticField)
    (R : ℝ)
    (hfield : monisticField Q)
    (hboundary : throatCompatible Q R) :
    (∀ θ,
      Q (spindlePhiPlus R) θ =
        Q (spindlePhiPlus R) 0 ∧
      Monistic (Q (spindlePhiPlus R) θ)) ∧
    (∀ θ,
      Q (spindlePhiMinus R) θ =
        Q (spindlePhiMinus R) 0 ∧
      Monistic (Q (spindlePhiMinus R) θ)) := by
  constructor
  · intro θ
    constructor
    · exact hboundary.1 θ 0
    · exact hfield _ _
  · intro θ
    constructor
    · exact hboundary.2 θ 0
    · exact hfield _ _

/-! ## 6. Explicit Glut Preservation -/

/-- A glut valuation remains a glut along the positive throat fiber. -/
theorem positive_throat_glut_preservation
    (Q : MonisticField)
    (R : ℝ)
    (hboundary : throatCompatible Q R)
    (hglut : Q (spindlePhiPlus R) 0 = Belnap4.B) :
    ∀ θ, Q (spindlePhiPlus R) θ = Belnap4.B := by
  intro θ
  rw [hboundary.1 θ 0]
  exact hglut

/-- A glut valuation remains a glut along the negative throat fiber. -/
theorem negative_throat_glut_preservation
    (Q : MonisticField)
    (R : ℝ)
    (hboundary : throatCompatible Q R)
    (hglut : Q (spindlePhiMinus R) 0 = Belnap4.B) :
    ∀ θ, Q (spindlePhiMinus R) θ = Belnap4.B := by
  intro θ
  rw [hboundary.2 θ 0]
  exact hglut

/-! ## 7. Throat-Valuation Identity -/

/--
The two throat valuations form the intrinsic boundary state
of the monistic spindle field.
-/
def ThroatState (Q : MonisticField) (R : ℝ) :=
  Belnap4 × Belnap4

noncomputable def throatState
    (Q : MonisticField) (R : ℝ) :
    ThroatState Q R :=
  (Q (spindlePhiPlus R) 0,
   Q (spindlePhiMinus R) 0)

/-- Both components of the throat state remain monistic. -/
theorem throat_state_monistic
    (Q : MonisticField)
    (R : ℝ)
    (hfield : monisticField Q) :
    Monistic (throatState Q R).1 ∧
    Monistic (throatState Q R).2 := by
  constructor
  · exact hfield _ _
  · exact hfield _ _

end Imscribing.Paraconsistent.Monism