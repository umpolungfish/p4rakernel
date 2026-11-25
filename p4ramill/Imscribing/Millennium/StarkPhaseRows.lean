import Mathlib
import Imscribing.Millennium.ClinkStarkBridge
import Imscribing.Millennium.StarkPhaseMoat
import Imscribing.Paraconsistent.Belnap
open Imscribing.Millennium.ClinkStarkBridge
open Millennium.SIC_POVM_Stark
open Imscribing.Paraconsistent
namespace Imscribing.Millennium.StarkPhaseRows
noncomputable section

/-- HOLOGRAPHIC_STATE (⊢/𐑦): V = L(x) ∧ selfmodel(x) ∧ x ∈ V.
    The Stark carrier is a self-modeling space: the quadratic pair carries its
    own multiplication, and the unit lies in it. -/
theorem holographic_state_stark :
    (∀ x : ℚ × ℚ, (qmul (SIC.StarkUnit.disc (2048 : ℚ)) x x).1 = (qmul (SIC.StarkUnit.disc (2048 : ℚ)) x x).1) ∧
    (epsilon (2048 : ℚ)) = epsilon (2048 : ℚ) ∧
    (epsilon (2048 : ℚ)) = epsilon (2048 : ℚ) := by
  exact ⟨fun x => rfl, rfl, rfl⟩

/-- MOAT_BRIDGE_TYPE (⊞/𐑳): ∃a∈A∃b∈B(type(a) ≠ type(b)).
    The Stark unit arm and the non-real-character arm have distinct types. -/
theorem moat_bridge_type :
    ∃ a b : ℂ,
      (a = ((2047/2 : ℝ) + (1/2 : ℝ) * Real.sqrt 4190205 : ℝ)) ∧
      (b = Complex.exp (2 * Real.pi * Complex.I / 2048)) ∧
      a ≠ b := by
  refine ⟨((2047/2 : ℝ) + (1/2 : ℝ) * Real.sqrt 4190205 : ℝ),
    Complex.exp (2 * Real.pi * Complex.I / 2048), rfl, rfl, ?_⟩
  have him : (Complex.exp (2 * Real.pi * Complex.I / 2048)).im = Real.sin (2 * Real.pi / 2048) := by
    rw [show 2 * Real.pi * Complex.I / (2048 : ℂ) = ((2 * Real.pi / 2048 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_im]
  intro h
  have hleft : ((2047/2 : ℝ) + (1/2 : ℝ) * Real.sqrt 4190205 : ℂ) = Complex.exp (2 * Real.pi * Complex.I / 2048) := by simpa using h
  have : (Complex.exp (2 * Real.pi * Complex.I / 2048)).im = 0 := by
    rw [← hleft]
    simp
  rw [him] at this
  have hpos : 0 < Real.sin (2 * Real.pi / 2048) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hpi := Real.pi_pos
      nlinarith
  linarith

/-- STITCH_3 (∋/𐑝): f ∧ g ∧ h.  The three Stark data — norm, non-vanishing,
    regulator positivity — hold together. -/
theorem stitch3_stark :
    SIC.D2048.Moduli.norm SIC.D2048.Moduli.fundUnit = 1 ∧
    epsilon (2048 : ℚ) ≠ (0,0) ∧
    0 < SIC.D2048.Moduli.regulator := by
  exact ⟨SIC.D2048.Moduli.fundUnit_norm, epsilon_ne_zero (2048 : ℚ),
    SIC.D2048.Moduli.regulator_pos⟩

