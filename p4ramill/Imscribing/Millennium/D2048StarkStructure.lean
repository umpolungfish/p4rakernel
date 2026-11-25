import Mathlib
import Imscribing.Millennium.ClinkStarkBridge
import Imscribing.Millennium.SIC_D2048_Moduli
open Imscribing.Millennium.ClinkStarkBridge
namespace Imscribing.Millennium.D2048StarkStructure
noncomputable section

/-- The concrete Stark structure at d=2048: the quadratic carrier, the unit
    with norm one and positive real embedding, and the exact Galois
    non-vanishing, assembled as the shadow data the conjecture quantifies. -/
theorem d2048_stark_structure :
    SIC.D2048.Moduli.norm SIC.D2048.Moduli.fundUnit = 1 ∧
    (1 : ℝ) < ((2047/2 : ℝ) + (1/2 : ℝ) * Real.sqrt 4190205) ∧
    epsilon (2048 : ℚ) ≠ (0,0) ∧
    qconj (SIC.StarkUnit.disc (2048 : ℚ)) (epsilon (2048 : ℚ)) ≠ (0,0) ∧
    (∀ n : ℕ, qpow (SIC.StarkUnit.disc (2048 : ℚ)) n (epsilon (2048 : ℚ)) ≠ (0,0)) := by
  refine ⟨SIC.D2048.Moduli.fundUnit_norm, SIC.D2048.Moduli.fundUnit_gt_one,
    epsilon_ne_zero (2048 : ℚ), epsilon_conj_ne_zero (2048 : ℚ), ?_⟩
  intro n
  exact epsilon_pow_ne_zero (2048 : ℚ) n

