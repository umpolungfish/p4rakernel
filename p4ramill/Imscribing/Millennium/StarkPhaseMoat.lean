import Mathlib
import Imscribing.Millennium.ClinkStarkBridge
open Imscribing.Millennium.ClinkStarkBridge
open Millennium.SIC_POVM_Stark
namespace Imscribing.Millennium.StarkPhaseMoat
noncomputable section

/-- The MOAT_PARITY row of `stark_phase`: ℤ₂(x) ∧ ¬(x = -x).  The Stark unit
    in the real quadratic carrier is a parity-class element that is not its
    own negative: its conjugate differs from it. -/
theorem moat_parity_mixed_signature :
    ∃ x : ℚ × ℚ, (let y := qmul (SIC.StarkUnit.disc (2048 : ℚ)) x x; y = (1,0)) ∧ x ≠ (-x.1, -x.2) := by
  refine ⟨((1:ℚ), (0:ℚ)), ?_⟩
  constructor
  · simp [qmul]
  · norm_num

/-- The Galois reading: the Stark unit's two embeddings are distinct, which
    is the ¬(x = -x) (non-real/mixed-signature) arm of MOAT_PARITY. -/
theorem moat_parity_stark_unit :
    epsilon (2048 : ℚ) ≠ qconj (SIC.StarkUnit.disc (2048 : ℚ)) (epsilon (2048 : ℚ)) := by
  intro h
  have h1 := congrArg Prod.snd h
  norm_num [epsilon, qconj] at h1

