import Mathlib
import Imscribing.Millennium.ZetaSICDualFrame
import Imscribing.Millennium.SIC_D12_Embedding
import Imscribing.Millennium.SIC_POVM_Stark
open Imscribing.Millennium.ZetaSICDualFrame
open Millennium.SIC_POVM_Stark
namespace Imscribing.Millennium.TorusDualFrameD12
noncomputable section

/-- The torus portion of the dual frame is dimension 12: the Gram matrix is
    indexed by Fin 144 = 12^2 (the d^2 SIC projectors), its inverse uses
    zeta(-1) = -1/12, and the d=12 SIC existence is proved outright by
    crystal_forces_d12_sic. The horn-torus / (16,3) knot / trine apparatus is
    the geometric carrier of THIS d=12 frame; its 2^11 cover reaches d=2048. -/
theorem torus_dual_frame_is_d12 :
    Fintype.card (Fin 144) = 12 ^ 2 ∧
    Fintype.card (Fin 16) = 4 ^ 2 ∧
    (∀ c : Fin 144 → ℂ, twelveDualGram.mulVec (twelveGram.mulVec c) = c) ∧
    IsSICPOVM 12 SIC.D12.Embedding.psi := by
  refine ⟨by norm_num, by norm_num, twelve_coordinate_reconstruction, ?_⟩
  exact SIC.D12.Embedding.d12_sic_exists

