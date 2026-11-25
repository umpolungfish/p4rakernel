import Mathlib
import Imscribing.Millennium.ClinkStarkBridge
import Imscribing.Millennium.ZaunerTransportMap

/-!
The missing plank named by the Uroboræus campaign: a BridgeRep witness at
n = 11, i.e. an exact unit vector in C^2048 with constant off-origin
Weyl-Heisenberg overlap.  This module does not assert such a witness; it
proves the reduction theorem the campaign asks for: the witness implies
SICPOVM_Exists 2048, via the Welch bridge.
-/

namespace Imscribing.Millennium.BridgeRepReduction

open Millennium.SIC_POVM_Stark
open Imscribing.Millennium.ClinkStarkBridge

noncomputable section

/-- A BridgeRep witness at n: an exact fiducial candidate in dimension 2^n
    whose off-origin WH overlaps are constant.  This is the single object the
    corpus leaves open; it is a structure, not an axiom. -/
structure BridgeRepWitness (n : ℕ) [NeZero (2^n)] where
  psi : Fin (2^n) → ℂ
  unit : wh_normSq (2^n) psi = 1
  constant : ∃ c : ℝ, ∀ a b : Fin (2^n), (a, b) ≠ (0, 0) →
    ‖wh_inner (2^n) psi (D_ah (2^n) a b 0 psi)‖ ^ 2 = c

/-- The reduction: a BridgeRep witness at n implies the shadow SIC theorem
    in dimension 2^n.  The constant is forced to 1/(2^n+1) by the Welch
    identity; no equiangularity hypothesis is assumed. -/
theorem bridge_rep_implies_sic (n : ℕ) [NeZero (2^n)] (hn : 2 ≤ 2^n)
    (w : BridgeRepWitness n) :
    SICPOVM_Exists (2^n) := by
  rcases w.constant with ⟨c, hc⟩
  exact sic_exists_of_constant_overlap (2^n) hn w.psi w.unit c hc

/-- The n = 11 instance: the exact claim named in the campaign. -/
theorem bridge_rep_11_implies_sic_2048 (w : BridgeRepWitness 11) :
    SICPOVM_Exists 2048 := by
  simpa using bridge_rep_implies_sic 11 (by norm_num) w

