/-
  Imscribing/YangMills/WilsonObservable.lean

  A concrete nonconstant gauge-invariant Wilson-loop observable indexed by
  spacetime points.  This supplies the `obs`, `gauge_inv` and `non_const`
  fields of `LatticeSinglePointObs` from the proved canonical-witness corpus.
-/
import Mathlib
import Imscribing.YangMills.CanonicalWitness
import Imscribing.YangMills.StrongCouplingInfVol
import Imscribing.YangMills.IIDWilsonLimit

set_option maxHeartbeats 8000000

open scoped BigOperators
open Complex Real Filter

namespace YangMills

/-- The normalized Wilson loop around the canonical plaquette at a point. -/
noncomputable def canonicalLoopObs (L N : ℕ) [NeZero L]
    (x : Space4) (U : WilsonConfig L L N) : ℂ :=
  normWilsonLoop4 (embedLoop4DZ L (canonicalLoop4DZ x)) U

/-- Gauge invariance of the canonical loop observable. -/
lemma canonicalLoopObs_gauge_inv (L N : ℕ) [NeZero L]
    (x : Space4)
    (g : GaugeTransform (cubicTorus4 L L) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : WilsonConfig L L N) :
    canonicalLoopObs L N x (gaugeAct g U) = canonicalLoopObs L N x U := by
  unfold canonicalLoopObs
  rw [normWilsonLoop4_gauge_inv (embedLoop4DZ_isPath L (canonicalLoop4DZ x)) g U]

/-- Nonconstancy of the canonical loop observable (square lattices, L >= 2). -/
lemma canonicalLoopObs_nonconst (N L : ℕ) (hN : 2 ≤ N) [NeZero L] (hL : 2 ≤ L)
    (x : Space4) :
    ∃ U₁ U₂ : WilsonConfig L L N,
      canonicalLoopObs L N x U₁ ≠ canonicalLoopObs L N x U₂ := by
  simpa [canonicalLoopObs] using canonicalWildcard_nonconst N hN L hL x

end YangMills
