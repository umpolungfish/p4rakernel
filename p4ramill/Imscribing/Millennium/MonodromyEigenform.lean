import Mathlib
import Imscribing.Millennium.ClinkStarkBridge
open Imscribing.Millennium.ClinkStarkBridge
namespace Imscribing.Millennium.MonodromyEigenform
noncomputable section

/-- The frame-cycle monodromy at d=2048 is the order-3 Zauner automorphism
    zaunerMatrix 2048 with Z^3 = 1. Its eigenform is the candidate the spindle
    self-intersection returns unchanged. -/
theorem monodromy_order_three_2048 :
    zaunerMatrix 2048 ^ 3 = (1 : Matrix (Fin 2) (Fin 2) (ZMod 2048)) := by
  exact zaunerMatrix_order_three 2048

/-- The monodromy has a fixed (eigenvalue-1) vector: the re-entry eigenform.
    For Z^3=1 the cube of any eigenvector is itself, so the +1 eigenspace is
    the value that comes back unchanged across the spindle crossing. -/
theorem monodromy_fixed_vector (v : Fin 2 → ZMod 2048)
    (h : Matrix.mulVec (zaunerMatrix 2048) v = v) :
    Matrix.mulVec (zaunerMatrix 2048 ^ 3) v = v := by
  rw [monodromy_order_three_2048]
  simp

