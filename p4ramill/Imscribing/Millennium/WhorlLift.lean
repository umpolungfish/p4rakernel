import Mathlib
import Imscribing.PrimeWhorlTheory
import Imscribing.PrimeWhorlLiveBraid
import Imscribing.Millennium.D2048GeometricPhaseRoute
open Imscribing.PrimeWhorl.Theory
open Imscribing.PrimeWhorl.Burau
namespace Imscribing.Millennium.WhorlLift
noncomputable section

/-- The 2^11 lift's Frobenius closure: a source-marked whorl sends its phase
    out through the deformation and the live phase-bearing braid, then
    reconstructs the source exactly. This is the geometric realization of
    mu o delta = id on the horn-torus cover that carries the SIC fiducial. -/
theorem whorl_lift_frobenius {N : ℕ} [NeZero N] (w : Whorl N) :
    w.reconstruct = w.copied := by
  exact Whorl.reconstruction w

theorem whorl_lift_continuation {N : ℕ} [NeZero N] (w : Whorl N)
    (a b : List (LiveStep (ZMod N))) :
    (w.withMoreBraid a).withMoreBraid b = w.withMoreBraid (a ++ b) := by
  exact Whorl.continuation_assoc w a b

theorem whorl_lift_cut_rotation {N : ℕ} [NeZero N] (w : Whorl N) :
    (w.rotateCut).reconstruct = w.reconstruct := by
  exact Whorl.rotating_cut_preserves_reconstruction w

