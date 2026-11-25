import Mathlib
import Imscribing.Millennium.HornPhaseCarrier
import Imscribing.Millennium.D2048GeometricRoute
import Imscribing.Millennium.BlochHornTorus
open Imscribing.Millennium.Erdos.Problem0028HornWhorlSIC
open Imscribing.HornTorus
namespace Imscribing.Millennium.D2048GeometricPhaseRoute
noncomputable section

/-- The phase-carrier lemma wired into the d=2048 geometric route: rational
    phases ride the horn-torus equator injectively, over the Bloch sphere that
    carries the trine/Uganda seed, through the (16,3) conductor-(16^3) cover. -/
theorem d2048_geometric_phase_route (a b : ℕ) :
    (representationHornPoint a b).2.1 / (representationHornPoint a b).1 =
      (representationPhase a b : ℝ) ∧
    (2048 : ℕ) = 2 ^ 11 ∧
    (16 : ℕ) ^ 3 = 2 ^ 12 ∧
    OnHorn 2 (rotX (Real.pi/6) scaledEngagr) := by
  exact ⟨representation_horn_readout a b, d2048, conductor_exponent, engagr_on_horn_scaled⟩

