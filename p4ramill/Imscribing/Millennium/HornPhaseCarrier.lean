import Mathlib
import Imscribing.Millennium.Erdos.Problem0028HornWhorlSIC
import Imscribing.Millennium.BlochHornTorus
open Imscribing.Millennium.Erdos.Problem0028HornWhorlSIC
namespace Imscribing.Millennium.HornPhaseCarrier
noncomputable section

/-- The horn-torus phase carrier: rational phases embed on the equator and
    are recoverable by the coordinate ratio (injective, not lossy).  This is
    the geometric seam through which the Stark S-unit phases can be carried
    on the way to the d=2048 fiducial. -/
theorem horn_phase_carrier (a b : ℕ) :
    (representationHornPoint a b).2.1 / (representationHornPoint a b).1 =
      (representationPhase a b : ℝ) := by
  exact representation_horn_readout a b

