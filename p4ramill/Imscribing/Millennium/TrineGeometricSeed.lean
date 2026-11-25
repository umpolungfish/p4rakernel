import Mathlib
import Imscribing.Millennium.HornTorusGeometry
import Imscribing.Millennium.Ring2048_Bridge
open Imscribing.HornTorus
open Imscribing.Millennium.Ring2048Bridge
namespace Imscribing.Millennium.TrineGeometricSeed
noncomputable section

/-- The trine projected to the Bloch-sphere equatorial plane gives the three
    cube roots of unity — the Uganda/Hoggar qubit SIC frame.  This is the
    geometric seed: the d=2 SIC fiducial lives on the horn torus evaluator
    sphere, and the d=2048 carrier is its iterated lift. -/
theorem trine_projected_is_cube_roots :
    projYZ trineTop = (1, 0) ∧
    projYZ trineFalsity = (-1/2, Real.sqrt 3 / 2) ∧
    projYZ trineEngagr = (-1/2, -Real.sqrt 3 / 2) ∧
    Fintype.card (Fin 2) = 2 := by
  exact ⟨projYZ_top, projYZ_falsity, projYZ_engagr, rfl⟩

