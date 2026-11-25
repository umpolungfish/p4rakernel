import Mathlib
import Imscribing.Millennium.HornTorusGeometry
import Imscribing.Millennium.D2048GeometricRoute
import Imscribing.Millennium.SIC_D4_Frame
open Imscribing.HornTorus
namespace Imscribing.Millennium.BlochHornTorus
noncomputable section

/-- The evaluator sphere of the horn torus is the Bloch sphere: radius
    λ_C = R/2 = 1 centred at the split shell. The d=2 qubit SIC (the d=4
    frame's Bloch predecessor) lives on this sphere, and the d=2048 carrier
    is the 2^11-fold geometric lift of that sphere. -/
theorem bloch_sphere_of_horn_torus :
    sqDist origin sphereCentre = 1 ∧
    sqDist omega sphereCentre = 1 ∧
    sqDist trineTop sphereCentre = 1 ∧
    sqDist trineFalsity sphereCentre = 1 ∧
    sqDist trineEngagr sphereCentre = 1 ∧
    sqDist trineTop trineFalsity = 3 ∧
    sqDist trineFalsity trineEngagr = 3 ∧
    sqDist trineTop trineEngagr = 3 := by
  exact ⟨origin_on_sphere, omega_on_sphere, trineTop_on_sphere,
    trineFalsity_on_sphere, trineEngagr_on_sphere,
    trine_equilateral_top_falsity, trine_equilateral_falsity_engagr,
    trine_equilateral_top_engagr⟩

