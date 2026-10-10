import Imscribing.NS_InjectionField

noncomputable section
namespace Imscribing.NSDifferentialConvention
open Imscribing.NSInjectionField
open scoped BigOperators

/-- Cartesian reconstruction of a velocity vector. -/
theorem basis_decomposition (v : Space) :
    ∑ i : Fin 3, v i • basisVector i = v := by
  ext j
  simp [basisVector, EuclideanSpace.single_apply, Pi.single_apply]

/-- The coordinate sum is the full spatial derivative applied to velocity. -/
theorem transport_eq_spatial_fderiv (u : Velocity) (z : Domain) :
    transport u z = fderiv ℝ (fun x : Space => u (z.1, x)) z.2 (u z) := by
  conv_rhs => rw [← basis_decomposition (u z)]
  simp only [map_sum, map_smul, transport, spatialDerivative]

end Imscribing.NSDifferentialConvention
