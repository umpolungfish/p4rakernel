import NavierStokes.R3.ProblemStatement
import Imscribing.NS_DifferentialConvention

noncomputable section
namespace InjectionConnection
open Imscribing.NSInjectionField Imscribing.NSDifferentialConvention
open scoped ContDiff

/-- Both libraries use time first and the same Euclidean coordinate basis. -/
theorem residual_eq_published (ν : ℝ) (u : Velocity) (p : Pressure) (z : Domain) :
    residualForce ν u p z =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p z.1 z.2 := by
  simp only [residualForce, momentumTerms, Imscribing.NSReentry.MomentumTerms.residual,
    NavierStokesR3.ProblemStatement.navierStokesResidual,
    NavierStokes.ProblemStatement.temporalDerivative, timeDerivative,
    transport_eq_spatial_fderiv, NavierStokes.ProblemStatement.advection,
    NavierStokes.ProblemStatement.spatialDerivative,
    spatialLaplacian, spatialDerivative, NavierStokes.ProblemStatement.spatialLaplacian,
    pressureGradient, NavierStokes.ProblemStatement.pressureGradient,
    basisVector, NavierStokes.ProblemStatement.coordinateVector,
    neg_smul, sub_eq_add_neg]

end InjectionConnection

#print axioms InjectionConnection.residual_eq_published
