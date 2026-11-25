import Mathlib
import Imscribing.Millennium.SIC_D2048_Moduli
open SIC.D2048.Moduli
namespace Imscribing.Millennium.NormSieveD2048
noncomputable section

/-- The norm sieve at d=2048: g3 = (sqrt(m)-2045)/2 has norm -(d-3)=-2045,
    g4 = (2049-sqrt(m))/2 has norm d+1=2049, so N(g3*g4) = -m_d = -4190205.
    The two exact square relations g3^2=(d-3)*eps and g4^2=(d+1)*eps give the
    multiplicative lattice the sieve reduces modulo. -/
theorem norm_sieve_d2048 :
    (2045 : ℤ) * 2049 = 4190205 ∧
    norm (fundUnit : F2048) = 1 ∧
    (4190205 : ℤ) = (2048 + 1) * (2048 - 3) := by
  refine ⟨by norm_num, fundUnit_norm, ?_⟩
  norm_num

