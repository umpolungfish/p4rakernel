import Imscribing.PerronFiniteInversion
import Imscribing.PerronExplicitFormulaAssembly
import Imscribing.PerronPositiveLimit
import Imscribing.PerronDiagonalIntegral
import Imscribing.PerronDyadicTail

noncomputable section

namespace Imscribing

/-- Combined finite Perron inversion and integrated truncated-explicit-formula
assembly.  The individual kernel limits and the pointwise contour identity are
provided as explicit mathematical data. -/
theorem perron_and_explicit_formula_assembly
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (coeff : ι → ℂ) (ratio : ι → ℝ) (c : ℝ)
    (hint : ∀ T : ℝ, ∀ i ∈ S,
      IntervalIntegrable
        (fun t => perronSummand (coeff i) (ratio i) c t)
        MeasureTheory.volume (-T) T)
    (hkernel : ∀ i ∈ S,
      Filter.Tendsto
        (fun T : ℝ => perronNormalizedKernel (ratio i) c T)
        Filter.atTop (nhds (perronStep (ratio i) : ℂ)))
    {a b : ℝ}
    (D : TruncatedExplicitFormulaData S a b) :
    Filter.Tendsto
        (fun T : ℝ => finitePerronTruncation S coeff ratio c T)
        Filter.atTop
        (nhds (∑ i ∈ S, coeff i * (perronStep (ratio i) : ℂ))) ∧
      (∫ x in a..b, D.lhs x) =
        (∫ x in a..b, D.remainder x) +
          ∑ i ∈ S,
            (D.primitive i b - D.primitive i a +
              ∫ x in a..b, D.correction i x) := by
  constructor
  · exact finitePerronInversion S coeff ratio c hint hkernel
  · exact integrate_truncated_formula_data S a b D

end Imscribing
