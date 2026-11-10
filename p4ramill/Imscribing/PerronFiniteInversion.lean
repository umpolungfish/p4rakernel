import Imscribing.PerronFinite
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section

namespace Imscribing

open MeasureTheory

/-- The normalized finite Perron kernel. -/
noncomputable def perronNormalizedKernel (u c T : ℝ) : ℂ :=
  perronScale * (∫ t in (-T)..T, verticalPerronKernelIntegrand u c t)

/-- The limiting step value of the Perron kernel at a positive ratio. -/
def perronStep (u : ℝ) : ℝ :=
  if 1 < u then 1 else if u = 1 then (1 / 2 : ℝ) else 0

/-- The finite-height integral of a finite Dirichlet polynomial. -/
noncomputable def finitePerronTruncation
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (c T : ℝ) : ℂ :=
  ∫ t in (-T)..T, finitePerronIntegrand S a u c t

/-- Pulling a coefficient through the normalized Perron kernel. -/
theorem perronTermContribution_eq_coeff_mul_normalizedKernel
    (a : ℂ) (u c T : ℝ) :
    perronTermContribution a u c T =
      a * perronNormalizedKernel u c T := by
  rw [perron_summand_integral_factor]
  simp only [perronNormalizedKernel, smul_eq_mul]
  ring

/-- A finite sum of pointwise limits is a pointwise limit. -/
theorem tendsto_finset_sum_complex
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℂ) (v : ι → ℂ)
    (h : ∀ i ∈ S,
      Filter.Tendsto (f i) Filter.atTop (nhds (v i))) :
    Filter.Tendsto
      (fun T : ℝ => ∑ i ∈ S, f i T)
      Filter.atTop
      (nhds (∑ i ∈ S, v i)) := by
  classical
  revert h
  induction S using Finset.induction_on with
  | empty =>
      intro h
      simp
  | @insert i S hi ih =>
      intro h
      have hi' : Filter.Tendsto (f i) Filter.atTop (nhds (v i)) :=
        h i (by simp)
      have hS : ∀ j ∈ S,
          Filter.Tendsto (f j) Filter.atTop (nhds (v j)) := by
        intro j hj
        exact h j (by simp [hj, hi])
      have hsum := hi'.add (ih hS)
      simpa [Finset.sum_insert, hi] using hsum

/-- Finite Perron inversion from the limits of its individual summands. -/
theorem finitePerronTruncation_tendsto_of_term_limits
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (c : ℝ)
    (hint : ∀ T : ℝ, ∀ i ∈ S,
      IntervalIntegrable
        (fun t => perronSummand (a i) (u i) c t)
        MeasureTheory.volume (-T) T)
    (v : ι → ℂ)
    (hterm : ∀ i ∈ S,
      Filter.Tendsto
        (fun T : ℝ => perronTermContribution (a i) (u i) c T)
        Filter.atTop (nhds (v i))) :
    Filter.Tendsto
      (fun T : ℝ => finitePerronTruncation S a u c T)
      Filter.atTop
      (nhds (∑ i ∈ S, v i)) := by
  have hsum := tendsto_finset_sum_complex S
    (fun i T => perronTermContribution (a i) (u i) c T) v hterm
  have hdecomp :
      (fun T : ℝ => finitePerronTruncation S a u c T) =
        (fun T : ℝ => ∑ i ∈ S,
          perronTermContribution (a i) (u i) c T) := by
    funext T
    exact finite_perron_interchange S a u c T (hint T)
  rw [hdecomp]
  exact hsum

/-- Finite Dirichlet-polynomial Perron inversion from normalized pointwise
kernel limits. -/
theorem finitePerronInversion
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (c : ℝ)
    (hint : ∀ T : ℝ, ∀ i ∈ S,
      IntervalIntegrable
        (fun t => perronSummand (a i) (u i) c t)
        MeasureTheory.volume (-T) T)
    (hkernel : ∀ i ∈ S,
      Filter.Tendsto
        (fun T : ℝ => perronNormalizedKernel (u i) c T)
        Filter.atTop (nhds (perronStep (u i) : ℂ))) :
    Filter.Tendsto
      (fun T : ℝ => finitePerronTruncation S a u c T)
      Filter.atTop
      (nhds (∑ i ∈ S, a i * (perronStep (u i) : ℂ))) := by
  apply finitePerronTruncation_tendsto_of_term_limits S a u c hint
  intro i hi
  have hk := (hkernel i hi).const_mul (a i)
  simpa [perronTermContribution_eq_coeff_mul_normalizedKernel] using hk

end Imscribing
