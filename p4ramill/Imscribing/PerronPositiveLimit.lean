import Imscribing.PerronDyadicTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section

namespace Imscribing

/-- The positive-height Perron integral truncated at the `N`-th dyadic height. -/
noncomputable def perronPositiveTruncatedIntegral
    (u c T : ℝ) (N : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..perronDyadicHeight T N,
    verticalPerronKernelIntegrand u c t

/-- Finite dyadic partition: the integral from `T` to the `N`-th dyadic
height is the sum of the first `N` dyadic block integrals. -/
theorem perronDyadicPartition_integral
    (u c T : ℝ) (hT : 0 < T) (hc : 0 < c) (N : ℕ) :
    (∫ t in T..perronDyadicHeight T N,
      verticalPerronKernelIntegrand u c t) =
      ∑ n ∈ Finset.range N, perronDyadicBlockIntegral u c T n := by
  have hint : ∀ k : ℕ, k < N →
      IntervalIntegrable (fun t => verticalPerronKernelIntegrand u c t)
        MeasureTheory.volume (perronDyadicHeight T k)
          (perronDyadicHeight T (k + 1)) := by
    intro k hk
    exact verticalPerronKernelIntegrand_intervalIntegrable u c
      (perronDyadicHeight T k) (perronDyadicHeight T (k + 1)) hc
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := perronDyadicHeight T) (n := N) hint
  simpa [perronDyadicHeight, perronDyadicBlockIntegral] using hsum.symm

/-- Decompose a positive-height truncation into its fixed initial segment
and finitely many dyadic blocks. -/
theorem perronPositiveTruncatedIntegral_eq_base_add_blocks
    (u c T : ℝ) (hT : 0 < T) (hc : 0 < c) (N : ℕ) :
    perronPositiveTruncatedIntegral u c T N =
      (∫ t in (0 : ℝ)..T, verticalPerronKernelIntegrand u c t) +
        ∑ n ∈ Finset.range N, perronDyadicBlockIntegral u c T n := by
  unfold perronPositiveTruncatedIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (verticalPerronKernelIntegrand_intervalIntegrable u c 0 T hc)
    (verticalPerronKernelIntegrand_intervalIntegrable u c T
      (perronDyadicHeight T N) hc)]
  rw [perronDyadicPartition_integral u c T hT hc N]

/-- The positive-height truncated Perron integrals converge along dyadic
heights whenever the off-diagonal dyadic block estimate holds. -/
theorem perronPositiveTruncatedIntegral_tendsto
    (u c T : ℝ) (hT : 0 < T) (hc : 0 < c)
    (ha : Real.log u ≠ 0)
    (hblock : ∀ n : ℕ,
      ‖perronDyadicBlockIntegral u c T n‖ ≤
        3 * Real.exp (c * Real.log u) /
          (|Real.log u| * perronDyadicHeight T n)) :
    Filter.Tendsto
      (fun N : ℕ => perronPositiveTruncatedIntegral u c T N)
      Filter.atTop
      (nhds
        ((∫ t in (0 : ℝ)..T, verticalPerronKernelIntegrand u c t) +
          ∑' n : ℕ, perronDyadicBlockIntegral u c T n)) := by
  have hblocks :
      Summable (fun n : ℕ => perronDyadicBlockIntegral u c T n) :=
    perronDyadicBlocks_summable u c T hT ha hblock
  have hsum := hblocks.tendsto_sum_tsum_nat
  have hlim :
      Filter.Tendsto
        (fun N : ℕ =>
          (∫ t in (0 : ℝ)..T, verticalPerronKernelIntegrand u c t) +
            ∑ n ∈ Finset.range N, perronDyadicBlockIntegral u c T n)
        Filter.atTop
        (nhds
          ((∫ t in (0 : ℝ)..T, verticalPerronKernelIntegrand u c t) +
            ∑' n : ℕ, perronDyadicBlockIntegral u c T n)) := by
    exact tendsto_const_nhds.add hsum
  have hdecomp := perronPositiveTruncatedIntegral_eq_base_add_blocks
    u c T hT hc
  have hfun :
      (fun N : ℕ => perronPositiveTruncatedIntegral u c T N) =
        (fun N : ℕ =>
          (∫ t in (0 : ℝ)..T, verticalPerronKernelIntegrand u c t) +
            ∑ n ∈ Finset.range N, perronDyadicBlockIntegral u c T n) := by
    funext N
    exact hdecomp N
  rw [hfun]
  exact hlim

end Imscribing
