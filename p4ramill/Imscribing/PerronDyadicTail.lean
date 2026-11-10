import Imscribing.PerronOffDiagonalBlock
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section

namespace Imscribing

/-- The height at the beginning of the `n`-th dyadic block. -/
def perronDyadicHeight (T : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ n * T

/-- The vertical Perron integral over the `n`-th dyadic block. -/
noncomputable def perronDyadicBlockIntegral
    (u c T : ℝ) (n : ℕ) : ℂ :=
  ∫ t in (perronDyadicHeight T n)..(perronDyadicHeight T (n + 1)),
    verticalPerronKernelIntegrand u c t

theorem perronDyadicHeight_pos {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 < perronDyadicHeight T n := by
  simp only [perronDyadicHeight]
  positivity

theorem perronDyadicHeight_succ
    (T : ℝ) (n : ℕ) :
    perronDyadicHeight T (n + 1) =
      2 * perronDyadicHeight T n := by
  simp only [perronDyadicHeight, pow_succ]
  ring

/--
Convert the `1 / height` block estimate into a geometric majorant.
The constant is the first-block scale `3 exp(c log u) / (|log u| T)`.
-/
theorem perronDyadicBlock_geometric_bound
    (u c T : ℝ)
    (hT : 0 < T)
    (ha : Real.log u ≠ 0)
    (hblock : ∀ n : ℕ,
      ‖perronDyadicBlockIntegral u c T n‖ ≤
        3 * Real.exp (c * Real.log u) /
          (|Real.log u| * perronDyadicHeight T n)) :
    ∀ n : ℕ,
      ‖perronDyadicBlockIntegral u c T n‖ ≤
        (3 * Real.exp (c * Real.log u) / (|Real.log u| * T)) *
          (1 / 2 : ℝ) ^ n := by
  intro n
  have hT0 : T ≠ 0 := ne_of_gt hT
  have ha0 : |Real.log u| ≠ 0 := abs_ne_zero.mpr ha
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hscale :
      3 * Real.exp (c * Real.log u) /
          (|Real.log u| * perronDyadicHeight T n) =
        (3 * Real.exp (c * Real.log u) / (|Real.log u| * T)) *
          (1 / 2 : ℝ) ^ n := by
    simp only [perronDyadicHeight]
    field_simp [ha0, hT0, hpow]
    rw [← mul_pow]
    norm_num
  calc
    ‖perronDyadicBlockIntegral u c T n‖ ≤
        3 * Real.exp (c * Real.log u) /
          (|Real.log u| * perronDyadicHeight T n) := hblock n
    _ = (3 * Real.exp (c * Real.log u) / (|Real.log u| * T)) *
          (1 / 2 : ℝ) ^ n := hscale

/--
The dyadic Perron block integrals are absolutely summable whenever each block
satisfies the integration-by-parts estimate `K * 2^{-n}`.
-/
theorem perronDyadicBlocks_summable
    (u c T : ℝ)
    (hT : 0 < T)
    (ha : Real.log u ≠ 0)
    (hblock : ∀ n : ℕ,
      ‖perronDyadicBlockIntegral u c T n‖ ≤
        3 * Real.exp (c * Real.log u) /
          (|Real.log u| * perronDyadicHeight T n)) :
    Summable (fun n : ℕ => perronDyadicBlockIntegral u c T n) := by
  let K : ℝ := 3 * Real.exp (c * Real.log u) / (|Real.log u| * T)
  have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hgeoK : Summable (fun n : ℕ => K * (1 / 2 : ℝ) ^ n) :=
    Summable.mul_left K hgeo
  have hbound : ∀ n : ℕ,
      ‖perronDyadicBlockIntegral u c T n‖ ≤ K * (1 / 2 : ℝ) ^ n := by
    intro n
    have h := perronDyadicBlock_geometric_bound u c T hT ha hblock n
    simpa [K] using h
  exact Summable.of_norm_bounded hgeoK hbound

/--
The tail beginning with dyadic block `N` has norm at most twice the first
geometric majorant at that scale.
-/
theorem perronDyadicTail_norm_bound
    (u c T : ℝ)
    (hT : 0 < T)
    (ha : Real.log u ≠ 0)
    (hblock : ∀ n : ℕ,
      ‖perronDyadicBlockIntegral u c T n‖ ≤
        3 * Real.exp (c * Real.log u) /
          (|Real.log u| * perronDyadicHeight T n))
    (N : ℕ) :
    ‖∑' n : ℕ, perronDyadicBlockIntegral u c T (n + N)‖ ≤
      2 * (3 * Real.exp (c * Real.log u) / (|Real.log u| * T)) *
        (1 / 2 : ℝ) ^ N := by
  let K : ℝ := 3 * Real.exp (c * Real.log u) / (|Real.log u| * T)
  have hgeom : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 :=
    hasSum_geometric_two
  have hgeomTail :
      HasSum
        (fun n : ℕ => (K * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ n)
        ((K * (1 / 2 : ℝ) ^ N) * 2) :=
    HasSum.mul_left (K * (1 / 2 : ℝ) ^ N) hgeom
  have hbound : ∀ n : ℕ,
      ‖perronDyadicBlockIntegral u c T (n + N)‖ ≤
        (K * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ n := by
    intro n
    have h := perronDyadicBlock_geometric_bound u c T hT ha hblock (n + N)
    calc
      ‖perronDyadicBlockIntegral u c T (n + N)‖ ≤
          K * (1 / 2 : ℝ) ^ (n + N) := by
            simpa [K] using h
      _ = (K * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ n := by
            rw [pow_add]
            ring
  have htailSummable :
      Summable (fun n : ℕ => perronDyadicBlockIntegral u c T (n + N)) :=
    Summable.of_norm_bounded hgeomTail.summable hbound
  have hnorm := htailSummable.hasSum.norm_le_of_bounded hgeomTail hbound
  calc
    ‖∑' n : ℕ, perronDyadicBlockIntegral u c T (n + N)‖ ≤
        (K * (1 / 2 : ℝ) ^ N) * 2 := hnorm
    _ = 2 * (3 * Real.exp (c * Real.log u) / (|Real.log u| * T)) *
          (1 / 2 : ℝ) ^ N := by
        dsimp [K]
        ring_nf

end Imscribing
