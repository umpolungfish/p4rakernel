/-
  Imscribing/YangMills/IIDScaling.lean

  Concrete lattice-to-continuum scaling sequences for the Wilson-limit bridge.
  All theorems here are unconditional (standard axioms only).
-/
import Mathlib
import Imscribing.YangMills.IIDSchwinger

set_option maxHeartbeats 4000000

open Filter Topology Real

namespace YangMills

/-- Spatial lattice size: (m+2)^2, always ≥ 4. -/
def ymLs (m : ℕ) : ℕ := (m + 2) ^ 2

/-- Temporal lattice size: (m+2)^2, always ≥ 4. -/
def ymLt (m : ℕ) : ℕ := (m + 2) ^ 2

/-- Lattice spacing: 1/(m+2) → 0⁺. -/
noncomputable def ymA (m : ℕ) : ℝ := 1 / ((m : ℝ) + 2)

/-- Inverse coupling: m → ∞. -/
def ymBeta (m : ℕ) : ℝ := (m : ℝ)

theorem ymLs_pos (m : ℕ) : 0 < ymLs m := by unfold ymLs; positivity
theorem ymLt_pos (m : ℕ) : 0 < ymLt m := by unfold ymLt; positivity

theorem ymLs_inf : Tendsto ymLs atTop atTop := by
  unfold ymLs
  refine tendsto_atTop_mono (fun m => ?_) (tendsto_add_atTop_nat 2)
  nlinarith [sq_nonneg (m + 2 : ℕ)]

theorem ymLt_inf : Tendsto ymLt atTop atTop := ymLs_inf

theorem ymA_pos (m : ℕ) : 0 < ymA m := by unfold ymA; positivity
theorem ymA_zero : Tendsto ymA atTop (𝓝 0) := by
  unfold ymA
  have hden : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)
  simpa [one_div] using (tendsto_inv_atTop_zero.comp hden)

theorem ymVol_s_inf : Tendsto (fun m => (ymLs m : ℝ) * ymA m) atTop atTop := by
  have h : (fun m : ℕ => (ymLs m : ℝ) * ymA m) = fun m : ℕ => (m : ℝ) + 2 := by
    funext m
    unfold ymLs ymA
    push_cast
    field_simp
  rw [h]
  exact tendsto_atTop_add_const_right atTop (2 : ℝ)
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)

theorem ymVol_t_inf : Tendsto (fun m => (ymLt m : ℝ) * ymA m) atTop atTop := ymVol_s_inf

theorem ymBeta_nonneg (m : ℕ) : 0 ≤ ymBeta m := by unfold ymBeta; positivity
theorem ymBeta_inf : Tendsto ymBeta atTop atTop := by unfold ymBeta; exact tendsto_natCast_atTop_atTop

#print axioms YangMills.ymLs_inf
#print axioms YangMills.ymA_zero
#print axioms YangMills.ymVol_s_inf

end YangMills
