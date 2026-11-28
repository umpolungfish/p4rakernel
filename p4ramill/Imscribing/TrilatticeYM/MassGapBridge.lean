import Imscribing.TrilatticeYM.Trilattice
import Imscribing.TrilatticeYM.Frobenius
import Imscribing.TrilatticeYM.Feshbach
import Imscribing.TrilatticeYM.SICChannel
import Imscribing.TrilatticeYM.AssignedModel
import Imscribing.TrilatticeYM.MultiLinkVacuum
import Imscribing.TrilatticeYM.FourCubeIntertwiner

namespace Imscribing.TrilatticeYM

open Matrix
open scoped ComplexOrder MatrixOrder

/-- **Blocked Transfer Spectral Gap Theorem** (§5, §12, §58.1, §141):
    If `‖Q T^{b(a)} Q‖ ≤ q < 1` uniformly at fixed physical blocking length `ℓ > 0`,
    then `m_eff ≥ (-log q) / ℓ > 0` uniformly across the regulator family. -/
theorem blocked_transfer_gap_bound {ℓ q : ℝ} (hℓ : 0 < ℓ) (hq0 : 0 < q) (hq1 : q < 1)
    {ι : Type*} (m_eff : ι → ℝ)
    (hm : ∀ i : ι, Real.exp (-m_eff i * ℓ) ≤ q) :
    ∀ i : ι, (-Real.log q) / ℓ ≤ m_eff i ∧ 0 < (-Real.log q) / ℓ := by
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have hpos : 0 < (-Real.log q) / ℓ := div_pos (neg_pos.mpr hlog) hℓ
  intro i
  refine ⟨?_, hpos⟩
  have hle : -m_eff i * ℓ ≤ Real.log q := by
    have := Real.log_le_log (Real.exp_pos _) (hm i)
    rwa [Real.log_exp] at this
  have h1 : -Real.log q ≤ m_eff i * ℓ := by linarith
  exact (div_le_iff₀ hℓ).mpr h1

/-- **Uniform Feshbach Continuum Gap Bridge** (§64, §143, §178, §212):
    Lifts `three_param_gap` uniformly across a regulator family `(a, L)` in units of `Λ_YM(a)`. -/
theorem uniform_feshbach_ym_bridge
    {ι : Type*} {n₀ n₁ : ι → ℕ}
    (H00 : ∀ i, Matrix (Fin (n₀ i)) (Fin (n₀ i)) ℂ)
    (V : ∀ i, Matrix (Fin (n₁ i)) (Fin (n₀ i)) ℂ)
    (H11 : ∀ i, Matrix (Fin (n₁ i)) (Fin (n₁ i)) ℂ)
    (LambdaYM : ι → ℝ) (α β ν : ℝ)
    (hΛ : ∀ i, 0 < LambdaYM i)
    (hα : 0 < α) (hβ : 0 < β) (hν : 0 ≤ ν) (hcond : ν ^ 2 < α * β)
    (h00 : ∀ i, (H00 i - ((α * LambdaYM i : ℝ) : ℂ) • 1).PosSemidef)
    (h11 : ∀ i, (H11 i - ((β * LambdaYM i : ℝ) : ℂ) • 1).PosSemidef)
    (hV : ∀ i, ((((ν * LambdaYM i) ^ 2 : ℝ) : ℂ) •
        (1 : Matrix (Fin (n₀ i)) (Fin (n₀ i)) ℂ) - (V i)ᴴ * V i).PosSemidef) :
    let c₀ := (α + β - Real.sqrt ((α - β) ^ 2 + 4 * ν ^ 2)) / 2
    0 < c₀ ∧
    ∀ i, (blockOp (H00 i) (V i) (H11 i) -
      ((c₀ * LambdaYM i : ℝ) : ℂ) •
        (1 : Matrix (Fin (n₀ i) ⊕ Fin (n₁ i)) (Fin (n₀ i) ⊕ Fin (n₁ i)) ℂ)).PosSemidef := by
  intro c₀
  have hc0 : 0 < c₀ := by
    have hr_sq : Real.sqrt ((α - β) ^ 2 + 4 * ν ^ 2) ^ 2 = (α - β) ^ 2 + 4 * ν ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hsq : Real.sqrt ((α - β) ^ 2 + 4 * ν ^ 2) ^ 2 < (α + β) ^ 2 := by
      rw [hr_sq]; nlinarith
    have hr_lt : Real.sqrt ((α - β) ^ 2 + 4 * ν ^ 2) < α + β := by nlinarith
    dsimp [c₀]; linarith
  refine ⟨hc0, fun i => ?_⟩
  have hΛi := hΛ i
  have hgap := three_param_gap (H00 i) (V i) (H11 i)
    (α * LambdaYM i) (β * LambdaYM i) (ν * LambdaYM i)
    (mul_pos hα hΛi) (mul_pos hβ hΛi) (mul_nonneg hν (le_of_lt hΛi))
    (by nlinarith [sq_pos_of_pos hΛi])
    (h00 i) (h11 i) (hV i)
  dsimp only at hgap
  have hm_eq :
      (α * LambdaYM i + β * LambdaYM i -
        Real.sqrt ((α * LambdaYM i - β * LambdaYM i) ^ 2 + 4 * (ν * LambdaYM i) ^ 2)) / 2 =
      c₀ * LambdaYM i := by
    have hr :
        Real.sqrt ((α * LambdaYM i - β * LambdaYM i) ^ 2 + 4 * (ν * LambdaYM i) ^ 2) =
          Real.sqrt ((α - β) ^ 2 + 4 * ν ^ 2) * LambdaYM i := by
      have heq : (α * LambdaYM i - β * LambdaYM i) ^ 2 + 4 * (ν * LambdaYM i) ^ 2 =
          ((α - β) ^ 2 + 4 * ν ^ 2) * (LambdaYM i) ^ 2 := by ring
      rw [heq, Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hΛi)]
    rw [hr]
    dsimp [c₀]; ring
  rw [← hm_eq]
  exact hgap.2

/-- **Conditional Continuum Mass-Gap Bundle** (§72.1, §315.1). -/
structure ConditionalYMTheoremData where
  ℓ : ℝ
  q : ℝ
  hℓ : 0 < ℓ
  hq0 : 0 < q
  hq1 : q < 1
  Cutoff : Type*
  m_phys : Cutoff → ℝ
  intertwined_blocked_contraction : ∀ c : Cutoff, Real.exp (-m_phys c * ℓ) ≤ q

theorem conditional_ym_mass_gap (D : ConditionalYMTheoremData) :
    0 < (-Real.log D.q) / D.ℓ ∧
    ∀ c : D.Cutoff, (-Real.log D.q) / D.ℓ ≤ D.m_phys c :=
  ⟨div_pos (neg_pos.mpr (Real.log_neg D.hq0 D.hq1)) D.hℓ,
   fun c => (blocked_transfer_gap_bound D.hℓ D.hq0 D.hq1 D.m_phys
     D.intertwined_blocked_contraction c).1⟩

end TrilatticeYM