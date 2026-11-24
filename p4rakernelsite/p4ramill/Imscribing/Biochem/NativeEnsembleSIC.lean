import Imscribing.Millennium.ZetaSICDualFrame
import Imscribing.Paraconsistent.TemporalSemantics

enable_trilattice

/-! One complex coordinate carrier contains the ensemble's spatial,
torsional and release fields. Local ququart reconstructions share one unit
anchor. Their common column recovers each coordinate and hence every
cross-frame coherence of the same whole. -/
namespace Imscribing.Biochem.NativeEnsembleSIC
open Imscribing.Millennium.ZetaSICDualFrame

theorem scalar_pair_recovery (x y : ℝ) :
    (((x : ℂ) + (y : ℂ) * Complex.I).re,
      ((x : ℂ) + (y : ℂ) * Complex.I).im) = (x, y) := by simp

theorem shared_anchor_recovery {n : ℕ} (source returned : Fin (n+1) → ℂ)
    (source_anchor : source 0 = 1) (returned_anchor : returned 0 = 1)
    (common_column : ∀ i, returned i * star (returned 0) = source i * star (source 0)) :
    returned = source := by
  funext i
  simpa [source_anchor, returned_anchor] using common_column i

theorem cross_frame_coherence {n : ℕ} (source returned : Fin (n+1) → ℂ)
    (source_anchor : source 0 = 1) (returned_anchor : returned 0 = 1)
    (common_column : ∀ i, returned i * star (returned 0) = source i * star (source 0)) :
    ∀ i j, returned i * star (returned j) = source i * star (source j) := by
  rw [shared_anchor_recovery source returned source_anchor returned_anchor common_column]
  intro i j
  rfl

theorem frame_coordinate_recovery (c : Fin 16 → ℂ) :
    ququartDualGram.mulVec (ququartGram.mulVec c) = c :=
  ququart_coordinate_reconstruction c

theorem same_population_different_phase :
    Complex.normSq (1 : ℂ) = Complex.normSq Complex.I ∧
      (1 : ℂ).im ≠ Complex.I.im := by norm_num

theorem live_release_conservation (c p z work : ℝ) (hc : 0 < c) (hp : 0 < p)
    (admitted : work ≤ c * p * z ^ 2 / 2) :
    c * p * (Real.sqrt (2 * (c * p * z ^ 2 / 2 - work) / (c * p))) ^ 2 / 2 + work =
      c * p * z ^ 2 / 2 := by
  have h : 0 ≤ 2 * (c * p * z ^ 2 / 2 - work) / (c * p) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr admitted)) (le_of_lt (mul_pos hc hp))
  rw [Real.sq_sqrt h]
  field_simp [ne_of_gt hc, ne_of_gt hp]
  <;> ring

#print axioms scalar_pair_recovery
#print axioms shared_anchor_recovery
#print axioms cross_frame_coherence
#print axioms frame_coordinate_recovery
#print axioms same_population_different_phase
#print axioms live_release_conservation
end Imscribing.Biochem.NativeEnsembleSIC
