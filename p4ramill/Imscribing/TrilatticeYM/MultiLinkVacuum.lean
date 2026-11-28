import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

namespace Imscribing.TrilatticeYM


open Matrix
open scoped ComplexOrder MatrixOrder

structure ColoredLatticeKSHam (D : ℕ) (Link : Type*) [Fintype Link] [DecidableEq Link] where
  color : Link → Fin 13
  H : Matrix (Fin D) (Fin D) ℂ
  E : Link → Matrix (Fin D) (Fin D) ℂ
  E0 : ℝ
  H_herm : H.IsHermitian
  E_herm : ∀ ℓ, (E ℓ).IsHermitian
  g0 : ℝ
  a : ℝ
  hg0 : 0 < g0
  ha : 0 < a
  monochromatic_bound :
    ∀ (r : Fin 13) (Sr : Finset Link), (∀ ℓ ∈ Sr, color ℓ = r) →
      (H - (E0 : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) -
        ((∑ ℓ ∈ Sr, E ℓ) -
          (((16 / (g0 ^ 2 * a) * (Sr.card : ℝ) : ℝ) : ℂ) •
            (1 : Matrix (Fin D) (Fin D) ℂ)))).PosSemidef

theorem multi_link_vacuum_subtraction {D : ℕ} {Link : Type*}
    [Fintype Link] [DecidableEq Link]
    (K : ColoredLatticeKSHam D Link) (S : Finset Link) :
    ((13 : ℂ) • (K.H - (K.E0 : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ)) -
      ((∑ ℓ ∈ S, K.E ℓ) -
        (((16 / (K.g0 ^ 2 * K.a) * (S.card : ℝ) : ℝ) : ℂ) •
          (1 : Matrix (Fin D) (Fin D) ℂ)))).PosSemidef := by
  let Sr : Fin 13 → Finset Link := fun r => S.filter (fun ℓ => K.color ℓ = r)
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 13)) Sr := by
    intro r₁ _ r₂ _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro ℓ h1 h2
    simp only [Sr, Finset.mem_filter] at h1 h2
    exact hne (h1.2.symm.trans h2.2)
  have hunion : Finset.univ.biUnion Sr = S := by
    ext ℓ; simp [Sr]
  have hpart_E : ∑ r : Fin 13, ∑ ℓ ∈ Sr r, K.E ℓ = ∑ ℓ ∈ S, K.E ℓ := by
    calc ∑ r : Fin 13, ∑ ℓ ∈ Sr r, K.E ℓ
        = ∑ ℓ ∈ Finset.univ.biUnion Sr, K.E ℓ := (Finset.sum_biUnion hdisj).symm
      _ = ∑ ℓ ∈ S, K.E ℓ := by rw [hunion]
  have hpart_card : ∑ r : Fin 13, ((Sr r).card : ℝ) = (S.card : ℝ) := by
    have hnat : ∑ r : Fin 13, (Sr r).card = S.card := by
      rw [← hunion]
      exact (Finset.card_biUnion hdisj).symm
    exact_mod_cast hnat
  have hterm : ∀ r : Fin 13,
      (K.H - (K.E0 : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) -
        ((∑ ℓ ∈ Sr r, K.E ℓ) -
          (((16 / (K.g0 ^ 2 * K.a) * ((Sr r).card : ℝ) : ℝ) : ℂ) •
            (1 : Matrix (Fin D) (Fin D) ℂ)))).PosSemidef :=
    fun r => K.monochromatic_bound r (Sr r) (fun ℓ hℓ => (Finset.mem_filter.mp hℓ).2)
  have hsum :
      (∑ r : Fin 13,
        (K.H - (K.E0 : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) -
          ((∑ ℓ ∈ Sr r, K.E ℓ) -
            (((16 / (K.g0 ^ 2 * K.a) * ((Sr r).card : ℝ) : ℝ) : ℂ) •
              (1 : Matrix (Fin D) (Fin D) ℂ))))).PosSemidef := by
    clear hpart_E hpart_card
    induction (Finset.univ : Finset (Fin 13)) using Finset.induction with
    | empty =>
        simp
        exact Matrix.PosSemidef.zero
    | @insert r s hrs ih =>
        rw [Finset.sum_insert hrs]
        exact (hterm r).add ih
  have heq :
      ∑ r : Fin 13,
        (K.H - (K.E0 : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) -
          ((∑ ℓ ∈ Sr r, K.E ℓ) -
            (((16 / (K.g0 ^ 2 * K.a) * ((Sr r).card : ℝ) : ℝ) : ℂ) •
              (1 : Matrix (Fin D) (Fin D) ℂ)))) =
      ((13 : ℂ) • (K.H - (K.E0 : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ)) -
        ((∑ ℓ ∈ S, K.E ℓ) -
          (((16 / (K.g0 ^ 2 * K.a) * (S.card : ℝ) : ℝ) : ℂ) •
            (1 : Matrix (Fin D) (Fin D) ℂ)))) := by
    have hconst :
        (∑ _r : Fin 13, (K.H - (K.E0 : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ))) =
          (13 : ℂ) • (K.H - (K.E0 : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ 13]
      norm_num
    have hcsum :
        (∑ r : Fin 13,
          (((16 / (K.g0 ^ 2 * K.a) * ((Sr r).card : ℝ) : ℝ) : ℂ) •
            (1 : Matrix (Fin D) (Fin D) ℂ))) =
        (((16 / (K.g0 ^ 2 * K.a) * (S.card : ℝ) : ℝ) : ℂ) •
          (1 : Matrix (Fin D) (Fin D) ℂ)) := by
      rw [← Finset.sum_smul]
      congr 1
      have hreal : ∑ r : Fin 13, (16 / (K.g0 ^ 2 * K.a) * ((Sr r).card : ℝ)) =
          16 / (K.g0 ^ 2 * K.a) * (S.card : ℝ) := by
        rw [← Finset.mul_sum, hpart_card]
      exact_mod_cast hreal
    simp only [Finset.sum_sub_distrib, hconst, hpart_E, hcsum]
  rw [← heq]
  exact hsum

theorem high_spin_diag_gap (g0 a J : ℝ) (hg0 : 0 < g0) (ha : 0 < a)
    (hcutoff : 64 ≤ g0 ^ 4 * (J + 1 / 2) * (J + 3 / 2)) :
    (g0 ^ 2 / (52 * a)) * (J + 1 / 2) * (J + 3 / 2) ≤
      (1 / 13 : ℝ) * ((g0 ^ 2 / (2 * a)) * (J + 1 / 2) * (J + 3 / 2) - 16 / (g0 ^ 2 * a)) := by
  have h1 : 16 / (g0 ^ 2 * a) ≤ (1 / 2 : ℝ) * ((g0 ^ 2 / (2 * a)) * (J + 1 / 2) * (J + 3 / 2)) := by
    have hmul := div_le_div_of_nonneg_right hcutoff (show 0 ≤ 4 * g0 ^ 2 * a by positivity)
    have hL : 64 / (4 * g0 ^ 2 * a) = 16 / (g0 ^ 2 * a) := by
      field_simp [ne_of_gt hg0, ne_of_gt ha]; ring
    have hR : g0 ^ 4 * (J + 1 / 2) * (J + 3 / 2) / (4 * g0 ^ 2 * a) =
        (1 / 2 : ℝ) * ((g0 ^ 2 / (2 * a)) * (J + 1 / 2) * (J + 3 / 2)) := by
      field_simp [ne_of_gt hg0, ne_of_gt ha]; ring
    linarith
  have h2 : (g0 ^ 2 / (52 * a)) * (J + 1 / 2) * (J + 3 / 2) =
      (1 / 13 : ℝ) * ((1 / 2 : ℝ) * ((g0 ^ 2 / (2 * a)) * (J + 1 / 2) * (J + 3 / 2))) := by
    field_simp [ne_of_gt hg0, ne_of_gt ha]; ring
  linarith

end Imscribing.TrilatticeYM
