import Mathlib
import Imscribing.Millennium.SIC_D2048_StarkGaloisAbelian

/-!
# SIC_D2048_StarkGaloisCard — |Gal(ℚ⟮√ε⟯/ℚ)| ≤ 4 at d = 2048

The cardinality rung. The map g ↦ g(s) sends every ℚ-automorphism of
E = ℚ⟮s⟯ into the four-root set {s, −s, t, −t} (t = s⁻¹ = √ε̄), by §6 of
SIC_D2048_StarkGalois; it is injective by §9 (`aut_ext`); and the four roots
are pairwise distinct, because s² = ε = √4190205 ∉ {1, −1}. Hence Gal(ℚ⟮s⟯/ℚ)
has at most four elements — the ambient cardinality of the Klein four-group
V₄ that §7/§10 realized as the sign-and-inverse action.

  §11  ε ∉ {1, −1} and pairwise distinctness of s, −s, t, −t;
  §12  the four-root set RootSet, finiteness, and the bound Nat.card ≤ 4.
-/

noncomputable section

namespace Imscribing.Millennium.StarkGaloisD2048

open Imscribing.Millennium.StarkAbelianityD2048

open scoped Real Polynomial

/-! ## §11 Pairwise distinctness of the four roots -/

/-- ε ≠ 1: the quadratic X² − 2047X + 1 vanishes on neither 1 nor ε. -/
theorem alpha_ne_one : alpha ≠ 1 := by
  intro h
  have h2 : alpha ^ 2 - 2047 * alpha + 1 = 0 := alpha_quadratic
  rw [h] at h2
  norm_num at h2

/-- The generator and its negative are distinct. -/
theorem s_ne_neg : s ≠ -s := by
  intro h
  linarith [s_pos, h]

/-- s ≠ s⁻¹, from s² = ε ≠ 1. -/
theorem s_ne_inv : s ≠ s⁻¹ := by
  intro h
  have h2 : s * s⁻¹ = 1 := mul_inv_cancel₀ s_ne_zero
  rw [← h] at h2
  exact alpha_ne_one (by rw [← s_sq, pow_two]; exact h2)

/-- s ≠ −s⁻¹, from s² = ε > 0. -/
theorem s_ne_neg_inv : s ≠ -(s⁻¹) := by
  intro h
  have h3 : s * s = -(1 : ℝ) := by
    nth_rewrite 2 [h]
    rw [mul_neg, mul_inv_cancel₀ s_ne_zero]
  have h4 : alpha = -(1 : ℝ) := by
    rw [← s_sq, pow_two]
    exact h3
  have hap := alpha_pos
  rw [h4] at hap
  linarith

/-- The inverse generator and its negative are distinct. -/
theorem t_ne_neg : t ≠ -t := by
  intro h
  rw [← t_eq_inv_s] at h
  linarith [inv_pos.mpr s_pos, h]

/-! ## §12 The four-root set and the cardinality bound -/

/-- The four roots of X⁴ − 2047X² + 1 in by-index order. -/
abbrev rootFour : Fin 4 → ℝ
  | ⟨0, _⟩ => s
  | ⟨1, _⟩ => -s
  | ⟨2, _⟩ => t
  | ⟨3, _⟩ => -t

/-- RootSet is the four-root set, presented as the range of the enumeration. -/
abbrev RootSet : Set ℝ := Set.range rootFour

theorem rootSet_finite : RootSet.Finite :=
  Set.finite_range rootFour

theorem rootSet_card_le : Nat.card RootSet ≤ 4 := by
  have h4 : Nat.card (Fin 4) = 4 := by
    rw [Nat.card_eq_fintype_card]
    simp
  calc Nat.card RootSet = Nat.card (Set.range rootFour) := rfl
    _ ≤ Nat.card (Fin 4) :=
      Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = 4 := h4

/-- Every automorphism value g(s) lands in the four-root set. -/
theorem aut_mem_rootSet (g : E ≃ₐ[ℚ] E) : (g sE : ℝ) ∈ RootSet := by
  rcases aut_case g with h | h | h | h
  · exact Set.mem_range.mpr ⟨⟨0, by norm_num⟩, by rw [h]; try rfl⟩
  · exact Set.mem_range.mpr ⟨⟨1, by norm_num⟩, by rw [h]; try rfl⟩
  · exact Set.mem_range.mpr ⟨⟨2, by norm_num⟩, by rw [h, s_inv_eq_tE]; try rfl⟩
  · exact Set.mem_range.mpr ⟨⟨3, by norm_num⟩, by rw [h, s_inv_eq_tE]; try rfl⟩

/-- Evaluation at the generator embeds the Galois group into the four-root
    set. -/
def galEmbed (g : E ≃ₐ[ℚ] E) : RootSet := ⟨(g sE : ℝ), aut_mem_rootSet g⟩

/-- Injectivity of the embedding is §9 (`aut_ext`). -/
theorem aut_embed_inj : Function.Injective galEmbed := by
  intro g h hgh
  have hv : (g sE : ℝ) = (h sE : ℝ) := by
    simp only [galEmbed, Subtype.mk.injEq] at hgh
    exact hgh
  exact aut_ext (Subtype.ext hv)

/-- Capstone: Gal(ℚ⟮√ε⟯/ℚ) has at most four elements. Combined with §7/§10,
    the group is a quotient of the Klein four-group V₄ acting by sign flip
    and inversion on the generator. -/
theorem galois_card_le : Nat.card (E ≃ₐ[ℚ] E) ≤ 4 := by
  haveI : Finite ↥RootSet := rootSet_finite.to_subtype
  refine le_trans (Nat.card_le_card_of_injective _ aut_embed_inj) ?_
  exact rootSet_card_le

end Imscribing.Millennium.StarkGaloisD2048

end
