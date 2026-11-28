import Mathlib
import Imscribing.Millennium.SIC_D2048_StarkAbelianity

/-!
# SIC_D2048_StarkGalois — splitting and automorphism structure at d = 2048

The intermediate field E = ℚ⟮√ε⟯ ⊆ ℝ, with √ε the dominant root of the
biquadratic X⁴ − 2047X² + 1 = (X² − ε)(X² − ε̄):
  §5  membership of s, −s, s⁻¹ (= √ε̄ = t), and ε = s² — so the real
      quadratic F_{2048} = ℚ(√4190205) = ℚ(ε) sits inside E;
  §6  every ℚ-automorphism of E sends s to one of s, −s, s⁻¹, −s⁻¹;
  §7  the composed action (g·h)(s) = h(g(s)) = g(h(s)) commutes at the
      generator — the sign-and-inverse action on {s, −s, s⁻¹, −s⁻¹} is
      abelian in structure.

Note m_{2048} = (2048−3)(2048+1) = 2045·2049 = 4190205, so the Stark base
F_{2048} = ℚ(√4190205) is precisely ℚ(ε).
-/

noncomputable section

namespace Imscribing.Millennium.StarkGaloisD2048

open Imscribing.Millennium.StarkAbelianityD2048

open scoped Real Polynomial

abbrev E : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ ({s} : Set ℝ)

/-- The generator as an element of its own adjunction. -/
abbrev sE : ↥E := ⟨s, IntermediateField.mem_adjoin_of_mem ℚ (Set.mem_singleton s)⟩

/-- s ≠ 0 as a carrier fact. -/
theorem sE_ne_zero : (sE : E) ≠ 0 := by
  intro h0
  exact s_ne_zero (congrArg Subtype.val h0)

/-! ## §5 Membership -/

/-- The contracting root lies in ℚ⟮s⟯: t = 1/s = aeval s 1 / aeval s X. -/
theorem tE_mem : (t : ℝ) ∈ E := by
  exact (IntermediateField.mem_adjoin_simple_iff (F := ℚ) (α := s) (x := t)).mpr
    ⟨Polynomial.C 1, Polynomial.X, by simp [t_eq_inv_s]⟩

/-- The contracting root as a carrier element. -/
abbrev tE : ↥E := ⟨t, tE_mem⟩

/-- −s ∈ ℚ⟮s⟯. -/
theorem neg_s_mem : (-s : ℝ) ∈ E :=
  (IntermediateField.mem_adjoin_simple_iff (F := ℚ) (α := s) (x := -s)).mpr
    ⟨-Polynomial.X, 1, by simp⟩

/-- s⁻¹ = t; the inverse of the generator is the carrier's contracting root. -/
theorem s_inv_eq_tE : (sE : E)⁻¹ = tE := by
  apply Subtype.ext
  simpa using t_eq_inv_s

/-- The dominant embedding ε = s² lies in ℚ⟮s⟯ — hence F_{2048} = ℚ(ε) ⊆ E. -/
theorem alpha_mem : (alpha : ℝ) ∈ E := by
  rw [← s_sq]
  exact (IntermediateField.mem_adjoin_simple_iff (F := ℚ) (α := s) (x := s ^ 2)).mpr
    ⟨Polynomial.X ^ 2, 1, by simp⟩

/-! ## §6 Automorphisms preserve the quartic root structure -/

/-- The quartic vanishes at the carrier generator, inside E itself. -/
theorem aeval_sqrt_quartic_E : Polynomial.aeval (sE : E) quarticQ = 0 := by
  have h1 : E.val (Polynomial.aeval (sE : E) quarticQ) = 0 := by
    rw [← Polynomial.aeval_algHom_apply E.val (sE : E) quarticQ]
    simpa using aeval_sqrt_quartic
  exact Subtype.ext (by simpa using h1)

/-- Any ℚ-automorphism of E sends s to a root of the quartic, in E. -/
theorem aeval_aut_quartic_E (g : E ≃ₐ[ℚ] E) : Polynomial.aeval (g sE : E) quarticQ = 0 := by
  rw [Polynomial.aeval_algHom_apply g (sE : E) quarticQ, aeval_sqrt_quartic_E, map_zero]

/-- For any real x, aeval x quarticQ = 0 implies the quartic form equation. -/
theorem quartic_form_of_aeval (x : ℝ) (h : Polynomial.aeval x quarticQ = 0) :
    x ^ 4 - 2047 * x ^ 2 + 1 = 0 := by
  rw [quarticQ] at h
  simpa using h

/-- Any ℚ-automorphism of E sends s to one of s, −s, s⁻¹, −s⁻¹. -/
theorem aut_case (g : E ≃ₐ[ℚ] E) :
    (g sE : E) = sE ∨ (g sE : E) = -sE ∨ (g sE : E) = (sE : E)⁻¹ ∨ (g sE : E) = -((sE : E)⁻¹) := by
  have hroot : Polynomial.aeval ((g sE : E) : ℝ) quarticQ = 0 := by
    have key := Polynomial.aeval_algHom_apply E.val (g sE) quarticQ
    rw [aeval_aut_quartic_E g, map_zero] at key
    exact key
  have hform := quartic_form_of_aeval ((g sE : E) : ℝ) hroot
  rcases real_root_structure (g sE : ℝ) hform with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · refine Or.inr (Or.inr (Or.inl (Subtype.ext ?_)))
    rw [s_inv_eq_tE, h]
  · refine Or.inr (Or.inr (Or.inr (Subtype.ext ?_)))
    rw [s_inv_eq_tE, h]
    rfl

/-! ## §7 The sign-and-inverse action commutes at the generator -/

/-- The composed automorphism action on the generator commutes: the values
    g(h(s)) and h(g(s)) agree. Every ℚ-automorphism sends s into
    {s, −s, s⁻¹, −s⁻¹}; the induced action is by sign flip and inversion,
    and sign and inversion commute. -/
theorem aut_compose_pointwise (g h : E ≃ₐ[ℚ] E) : g (h sE : E) = h (g sE : E) := by
  rcases aut_case g with hg | hg | hg | hg <;>
    rcases aut_case h with hh | hh | hh | hh <;>
    simp only [hg, hh, map_neg, map_inv₀] <;>
    simp only [neg_neg, neg_inv, inv_inv]

end Imscribing.Millennium.StarkGaloisD2048

end
