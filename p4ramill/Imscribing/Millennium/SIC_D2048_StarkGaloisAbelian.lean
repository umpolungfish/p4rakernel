import Mathlib
import Imscribing.Millennium.SIC_D2048_StarkGalois

/-!
# SIC_D2048_StarkGaloisAbelian — Gal(ℚ⟮√ε⟯/ℚ) is abelian at d = 2048

The transport rung. Every element of E = ℚ⟮s⟯ is a rational function in the
generator s (by `mem_adjoin_simple_iff`), automorphisms commute with
polynomial evaluation at the generator (`aeval_algHom_apply` + the
16-case action theorem `aut_compose_pointwise`), and they respect division
(`map_div₀`). Composition of automorphisms therefore commutes:
the Klein four-group structure {1, neg, inv, neg∘inv} closes at group level.

  §8  the carrier formula: x = aeval sE r / aeval sE q for all x ∈ E;
  §9  automorphism agreement on the generator determines the automorphism
      (`aut_ext`);
  §10 group-level abelianity: g.trans h = h.trans g, with the pointwise
      form ∀ x, g (h x) = h (g x).
-/

noncomputable section

namespace Imscribing.Millennium.StarkGaloisD2048

open Imscribing.Millennium.StarkAbelianityD2048

open scoped Real Polynomial

/-! ## §8 Every element of ℚ⟮s⟯ is a rational function of the generator -/

theorem aevalE_coe (p : ℚ[X]) :
    E.val (Polynomial.aeval (sE : E) p) = Polynomial.aeval (s : ℝ) p := by
  rw [← Polynomial.aeval_algHom_apply E.val (sE : E) p]
  rfl

/-- Carrier formula: every element of E is a quotient of polynomial
    evaluations at the generator, presented inside E. -/
theorem mem_eq_frac (x : ↥E) (r q : ℚ[X])
    (hx : (x : ℝ) = Polynomial.aeval (s : ℝ) r / Polynomial.aeval (s : ℝ) q) :
    x = (Polynomial.aeval (sE : E) r) / (Polynomial.aeval (sE : E) q) := by
  apply Subtype.ext
  show (x : ℝ) = E.val (Polynomial.aeval (sE : E) r / Polynomial.aeval (sE : E) q)
  rw [map_div₀ E.val, aevalE_coe r, aevalE_coe q, hx]

/-! ## §9 The generator determines the automorphism -/

/-- Polynomial evaluation at the generator transports along automorphisms:
    the evaluation commutes with the automorphism application. -/
theorem aeval_aut_apply (g : E ≃ₐ[ℚ] E) (p : ℚ[X]) :
    Polynomial.aeval (g sE : E) p = g (Polynomial.aeval (sE : E) p) :=
  Polynomial.aeval_algHom_apply g (sE : E) p

/-- Agreement on the generator determines the automorphism. -/
theorem aut_ext {g h : E ≃ₐ[ℚ] E} (hgh : (g sE : E) = (h sE : E)) : g = h := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨r, q, hx⟩ := (IntermediateField.mem_adjoin_simple_iff (F := ℚ) (α := s)
    (x := (x : ℝ))).mp x.property
  have hgN : g (Polynomial.aeval (sE : E) r) = h (Polynomial.aeval (sE : E) r) := by
    rw [← aeval_aut_apply g, ← aeval_aut_apply h, hgh]
  have hgD : g (Polynomial.aeval (sE : E) q) = h (Polynomial.aeval (sE : E) q) := by
    rw [← aeval_aut_apply g, ← aeval_aut_apply h, hgh]
  rw [mem_eq_frac x r q hx, map_div₀ g, hgN, hgD, map_div₀ h]

/-! ## §10 Group-level abelianity -/

/-- Pointwise abelianity: automorphisms commute at every element. -/
theorem galois_abelian_pointwise (g h : E ≃ₐ[ℚ] E) :
    ∀ x : ↥E, g (h x) = h (g x) := by
  intro x
  obtain ⟨r, q, hx⟩ := (IntermediateField.mem_adjoin_simple_iff (F := ℚ) (α := s)
    (x := (x : ℝ))).mp x.property
  have hcomm : ∀ p : ℚ[X],
      g (h (Polynomial.aeval (sE : E) p)) = h (g (Polynomial.aeval (sE : E) p)) := by
    intro p
    have eL : g (h (Polynomial.aeval (sE : E) p))
        = Polynomial.aeval ((g (h sE : E)) : E) p := by
      rw [← Polynomial.aeval_algHom_apply h (sE : E) p,
        ← Polynomial.aeval_algHom_apply g (h sE : E) p]
    have eR : h (g (Polynomial.aeval (sE : E) p))
        = Polynomial.aeval ((h (g sE : E)) : E) p := by
      rw [← Polynomial.aeval_algHom_apply g (sE : E) p,
        ← Polynomial.aeval_algHom_apply h (g sE : E) p]
    rw [eL, eR, aut_compose_pointwise g h]
  have hgN := hcomm r
  have hgD := hcomm q
  calc g (h x)
      _ = g (h (Polynomial.aeval (sE : E) r / Polynomial.aeval (sE : E) q)) := by
        rw [mem_eq_frac x r q hx]
      _ = g (h (Polynomial.aeval (sE : E) r) / h (Polynomial.aeval (sE : E) q)) := by
        rw [map_div₀ h]
      _ = g (h (Polynomial.aeval (sE : E) r)) / g (h (Polynomial.aeval (sE : E) q)) :=
        map_div₀ g _ _
      _ = h (g (Polynomial.aeval (sE : E) r)) / h (g (Polynomial.aeval (sE : E) q)) := by
        rw [hgN, hgD]
      _ = h (g (Polynomial.aeval (sE : E) r) / g (Polynomial.aeval (sE : E) q)) :=
        (map_div₀ h _ _).symm
      _ = h (g (Polynomial.aeval (sE : E) r / Polynomial.aeval (sE : E) q)) := by
        rw [map_div₀ g]
      _ = h (g x) := by rw [← mem_eq_frac x r q hx]

/-- Group-level abelianity: composition of automorphisms of ℚ⟮√ε⟯/ℚ commutes.
    The Galois group Gal(ℚ⟮√ε⟯/ℚ) acts by sign flip and inversion on the
    generator, so it is (a quotient of) the Klein four-group V₄. -/
theorem galois_abelian_trans (g h : E ≃ₐ[ℚ] E) : g.trans h = h.trans g := by
  apply AlgEquiv.ext
  intro x
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  exact (galois_abelian_pointwise g h x).symm

end Imscribing.Millennium.StarkGaloisD2048

end
