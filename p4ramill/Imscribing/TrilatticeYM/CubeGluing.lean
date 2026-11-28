import Imscribing.TrilatticeYM.FourCubeIntertwiner
import Imscribing.TrilatticeYM.FourCubeSpectrum

/-!
# 4-Cube Spatial–Temporal Slab Decomposition and Multi-Edge Bell Gluing (§§447–448)

Formalizes:
1. Exact partition `32 = 12 + 8 + 12` (`E₀ ⊔ Eₜ ⊔ E₁`) and `24 = 6 + 12 + 6` (`F₀ ⊔ Fₜ ⊔ F₁`)
   together with all edge-face boundary incidences on the 4-cube.
2. Exact `r`-edge Bell gluing identity (448.1):
   `Tr(Π_glue^{⊗ r} (ρ₁ ⊗ ρ₂)) = (1/2)^r Tr(ρ₁ ρ₂ᵀ)`.
-/

namespace Imscribing.TrilatticeYM

open Matrix

/-- Bottom (`x₀ = 0`) spatial edges of the 4-cube (`12` edges). -/
def isBottomEdge (e : CubeEdge) : Bool := e.1.1 != 0 && vBit e.1.2 0 == 0

/-- Top (`x₀ = 1`) spatial edges of the 4-cube (`12` edges). -/
def isTopEdge (e : CubeEdge) : Bool := e.1.1 != 0 && vBit e.1.2 0 == 1

/-- Temporal strut edges (`dir = 0`, `8` edges). -/
def isTimeEdge (e : CubeEdge) : Bool := e.1.1 == 0

/-- Bottom (`x₀ = 0`) spatial faces (`6` faces). -/
def isBottomFace (f : CubeFace) : Bool := 3 ≤ f.1.val && f.2.val % 2 == 0

/-- Top (`x₀ = 1`) spatial faces (`6` faces). -/
def isTopFace (f : CubeFace) : Bool := 3 ≤ f.1.val && f.2.val % 2 == 1

/-- Temporal plaquettes (`dir₀ = 0`, `12` faces). -/
def isTimeFace (f : CubeFace) : Bool := f.1.val < 3

/-- Exact `12 + 8 + 12 = 32` edge partition, `6 + 12 + 6 = 24` face partition,
    and all spatial-temporal edge-face incidences (§447). -/
theorem cube_slab_partition_and_incidences :
    ((∑ e : CubeEdge, if isBottomEdge e then (1 : ℕ) else 0) = 12) ∧
    ((∑ e : CubeEdge, if isTopEdge e then (1 : ℕ) else 0) = 12) ∧
    ((∑ e : CubeEdge, if isTimeEdge e then (1 : ℕ) else 0) = 8) ∧
    ((∑ f : CubeFace, if isBottomFace f then (1 : ℕ) else 0) = 6) ∧
    ((∑ f : CubeFace, if isTopFace f then (1 : ℕ) else 0) = 6) ∧
    ((∑ f : CubeFace, if isTimeFace f then (1 : ℕ) else 0) = 12) ∧
    (∀ e : CubeEdge, isBottomEdge e = true →
      (∑ f : CubeFace, if edgeInFace e f && isBottomFace f then (1 : ℕ) else 0) = 2 ∧
      (∑ f : CubeFace, if edgeInFace e f && isTimeFace f then (1 : ℕ) else 0) = 1 ∧
      (∑ f : CubeFace, if edgeInFace e f && isTopFace f then (1 : ℕ) else 0) = 0) ∧
    (∀ e : CubeEdge, isTopEdge e = true →
      (∑ f : CubeFace, if edgeInFace e f && isTopFace f then (1 : ℕ) else 0) = 2 ∧
      (∑ f : CubeFace, if edgeInFace e f && isTimeFace f then (1 : ℕ) else 0) = 1 ∧
      (∑ f : CubeFace, if edgeInFace e f && isBottomFace f then (1 : ℕ) else 0) = 0) ∧
    (∀ e : CubeEdge, isTimeEdge e = true →
      (∑ f : CubeFace, if edgeInFace e f && isTimeFace f then (1 : ℕ) else 0) = 3 ∧
      (∑ f : CubeFace, if edgeInFace e f && (isBottomFace f || isTopFace f) then (1 : ℕ) else 0) = 0) ∧
    (∀ f : CubeFace, isTimeFace f = true →
      (∑ e : CubeEdge, if edgeInFace e f && isBottomEdge e then (1 : ℕ) else 0) = 1 ∧
      (∑ e : CubeEdge, if edgeInFace e f && isTopEdge e then (1 : ℕ) else 0) = 1 ∧
      (∑ e : CubeEdge, if edgeInFace e f && isTimeEdge e then (1 : ℕ) else 0) = 2) := by
  decide

private lemma prod_bell_delta {r : ℕ} (f f' g g' : Fin r → Fin 2) :
    (∏ e : Fin r, (if f e = g e ∧ f' e = g' e then (1 : ℝ) / 2 else 0)) =
      if g = f then (if g' = f' then (1 / 2 : ℝ) ^ r else 0) else 0 := by
  by_cases hg : g = f
  · subst hg
    by_cases hg' : g' = f'
    · subst hg'
      simp [Finset.prod_const, Finset.card_fin]
    · have hne : ∃ e : Fin r, f' e ≠ g' e := by
        by_contra h; push_neg at h; exact hg' (funext h).symm
      obtain ⟨e, he⟩ := hne
      rw [if_pos rfl, if_neg hg']
      exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])
  · have hne : ∃ e : Fin r, f e ≠ g e := by
      by_contra h; push_neg at h; exact hg (funext h).symm
    obtain ⟨e, he⟩ := hne
    rw [if_neg hg]
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

/-- **Exact `r`-edge Bell gluing trace identity** (§448, `(448.1)`):
    Contracting two reduced multiplicity matrices `ρ₁, ρ₂ : M_{2^r}(ℝ)` across `r` shared
    `j = 1/2` edges via `Π_glue^{⊗ r} = |Φ⁺⟩⟨Φ⁺|^{⊗ r}` yields `2^{-r} Tr(ρ₁ ρ₂ᵀ)`. -/
theorem bell_gluing_tensor (r : ℕ)
    (ρ₁ ρ₂ : Matrix (Fin r → Fin 2) (Fin r → Fin 2) ℝ) :
    ∑ f : Fin r → Fin 2, ∑ f' : Fin r → Fin 2,
      ∑ g : Fin r → Fin 2, ∑ g' : Fin r → Fin 2,
        (∏ e : Fin r, ∑ a : Fin 4, Bcomp a (f e) (f' e) * Bcomp a (g e) (g' e)) *
          ρ₁ f' f * ρ₂ g' g =
      (1 / 2 : ℝ) ^ r * (ρ₁ * ρ₂ᵀ).trace := by
  have h1 : ∀ f f' g g' : Fin r → Fin 2,
      (∏ e : Fin r, ∑ a : Fin 4, Bcomp a (f e) (f' e) * Bcomp a (g e) (g' e)) =
      if g = f then (if g' = f' then (1 / 2 : ℝ) ^ r else 0) else 0 := by
    intro f f' g g'
    calc (∏ e : Fin r, ∑ a : Fin 4, Bcomp a (f e) (f' e) * Bcomp a (g e) (g' e))
        = ∏ e : Fin r, (if f e = g e ∧ f' e = g' e then (1 : ℝ) / 2 else 0) := by
            refine Finset.prod_congr rfl fun e _ => Bcomp_glued_bell_projector (f e) (f' e) (g e) (g' e)
      _ = if g = f then (if g' = f' then (1 / 2 : ℝ) ^ r else 0) else 0 := prod_bell_delta f f' g g'
  simp_rw [h1]
  have hcollapse :
      (∑ f : Fin r → Fin 2, ∑ f' : Fin r → Fin 2,
        ∑ g : Fin r → Fin 2, ∑ g' : Fin r → Fin 2,
          (if g = f then (if g' = f' then (1 / 2 : ℝ) ^ r else 0) else 0) * ρ₁ f' f * ρ₂ g' g) =
      ∑ f : Fin r → Fin 2, ∑ f' : Fin r → Fin 2,
        (1 / 2 : ℝ) ^ r * (ρ₁ f' f * ρ₂ f' f) := by
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun f' _ => ?_
    have hg : ∀ g : Fin r → Fin 2,
        (∑ g' : Fin r → Fin 2,
          (if g = f then (if g' = f' then (1 / 2 : ℝ) ^ r else 0) else 0) * ρ₁ f' f * ρ₂ g' g) =
        if g = f then (1 / 2 : ℝ) ^ r * ρ₁ f' f * ρ₂ f' g else 0 := by
      intro g
      by_cases hgf : g = f
      · simp [hgf]
      · simp [hgf]
    simp_rw [hg]
    simp [mul_assoc]
  rw [hcollapse]
  calc (∑ f : Fin r → Fin 2, ∑ f' : Fin r → Fin 2, (1 / 2 : ℝ) ^ r * (ρ₁ f' f * ρ₂ f' f))
      = (1 / 2 : ℝ) ^ r * ∑ f : Fin r → Fin 2, ∑ f' : Fin r → Fin 2, ρ₁ f' f * ρ₂ f' f := by
          simp_rw [← Finset.mul_sum]
    _ = (1 / 2 : ℝ) ^ r * (ρ₁ * ρ₂ᵀ).trace := by
          congr 1
          rw [Finset.sum_comm]
          simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

end TrilatticeYM