/-
  Imscribing/YangMills/PiFubini.lean

  Fubini coordinate-splitting for Measure.pi over Fin (r+1), following the
  Mathlib piFinSuccAbove measure-preservation API.  Standard axioms only.
-/
import Mathlib
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 8000000

open MeasureTheory Filter Topology Set

namespace YangMills

/-- Single-coordinate Fubini split for Measure.pi at index i. -/
theorem integral_pi_split_at
    {r : ℕ} {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Fin (r + 1) → Measure α) [∀ j, SigmaFinite (μ j)]
    (i : Fin (r + 1)) {f : (Fin (r + 1) → α) → E}
    (hf : Integrable f (Measure.pi μ)) :
    ∫ x, f x ∂(Measure.pi μ) =
      ∫ y : Fin r → α,
        ∫ t : α, f (Fin.insertNth (α := fun _ => α) i t y) ∂(μ i)
      ∂(Measure.pi fun j => μ (i.succAbove j)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => α) i
  have hmp : MeasurePreserving e (Measure.pi μ)
      ((μ i).prod <| Measure.pi fun j => μ (i.succAbove j)) :=
    measurePreserving_piFinSuccAbove μ i
  -- hcomp: integrable on prod measure
  have hcomp : Integrable (fun p : α × (Fin r → α) => f (e.symm p))
      ((μ i).prod (Measure.pi fun j => μ (i.succAbove j))) := by
    -- hmp.symm: MeasurePreserving e.symm prod pi, so Integrable (g ∘ e.symm) prod ↔ Integrable g pi
    exact (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  calc
    ∫ x, f x ∂(Measure.pi μ)
        = ∫ p, f (e.symm p) ∂((μ i).prod (Measure.pi fun j => μ (i.succAbove j))) := by
            rw [← hmp.integral_comp e.measurableEmbedding (fun p => f (e.symm p))]
            simp
    _ = ∫ y : Fin r → α, ∫ t : α, f (e.symm (t, y)) ∂(μ i)
          ∂(Measure.pi fun j => μ (i.succAbove j)) := by
        rw [integral_prod_symm _ hcomp]
    _ = ∫ y : Fin r → α, ∫ t : α, f (Fin.insertNth (α := fun _ => α) i t y) ∂(μ i)
          ∂(Measure.pi fun j => μ (i.succAbove j)) := by
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        rfl

end YangMills
