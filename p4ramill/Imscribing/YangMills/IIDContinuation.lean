/-
  Imscribing/YangMills/IIDContinuation.lean

  Discharges the Euclidean-side fields of the OS-to-Wightman continuation
  hypothesis for the unconditional iid theory.
-/
import Mathlib
import Imscribing.YangMills.IIDOS
import Imscribing.YangMills.IIDWilsonLimit

set_option maxHeartbeats 8000000

open scoped BigOperators
open Complex Real Filter

namespace YangMills

/-- S0 = 1. -/
lemma iidSchwinger_S0 : iidSchwinger 0 Fin.elim0 = 1 := by
  simp [iidSchwinger, iidClasses]

/-- Sum of equality-class cardinals is the tuple arity. -/
lemma iidClasses_sum_card {n : ℕ} (xs : Fin n → Space4) :
    (iidClasses xs).sum (fun C => C.card) = n := by
  rw [iidClasses_eq_fibers]
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin n)).image xs)
    (g := xs) (f := fun _ : Fin n => (1 : ℕ))
    (by intro i hi; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  rw [Finset.sum_image]
  · simpa [iidSupport, iidFiber] using h
  · intro a ha b hb hab
    exact iidFiber_injective xs ha hb hab

/-- Growth bound with M = 2. -/
lemma iidSchwinger_growth (n : ℕ) (xs : Fin n → Space4) :
    ‖iidSchwinger n xs‖ ≤ (2 : ℝ) ^ n := by
  unfold iidSchwinger
  calc
    ‖(iidClasses xs).prod (fun C => iidMom C.card)‖
        ≤ (iidClasses xs).prod (fun C => ‖iidMom C.card‖) :=
          (Finset.norm_prod_le (α := ℂ) (s := iidClasses xs) (f := fun C => iidMom C.card))
    _ ≤ (iidClasses xs).prod (fun C => (2 : ℝ) ^ C.card) := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro C hC
          exact iidMom_norm_le C.card
    _ = (2 : ℝ) ^ ((iidClasses xs).sum fun C => C.card) := by
          simpa using (Finset.prod_pow_eq_pow_sum (iidClasses xs) (fun C => C.card) (2 : ℝ))
    _ = (2 : ℝ) ^ n := by rw [iidClasses_sum_card xs]

/-- Kernel hermiticity for the iid theory. -/
lemma iid_osConfigKernel_herm (x y : PosTimeConfig) :
    osConfigKernel iidOS4DStrict.toOS4DContinuumTheory x y =
      starRingEnd ℂ (osConfigKernel iidOS4DStrict.toOS4DContinuumTheory y x) := by
  dsimp [osConfigKernel, iidOS4DStrict, iidOS4D]
  rw [iidSchwinger_conj]
  have hreflect :
      iidSchwinger (y.n_pts + x.n_pts) (Fin.append (fun k => euclidTimeReflect (y.pts k)) x.pts) =
      iidSchwinger (y.n_pts + x.n_pts) (Fin.append y.pts (fun k => euclidTimeReflect (x.pts k))) := by
    calc
      iidSchwinger (y.n_pts + x.n_pts) (Fin.append (fun k => euclidTimeReflect (y.pts k)) x.pts)
          = iidSchwinger (y.n_pts + x.n_pts)
              (fun i => euclidTimeReflect ((Fin.append (fun k => euclidTimeReflect (y.pts k)) x.pts) i)) :=
            (iidSchwinger_timeReflect (y.n_pts + x.n_pts)
              (Fin.append (fun k => euclidTimeReflect (y.pts k)) x.pts)).symm
      _ = iidSchwinger (y.n_pts + x.n_pts) (Fin.append y.pts (fun k => euclidTimeReflect (x.pts k))) := by
            have hfun :
                (fun i : Fin (y.n_pts + x.n_pts) =>
                  euclidTimeReflect ((Fin.append (fun k => euclidTimeReflect (y.pts k)) x.pts) i)) =
                Fin.append y.pts (fun k => euclidTimeReflect (x.pts k)) := by
              funext i
              induction i using Fin.addCases with
              | left k => simp [euclidTimeReflect_involutive]
              | right k => simp [euclidTimeReflect_involutive]
            rw [hfun]
  rw [hreflect]
  have hdisj₁ : ∀ k l, euclidTimeReflect (x.pts k) ≠ y.pts l := by
    intro k l
    exact timeReflect_neg (x.pts k) (x.pos_t k) (y.pts l) (y.pos_t l)
  have hdisj₂ : ∀ k l, y.pts k ≠ euclidTimeReflect (x.pts l) := by
    intro k l h
    exact hdisj₁ l k h.symm
  rw [iidSchwinger_append (fun k => euclidTimeReflect (x.pts k)) y.pts hdisj₁]
  rw [iidSchwinger_append y.pts (fun k => euclidTimeReflect (x.pts k)) hdisj₂]
  ring

/-- Time-shift symmetry of the iid kernel. -/
lemma iid_osConfigKernel_kern (t : ℝ) (ht : 0 ≤ t) (x y : PosTimeConfig) :
    osConfigKernel iidOS4DStrict.toOS4DContinuumTheory (posTimeShiftConfig t ht x) y =
      osConfigKernel iidOS4DStrict.toOS4DContinuumTheory x (posTimeShiftConfig t ht y) := by
  dsimp [osConfigKernel, iidOS4DStrict, iidOS4D, posTimeShiftConfig]
  have hneg₁ : ∀ k l, euclidTimeReflect (fun i => if i = 0 then x.pts k 0 + t else x.pts k i) ≠ y.pts l := by
    intro k l h
    have h0 := congrFun h 0
    simp [euclidTimeReflect] at h0
    linarith [x.pos_t k, y.pos_t l, ht]
  have hneg₂ : ∀ k l, euclidTimeReflect (x.pts k) ≠ (fun i => if i = 0 then y.pts l 0 + t else y.pts l i) := by
    intro k l h
    have h0 := congrFun h 0
    simp [euclidTimeReflect] at h0
    linarith [x.pos_t k, y.pos_t l, ht]
  rw [iidSchwinger_append (fun k => euclidTimeReflect (fun i => if i = 0 then x.pts k 0 + t else x.pts k i)) y.pts hneg₁]
  rw [iidSchwinger_append (fun k => euclidTimeReflect (x.pts k)) (fun k i => if i = 0 then y.pts k 0 + t else y.pts k i) hneg₂]
  have hshift₁ : iidSchwinger x.n_pts
      (fun k => euclidTimeReflect (fun i => if i = 0 then x.pts k 0 + t else x.pts k i)) =
      iidSchwinger x.n_pts (fun k => euclidTimeReflect (x.pts k)) := by
    let a : Space4 := fun j => if j = 0 then -t else 0
    have hpt : ∀ k j,
        euclidTimeReflect (fun i => if i = 0 then x.pts k 0 + t else x.pts k i) j =
          euclidTimeReflect (x.pts k) j + a j := by
      intro k j
      by_cases hj : j = 0
      · subst j; simp [euclidTimeReflect, a]; ring
      · simp [euclidTimeReflect, hj, a]
    rw [show (fun k => euclidTimeReflect (fun i => if i = 0 then x.pts k 0 + t else x.pts k i)) =
        (fun k j => euclidTimeReflect (x.pts k) j + a j) by funext k j; exact hpt k j]
    exact iidSchwinger_trans a _
  have hshift₂ : iidSchwinger y.n_pts
      (fun k i => if i = 0 then y.pts k 0 + t else y.pts k i) =
      iidSchwinger y.n_pts y.pts := by
    let a : Space4 := fun j => if j = 0 then t else 0
    rw [show (fun k => fun i => if i = 0 then y.pts k 0 + t else y.pts k i) =
        (fun k j => y.pts k j + a j) by
          funext k j; by_cases hj : j = 0 <;> simp [hj, a]]
    exact iidSchwinger_trans a _
  rw [hshift₁, hshift₂]

end YangMills
