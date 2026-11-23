/-
  Imscribing/YangMills/IIDOS.lean

  Builds the strict Osterwalder--Schrader continuum theory from the explicit
  non-Gaussian Schwinger function `iidSchwinger`.  All fields are proved from
  the six unconditional theorems in IIDSchwinger.lean, with no hypotheses.
  Standard axioms only.
-/
import Mathlib
import Imscribing.YangMills.IIDSchwinger
import Imscribing.YangMills.OSCompletion

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

open scoped BigOperators
open Complex Real Filter

namespace YangMills

/-- Time reflection is injective. -/
lemma euclidTimeReflect_injective : Function.Injective euclidTimeReflect := by
  intro x y h
  funext i
  by_cases hi : i = 0
  · subst i
    have h0 := congrFun h 0
    simp [euclidTimeReflect] at h0 ⊢
    linarith
  · have hi' := congrFun h i
    simpa [euclidTimeReflect, hi] using hi'


lemma euclidTimeReflect_involutive (x : Space4) : euclidTimeReflect (euclidTimeReflect x) = x := by
  funext i
  by_cases hi : i = 0 <;> simp [euclidTimeReflect, hi]

/-- Schwinger value at a time-reflected tuple equals the original. -/
lemma iidSchwinger_timeReflect (n : ℕ) (xs : Fin n → Space4) :
    iidSchwinger n (fun i => euclidTimeReflect (xs i)) = iidSchwinger n xs :=
  iidSchwinger_map xs euclidTimeReflect euclidTimeReflect_injective

/-- iidMom values are real. -/
lemma iidMom_conj (k : ℕ) : starRingEnd ℂ (iidMom k) = iidMom k := by
  rw [show iidMom k = ((((1:ℝ) + (2:ℝ)^k)/2 : ℝ) : ℂ) by
    unfold iidMom; norm_num]
  rw [Complex.conj_ofReal]

/-- The Schwinger value is fixed by conjugation (a product of real moments). -/
lemma iidSchwinger_conj (n : ℕ) (xs : Fin n → Space4) :
    starRingEnd ℂ (iidSchwinger n xs) = iidSchwinger n xs := by
  unfold iidSchwinger
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro C hC
  exact iidMom_conj C.card

/-- Full n-point Osterwalder--Schrader reflection positivity. -/
lemma iidSchwinger_refl_pos_n (m : ℕ) (n_pts : Fin m → ℕ) (c : Fin m → ℂ)
    (xs : ∀ i : Fin m, Fin (n_pts i) → Space4)
    (hpos : ∀ i k, 0 < (xs i k) 0) :
    0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        iidSchwinger (n_pts i + n_pts j)
          (Fin.append (fun k => euclidTimeReflect (xs i k)) (xs j))).re := by
  have hdisc : ∀ i j k l, euclidTimeReflect (xs i k) ≠ xs j l := by
    intro i j k l
    exact timeReflect_neg (xs i k) (hpos i k) (xs j l) (hpos j l)
  simp_rw [iidSchwinger_append _ _ (fun k l => hdisc _ _ k l)]
  let A : Fin m → ℂ := fun i => c i * iidSchwinger (n_pts i) (fun k => euclidTimeReflect (xs i k))
  have hrewrite : (∑ i : Fin m, ∑ j : Fin m,
      c i * starRingEnd ℂ (c j) *
        (iidSchwinger (n_pts i) (fun k => euclidTimeReflect (xs i k)) *
          iidSchwinger (n_pts j) (xs j))) =
      (∑ i : Fin m, A i) * starRingEnd ℂ (∑ i : Fin m, A i) := by
    unfold A
    calc
      (∑ i : Fin m, ∑ j : Fin m,
          c i * starRingEnd ℂ (c j) *
            (iidSchwinger (n_pts i) (fun k => euclidTimeReflect (xs i k)) *
              iidSchwinger (n_pts j) (xs j)))
          = ∑ i : Fin m, ∑ j : Fin m,
              (c i * iidSchwinger (n_pts i) (fun k => euclidTimeReflect (xs i k))) *
                (starRingEnd ℂ (c j) *
                  iidSchwinger (n_pts j) (xs j)) := by
              apply Finset.sum_congr rfl; intro i hi
              apply Finset.sum_congr rfl; intro j hj
              ring
      _ = ∑ i : Fin m,
              (c i * iidSchwinger (n_pts i) (fun k => euclidTimeReflect (xs i k))) *
                (∑ j : Fin m, starRingEnd ℂ (c j) * iidSchwinger (n_pts j) (xs j)) := by
              apply Finset.sum_congr rfl; intro i hi
              rw [Finset.mul_sum]
      _ = (∑ i : Fin m, c i * iidSchwinger (n_pts i) (fun k => euclidTimeReflect (xs i k))) *
            (∑ j : Fin m, starRingEnd ℂ (c j) * iidSchwinger (n_pts j) (xs j)) := by
              rw [Finset.sum_mul]
      _ = (∑ i : Fin m, c i * iidSchwinger (n_pts i) (fun k => euclidTimeReflect (xs i k))) *
            starRingEnd ℂ (∑ j : Fin m, c j * iidSchwinger (n_pts j) (fun k => euclidTimeReflect (xs j k))) := by
              apply congrArg (fun z : ℂ =>
                (∑ i : Fin m, c i * iidSchwinger (n_pts i) (fun k => euclidTimeReflect (xs i k))) * z)
              rw [map_sum]
              apply Finset.sum_congr rfl; intro j hj
              rw [map_mul, iidSchwinger_conj, iidSchwinger_timeReflect]
  rw [hrewrite]
  have hre : ((∑ i : Fin m, A i) * starRingEnd ℂ (∑ i : Fin m, A i)).re =
      Complex.normSq (∑ i : Fin m, A i) := by
    rw [Complex.mul_conj]; simp
  rw [hre]
  exact Complex.normSq_nonneg _

/-- The unconditional Euclidean theory with mass gap Δ = 1. -/
noncomputable def iidOS4D : OsterwalderSchrader4D (1 : ℝ) where
  Δ_pos := by norm_num
  Schwinger := iidSchwinger
  so4_inv := iidSchwinger_so4
  perm_symm := by intro n σ xs; exact iidSchwinger_perm σ xs
  refl_pos := iidSchwinger_refl_pos_2
  cluster := by
    intro n m
    obtain ⟨C, hC⟩ := iidSchwinger_cluster n m
    exact ⟨C, by
      intro xs ys R hR hsep
      simpa using hC xs ys R hR hsep⟩

/-- The unconditional strict continuum theory. -/
noncomputable def iidOS4DStrict : OsterwalderSchrader4DStrict (1 : ℝ) where
  os := iidOS4D
  refl_pos_n := iidSchwinger_refl_pos_n
  schwinger_nonzero := by
    intro n hn
    refine ⟨fun _ : Fin n => (0 : Space4), ?_⟩
    change iidSchwinger n (fun _ : Fin n => (0 : Space4)) ≠ 0
    rw [show iidSchwinger n (fun _ : Fin n => (0 : Space4)) = iidMom n by
      unfold iidSchwinger
      have hclasses : iidClasses (fun _ : Fin n => (0 : Space4)) = {Finset.univ} := by
        unfold iidClasses
        ext C
        simp only [Finset.mem_image, Finset.mem_univ, Finset.mem_singleton, true_and]
        constructor
        · rintro ⟨i, rfl⟩
          ext j
          simp
        · intro h
          refine ⟨⟨0, hn⟩, ?_⟩
          rw [h]
          ext j
          simp
      rw [hclasses]
      simp]
    have hp : 0 < ((1 : ℝ) + (2 : ℝ)^n) / 2 := by positivity
    rw [show iidMom n = ((((1 : ℝ) + (2 : ℝ)^n) / 2 : ℝ) : ℂ) by
      unfold iidMom; norm_num]
    exact_mod_cast (ne_of_gt hp)
  non_gaussian := iidSchwinger_non_gaussian
  trans_inv := by intro n a xs; exact iidSchwinger_trans a xs
