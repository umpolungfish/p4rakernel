import Mathlib

open scoped BigOperators
open Finset
open scoped Topology
noncomputable section

/-- Number of ordered unit-distance pairs in A. -/
def unit_distances (A : Finset (ℝ × ℝ)) : ℕ :=
  ((A.product A) |>.filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)).card

/-- N distinct points on the x-axis: {(1,0), (2,0), ..., (N,0)}. -/
def line_points (N : ℕ) : Finset (ℝ × ℝ) :=
  (Finset.univ : Finset (Fin N)).image (fun i => (((i.val + 1 : ℕ) : ℝ), (0 : ℝ)))

/-- The N ≥ 2 collinear lattice points on a line carry N−1 unit distances,
    hence (unit_distances ≥ (N−1) ≥ (1/2)·N). This disproves any conjectured
    sub-linear bound. -/
theorem grid_unit_distances :
    ∃ c > 0, ∀ N : ℕ, N ≥ 2 → ∃ A : Finset (ℝ × ℝ),
      A.card = N ∧ (unit_distances A : ℝ) ≥ (c : ℝ) * N := by
  refine ⟨(1 / 2 : ℝ), by norm_num, fun N hN => ?_⟩
  use line_points N
  have hlinj : Function.Injective (fun i : Fin N => (((i.val + 1 : ℕ) : ℝ), (0 : ℝ))) := by
    intro a b h
    have hfst : ((a.val + 1 : ℕ) : ℝ) = ((b.val + 1 : ℕ) : ℝ) := by
      have := congrArg (fun p : ℝ × ℝ => p.1) h
      exact this
    have hv : a.val + 1 = b.val + 1 := by exact_mod_cast hfst
    have : a.val = b.val := by omega
    exact Fin.ext this
  constructor
  · -- |line_points N| = N
    unfold line_points
    rw [Finset.card_image_of_injective _ hlinj, Finset.card_univ, Fintype.card_fin]
  · -- unit_distances (line_points N) ≥ (1/2)·N
    let adj_pairs : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
      (Finset.univ : Finset (Fin (N - 1))).image
        (fun j : Fin (N - 1) =>
          ((((j.val + 1 : ℕ) : ℝ), (0 : ℝ)),
           (((j.val + 2 : ℕ) : ℝ), (0 : ℝ))))
    have hadjcard : adj_pairs.card = N - 1 := by
      unfold adj_pairs
      have hinj : Function.Injective
          (fun j : Fin (N - 1) =>
            ((((j.val + 1 : ℕ) : ℝ), (0 : ℝ)),
             (((j.val + 2 : ℕ) : ℝ), (0 : ℝ)))) := by
        intro a b hab
        have hfst : ((a.val + 1 : ℕ) : ℝ) = ((b.val + 1 : ℕ) : ℝ) := by
          have := congrArg (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1) hab
          simpa using this
        have hv : a.val + 1 = b.val + 1 := by exact_mod_cast hfst
        have : a.val = b.val := by omega
        exact Fin.ext this
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hWgood : ∀ w ∈ adj_pairs,
        w.1 ∈ line_points N ∧ w.2 ∈ line_points N ∧ w.1 ≠ w.2 ∧ dist w.1 w.2 = 1 := by
      intro w hw
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
      have h1 : (((j.val + 1 : ℕ) : ℝ), (0 : ℝ)) ∈ line_points N := by
        unfold line_points
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        have hjN : j.val < N := by
          have := j.isLt
          omega
        exact ⟨⟨j.val, hjN⟩, by simp⟩
      have h2 : (((j.val + 2 : ℕ) : ℝ), (0 : ℝ)) ∈ line_points N := by
        unfold line_points
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        have hjN : j.val + 1 < N := by
          have := j.isLt
          omega
        refine ⟨⟨j.val + 1, hjN⟩, ?_⟩
        ext <;> push_cast <;> ring
      have hne : (((j.val + 1 : ℕ) : ℝ), (0 : ℝ)) ≠ (((j.val + 2 : ℕ) : ℝ), (0 : ℝ)) := by
        intro h
        have h1 : ((j.val + 1 : ℕ) : ℝ) = ((j.val + 2 : ℕ) : ℝ) := by
          have := congrArg (fun p : ℝ × ℝ => p.1) h
          simpa using this
        have h2 : j.val + 1 = j.val + 2 := by exact_mod_cast h1
        omega
      have hdist : dist (((j.val + 1 : ℕ) : ℝ), (0 : ℝ)) (((j.val + 2 : ℕ) : ℝ), (0 : ℝ)) = 1 := by
        rw [Prod.dist_eq]
        have hx : dist (((j.val + 1 : ℕ) : ℝ)) (((j.val + 2 : ℕ) : ℝ)) = 1 := by
          rw [Real.dist_eq]
          have h : ((j.val + 1 : ℕ) : ℝ) - ((j.val + 2 : ℕ) : ℝ) = -1 := by
            push_cast
            ring
          rw [h]
          norm_num
        have hy : dist (0 : ℝ) (0 : ℝ) = 0 := by simp
        rw [hx, hy]
        simp
      exact ⟨h1, h2, hne, hdist⟩
    let F := (line_points N).product (line_points N) |>.filter
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)
    have hsub : adj_pairs ⊆ F := by
      intro w hw
      obtain ⟨hA1, hA2, hne, hdist⟩ := hWgood w hw
      dsimp only [F]
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨hA1, hA2⟩
      · exact ⟨hne, hdist⟩
    have hbound_nat : (N - 1 : ℕ) ≤ unit_distances (line_points N) := by
      calc
        (N - 1 : ℕ) = adj_pairs.card := by rw [hadjcard]
        _ ≤ F.card := Finset.card_le_card hsub
        _ = unit_distances (line_points N) := by
          dsimp only [F, unit_distances]
    have hbound_real : ((N - 1 : ℕ) : ℝ) ≤ (unit_distances (line_points N) : ℝ) := by
      exact_mod_cast hbound_nat
    have hcalc : ((N - 1 : ℕ) : ℝ) ≥ (1 / 2 : ℝ) * (N : ℝ) := by
      have hN1 : (1 : ℕ) ≤ N := by omega
      have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      rw [Nat.cast_sub hN1]
      norm_num
      nlinarith
    linarith [hbound_real, hcalc]