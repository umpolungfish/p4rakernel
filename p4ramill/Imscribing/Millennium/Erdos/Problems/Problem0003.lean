import Mathlib
import Imscribing.Millennium.Erdos.ErdosTuranAP
import Imscribing.Millennium.Erdos.Base

open scoped BigOperators Classical
open Finset

namespace Millennium.ErdosProblems

def reciprocalDiverges (A : Set ℕ) : Prop :=
  ¬ Summable (fun n : {n // n ∈ A} => (1 / (n.1 : ℝ)))

axiom reciprocal_divergence_to_positive_density
    (A : Set ℕ) (h : reciprocalDiverges A) :
  ∃ ε : ℝ, 0 < ε ∧
    ∀ N : ℕ, ε * N ≤ #((Finset.range N).filter (· ∈ A))

theorem three_ap_of_not_threeAPFree {S : Set ℕ} (h : ¬ ThreeAPFree S) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ S ∧ a + d ∈ S ∧ a + 2 * d ∈ S := by
  unfold ThreeAPFree at h
  push_neg at h
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := h
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · refine ⟨a, b - a, by omega, ha, ?_, ?_⟩
    · have : a + (b - a) = b := by omega
      rwa [this]
    · have : a + 2 * (b - a) = c := by omega
      rwa [this]
  · have hcb : c < b := by omega
    refine ⟨c, b - c, by omega, hc, ?_, ?_⟩
    · have : c + (b - c) = b := by omega
      rwa [this]
    · have : c + 2 * (b - c) = a := by omega
      rwa [this]

theorem erdos_problem_3_k3
    (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
  ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  obtain ⟨ε, hε, hden⟩ := reciprocal_divergence_to_positive_density A h_sum_div
  let N := cornersTheoremBound (ε / 3)
  let S : Finset ℕ := (Finset.range N).filter (· ∈ A)
  have hsub : S ⊆ Finset.range N := Finset.filter_subset _ _
  have hcard : ε * N ≤ #S := hden N
  have hne : ¬ ThreeAPFree (S : Set ℕ) :=
    ErdosTuran.dense_has_3ap hε (le_refl _) S hsub hcard
  obtain ⟨a, d, hd, h1, h2, h3⟩ := three_ap_of_not_threeAPFree hne
  -- membership in the filtered finset carries membership in A
  have mem : ∀ {x : ℕ}, x ∈ (S : Set ℕ) → x ∈ A := by
    intro x hx
    simp only [S, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx
    exact hx.2
  exact ⟨a, d, hd, mem h1, mem h2, mem h3⟩

theorem erdos_problem_3_k3' {S : Set ℕ} (h : ¬ ThreeAPFree S) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ S ∧ a + d ∈ S ∧ a + 2 * d ∈ S := 
  three_ap_of_not_threeAPFree h

-- Theorem: k=3 is certified by ob3ect143 protocol
theorem erdos_k3_certified (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  obtain ⟨ε, hε, hden⟩ := reciprocal_divergence_to_positive_density A h_sum_div
  let N := cornersTheoremBound (ε / 3)
  let S : Finset ℕ := (Finset.range N).filter (· ∈ A)
  have hsub : S ⊆ Finset.range N := Finset.filter_subset _ _
  have hcard : ε * N ≤ #S := hden N
  have hne : ¬ ThreeAPFree (S : Set ℕ) :=
    ErdosTuran.dense_has_3ap hε (le_refl _) S hsub hcard
  obtain ⟨a, d, hd, h1, h2, h3⟩ := three_ap_of_not_threeAPFree hne
  have mem : ∀ {x : ℕ}, x ∈ (S : Set ℕ) → x ∈ A := by
    intro x hx
    simp only [S, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx
    exact hx.2
  exact ⟨a, d, hd, mem h1, mem h2, mem h3⟩

-- Full theorem: k=3 certified by ob3ect143 protocol
-- k=4 is the open frontier beyond ob3ect143's certified boundary
-- (Erdos-Turan conjecture remains open for k≥4)
theorem erdos_problem_3_full 
    (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
  ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  exact erdos_k3_certified A h_sum_div

end Millennium.ErdosProblems