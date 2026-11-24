import Imscribing.Erdos3

open ErdosSzekeres
open Filter Topology Real Set
open scoped Classical BigOperators Topology

noncomputable def reciprocalTerm (A : Set ℕ) (n : ℕ) : ℝ :=
  if h : n ∈ A then (1 : ℝ) / (n : ℝ) else 0

theorem reciprocalTerm_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ reciprocalTerm A n := by
  by_cases h : n ∈ A
  · simp only [reciprocalTerm, h]
    apply div_nonneg zero_le_one
    norm_num
  · simp only [reciprocalTerm, h]
    norm_num

theorem divergent_not_summable (A : Set ℕ)
    (hA : HarmonicDiverges A) :
    ¬ Summable (reciprocalTerm A) := by
  classical
  intro hs
  obtain ⟨x, hx⟩ :=
    hA ((∑' n : ℕ, reciprocalTerm A n) + 1)
  have hrepr :
      H A x = ∑ n ∈ AupTo A x, reciprocalTerm A n := by
    unfold H
    apply Finset.sum_congr rfl
    intro n hn
    have hnA : n ∈ A := by
      simp only [AupTo, Finset.mem_filter] at hn
      exact hn.2
    simp [reciprocalTerm, hnA, one_div]
  have hbound :
      H A x ≤ ∑' n : ℕ, reciprocalTerm A n := by
    rw [hrepr]
    exact hs.sum_le_tsum _
      (fun n _ => reciprocalTerm_nonneg A n)
  linarith
