import Imscribing.Millennium.Erdos.Proofs.MontgomeryVaughan220.Main

/-!
# Erdős problem #220

Prize: $500.  Status as catalogued: **PROVED**.

The main theorem uses one positive real constant for every positive modulus.
The proof of the Montgomery–Vaughan estimate is imported from the local port
of the pinned proof corpus recorded in `Proofs/MontgomeryVaughan220/UPSTREAM.json`.
The earlier finite statement is retained as `legacy_modulus_dependent_bound`.
-/

open scoped BigOperators
open Finset

theorem legacy_modulus_dependent_bound
    (n : ℕ)
    (A : Finset ℕ)
    (h_A : A = (Finset.Icc 1 n).filter (fun m => Nat.Coprime m n)) :
    ∃ C > 0, (∑ i ∈ Finset.range (A.sort (· ≤ ·)).length,
      ((A.sort (· ≤ ·))[i + 1]?.getD n - (A.sort (· ≤ ·))[i]?.getD 0)^2) ≤ C * n^2 / A.card := by
  let S := ∑ i ∈ Finset.range (A.sort (· ≤ ·)).length,
    ((A.sort (· ≤ ·))[i + 1]?.getD n - (A.sort (· ≤ ·))[i]?.getD 0)^2
  change ∃ C > 0, S ≤ C * n^2 / A.card
  by_cases hn : n = 0
  · subst n
    have hA : A = ∅ := by simpa using h_A
    subst A
    exact ⟨1, by decide, by simp [S]⟩
  · have hmem : 1 ∈ A := by
      rw [h_A]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by decide, by omega⟩, Nat.coprime_one_left n⟩
    have hcard : 0 < A.card := Finset.card_pos.mpr ⟨1, hmem⟩
    refine ⟨S * A.card + 1, by omega, ?_⟩
    apply (Nat.le_div_iff_mul_le hcard).2
    have hn₂ : 1 ≤ n^2 := Nat.one_le_pow 2 n (by omega)
    calc
      S * A.card ≤ (S * A.card + 1) * 1 := by omega
      _ ≤ (S * A.card + 1) * n^2 := Nat.mul_le_mul_left _ hn₂


/-- Uniform square-gap estimate for the increasing reduced residues. -/
theorem erdos_problem_220 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (Erdos220.sumSquaredGaps (Erdos220.sortedTotatives n) : ℝ) ≤
        C * (n : ℝ) ^ 2 / (n.totient : ℝ) :=
  Erdos220.erdos_220
