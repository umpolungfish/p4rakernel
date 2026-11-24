import Mathlib

open scoped BigOperators

/-!
A finite fractional matching implies Hall's condition, and therefore an
integral matching. This file is independent of the number-theoretic part of
the prime-entry construction.

`adj i x` says that left vertex `i` is allowed to use right vertex `x`.
`q i x` is its nonnegative fractional allocation.
-/

theorem fractionalFlow_hall
    {L R : Type*} [Fintype L] [Fintype R]
    (adj : L → R → Prop) [DecidableRel adj]
    (q : L → R → ℝ)
    (hq_nonneg : ∀ i x, 0 ≤ q i x)
    (hq_zero : ∀ i x, ¬ adj i x → q i x = 0)
    (hq_row : ∀ i, (∑ x : R, q i x) = 1)
    (hq_col : ∀ x, (∑ i : L, q i x) ≤ 1)
    (S : Finset L) :
    (S.card : ℝ) ≤
      ((Finset.univ.filter fun x : R => ∃ i ∈ S, adj i x).card : ℝ) := by
  classical
  let N : Finset R := Finset.univ.filter (fun x => ∃ i ∈ S, adj i x)

  have hrows :
      (S.card : ℝ) = ∑ i ∈ S, ∑ x : R, q i x := by
    calc
      (S.card : ℝ) = ∑ i ∈ S, (1 : ℝ) := by simp
      _ = ∑ i ∈ S, ∑ x : R, q i x := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hq_row i).symm

  have hswap :
      (∑ i ∈ S, ∑ x : R, q i x) =
        ∑ x : R, ∑ i ∈ S, q i x := by
    rw [Finset.sum_comm]

  have hzeroOutside (x : R) (hxN : x ∉ N) :
      (∑ i ∈ S, q i x) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply hq_zero
    intro hadj
    apply hxN
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, hi, hadj⟩

  have hrestrict :
      (∑ x ∈ N, ∑ i ∈ S, q i x) =
        ∑ x : R, ∑ i ∈ S, q i x := by
    apply Finset.sum_subset (Finset.subset_univ N)
    intro x hxU hxN
    exact hzeroOutside x hxN

  have hcolS (x : R) : (∑ i ∈ S, q i x) ≤ 1 := by
    calc
      (∑ i ∈ S, q i x) ≤ ∑ i : L, q i x :=
        Finset.sum_le_univ_sum_of_nonneg (fun i => hq_nonneg i x)
      _ ≤ 1 := hq_col x

  have hN :
      (∑ x ∈ N, ∑ i ∈ S, q i x) ≤ (N.card : ℝ) := by
    calc
      (∑ x ∈ N, ∑ i ∈ S, q i x) ≤ ∑ x ∈ N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        exact hcolS x
      _ = (N.card : ℝ) := by simp

  have hreal : (S.card : ℝ) ≤ (N.card : ℝ) := by
    calc
      (S.card : ℝ) = ∑ i ∈ S, ∑ x : R, q i x := hrows
      _ = ∑ x : R, ∑ i ∈ S, q i x := hswap
      _ = ∑ x ∈ N, ∑ i ∈ S, q i x := hrestrict.symm
      _ ≤ (N.card : ℝ) := hN

  simpa [N] using hreal

/--
The fractional allocation produces an actual injective choice of an
adjacent right-hand vertex for every left-hand vertex.
-/
theorem fractionalFlow_matching
    {L R : Type*} [Fintype L] [Fintype R]
    (adj : L → R → Prop)
    (q : L → R → ℝ)
    (hq_nonneg : ∀ i x, 0 ≤ q i x)
    (hq_zero : ∀ i x, ¬ adj i x → q i x = 0)
    (hq_row : ∀ i, (∑ x : R, q i x) = 1)
    (hq_col : ∀ x, (∑ i : L, q i x) ≤ 1) :
    ∃ f : L → R, Function.Injective f ∧ ∀ i, adj i (f i) := by
  classical
  let t : L → Finset R := fun i => Finset.univ.filter (fun x => adj i x)

  have hHall : ∀ S : Finset L, S.card ≤ (S.biUnion t).card := by
    intro S
    have hNat :
        S.card ≤
          (Finset.univ.filter (fun x : R => ∃ i ∈ S, adj i x)).card := by
      exact_mod_cast
        (fractionalFlow_hall adj q hq_nonneg hq_zero hq_row hq_col S)
    have hN :
        S.biUnion t =
          Finset.univ.filter (fun x : R => ∃ i ∈ S, adj i x) := by
      ext x
      simp [t]
    rw [hN]
    exact hNat

  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  refine ⟨f, hf_inj, ?_⟩
  intro i
  simpa [t] using hf_mem i
