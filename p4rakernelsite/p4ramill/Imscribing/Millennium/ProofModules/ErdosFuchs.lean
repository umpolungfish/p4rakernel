/-
PROOF MODULE: Erdős–Fuchs

The Erdős–Fuchs theorem is about the ERROR TERM in the counting function, not
about the average. For `A ⊆ ℕ` with representation function
`r_A(n) = #{(a,b) ∈ A×A : a+b = n}`, it says that

    ∑_{n ≤ N} r_A(n) = cN + o(N^{1/4} (log N)^{-1/2})

is impossible for `c > 0`: the partial sums cannot hug a linear function that
closely. The average `(1/N) ∑_{n<N} r_A(n)` is a different quantity, and it is
BOUNDED for a basis of square-root density rather than unbounded.

This module previously asserted two statements under `sorry`:

    erdos_fuchs_full            : basis of order 2 → avg_repr → ∞
    erdos_fuchs_effective_growth: basis of order 2 → avg_repr ≥ √(log N)

Neither is the Erdős–Fuchs theorem, and `sum_repr_le_card_sq` below refutes the
shape of both. The average is squeezed between two bounds that the basis
hypothesis itself supplies: at least `1 − N₀/N` from below, since every large
`n` has a representation, and at most `|A ∩ [0,N)|² / N` from above. A basis
with `|A ∩ [0,N)| ≤ C√N` therefore has average at most `C²` at every `N`, so no
divergence — let alone a `√(log N)` rate — follows from being a basis.

What the basis hypothesis does give, and it is the useful consequence, is the
square-root density bound `N − N₀ ≤ |A ∩ [0,N)|²`.

Author: Lando⊗⊙perator
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Millennium.ProofModules.ErdosFuchs

open scoped BigOperators Pointwise Classical
open Asymptotics Filter

/-- Representation function: `r_A(n) = #{(a,b) ∈ A×A : a+b = n}`. -/
noncomputable def repr_func (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card

/-- The average of the representation function over `[0,N)`. -/
noncomputable def avg_repr (A : Set ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, (repr_func A n : ℝ)) / (N : ℝ)

/-- The elements of `A` below `N`. -/
noncomputable def belowN (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun a => a ∈ A)

/-- The pairs counted by the partial sum: both entries in `A`, sum below `N`. -/
noncomputable def pairsBelow (A : Set ℕ) (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N) ×ˢ (Finset.range N)).filter
    (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 < N)

/-- **The partial sum counts exactly those pairs.** Fibering `pairsBelow` over
the sum recovers the representation function term by term. -/
theorem sum_repr_eq_card_pairs (A : Set ℕ) (N : ℕ) :
    ∑ n ∈ Finset.range N, repr_func A n = (pairsBelow A N).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun p : ℕ × ℕ => p.1 + p.2) (t := Finset.range N) ?_]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    have hnN : n < N := Finset.mem_range.1 hn
    have hfe : (pairsBelow A N).filter (fun p => p.1 + p.2 = n)
        = (Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A) := by
      ext p
      simp only [pairsBelow, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, Finset.mem_antidiagonal]
      constructor
      · intro h; exact ⟨h.2, h.1.2.1, h.1.2.2.1⟩
      · intro h
        refine ⟨⟨⟨?_, ?_⟩, h.2.1, h.2.2, ?_⟩, h.1⟩ <;> omega
    unfold repr_func
    exact congrArg Finset.card hfe.symm
  · intro p hp
    have h : p.1 + p.2 < N := by
      simpa only [pairsBelow, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] using (Finset.mem_filter.1 hp).2.2.2
    exact Finset.mem_range.2 h

/-- **The upper bound.** Every counted pair has both entries in `A ∩ [0,N)`, so
the partial sum is at most the square of that count. This is what refutes the
shape of the two statements this module used to assert: a basis of square-root
density has bounded average. -/
theorem sum_repr_le_card_sq (A : Set ℕ) (N : ℕ) :
    ∑ n ∈ Finset.range N, repr_func A n ≤ (belowN A N).card ^ 2 := by
  classical
  rw [sum_repr_eq_card_pairs, sq, ← Finset.card_product]
  refine Finset.card_le_card ?_
  rintro ⟨a, b⟩ hp
  simp only [pairsBelow, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
  simp only [Finset.mem_product, belowN, Finset.mem_filter, Finset.mem_range]
  exact ⟨⟨hp.1.1, hp.2.1⟩, ⟨hp.1.2, hp.2.2.1⟩⟩

/-- **The lower bound.** Past `N₀` every `n` has a representation, so each such
term contributes at least one. -/
theorem one_le_repr_of_mem (A : Set ℕ) {n : ℕ} (h : ∃ a ∈ A, ∃ b ∈ A, a + b = n) :
    1 ≤ repr_func A n := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := h
  unfold repr_func
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  exact ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_antidiagonal.2 hab, ha, hb⟩⟩

/-- **Square-root density is what the basis hypothesis buys.** Every `n` in
`[N₀, N)` needs its own representation, so `N − N₀ ≤ |A ∩ [0,N)|²`. -/
theorem basis_sqrt_density (A : Set ℕ) (N₀ N : ℕ)
    (hbasis : ∀ n, N₀ ≤ n → ∃ a ∈ A, ∃ b ∈ A, a + b = n) (hN : N₀ ≤ N) :
    N - N₀ ≤ (belowN A N).card ^ 2 := by
  classical
  have hlow : N - N₀ ≤ ∑ n ∈ Finset.range N, repr_func A n := by
    have hsub : Finset.Ico N₀ N ⊆ Finset.range N := by
      intro x hx
      exact Finset.mem_range.2 (Finset.mem_Ico.1 hx).2
    calc N - N₀ = ∑ _n ∈ Finset.Ico N₀ N, 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]
      _ ≤ ∑ n ∈ Finset.Ico N₀ N, repr_func A n :=
          Finset.sum_le_sum (fun n hn =>
            one_le_repr_of_mem A (hbasis n (Finset.mem_Ico.1 hn).1))
      _ ≤ ∑ n ∈ Finset.range N, repr_func A n :=
          Finset.sum_le_sum_of_subset hsub
  exact le_trans hlow (sum_repr_le_card_sq A N)

/-- **The average is bounded whenever the density is.** If `|A ∩ [0,N)| ≤ C√N`
— square-root density, which every basis of order 2 is allowed to have — then
`avg_repr A N ≤ C²`. So neither divergence nor a `√(log N)` rate follows from
being a basis, which is what the two `sorry`ed statements asserted. -/
theorem avg_bounded_of_sqrt_density (A : Set ℕ) (N : ℕ) (C : ℝ) (hN : 0 < N)
    (hden : ((belowN A N).card : ℝ) ≤ C * Real.sqrt N) :
    avg_repr A N ≤ C ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hCnn : 0 ≤ C := by
    by_contra hc
    push_neg at hc
    have : C * Real.sqrt N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc.le (Real.sqrt_nonneg _)
    have hcard : (0 : ℝ) ≤ ((belowN A N).card : ℝ) := by positivity
    have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
    nlinarith [hden, hcard, hsq]
  have hsum : (∑ n ∈ Finset.range N, (repr_func A n : ℝ)) ≤ (((belowN A N).card : ℝ)) ^ 2 := by
    have := sum_repr_le_card_sq A N
    push_cast
    exact_mod_cast this
  have hsq : (((belowN A N).card : ℝ)) ^ 2 ≤ C ^ 2 * N := by
    have hcard : (0 : ℝ) ≤ ((belowN A N).card : ℝ) := by positivity
    have h2 : (C * Real.sqrt N) ^ 2 = C ^ 2 * N := by
      rw [mul_pow, Real.sq_sqrt hNpos.le]
    nlinarith [hden, hcard, h2]
  unfold avg_repr
  rw [div_le_iff₀ hNpos]
  linarith [hsum, hsq]

#print axioms sum_repr_eq_card_pairs
#print axioms sum_repr_le_card_sq
#print axioms basis_sqrt_density
#print axioms avg_bounded_of_sqrt_density

end Millennium.ProofModules.ErdosFuchs
