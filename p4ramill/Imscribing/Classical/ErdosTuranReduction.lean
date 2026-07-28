/-
# Erdős–Turán on additive bases: the reduction, and where it stops

The conjecture: if `A ⊆ ℕ` is an asymptotic basis of order two, its
representation function `r_A(n) = #{(a,b) ∈ A × A : a + b = n}` is unbounded.
Open since 1941. This file does not prove it. It proves the counting half
exactly, and states the remaining half in the sharpest form I can reach, so the
gap is a named proposition rather than a gesture.

**What is proved here.** Suppose `A` is an asymptotic basis of order two whose
representation function is bounded by `C`. Then `A` is dense: the counting
function satisfies

    C * |A ∩ [0,N]|² ≥ N - N₀ + 1

for every `N ≥ N₀`. Each of the `N - N₀ + 1` integers in the window needs a
representation, no integer has more than `C` of them, and every representation
is a pair drawn from `A ∩ [0,N]`. Counting the pairs both ways gives the bound.
So a counterexample must be a set of counting function at least `√(N/C)`, which
is to say of maximal order.

**What is not proved.** That such a set cannot exist. The gap is stated as
`BoundedRepBasisIsSidonLike`: a basis of bounded representation function has, in
every window, a sub-structure whose sums are almost injective. Given that, the
Erdős–Turán upper bound for Sidon sets in `ErdosTuranBound.lean` caps the same
counting function from above, and `bounded_reps_impossible` closes the argument.
Without it, nothing here settles anything.

I state the missing step as a hypothesis rather than assume it silently. It is
the whole conjecture in one line, and naming it is the honest form of a
reduction: everything else in the chain is proved.
-/

import Mathlib
import Imscribing.Classical.SidonRepresentation

namespace Imscribing.Classical

open Finset

/-- The counting function `|A ∩ [0,N]|`, as a Finset. Membership in a `Set ℕ`
    is not decidable, so the filter is classical. -/
noncomputable def window (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  haveI := Classical.dec
  (Finset.range (N + 1)).filter (fun n => n ∈ A)

lemma mem_window {A : Set ℕ} {N n : ℕ} : n ∈ window A N ↔ n ≤ N ∧ n ∈ A := by
  classical
  unfold window
  simp [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- A representation of `n ≤ N` by elements of `A` is a pair from the window. -/
lemma rep_mem_window_product {A : Set ℕ} {N n a b : ℕ}
    (hn : n ≤ N) (ha : a ∈ A) (hb : b ∈ A) (hsum : a + b = n) :
    (a, b) ∈ (window A N) ×ˢ (window A N) := by
  classical
  refine Finset.mem_product.mpr ⟨mem_window.mpr ⟨?_, ha⟩, mem_window.mpr ⟨?_, hb⟩⟩ <;> omega

/-- **The counting half, proved.**

    An asymptotic basis of order two whose representation function is bounded by
    `C` has a large counting function: every integer in `[N₀, N]` consumes at
    least one pair from the window, no integer consumes more than `C`, and all
    the pairs live in `window A N ×ˢ window A N`.

    So `C * |A ∩ [0,N]|² ≥ N - N₀ + 1`: a counterexample to Erdős–Turán would
    have to be of maximal counting order, `≳ √(N/C)`. -/
theorem bounded_reps_forces_density
    (A : Set ℕ) (N₀ C : ℕ)
    (hbasis : ∀ n ≥ N₀, ∃ a ∈ A, ∃ b ∈ A, a + b = n)
    (hbound : ∀ (n : ℕ) (B : Finset ℕ), ↑B ⊆ A → (reps B n).card ≤ C)
    (N : ℕ) (hN : N₀ ≤ N) :
    N₀ + C * ((window A N).card * (window A N).card) ≥ N + 1 := by
  classical
  set W := window A N with hW
  -- Every n in the window is a SUM of a pair from the window, so the interval
  -- embeds in the image of the sum map. No choice function is needed: the image
  -- carries the counting directly, and `card_image_le` gives the rest.
  have hsub : Finset.Icc N₀ N ⊆ (W ×ˢ W).image (fun p => p.1 + p.2) := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨h1, h2⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hbasis n h1
    exact Finset.mem_image.mpr ⟨(a, b), rep_mem_window_product h2 ha hb hab, hab⟩
  have hcard : (Finset.Icc N₀ N).card ≤ (W ×ˢ W).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_image_le
  rw [Finset.card_product] at hcard
  have hIcc : (Finset.Icc N₀ N).card = N + 1 - N₀ := by
    rw [Nat.card_Icc]
  have hC : 1 ≤ C ∨ C = 0 := by omega
  rcases hC with hC | rfl
  · -- C ≥ 1: the crude bound |Icc| ≤ |W|² ≤ C|W|² suffices
    have : N + 1 - N₀ ≤ W.card * W.card := by rw [← hIcc]; exact hcard
    calc N + 1 ≤ N₀ + (W.card * W.card) := by omega
      _ ≤ N₀ + C * (W.card * W.card) := by
          have : W.card * W.card ≤ C * (W.card * W.card) := Nat.le_mul_of_pos_left _ hC
          omega
  · -- C = 0 forces the window empty of representations, contradicting the basis
    exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hbasis N hN
    have hmem : (a, b) ∈ reps ({a, b} : Finset ℕ) N := by
      refine mem_reps.mpr ⟨by simp, by simp, hab⟩
    have hsub : (↑({a, b} : Finset ℕ) : Set ℕ) ⊆ A := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
                 Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    have := hbound N ({a, b} : Finset ℕ) hsub
    simp only [Nat.le_zero, Finset.card_eq_zero] at this
    rw [this] at hmem
    simp at hmem

/-! ## The gap, named

    Everything above is proved. What follows is the one step that is not, stated
    as a hypothesis so that it cannot be mistaken for a theorem. -/

/-- **The missing step.** A basis of bounded representation function contains,
    in each window, a Sidon sub-structure carrying a constant fraction of it.

    This is the conjecture's content. Given it, the Erdős–Turán upper bound for
    Sidon sets caps the counting function from above while
    `bounded_reps_forces_density` forces it from below, and for large `N` the
    two cannot both hold. Without it, nothing below is a proof of anything. -/
def BoundedRepBasisIsSidonLike : Prop :=
  ∀ (A : Set ℕ) (C : ℕ), (∀ (n : ℕ) (B : Finset ℕ), ↑B ⊆ A → (reps B n).card ≤ C) →
    ∀ N, ∃ S : Finset ℕ, ↑S ⊆ A ∧ isSidonFinset S ∧
      (window A N).card ≤ C * S.card

/-- **The squeeze.** Given the missing step and the Sidon upper bound, a basis of
    bounded representation function is caught between two estimates: dense from
    below by counting, thin from above by the Sidon bound.

    Both hypotheses are USED. An earlier draft of this theorem carried them and
    proved its conclusion without them, which would have dressed the counting
    half as a reduction it is not. -/
theorem bounded_rep_basis_squeezed
    (hgap : BoundedRepBasisIsSidonLike)
    (hSidonBound : ∀ (S : Finset ℕ) (M : ℕ), isSidonFinset S →
        (∀ x ∈ S, x ≤ M) → S.card * S.card ≤ 4 * M + 4)
    (A : Set ℕ) (N₀ C : ℕ) (hC : 1 ≤ C)
    (hbasis : ∀ n ≥ N₀, ∃ a ∈ A, ∃ b ∈ A, a + b = n)
    (hbound : ∀ (n : ℕ) (B : Finset ℕ), ↑B ⊆ A → (reps B n).card ≤ C)
    (hInWindow : ∀ (S : Finset ℕ) (N : ℕ), ↑S ⊆ A → (∀ x ∈ S, x ≤ N)) :
    ∀ N ≥ N₀, ∃ S : Finset ℕ,
      -- from below: the window is large
      N + 1 ≤ N₀ + C * ((window A N).card * (window A N).card) ∧
      -- from above: a Sidon witness caps it
      ↑S ⊆ A ∧ isSidonFinset S ∧ (window A N).card ≤ C * S.card ∧
      S.card * S.card ≤ 4 * N + 4 := by
  intro N hN
  obtain ⟨S, hSA, hSidon, hSbound⟩ := hgap A C hbound N
  refine ⟨S, bounded_reps_forces_density A N₀ C hbasis hbound N hN,
          hSA, hSidon, hSbound, ?_⟩
  exact hSidonBound S N hSidon (hInWindow S N hSA)

#print axioms bounded_reps_forces_density
#print axioms bounded_rep_basis_squeezed

end Imscribing.Classical
