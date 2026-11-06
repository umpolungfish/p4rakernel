/-
# The representation function of a Sidon set

The Erdős–Turán conjecture on additive bases: if `A ⊆ ℕ` is an asymptotic basis
of order two, then its representation function

    r_A(n) = #{ (a,b) ∈ A × A : a + b = n }

is unbounded. It is open.

This file proves the bridge between that conjecture and the Sidon condition,
which is the part of the statement `ErdosTuranBound.lean` was already halfway
to. A Sidon set is exactly one whose sums are almost injective, so its
representation function is bounded by two, everywhere and with no hypotheses on
`n`. The consequence is immediate and is the reason Sidon sets are where one
looks for a counterexample: a Sidon set that were an asymptotic basis of order
two would refute the conjecture outright.

The proof shape is the banked count. Fix `n`, split the pairs, hold the pair
`{a,b}` in scope while the swap is applied, and fuse: the Sidon property says
the unordered pair is determined, and the ordered pairs over it are exactly two.
The swap involution `(a,b) ↦ (b,a)` is the same one that carries
`card_unorderedPairs` in `ErdosTuranBound.lean`.
-/

import Mathlib

namespace Imscribing.Classical

open Finset

/-- `B` is Sidon: `a + b = c + d` with all four in `B` forces `{a,b} = {c,d}`. -/
def isSidonFinset (B : Finset ℕ) : Prop :=
  ∀ {a b c d : ℕ}, a ∈ B → b ∈ B → c ∈ B → d ∈ B →
    a + b = c + d → (({a, b} : Finset ℕ) = ({c, d} : Finset ℕ))

/-- The ordered pairs from `B` summing to `n`. This is `r_B(n)` before counting. -/
def reps (B : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (B ×ˢ B).filter (fun p => p.1 + p.2 = n)

/-- Membership in `reps`, unfolded. -/
lemma mem_reps {B : Finset ℕ} {n : ℕ} {p : ℕ × ℕ} :
    p ∈ reps B n ↔ p.1 ∈ B ∧ p.2 ∈ B ∧ p.1 + p.2 = n := by
  simp [reps, mem_filter, mem_product, and_assoc]

/-- Two numbers are determined, as an ordered pair, by their unordered pair.

    `{a,b} = {c,d}` as finsets leaves exactly two ways to order them, and this
    is where the swap enters: the involution `(a,b) ↦ (b,a)` acts on the fibre
    over an unordered pair, and the fibre has at most two points because that is
    the size of the orbit. -/
lemma pair_cases {a b c d : ℕ} (h : ({a, b} : Finset ℕ) = {c, d}) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  classical
  have hc : c = a ∨ c = b := by
    have hm : c ∈ ({a, b} : Finset ℕ) := by rw [h]; simp
    simpa using hm
  have hd : d = a ∨ d = b := by
    have hm : d ∈ ({a, b} : Finset ℕ) := by rw [h]; simp
    simpa using hm
  have hbmem : b = c ∨ b = d := by
    have hm : b ∈ ({c, d} : Finset ℕ) := by rw [← h]; simp
    simpa using hm
  have hamem : a = c ∨ a = d := by
    have hm : a ∈ ({c, d} : Finset ℕ) := by rw [← h]; simp
    simpa using hm
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · -- c = a and d = a: then {c,d} is a singleton, so b must be a too
    subst hc; subst hd
    rcases hbmem with hb | hb
    · exact Or.inl ⟨rfl, hb.symm⟩
    · exact Or.inl ⟨rfl, hb.symm⟩
  · exact Or.inl ⟨hc, hd⟩
  · exact Or.inr ⟨hc, hd⟩
  · -- c = b and d = b: singleton again, so a = b
    subst hc; subst hd
    rcases hamem with ha | ha
    · exact Or.inl ⟨ha.symm, rfl⟩
    · exact Or.inl ⟨ha.symm, rfl⟩

/-- **The representation function of a Sidon set is bounded by two.**

    For every `n`, with no hypothesis on `n` and no asymptotics: a Sidon set
    admits at most two ordered representations of any number, and the two are a
    single unordered pair with its swap.

    This is the Sidon condition read as a statement about `r`, which is the
    quantity the Erdős–Turán conjecture on additive bases is about. -/
theorem sidon_reps_le_two (B : Finset ℕ) (hB : isSidonFinset B) (n : ℕ) :
    (reps B n).card ≤ 2 := by
  classical
  -- If there is nothing to count we are done; otherwise fix one representation
  -- and hold it while the swap runs. That fixed pair is the banked count.
  rcases Finset.eq_empty_or_nonempty (reps B n) with h | ⟨⟨a, b⟩, hab⟩
  · simp [h]
  obtain ⟨ha, hb, hsum⟩ := mem_reps.mp hab
  -- every representation is that pair or its swap
  have hsub : reps B n ⊆ ({(a, b), (b, a)} : Finset (ℕ × ℕ)) := by
    intro ⟨c, d⟩ hcd
    obtain ⟨hc, hd, hcd'⟩ := mem_reps.mp hcd
    have := hB ha hb hc hd (by omega)
    rcases pair_cases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  calc (reps B n).card
      ≤ ({(a, b), (b, a)} : Finset (ℕ × ℕ)).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)

/-- **The finite-fiber converse.** If every sum has at most two ordered
    representations from `B`, then `B` is Sidon. Two different unordered
    pairs with the same sum would contribute at least three ordered pairs:
    both orientations of one off-diagonal pair and one orientation of the
    other, or one diagonal pair and both orientations of the off-diagonal pair.
    This is the direction needed to feed a representation bound into the
    windowed Sidon argument. -/
theorem isSidon_of_reps_card_le_two (B : Finset ℕ)
    (hB : ∀ n : ℕ, (reps B n).card ≤ 2) : isSidonFinset B := by
  classical
  intro a b c d ha hb hc hd hsum
  by_contra hpair
  let x : ℕ × ℕ := (a, b)
  let y : ℕ × ℕ := (b, a)
  let z : ℕ × ℕ := (c, d)
  let w : ℕ × ℕ := (d, c)
  have hx : x ∈ reps B (a + b) := by
    simp [x, reps, ha, hb]
  have hy : y ∈ reps B (a + b) := by
    simp [y, reps, ha, hb, Nat.add_comm]
  have hz : z ∈ reps B (a + b) := by
    simp [z, reps, hc, hd, hsum]
  have hw : w ∈ reps B (a + b) := by
    simp [w, reps, hc, hd, Nat.add_comm, hsum]
  have hzx : z ≠ x := by
    intro h
    apply hpair
    have ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl
  have hzy : z ≠ y := by
    intro h
    apply hpair
    have ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact Finset.pair_comm _ _
  by_cases hab : a = b
  · subst b
    have hcd : c ≠ d := by
      intro h
      apply hpair
      have hac : a = c := by omega
      simp [hac, h]
    have hxz : x ≠ z := by
      intro h
      apply hpair
      have ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl
    have hxw : x ≠ w := by
      intro h
      apply hpair
      have ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl
    have hthree : 3 ≤ ({x, z, w} : Finset (ℕ × ℕ)).card := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · simp
        · simp [z, w, hcd]
      · simp [hxz, hxw]
    have hsub : ({x, z, w} : Finset (ℕ × ℕ)) ⊆ reps B (a + a) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hx
      · exact hz
      · exact hw
    have := Finset.card_le_card hsub
    have := hB (a + a)
    omega
  · have hxy : x ≠ y := by simp [x, y, hab]
    have hthree : 3 ≤ ({x, y, z} : Finset (ℕ × ℕ)).card := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · simp
        · simp [Ne.symm hzy]
      · simp [hxy, Ne.symm hzx]
    have hsub : ({x, y, z} : Finset (ℕ × ℕ)) ⊆ reps B (a + b) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    have := Finset.card_le_card hsub
    have := hB (a + b)
    omega

/-- The bound is attained, so two is the right constant and not merely an upper
    bound one could improve. -/
theorem sidon_reps_eq_two_example :
    ∃ (B : Finset ℕ) (n : ℕ), isSidonFinset B ∧ (reps B n).card = 2 := by
  refine ⟨{0, 1}, 1, ?_, by decide⟩
  intro a b c d ha hb hc hd h
  fin_cases ha <;> fin_cases hb <;> fin_cases hc <;> fin_cases hd <;>
    simp_all <;> decide

/-! ## The consequence for Erdős–Turán -/

/-- `A` is an asymptotic basis of order two: every sufficiently large `n` is a
    sum of two elements. -/
def isAsymptoticBasisTwo (A : Set ℕ) : Prop :=
  ∃ N₀, ∀ n ≥ N₀, ∃ a ∈ A, ∃ b ∈ A, a + b = n

/-- The Erdős–Turán conjecture on additive bases, stated over finite windows:
    an asymptotic basis of order two has unbounded representation function. -/
def ErdosTuranAdditiveBases : Prop :=
  ∀ (A : Set ℕ), isAsymptoticBasisTwo A →
    ∀ C : ℕ, ∃ (n : ℕ) (B : Finset ℕ), (↑B ⊆ A) ∧ C < (reps B n).card

/-- **A Sidon set cannot witness the conjecture.**

    If the conjecture holds, no set that is Sidon on every finite window is an
    asymptotic basis of order two: the conjecture demands representation counts
    above every bound, and `sidon_reps_le_two` caps them at two.

    This is why Sidon sets are where a counterexample would have to live, and
    equally why one has never been produced there: the same property that makes
    the sums nearly injective is the property that bounds `r`. -/
theorem sidon_not_basis_of_erdos_turan
    (hET : ErdosTuranAdditiveBases) (A : Set ℕ)
    (hSidon : ∀ B : Finset ℕ, ↑B ⊆ A → isSidonFinset B) :
    ¬ isAsymptoticBasisTwo A := by
  intro hbasis
  obtain ⟨n, B, hBA, hcard⟩ := hET A hbasis 2
  exact absurd (sidon_reps_le_two B (hSidon B hBA) n) (by omega)

#print axioms sidon_reps_le_two
#print axioms isSidon_of_reps_card_le_two
#print axioms sidon_not_basis_of_erdos_turan

end Imscribing.Classical
