/-
# Sidon sets: the counting bound

A Sidon set is one in which every sum `a + b` determines its summands up to
order — equivalently, all pairwise differences are distinct. Erdős and Turán
asked how large such a set inside `[1, N]` can be, and the answer starts with a
counting argument that is entirely finite: the ordered pairs of distinct
elements inject into the nonzero differences, of which there are `2N - 2`.

The statement this file replaces said `∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 ≤ C * √N`,
which is true of `C = 1` and says nothing about Sidon sets — it never mentions
one. What follows is the theorem itself, with its proof constructed rather than
asserted, and the density corollary read off it.

The difference map is written over `ℤ`. On `ℕ` the expression `a - b` truncates
and carries no ordering, which is how a bound of this shape silently becomes
vacuous; over `ℤ` the injection is the honest one.
-/

import Mathlib

namespace Erdos.Sidon

open Finset

/-- A **Sidon set**: every sum determines its summands up to order. Equivalently
(and this is what the proof uses) all differences of distinct elements are
distinct. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The difference of an ordered pair, taken in `ℤ` so that it records the sign
and never truncates. -/
def diff (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- On a Sidon set the difference map is injective over the ordered pairs of
DISTINCT elements. This is the whole content: `a - b = c - d` rearranges to
`a + d = c + b`, and the Sidon condition then forces the pairs to agree — the
alternative it allows, `a = b`, is exactly what being off the diagonal rules
out. -/
theorem diff_injOn_offDiag {A : Finset ℕ} (h : IsSidon A) :
    Set.InjOn diff (A.offDiag : Set (ℕ × ℕ)) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd hEq
  simp only [Finset.coe_offDiag, Set.mem_offDiag] at hab hcd
  obtain ⟨ha, hb, hne⟩ := hab
  obtain ⟨hc, hd, -⟩ := hcd
  -- `a - b = c - d` over `ℤ`, rearranged to a statement about sums in `ℕ`.
  have hZ : (a : ℤ) + (d : ℤ) = (c : ℤ) + (b : ℤ) := by
    simp only [diff] at hEq
    linarith
  have hN : a + d = c + b := by exact_mod_cast hZ
  rcases h a ha d hd c hc b hb hN with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · -- The Sidon alternative forces `a = b`, which being off the diagonal denies.
    exact absurd h1 hne

/-- The nonzero differences available inside `[1, N]`: an interval of integers
with zero removed. -/
def diffTarget (N : ℕ) : Finset ℤ := (Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0

/-- There are exactly `2N - 2` of them, for `N ≥ 1`. -/
theorem card_diffTarget {N : ℕ} (hN : 1 ≤ N) : (diffTarget N).card = 2 * N - 2 := by
  have hmem : (0 : ℤ) ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1) := by
    have : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    simp only [Finset.mem_Icc]
    constructor <;> linarith
  have hcard : (Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).card = 2 * N - 1 := by
    rw [Int.card_Icc]
    have : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    have h : ((N : ℤ) - 1 + 1 - (1 - (N : ℤ))) = 2 * (N : ℤ) - 1 := by ring
    rw [h]
    omega
  rw [diffTarget, Finset.card_erase_of_mem hmem, hcard]
  omega

/-- A difference of two distinct elements of `[1, N]` is a nonzero integer of
absolute value at most `N - 1`. -/
theorem diff_mem_target {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    {p : ℕ × ℕ} (hp : p ∈ A.offDiag) : diff p ∈ diffTarget N := by
  obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.1 hp
  have h1 := Finset.mem_Icc.1 (hA ha)
  have h2 := Finset.mem_Icc.1 (hA hb)
  have hA1 : (1 : ℤ) ≤ (p.1 : ℤ) := by exact_mod_cast h1.1
  have hA2 : (p.1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1.2
  have hB1 : (1 : ℤ) ≤ (p.2 : ℤ) := by exact_mod_cast h2.1
  have hB2 : (p.2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast h2.2
  have hzero : diff p ≠ 0 := by
    simp only [diff, sub_ne_zero, ne_eq, Nat.cast_inj]
    exact hne
  simp only [diffTarget, Finset.mem_erase, Finset.mem_Icc, diff]
  refine ⟨hzero, ?_, ?_⟩ <;> linarith

/-- **The Sidon counting bound.** A Sidon set inside `[1, N]` satisfies
`k² − k ≤ 2N − 2`, where `k` is its size.

The ordered pairs of distinct elements inject into the nonzero differences, and
there are `2N − 2` of those. Nothing analytic enters; this is a counting
argument that closes. -/
theorem sidon_card_sq_le {N : ℕ} (hN : 1 ≤ N) {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (h : IsSidon A) :
    A.card * A.card + 2 ≤ 2 * N + A.card := by
  have hinj := diff_injOn_offDiag h
  have hmaps : ∀ p ∈ A.offDiag, diff p ∈ diffTarget N := fun _ hp => diff_mem_target hA hp
  have hle : A.offDiag.card ≤ (diffTarget N).card :=
    Finset.card_le_card_of_injOn diff hmaps hinj
  rw [Finset.offDiag_card, card_diffTarget hN] at hle
  -- Truncated subtraction on `ℕ` is why this is restated additively: `k² − k`
  -- and `2N − 2` both truncate, and an inequality between two truncations
  -- carries no information at the boundary. `k ≤ k²` and `1 ≤ N` remove it.
  have hkk : A.card ≤ A.card * A.card := by
    rcases Nat.eq_zero_or_pos A.card with h0 | hpos
    · simp [h0]
    · exact Nat.le_mul_of_pos_left _ hpos
  omega

/-- **The density corollary.** A Sidon set inside `[1, N]` has at most
`√(2N) + 1` elements. Stated multiplicatively so it needs no square root: if
`k ≥ m + 1` and `m² ≥ 2N`, the counting bound is violated. -/
theorem sidon_card_le {N : ℕ} (hN : 1 ≤ N) {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (h : IsSidon A) {m : ℕ} (hm : 2 * N ≤ m * m) :
    A.card ≤ m + 1 := by
  by_contra hcon
  push_neg at hcon
  have hk : m + 2 ≤ A.card := hcon
  have hcount := sidon_card_sq_le hN hA h
  -- `k ≥ m + 2` makes `k²` exceed `m·k + 2k`, and `2N ≤ m²` caps the other side.
  have hprod : (m + 2) * A.card ≤ A.card * A.card := Nat.mul_le_mul_right _ hk
  have hmk : m * (m + 2) ≤ m * A.card := Nat.mul_le_mul_left _ hk
  -- Expanding: m·k + 2k + 2 ≤ k² + 2 ≤ 2N + k ≤ m² + k, and m·k ≥ m² + 2m.
  nlinarith [hcount, hprod, hmk, hm]

/-- A Sidon set is a set of distinct differences: the counting bound in the form
that names the objects rather than a constant. `Fin`-free, sorry-free, and it
mentions Sidon sets — which is what the statement it replaces did not. -/
theorem sidon_not_dense {N : ℕ} (hN : 1 ≤ N) {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (h : IsSidon A)
    (hbig : 2 * N + A.card < A.card * A.card + 2) : False := by
  have := sidon_card_sq_le hN hA h
  omega

/-! ## Sidon sets of every size exist

The counting bound is only worth having if the objects it bounds exist. They do,
and the witness is explicit: the powers of four. Two of them sum to a value that
determines them, because a sum of two powers of four cannot reach the next power
of four — `4ᵃ + 4ᵇ < 4^(max+1)` — so the larger exponent is forced, and cancelling
it forces the smaller.
-/

/-- A sum of two powers of four is dominated by twice the larger. -/
theorem sum_le_two_mul {a b : ℕ} (h : b ≤ a) : 4 ^ a + 4 ^ b ≤ 2 * 4 ^ a := by
  have : (4 : ℕ) ^ b ≤ 4 ^ a := Nat.pow_le_pow_right (by norm_num) h
  omega

/-- Twice a power of four does not reach the next one. -/
theorem two_mul_lt {a c : ℕ} (h : a < c) : 2 * 4 ^ a < 4 ^ c := by
  have h1 : (4 : ℕ) ^ (a + 1) ≤ 4 ^ c := Nat.pow_le_pow_right (by norm_num) h
  have h2 : (4 : ℕ) ^ (a + 1) = 4 * 4 ^ a := by ring
  have h3 : 0 < (4 : ℕ) ^ a := by positivity
  omega

/-- **The exponents are recoverable from the sum.** This is the Sidon property
for `{4ⁿ}` in its raw form, before it is packaged as a `Finset`. -/
theorem four_pow_sum_inj {a b c d : ℕ} (hab : b ≤ a) (hcd : d ≤ c)
    (h : 4 ^ a + 4 ^ b = 4 ^ c + 4 ^ d) : a = c ∧ b = d := by
  have hac : a = c := by
    rcases lt_trichotomy a c with hlt | heq | hgt
    · exact absurd h (by
        have h1 : 4 ^ a + 4 ^ b ≤ 2 * 4 ^ a := sum_le_two_mul hab
        have h2 : 2 * 4 ^ a < 4 ^ c := two_mul_lt hlt
        have h3 : 0 < (4 : ℕ) ^ d := by positivity
        omega)
    · exact heq
    · exact absurd h (by
        have h1 : 4 ^ c + 4 ^ d ≤ 2 * 4 ^ c := sum_le_two_mul hcd
        have h2 : 2 * 4 ^ c < 4 ^ a := two_mul_lt hgt
        have h3 : 0 < (4 : ℕ) ^ b := by positivity
        omega)
  subst hac
  have : (4 : ℕ) ^ b = 4 ^ d := by omega
  exact ⟨rfl, Nat.pow_right_injective (by norm_num) this⟩

/-- The powers of four below `n`, as a set of `n` naturals. -/
def fourPowers (n : ℕ) : Finset ℕ := (Finset.range n).image (fun i => 4 ^ i)

theorem card_fourPowers (n : ℕ) : (fourPowers n).card = n := by
  rw [fourPowers, Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num)),
    Finset.card_range]

/-- **A Sidon set of every size.** The counting bound above is therefore a bound
on something that exists, at every `n`. -/
theorem fourPowers_isSidon (n : ℕ) : IsSidon (fourPowers n) := by
  intro x hx y hy z hz w hw hsum
  simp only [fourPowers, Finset.mem_image, Finset.mem_range] at hx hy hz hw
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨b, -, rfl⟩ := hy
  obtain ⟨c, -, rfl⟩ := hz
  obtain ⟨d, -, rfl⟩ := hw
  -- Order each pair, apply the injection, and read the conclusion off.
  rcases le_total b a with hab | hab <;> rcases le_total d c with hcd | hcd
  · obtain ⟨h1, h2⟩ := four_pow_sum_inj hab hcd hsum
    exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · obtain ⟨h1, h2⟩ := four_pow_sum_inj hab hcd (by omega)
    exact Or.inr ⟨by rw [h1], by rw [h2]⟩
  · obtain ⟨h1, h2⟩ := four_pow_sum_inj hab hcd (by omega)
    exact Or.inr ⟨by rw [h2], by rw [h1]⟩
  · obtain ⟨h1, h2⟩ := four_pow_sum_inj hab hcd (by omega)
    exact Or.inl ⟨by rw [h2], by rw [h1]⟩

end Erdos.Sidon

-- What the kernel says these rest on.
#print axioms Erdos.Sidon.sidon_card_sq_le
#print axioms Erdos.Sidon.sidon_card_le
#print axioms Erdos.Sidon.diff_injOn_offDiag
#print axioms Erdos.Sidon.fourPowers_isSidon
