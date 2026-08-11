/-
# The ratio set is sharp, and geometric progressions do not witness it

For a finite set `A` of positive integers the ratio set `{a/b : a, b ∈ A}` has at
most `|A|² − |A| + 1` elements: the `|A|` diagonal pairs all give `1`, leaving
`|A|² − |A|` others. The question is whether that is attained.

The claim attached to this statement was that geometric progressions witness it.
They do not. For `A = {r⁰, …, rⁿ⁻¹}` the ratios are `r^(i−j)`, and the exponent
difference `i − j` ranges over `−(n−1) … (n−1)`, so the ratio set has `2n − 1`
elements — linear in `n`, not quadratic. A progression is the WORST case among
sets of distinct ratios, not the best: its exponents are an arithmetic
progression, whose differences collide maximally.

What sharpness needs is exponents whose differences are all distinct, which is a
Sidon set. Taking `A = {2^e : e ∈ S}` for a Sidon `S` makes `a/b = 2^(e−f)`
injective off the diagonal, and `Erdos.Sidon.fourPowers` supplies such an `S` at
every size. The witness is therefore a doubly-exponential set, `{2^(4ⁱ)}`, and
the bound is attained.
-/

import Imscribing.Millennium.Erdos.SidonCounting
import Imscribing.Millennium.ErdosFormalize2

open Finset
open Erdos.Sidon

namespace Erdos.RatioSet

/-- The witness: `2` raised to the powers of four, `{2^(4⁰), …, 2^(4ⁿ⁻¹)}`. -/
noncomputable def witness (n : ℕ) : Finset ℕ := (fourPowers n).image (fun e => 2 ^ e)

theorem card_witness (n : ℕ) : (witness n).card = n := by
  rw [witness, Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num)),
    card_fourPowers]

/-- Membership in the witness, named: every element is `2` to an exponent drawn
from the Sidon set. -/
theorem mem_witness {n : ℕ} {x : ℕ} (hx : x ∈ witness n) :
    ∃ e ∈ fourPowers n, x = 2 ^ e := by
  simp only [witness, Finset.mem_image] at hx
  obtain ⟨e, he, hxe⟩ := hx
  exact ⟨e, he, hxe.symm⟩

theorem witness_pos {n : ℕ} {a : ℕ} (ha : a ∈ witness n) : 0 < a := by
  obtain ⟨e, -, he⟩ := mem_witness ha
  rw [he]
  positivity

/-- The ratio map, as `ErdosFormalize2.ratioSet` uses it. -/
noncomputable def ratio (p : ℕ × ℕ) : ℚ := (p.1 : ℚ) / (p.2 : ℚ)

/-- The same function `ratioSet` images with, so the two can be rewritten into
each other rather than relying on definitional unfolding inside `image`. -/
theorem ratio_eq : ratio = fun p : ℕ × ℕ => (p.1 : ℚ) / (p.2 : ℚ) := rfl

/-- Off the diagonal the ratio map is injective on the witness: a quotient of
powers of two is `2^(e−f)`, and the Sidon property of the exponents makes the
pair recoverable. -/
theorem ratio_injOn {n : ℕ} : Set.InjOn ratio ((witness n).offDiag : Set (ℕ × ℕ)) := by
  rintro p hp q hq hEq
  simp only [Finset.coe_offDiag, Set.mem_offDiag] at hp hq
  obtain ⟨hp1, hp2, hpne⟩ := hp
  obtain ⟨hq1, hq2, -⟩ := hq
  obtain ⟨a, ha, hpa⟩ := mem_witness hp1
  obtain ⟨b, hb, hpb⟩ := mem_witness hp2
  obtain ⟨c, hc, hqc⟩ := mem_witness hq1
  obtain ⟨d, hd, hqd⟩ := mem_witness hq2
  -- `2^a / 2^b = 2^c / 2^d` clears to `2^(a+d) = 2^(c+b)` over `ℚ`.
  have hQ : ((2 : ℚ) ^ a) / ((2 : ℚ) ^ b) = ((2 : ℚ) ^ c) / ((2 : ℚ) ^ d) := by
    simpa [ratio, hpa, hpb, hqc, hqd] using hEq
  have hb0 : ((2 : ℚ) ^ b) ≠ 0 := by positivity
  have hd0 : ((2 : ℚ) ^ d) ≠ 0 := by positivity
  have hmul : (2 : ℚ) ^ a * (2 : ℚ) ^ d = (2 : ℚ) ^ c * (2 : ℚ) ^ b := by
    field_simp at hQ
    linarith [hQ]
  have hpow : (2 : ℚ) ^ (a + d) = (2 : ℚ) ^ (c + b) := by
    rw [pow_add, pow_add]; exact hmul
  -- Down to `ℕ`, where the exponent injectivity of `2 ^ ·` is available.
  have hnat : (2 : ℕ) ^ (a + d) = (2 : ℕ) ^ (c + b) := by exact_mod_cast hpow
  have hexp : a + d = c + b := Nat.pow_right_injective (le_refl 2) hnat
  -- The Sidon property of the exponents recovers the pair.
  rcases fourPowers_isSidon n a ha d hd c hc b hb hexp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- a = c and d = b: the pairs agree.
    have e1 : p.1 = q.1 := by rw [hpa, hqc, h1]
    have e2 : p.2 = q.2 := by rw [hpb, hqd, h2]
    exact Prod.ext e1 e2
  · -- a = b: the two entries of `p` coincide, which off the diagonal is denied.
    exact absurd (by rw [hpa, hpb, h1] : p.1 = p.2) hpne

/-- On the diagonal every ratio is `1`. -/
theorem ratio_diag {n : ℕ} {a : ℕ} (ha : a ∈ witness n) : ratio (a, a) = 1 := by
  have : 0 < a := witness_pos ha
  simp only [ratio]
  field_simp

/-- Off the diagonal no ratio is `1`. -/
theorem ratio_ne_one {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ (witness n).offDiag) : ratio p ≠ 1 := by
  obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.1 hp
  have hp1 : 0 < p.1 := witness_pos h1
  have hp2 : 0 < p.2 := witness_pos h2
  simp only [ratio, ne_eq, div_eq_one_iff_eq (by positivity : (p.2 : ℚ) ≠ 0), Nat.cast_inj]
  exact hne

/-- **The ratio set of the witness attains the bound.** -/
theorem card_ratioSet_witness {n : ℕ} (hn : 0 < n) :
    (ErdosFormalize2.ratioSet (witness n)).card = n * n - n + 1 := by
  classical
  have hsplit : (witness n) ×ˢ (witness n) = (witness n).diag ∪ (witness n).offDiag := by
    rw [Finset.diag_union_offDiag]
  have hne : (witness n).Nonempty := by
    rw [← Finset.card_pos, card_witness]; exact hn
  obtain ⟨a₀, ha₀⟩ := hne
  -- The diagonal contributes exactly `{1}`.
  have hdiag : (witness n).diag.image ratio = {1} := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨p, hp, hval⟩ := Finset.mem_image.1 hv
      obtain ⟨hp1, hpe⟩ := Finset.mem_diag.1 hp
      have hp0 : 0 < p.1 := witness_pos hp1
      have hone : ratio p = 1 := by
        simp only [ratio, ← hpe]
        field_simp
      rw [← hval, hone]
      exact Finset.mem_singleton_self 1
    · intro v hv
      rw [Finset.mem_singleton] at hv
      subst hv
      refine Finset.mem_image.2 ⟨(a₀, a₀), Finset.mem_diag.2 ⟨ha₀, rfl⟩, ?_⟩
      have h0 : 0 < a₀ := witness_pos ha₀
      simp only [ratio]
      field_simp
  have himg : ErdosFormalize2.ratioSet (witness n)
      = insert 1 ((witness n).offDiag.image ratio) := by
    unfold ErdosFormalize2.ratioSet
    rw [← ratio_eq, hsplit, Finset.image_union, hdiag, Finset.singleton_union]
  rw [himg, Finset.card_insert_of_notMem, Finset.card_image_of_injOn ratio_injOn,
    Finset.offDiag_card, card_witness]
  · intro hmem
    obtain ⟨p, hp, hval⟩ := Finset.mem_image.1 hmem
    exact ratio_ne_one hp hval

/-- **`RatioSetSharp`, proved.** For every `n > 0` there is a set of `n` positive
integers whose ratio set has exactly `n² − n + 1` elements — the maximum. -/
theorem ratioSetSharp : ErdosFormalize2.RatioSetSharp := by
  intro n hn
  exact ⟨witness n, card_witness n, card_ratioSet_witness hn⟩

/-- And the record of what the suggested witness actually gives: a geometric
progression's ratio set is LINEAR in `n`. Its ratios are `2^(i−j)` with
`|i − j| < n`, so they all lie in a set of `2n − 1` powers — quadratic sharpness
is out of reach for it by a whole order. -/
theorem geometric_ratios_are_linear (n : ℕ) :
    (ErdosFormalize2.ratioSet ((Finset.range n).image (fun i => 2 ^ i))).card
      ≤ (Finset.Ioo (-(n : ℤ)) (n : ℤ)).card := by
  classical
  have hsub : ErdosFormalize2.ratioSet ((Finset.range n).image (fun i => 2 ^ i))
      ⊆ (Finset.Ioo (-(n : ℤ)) (n : ℤ)).image (fun k : ℤ => (2 : ℚ) ^ k) := by
    intro v hv
    unfold ErdosFormalize2.ratioSet at hv
    obtain ⟨p, hp, hval⟩ := Finset.mem_image.1 hv
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_image.1 hp1
    obtain ⟨j, hj, hpj⟩ := Finset.mem_image.1 hp2
    rw [Finset.mem_range] at hi hj
    refine Finset.mem_image.2 ⟨(i : ℤ) - (j : ℤ), Finset.mem_Ioo.2 ⟨by omega, by omega⟩, ?_⟩
    rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), ← hval, ← hpi, ← hpj]
    push_cast
    rfl
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

#print axioms Erdos.RatioSet.ratioSetSharp

end Erdos.RatioSet
