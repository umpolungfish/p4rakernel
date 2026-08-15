import Mathlib

/-!
# The Cauchy–Schwarz lower bound on additive energy

`E(A) ≥ |A|⁴/|G|` for a finite abelian group `G` and `A ⊆ G`.

Elementary: the representation counts `r_A(x) = #{(a,b) ∈ A² : a + b = x}` sum to
`|A|²` across `|G|` points, so their squares cannot sum to less than the square
of the mean.

The statement is worth pinning because it is easy to misname. It is not the
Bloom–Sisask theorem, which bounds the size of a progression-free subset of
`[N]` by `C·N/(log N)^{1+c}`; no progression appears here at all. It is also
easy to state weaker than it is: `E(A) ≥ α³|G|`, with `α = |A|/|G|`, is implied
by this and falls short of it by a factor of `|A|·|G|`.

Everything is over `Finset` and ℕ-valued counts, deliberately. Phrasing it over
`Set G` with `Fintype ↑A` and a ℂ-valued indicator needs a `Decidable (x ∈ A)`
instance and a `Fintype` on the coercion that do not arrive on their own, and the
definitions fail to elaborate before any proof is reached.
-/

open Finset
open scoped BigOperators

noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The additive-energy count: quadruples with `a + b = c + d`, counted as the
number of representations of each `x` as a sum of two elements of `A`, squared
and summed. Real-valued and stated over a `Finset`, so it elaborates without
choice-of-instance games on a `Set`. -/
def reps (A : Finset G) (x : G) : ℕ := (A ×ˢ A).filter (fun p => p.1 + p.2 = x) |>.card

def energy (A : Finset G) : ℕ := ∑ x : G, (reps A x) ^ 2

/-- Every pair contributes to exactly one `x`, so the representation counts sum
to `|A|²`. -/
theorem sum_reps (A : Finset G) : ∑ x : G, reps A x = A.card ^ 2 := by
  classical
  unfold reps
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun p : G × G => p.1 + p.2)
      (s := A ×ˢ A) (t := (Finset.univ : Finset G)) (fun _ _ => Finset.mem_univ _)]
  · rw [Finset.card_product, sq]

/-- **The Cauchy–Schwarz lower bound on additive energy.**

`E(A) ≥ |A|⁴ / |G|`. The representation counts sum to `|A|²` over `|G|` points,
so squaring cannot be smaller than the square of the mean. This is the standard
bound, and it is the one an argument about energy actually uses; it is strictly
stronger than `E(A) ≥ α³|G|`, by a factor of `|A|·|G|`. -/
theorem energy_ge (A : Finset G) :
    (A.card : ℝ) ^ 4 / (Fintype.card G : ℝ) ≤ (energy A : ℝ) := by
  classical
  have hG : (0 : ℝ) < (Fintype.card G : ℝ) := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this
  have hcs : ((∑ x : G, (reps A x : ℝ))) ^ 2
      ≤ (Fintype.card G : ℝ) * ∑ x : G, (reps A x : ℝ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset G))
      (f := fun x => (reps A x : ℝ))
    simpa using this
  have hsum : (∑ x : G, (reps A x : ℝ)) = (A.card : ℝ) ^ 2 := by
    have h := sum_reps A
    calc (∑ x : G, (reps A x : ℝ)) = ((∑ x : G, reps A x : ℕ) : ℝ) := by push_cast; ring
      _ = ((A.card ^ 2 : ℕ) : ℝ) := by rw [h]
      _ = (A.card : ℝ) ^ 2 := by push_cast; ring
  rw [hsum] at hcs
  have hE : (energy A : ℝ) = ∑ x : G, (reps A x : ℝ) ^ 2 := by
    unfold energy; push_cast; ring
  rw [hE]
  rw [div_le_iff₀ hG]
  calc (A.card : ℝ) ^ 4 = ((A.card : ℝ) ^ 2) ^ 2 := by ring
    _ ≤ (Fintype.card G : ℝ) * ∑ x : G, (reps A x : ℝ) ^ 2 := hcs
    _ = (∑ x : G, (reps A x : ℝ) ^ 2) * (Fintype.card G : ℝ) := by ring

#print axioms sum_reps
#print axioms energy_ge

end

/-! ## The submitted formalisation, repaired

A file arrived stating this bound over `Set G` with a ℂ-valued indicator and a
convolution. It did not compile — the definitions failed to elaborate for want of
`Decidable (x ∈ A)` and `Fintype ↑A`, `λ` was used as a binder (it is notation
for `fun`), and six `sorry`s carried the analytic content.

Repaired here rather than replaced: the same definitions, the same conclusion,
discharged. `convolution_eq_reps` is the bridge — the convolution of indicators
at `x` counts the representations of `x`, so the ℂ-valued energy is the ℕ-valued
one and `energy_ge` applies.
-/

namespace BloomSisaskSubmitted

open scoped Classical

noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Characteristic function of a set, taking values in ℂ. -/
def indicator (A : Set G) (x : G) : ℂ := if x ∈ A then 1 else 0

/-- Convolution of two functions on a finite group. -/
def convolution (f g : G → ℂ) (x : G) : ℂ := ∑ y : G, f y * g (x - y)

/-- The density of a set `A` in `G`. -/
def density (A : Set G) : ℝ := (A.toFinset.card : ℝ) / (Fintype.card G : ℝ)

/-- The additive energy of a set `A`. -/
def additive_energy (A : Set G) : ℝ :=
  ∑ x : G, ‖convolution (indicator A) (indicator A) x‖ ^ 2

/-- The convolution of indicators counts representations. -/
theorem convolution_eq_reps (A : Set G) (x : G) :
    convolution (indicator A) (indicator A) x = (reps A.toFinset x : ℂ) := by
  classical
  -- both sides count the same thing; name each count first
  set S : Finset G := Finset.univ.filter (fun y => y ∈ A ∧ x - y ∈ A) with hS
  have hL : convolution (indicator A) (indicator A) x = (S.card : ℂ) := by
    unfold convolution indicator
    rw [hS, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases h1 : y ∈ A <;> by_cases h2 : x - y ∈ A <;> simp [h1, h2]
  have hcard : S.card = reps A.toFinset x := by
    unfold reps
    refine Finset.card_bij' (fun y _ => (y, x - y)) (fun p _ => p.1) ?_ ?_ ?_ ?_
    · intro y hy
      rw [hS, Finset.mem_filter] at hy
      simp only [Finset.mem_filter, Finset.mem_product, Set.mem_toFinset]
      exact ⟨⟨hy.2.1, hy.2.2⟩, by abel⟩
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_product, Set.mem_toFinset, Set.mem_toFinset] at hp
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hp.1.1, ?_⟩
      have : x - p.1 = p.2 := by rw [← hp.2]; abel
      rw [this]; exact hp.1.2
    · intro y _; rfl
    · intro p hp
      rw [Finset.mem_filter] at hp
      have : x - p.1 = p.2 := by rw [← hp.2]; abel
      simp [this]
  rw [hL, hcard]

/-- The submitted conclusion, proved: `E(A) ≥ α³·|G|`.

Kept under the name it arrived with so the file it came from is fixed rather
than replaced, but the name is not accurate: this is the Cauchy–Schwarz lower
bound on additive energy, not the Bloom–Sisask theorem, which bounds a
progression-free subset of `[N]` by `C·N/(log N)^{1+c}` and involves no
convolution. It is also weaker than what the argument gives — `energy_ge`
supplies `|A|⁴/|G|`, and this follows from it by `|A|·|G| ≥ 1`. -/
theorem bloom_sisask_lemma (A : Set G) (h_nonempty : A.Nonempty) :
    additive_energy A ≥ density A ^ 3 * (Fintype.card G : ℝ) := by
  classical
  set n : ℕ := A.toFinset.card with hn
  have hGpos : (0 : ℝ) < (Fintype.card G : ℝ) := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 0 < n := by
      rw [hn, Finset.card_pos]
      exact (Set.toFinset_nonempty).mpr h_nonempty
    exact_mod_cast this
  have hG1 : (1 : ℝ) ≤ (Fintype.card G : ℝ) := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this
  -- the ℂ energy is the ℕ energy
  have hEq : additive_energy A = (energy A.toFinset : ℝ) := by
    unfold additive_energy energy
    push_cast
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [convolution_eq_reps]
    simp
  -- Cauchy–Schwarz, from the corpus
  have hCS : (n : ℝ) ^ 4 / (Fintype.card G : ℝ) ≤ (energy A.toFinset : ℝ) :=
    energy_ge A.toFinset
  -- and α³|G| ≤ |A|⁴/|G|, because |A|·|G| ≥ 1
  have hDens : density A ^ 3 * (Fintype.card G : ℝ) ≤ (n : ℝ) ^ 4 / (Fintype.card G : ℝ) := by
    unfold density
    rw [div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hGpos]
    have h1 : (1 : ℝ) ≤ (n : ℝ) * (Fintype.card G : ℝ) := by nlinarith
    have hkey := mul_le_mul_of_nonneg_left h1
      (show (0:ℝ) ≤ (n : ℝ) ^ 3 * (Fintype.card G : ℝ) ^ 2 by positivity)
    nlinarith [hkey]
  rw [hEq]
  exact le_trans hDens hCS


end
end BloomSisaskSubmitted

#print axioms BloomSisaskSubmitted.convolution_eq_reps
#print axioms BloomSisaskSubmitted.bloom_sisask_lemma
