import Imscribing.Erdos710_smooth_unconditional

open scoped BigOperators

namespace Erdos710

/-!
The finite-prime part of the binary-slicing proof is represented by exponent
vectors. This file develops the elementary finite-dimensional estimates used
to compare the smooth demand and supply shells.
-/

/-- The box of exponent vectors with every coordinate at most `L`. -/
def exponentBox (α : Type*) [Fintype α] [DecidableEq α] (L : ℕ) :
    Finset (α → ℕ) :=
  Fintype.piFinset (fun _ : α => Finset.Icc 0 L)

/-- Cardinality of the exponent box. -/
theorem exponentBox_card (α : Type*) [Fintype α] [DecidableEq α] (L : ℕ) :
    (exponentBox α L).card = (L + 1) ^ Fintype.card α := by
  simp [exponentBox]

/-- The product represented by a finite prime exponent vector. -/
def exponentProduct (α : Type*) [Fintype α] [DecidableEq α]
    (p e : α → ℕ) : ℕ :=
  ∏ i : α, p i ^ e i

/-- If each prime coordinate is bounded by `2^K`, a box of exponent vectors
maps below the corresponding power of two. -/
theorem exponentProduct_le_pow_of_box (α : Type*) [Fintype α] [DecidableEq α]
    (K L : ℕ) (p : α → ℕ) (hp : ∀ i, p i ≤ 2 ^ K) (e : α → ℕ)
    (he : e ∈ exponentBox α L) :
    exponentProduct α p e ≤ 2 ^ (K * Fintype.card α * L) := by
  have hecoord : ∀ i, e i ≤ L := by
    intro i
    have hi := Fintype.mem_piFinset.mp he i
    exact (Finset.mem_Icc.mp hi).2
  unfold exponentProduct exponentBox at *
  calc
    (∏ i : α, p i ^ e i) ≤ ∏ i : α, (2 ^ K) ^ e i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Nat.zero_le _
      · intro i hi
        exact Nat.pow_le_pow_left (hp i) (e i)
    _ = (2 ^ K) ^ ∑ i : α, e i := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ (2 ^ K) ^ (Fintype.card α * L) := by
      apply Nat.pow_le_pow_right (by simp)
      calc
        ∑ i : α, e i ≤ ∑ _i : α, L :=
          Finset.sum_le_sum fun i _ => hecoord i
        _ = Fintype.card α * L := by simp
    _ = 2 ^ (K * Fintype.card α * L) := by
      calc
        (2 ^ K) ^ (Fintype.card α * L) =
            ((2 ^ K) ^ Fintype.card α) ^ L := by rw [pow_mul]
        _ = (2 ^ (K * Fintype.card α)) ^ L := by
          congr 1
          rw [← pow_mul]
        _ = 2 ^ ((K * Fintype.card α) * L) := by rw [← pow_mul]
        _ = 2 ^ (K * Fintype.card α * L) := by rfl

/-- Prime exponent vectors encode integers injectively. -/
def primeExponentProduct {P : Finset ℕ} (e : {p // p ∈ P} → ℕ) : ℕ :=
  exponentProduct {p // p ∈ P} (fun p => p.1) e

theorem primeExponentProduct_injective (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    Function.Injective (primeExponentProduct (P := P)) := by
  intro e₁ e₂ h
  apply funext
  intro p
  have hp := hP p.1 p.2
  have hfac := congrArg (fun n : ℕ => n.factorization p.1) h
  change (Finset.univ.prod fun q : {q // q ∈ P} => q.1 ^ e₁ q).factorization p.1 =
      (Finset.univ.prod fun q : {q // q ∈ P} => q.1 ^ e₂ q).factorization p.1 at hfac
  rw [Nat.factorization_prod_apply (p := p.1) (S := Finset.univ)
      (g := fun q : {q // q ∈ P} => q.1 ^ e₁ q)
      (by intro q hq; exact pow_ne_zero _ (hP q.1 q.2).ne_zero),
    Nat.factorization_prod_apply (p := p.1) (S := Finset.univ)
      (g := fun q : {q // q ∈ P} => q.1 ^ e₂ q)
      (by intro q hq; exact pow_ne_zero _ (hP q.1 q.2).ne_zero)] at hfac
  have hterm (q : {q // q ∈ P}) :
      (q.1 ^ e₁ q).factorization p.1 = if q = p then e₁ p else 0 := by
    rw [Nat.factorization_pow]
    by_cases hqp : q = p
    · subst q
      simp [hp.factorization]
    · have hval : q.1 ≠ p.1 := by
        intro hval
        apply hqp
        exact Subtype.ext hval
      have hzero : q.1.factorization p.1 = 0 := by
        by_contra hn
        exact hval (Nat.Prime.eq_of_factorization_pos (hP q.1 q.2) hn)
      simp [hzero, hqp]
  have hterm₂ (q : {q // q ∈ P}) :
      (q.1 ^ e₂ q).factorization p.1 = if q = p then e₂ p else 0 := by
    rw [Nat.factorization_pow]
    by_cases hqp : q = p
    · subst q
      simp [hp.factorization]
    · have hval : q.1 ≠ p.1 := by
        intro hval
        apply hqp
        exact Subtype.ext hval
      have hzero : q.1.factorization p.1 = 0 := by
        by_contra hn
        exact hval (Nat.Prime.eq_of_factorization_pos (hP q.1 q.2) hn)
      simp [hzero, hqp]
  simp_rw [hterm, hterm₂] at hfac
  simp at hfac
  exact hfac

/-- A product supported on primes below the cutoff is smooth. -/
theorem primeExponentProduct_smooth (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (y : ℕ)
    (hcut : ∀ p ∈ P, p < y) (e : {p // p ∈ P} → ℕ) :
    primeExponentProduct e ∈ Nat.smoothNumbers y := by
  apply Nat.mem_smoothNumbers'.2
  intro q hqprime hqdiv
  change q ∣ Finset.univ.prod (fun p : {p // p ∈ P} => p.1 ^ e p) at hqdiv
  obtain ⟨p, hpP, hdiv⟩ :=
    (hqprime.prime.dvd_finset_prod_iff
      (fun p : {p // p ∈ P} => p.1 ^ e p)).mp hqdiv
  have hqp : q = p.1 := by
    exact Nat.prime_eq_prime_of_dvd_pow hqprime (hP p.1 p.2) hdiv
  rw [hqp]
  exact hcut p.1 p.2

/-- The box of prime exponent vectors with each exponent at most `L`. -/
def primeExponentBox (P : Finset ℕ) (L : ℕ) :
    Finset ({p // p ∈ P} → ℕ) :=
  exponentBox {p // p ∈ P} L

theorem primeExponentBox_card (P : Finset ℕ) (L : ℕ) :
    (primeExponentBox P L).card = (L + 1) ^ P.card := by
  simp [primeExponentBox, exponentBox_card]

/-- Distinct prime exponent vectors in a box produce that many distinct smooth
integers below the indicated power-of-two cutoff. -/
theorem primeExponentBox_smooth_lower_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (K L y : ℕ)
    (hpBound : ∀ p ∈ P, p ≤ 2 ^ K)
    (hpCut : ∀ p ∈ P, p < y) :
    (Nat.smoothNumbersUpTo (2 ^ (K * P.card * L)) y).card ≥ (L + 1) ^ P.card := by
  let image := (primeExponentBox P L).image primeExponentProduct
  have hsubset : image ⊆ Nat.smoothNumbersUpTo (2 ^ (K * P.card * L)) y := by
    intro n hn
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hn
    rw [Nat.mem_smoothNumbersUpTo]
    constructor
    · have hbound := exponentProduct_le_pow_of_box
        {p // p ∈ P} K L (fun p => p.1) (fun p => hpBound p.1 p.2) e he
      simpa [primeExponentProduct, exponentProduct] using hbound
    · exact primeExponentProduct_smooth P hP y hpCut e
  have hcard : image.card = (primeExponentBox P L).card := by
    dsimp [image]
    exact Finset.card_image_of_injective _ (primeExponentProduct_injective P hP)
  calc
    (L + 1) ^ P.card = (primeExponentBox P L).card := (primeExponentBox_card P L).symm
    _ = image.card := hcard.symm
    _ ≤ (Nat.smoothNumbersUpTo (2 ^ (K * P.card * L)) y).card := Finset.card_le_card hsubset

/-- The odd primes below the smoothness cutoff. -/
def oddPrimesBelow (y : ℕ) : Finset ℕ := y.primesBelow.erase 2

theorem insert_two_oddPrimesBelow (y : ℕ) (hy : 3 ≤ y) :
    insert 2 (oddPrimesBelow y) = y.primesBelow := by
  have h2 : 2 ∈ y.primesBelow := by
    rw [Nat.mem_primesBelow]
    norm_num
    omega
  simp [oddPrimesBelow, h2]

/-- Mathlib's exact factorization equivalence splits each `y`-smooth integer
into its power of two and its odd smooth part. -/
def splitSmoothAtTwo (y : ℕ) (hy : 3 ≤ y) :
    ℕ × Nat.factoredNumbers (oddPrimesBelow y) ≃ Nat.smoothNumbers y := by
  have hnot : 2 ∉ oddPrimesBelow y := by simp [oddPrimesBelow]
  have hsets : Nat.factoredNumbers (insert 2 (oddPrimesBelow y)) =
      Nat.smoothNumbers y := by
    rw [insert_two_oddPrimesBelow y hy, Nat.smoothNumbers_eq_factoredNumbers_primesBelow]
  exact (Nat.equivProdNatFactoredNumbers Nat.prime_two hnot).trans
    (Equiv.setCongr hsets)

/-- A binary exponent interval of integral logarithmic width `j` contains
exactly `j` integer exponents. -/
theorem binaryExponentInterval_card (a j : ℕ) :
    (Finset.Ioc a (a + j)).card = j := by
  simp

/-- A finite set of naturals whose diameter is at most `K` has at most
`K+1` elements. -/
theorem card_le_diameter_add_one (s : Finset ℕ) (K : ℕ)
    (hdiam : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → b - a ≤ K) :
    s.card ≤ K + 1 := by
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    have hm : m ∈ s := Finset.min'_mem s hs
    have hsub : s ⊆ Finset.Icc m (m + K) := by
      intro x hx
      have hmx : m ≤ x := Finset.min'_le s x hx
      have hdiff := hdiam m hm x hx hmx
      refine Finset.mem_Icc.mpr ⟨hmx, ?_⟩
      omega
    have hcard := Finset.card_le_card hsub
    have hcard' : s.card ≤ m + K + 1 - m := by simpa using hcard
    omega

/-- Weighted products indexed by a finite exponent vector. -/
def weightedProduct {d : ℕ} (p e : Fin d → ℕ) : ℕ :=
  ∏ i : Fin d, p i ^ e i

/-- The exponent vectors whose weighted products lie in a binary shell. -/
def weightedShell (d M j : ℕ) (p : Fin (d + 1) → ℕ) :
    Finset (Fin (d + 1) → ℕ) :=
  (exponentBox (Fin (d + 1)) (M + j)).filter fun e =>
    2 ^ (M - 2 * j) < weightedProduct p e ∧
      weightedProduct p e ≤ 2 ^ (M + j)

/-- The odd-coordinate fiber of a weighted binary shell. -/
def binaryHeadFiber (d M j : ℕ) (p : Fin (d + 1) → ℕ)
    (tail : Fin d → ℕ) : Finset ℕ :=
  (Finset.Icc 0 (M + j)).filter fun a =>
    2 ^ (M - 2 * j) < weightedProduct p (Fin.cons a tail) ∧
      weightedProduct p (Fin.cons a tail) ≤ 2 ^ (M + j)

/-- In one binary shell, changing the selected odd-prime exponent has a
bounded span. -/
theorem binaryHeadFiber_diameter (d M j : ℕ) (p : Fin (d + 1) → ℕ)
    (hM : 2 * j ≤ M) (hp0 : 2 ≤ p 0)
    (htail : ∀ i, 1 ≤ p i.succ) (tail : Fin d → ℕ)
    {a b : ℕ} (ha : a ∈ binaryHeadFiber d M j p tail)
    (hb : b ∈ binaryHeadFiber d M j p tail) (hab : a ≤ b) :
    b - a ≤ 3 * j := by
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  have hpowtail : 0 < weightedProduct p.tail tail := by
    apply Finset.prod_pos
    intro i hi
    exact pow_pos (by positivity : 0 < p i.succ) _
  have hlow : 2 ^ (M - 2 * j) <
      p 0 ^ a * weightedProduct p.tail tail := by
    simpa [weightedProduct, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using ha'.1
  have hhigh : p 0 ^ b * weightedProduct p.tail tail ≤ 2 ^ (M + j) := by
    simpa [weightedProduct, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using hb'.2
  have hdiff : a + (b - a) = b := Nat.add_sub_of_le hab
  have hmul : 2 ^ (M - 2 * j) * p 0 ^ (b - a) < 2 ^ (M + j) := by
    have hleft := Nat.mul_lt_mul_of_pos_right hlow (pow_pos (by omega : 0 < p 0) (b - a))
    have heq : p 0 ^ a * weightedProduct p.tail tail * p 0 ^ (b - a) =
        p 0 ^ b * weightedProduct p.tail tail := by
      rw [← mul_assoc, ← pow_add, hdiff]
      ac_rfl
    rw [heq] at hleft
    exact hleft.trans_le hhigh
  have hpowle : 2 ^ (b - a) ≤ p 0 ^ (b - a) :=
    Nat.pow_le_pow_left hp0
  have hpowcmp : 2 ^ (M - 2 * j + (b - a)) < 2 ^ (M + j) := by
    have := Nat.mul_le_mul_left (2 ^ (M - 2 * j)) hpowle
    rw [← pow_add] at this
    exact lt_of_le_of_lt this hmul
  have hexp : M - 2 * j + (b - a) < M + j :=
    (pow_lt_pow_iff_right' (by norm_num : 1 < (2 : ℕ))).mp hpowcmp
  omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty]
    omega

end Erdos710

#print axioms Erdos710.exponentBox_card
#print axioms Erdos710.exponentProduct_le_pow_of_box
#print axioms Erdos710.primeExponentProduct_injective
#print axioms Erdos710.primeExponentProduct_smooth
#print axioms Erdos710.primeExponentBox_smooth_lower_bound
#print axioms Erdos710.insert_two_oddPrimesBelow
#print axioms Erdos710.splitSmoothAtTwo
#print axioms Erdos710.binaryExponentInterval_card
