import Mathlib

namespace Imscribing.Idempotent

/-! ## 1. General ring facts (any commutative ring)

An idempotent `e` splits `1 = e + (1-e)` into orthogonal pieces. -/

theorem compl_idem {R : Type*} [CommRing R] (e : R) (h : e * e = e) :
    (1 - e) * (1 - e) = 1 - e := by
  have h1 : (1 - e) * (1 - e) = 1 - 2 * e + e * e := by ring
  rw [h1, h]; ring

/-- Orthogonality: e · (1 - e) = 0. (The "false arm".) -/
theorem orth {R : Type*} [CommRing R] (e : R) (h : e * e = e) :
    e * (1 - e) = 0 := by
  have h1 : e * (1 - e) = e - e * e := by ring
  rw [h1, h]; ring

/-- Fuse: e + (1 - e) = 1. (The "μ ∘ δ = id" identity.) -/
theorem fuse {R : Type*} [CommRing R] (e : R) : e + (1 - e) = 1 := by ring

/-- An idempotent gives a square root of 1: (2e - 1)² = 1. -/
theorem sqrt_one_of_idem {R : Type*} [CommRing R] (e : R) (h : e * e = e) :
    (2 * e - 1) * (2 * e - 1) = 1 := by
  have h1 : (2 * e - 1) * (2 * e - 1) = 4 * (e * e) - 4 * e + 1 := by ring
  rw [h1, h]; ring

/-- Conversely, a square root s of 1 gives e = (s+1)/2, i.e. 2e = s + 1,
satisfying 2·(e·e - e) = 0 (so e idempotent when 2 is a nonzerodivisor). -/
theorem idem_of_sqrt_one {R : Type*} [CommRing R] (s e : R)
    (hs : s * s = 1) (he : 2 * e = s + 1) :
    4 * (e * e) = 4 * e := by
  have h1 : 4 * (e * e) = (2 * e) * (2 * e) := by ring
  rw [h1, he]
  have h2 : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by ring
  have h3 : 4 * e = 2 * (2 * e) := by ring
  rw [h2, hs, h3, he]; ring

/-! ## 2. Extraction: factors from the idempotent via gcd

If e ≡ 1 (mod p) and q ∣ e, then gcd(e, pq) = q. -/

theorem gcd_crt_idem (p q e : ℕ) (hp : p.Prime) (h1 : e % p = 1) (h2 : q ∣ e) :
    Nat.gcd e (p * q) = q := by
  apply Nat.dvd_antisymm
  · have hcop : Nat.Coprime (Nat.gcd e (p * q)) p := by
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hpd
      have hpe : p ∣ e := dvd_trans hpd (Nat.gcd_dvd_left _ _)
      have h0 : e % p = 0 := Nat.mod_eq_zero_of_dvd hpe
      rw [h1] at h0
      exact one_ne_zero h0
    exact hcop.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)
  · exact Nat.dvd_gcd h2 (dvd_mul_left q p)

/-- Symmetric form: if f ≡ 1 (mod q) and p ∣ f, then gcd(f, pq) = p. -/
theorem gcd_crt_idem' (p q f : ℕ) (hq : q.Prime) (h1 : f % q = 1) (h2 : p ∣ f) :
    Nat.gcd f (p * q) = p := by
  rw [mul_comm]
  exact gcd_crt_idem q p f hq h1 h2

/-! ## 3. The N = 15 instance (p = 5, q = 3 for e = 10; swapped for 6) -/

theorem idem_ten : (10 : ZMod 15) * 10 = 10 := by decide
theorem idem_six : (6 : ZMod 15) * 6 = 6 := by decide
theorem fuse_15 : (10 : ZMod 15) + 6 = 1 := by decide
theorem orth_15 : (10 : ZMod 15) * 6 = 0 := by decide
theorem sqrt_15 : (2 * 10 - 1 : ZMod 15) = 4 := by decide
theorem four_sq : (4 : ZMod 15) * 4 = 1 := by decide
theorem four_not_idem : (4 : ZMod 15) * 4 ≠ 4 := by decide

/-- gcd(10, 15) = 5, obtained from the general theorem. -/
theorem gcd_ten : Nat.gcd 10 (5 * 3) = 5 :=
  gcd_crt_idem' 5 3 10 (by norm_num) (by norm_num) (by norm_num)

/-- gcd(6, 15) = 3, obtained from the general theorem. -/
theorem gcd_six : Nat.gcd 6 (3 * 5) = 3 :=
  gcd_crt_idem' 3 5 6 (by norm_num) (by norm_num) (by norm_num)

/-! ## 4. Square case: Z/9 is local, only trivial idempotents -/

theorem only_trivial_idem_9 :
    ∀ x : ZMod 9, x * x = x → x = 0 ∨ x = 1 := by decide

/-! ## 5. A minimal BNTF / FDE layer: (t, f) supports

T = (1,0), F = (0,1), B = (1,1), N = (0,0). -/

structure Supp where
  t : Bool
  f : Bool
  deriving DecidableEq, Repr

namespace Supp

def T : Supp := ⟨true, false⟩
def F : Supp := ⟨false, true⟩
def B : Supp := ⟨true, true⟩
def N : Supp := ⟨false, false⟩

def neg (a : Supp) : Supp := ⟨a.f, a.t⟩
def and (a b : Supp) : Supp := ⟨a.t && b.t, a.f || b.f⟩
def or (a b : Supp) : Supp := ⟨a.t || b.t, a.f && b.f⟩

theorem neg_neg (a : Supp) : a.neg.neg = a := by cases a; rfl

theorem neg_B : B.neg = B := by decide
theorem neg_N : N.neg = N := by decide
theorem neg_T : T.neg = F := by decide

/-- De Morgan holds support-wise. -/
theorem deMorgan_and (a b : Supp) : (a.and b).neg = a.neg.or b.neg := by
  cases a; cases b; simp [neg, and, or]

theorem deMorgan_or (a b : Supp) : (a.or b).neg = a.neg.and b.neg := by
  cases a; cases b; simp [neg, and, or]

/-- No explosion: B ∧ ¬B is B, not F; a contradiction does not become
everything-false. -/
theorem B_and_negB : B.and B.neg = B := by decide

/-- ...and B does not absorb N: B ∧ N = F, B ∨ N = T (FDE lattice). -/
theorem B_and_N : B.and N = F := by decide
theorem B_or_N : B.or N = T := by decide

end Supp

/-! ## 6. The open target, stated honestly

`idempotent_arev` would be a function `ℕ → ℕ` that, given a squarefree
semiprime N, returns a nontrivial idempotent of `ZMod N`. By section 2 it
would give a factoring algorithm; its status is N = (0,0). It is left as a
`Prop`, not an axiom, so the file's axiom set stays standard. -/

def IdempotentArev (f : ℕ → ℕ) : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    (f (p * q) : ZMod (p * q)) * (f (p * q) : ZMod (p * q)) = (f (p * q) : ZMod (p * q)) ∧
    (f (p * q) : ZMod (p * q)) ≠ 0 ∧ (f (p * q) : ZMod (p * q)) ≠ 1

end Imscribing.Idempotent
