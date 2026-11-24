import Mathlib

namespace Imscribing.IdempotentBijection

/-- In a field, a * a = a forces a = 0 or a = 1. -/
theorem idem_field {K : Type*} [Field K] (a : K) (h : a * a = a) :
    a = 0 ∨ a = 1 := by
  have h1 : a * (a - 1) = 0 := by
    have h2 : a * (a - 1) = a * a - a := by ring
    rw [h2, h, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (sub_eq_zero.mp h2)

/-- Classification: if R ≅ A × B with A, B fields, the idempotents of R are
exactly 0, 1, e = φ⁻¹(1,0) and f = φ⁻¹(0,1). -/
theorem idem_classify {A B R : Type*} [Field A] [Field B] [CommRing R]
    (φ : R ≃+* A × B) (x : R) :
    x * x = x ↔
      (x = 0 ∨ x = 1 ∨ x = φ.symm ((1 : A), (0 : B)) ∨ x = φ.symm ((0 : A), (1 : B))) := by
  constructor
  · intro h
    have h' : φ x * φ x = φ x := by rw [← map_mul, h]
    have h1 : (φ x).1 * (φ x).1 = (φ x).1 := by simpa using congrArg Prod.fst h'
    have h2 : (φ x).2 * (φ x).2 = (φ x).2 := by simpa using congrArg Prod.snd h'
    have key : φ x = ((0 : A), (0 : B)) ∨ φ x = ((1 : A), (0 : B)) ∨
        φ x = ((0 : A), (1 : B)) ∨ φ x = ((1 : A), (1 : B)) := by
      rcases idem_field _ h1 with a | a <;> rcases idem_field _ h2 with b | b
      · exact Or.inl (Prod.ext a b)
      · exact Or.inr (Or.inr (Or.inl (Prod.ext a b)))
      · exact Or.inr (Or.inl (Prod.ext a b))
      · exact Or.inr (Or.inr (Or.inr (Prod.ext a b)))
    have hx : x = φ.symm (φ x) := (φ.symm_apply_apply x).symm
    rcases key with k | k | k | k <;> rw [k] at hx
    · left
      rw [hx]
      exact map_zero φ.symm
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
    · right; left
      rw [hx]
      exact map_one φ.symm
  · rintro (rfl | rfl | rfl | rfl)
    · simp
    · simp
    · have hm := map_mul φ.symm ((1 : A), (0 : B)) ((1 : A), (0 : B))
      rw [← hm]
      congr 1
      ext <;> simp
    · have hm := map_mul φ.symm ((0 : A), (1 : B)) ((0 : A), (1 : B))
      rw [← hm]
      congr 1
      ext <;> simp

/-- e + f = 1 : the two nontrivial idempotents are complementary. -/
theorem e_add_f {A B R : Type*} [Field A] [Field B] [CommRing R]
    (φ : R ≃+* A × B) :
    φ.symm ((1 : A), (0 : B)) + φ.symm ((0 : A), (1 : B)) = 1 := by
  rw [← map_add]
  have : ((1 : A), (0 : B)) + ((0 : A), (1 : B)) = 1 := by
    ext <;> simp
  rw [this]
  exact map_one φ.symm

/-- e · f = 0 : orthogonality. -/
theorem e_mul_f {A B R : Type*} [Field A] [Field B] [CommRing R]
    (φ : R ≃+* A × B) :
    φ.symm ((1 : A), (0 : B)) * φ.symm ((0 : A), (1 : B)) = 0 := by
  rw [← map_mul]
  have : ((1 : A), (0 : B)) * ((0 : A), (1 : B)) = 0 := by
    ext <;> simp
  rw [this]
  exact map_zero φ.symm

/-- e is nontrivial: e ≠ 0. -/
theorem e_ne_zero {A B R : Type*} [Field A] [Field B] [CommRing R]
    (φ : R ≃+* A × B) : φ.symm ((1 : A), (0 : B)) ≠ 0 := by
  intro h
  have h2 : ((1 : A), (0 : B)) = 0 :=
    φ.symm.injective (h.trans (map_zero φ.symm).symm)
  simpa using h2

/-- e is nontrivial: e ≠ 1. -/
theorem e_ne_one {A B R : Type*} [Field A] [Field B] [CommRing R]
    (φ : R ≃+* A × B) : φ.symm ((1 : A), (0 : B)) ≠ 1 := by
  intro h
  have h2 : ((1 : A), (0 : B)) = 1 :=
    φ.symm.injective (h.trans (map_one φ.symm).symm)
  simpa using h2

/-- f is nontrivial: f ≠ 0. -/
theorem f_ne_zero {A B R : Type*} [Field A] [Field B] [CommRing R]
    (φ : R ≃+* A × B) : φ.symm ((0 : A), (1 : B)) ≠ 0 := by
  intro h
  have h2 : ((0 : A), (1 : B)) = 0 :=
    φ.symm.injective (h.trans (map_zero φ.symm).symm)
  simpa using h2

/-- f is nontrivial: f ≠ 1. -/
theorem f_ne_one {A B R : Type*} [Field A] [Field B] [CommRing R]
    (φ : R ≃+* A × B) : φ.symm ((0 : A), (1 : B)) ≠ 1 := by
  intro h
  have h2 : ((0 : A), (1 : B)) = 1 :=
    φ.symm.injective (h.trans (map_one φ.symm).symm)
  simpa using h2

/-! ### Specialization: Z/pq for distinct primes p, q -/

/-- The four idempotents of ZMod (p*q), p ≠ q prime, via the CRT isomorphism. -/
theorem idem_zmod_pq (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : Nat.Coprime p q) (x : ZMod (p * q)) :
    x * x = x ↔
      (x = 0 ∨ x = 1 ∨
        x = (ZMod.chineseRemainder hpq).symm ((1 : ZMod p), (0 : ZMod q)) ∨
        x = (ZMod.chineseRemainder hpq).symm ((0 : ZMod p), (1 : ZMod q))) :=
  idem_classify (ZMod.chineseRemainder hpq) x

end Imscribing.IdempotentBijection
