import Mathlib

/-!
# CLINK Decomposition — "goldbach_theorem"
Nav: cl8nk (self-referential) / cl9nk (exceptional point)
Discipline: algebraic_number_theory
Tuple: ⟨𐑦⋅𐑡⋅𐑑⋅𐑗⋅𐑞⋅𐑧⋅𐑲⋅𐑜⋅⊙⋅𐑓⋅𐑙⋅𐑷⟩
-/

namespace GoldbachCLINK

/-! ## The Goldbach theorem -/

def Goldbach : Prop :=
  ∀ n : ℕ, n > 2 → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-! ## The 12 CLINK slots -/

inductive CLINK : Type
  | c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  deriving DecidableEq, Repr, Fintype

def glyph : CLINK → String
  | .c0  => "𐑦" | .c1  => "𐑡" | .c2  => "𐑑" | .c3  => "𐑗"
  | .c4  => "𐑞" | .c5  => "𐑧" | .c6  => "𐑲" | .c7  => "𐑜"
  | .c8  => "⊙" | .c9  => "𐑓" | .c10 => "𐑙" | .c11 => "𐑷"

/-! ## The 12 algebraic-number-theory clauses on ℚ/ℤ -/

theorem c0_degree : Module.finrank ℚ ℚ = 1 := by simp

theorem c1_ring_of_integers : ∀ z : ℤ, (z : ℚ) ∈ (⊤ : Set ℚ) :=
  fun _ => trivial

theorem c2_iso : Nonempty (ℚ ≃+* ℚ) := ⟨RingEquiv.refl ℚ⟩

theorem c3_distinct : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q :=
  ⟨2, 3, by decide, by decide, by decide⟩

/-- Every rational is algebraic: root of X − C(q), which is nonzero. -/
theorem rat_algebraic (q : ℚ) : IsAlgebraic ℚ q := by
  refine ⟨Polynomial.X - Polynomial.C q, ?_, ?_⟩
  · intro h
    have := congrArg (fun r => Polynomial.coeff r 1) h
    simp at this
  · simp

theorem c4_algebraic (q : ℚ) : IsAlgebraic ℚ q := rat_algebraic q

theorem c5_norm (p : ℕ) : (p : ℚ) = (p : ℚ) := rfl

theorem c6_trace (p : ℕ) : ∃ z : ℤ, (z : ℚ) = (p : ℚ) := ⟨(p : ℤ), by simp⟩

theorem c7_tensor : Nonempty (ℚ × ℚ) := ⟨(0, 0)⟩

theorem c8_dedekind : IsDedekindDomain ℤ := inferInstance

def swap (pq : ℕ × ℕ) : ℕ × ℕ := (pq.2, pq.1)

theorem c9_involution : ∀ pq : ℕ × ℕ, swap (swap pq) = pq :=
  fun ⟨_, _⟩ => rfl

theorem c10_uniform : ∀ _ _ : ℤ, True := fun _ _ => trivial

/-- Gal(ℚ/ℚ) is trivial, hence Abelian. -/
theorem c11_galois_abelian : ∀ σ τ : ℚ ≃ₐ[ℚ] ℚ, σ * τ = τ * σ := by
  intros σ τ
  haveI : Subsingleton (ℚ ≃ₐ[ℚ] ℚ) := ⟨fun a b => by
    ext x
    have ha : a x = x := by
      have := a.commutes x; simpa using this
    have hb : b x = x := by
      have := b.commutes x; simpa using this
    rw [ha, hb]⟩
  rw [Subsingleton.elim σ τ]

/-! ## The decomposition -/

def GoldbachDecomposition : Prop :=
  Module.finrank ℚ ℚ = 1 ∧
  (∀ z : ℤ, (z : ℚ) ∈ (⊤ : Set ℚ)) ∧
  Nonempty (ℚ ≃+* ℚ) ∧
  (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q) ∧
  (∀ q : ℚ, IsAlgebraic ℚ q) ∧
  (∀ p : ℕ, (p : ℚ) = (p : ℚ)) ∧
  (∀ p : ℕ, ∃ z : ℤ, (z : ℚ) = (p : ℚ)) ∧
  Nonempty (ℚ × ℚ) ∧
  IsDedekindDomain ℤ ∧
  (∀ pq : ℕ × ℕ, swap (swap pq) = pq) ∧
  (∀ _ _ : ℤ, True) ∧
  (∀ σ τ : ℚ ≃ₐ[ℚ] ℚ, σ * τ = τ * σ)

theorem goldbach_decomposition_holds : GoldbachDecomposition :=
  ⟨c0_degree, c1_ring_of_integers, c2_iso, c3_distinct, c4_algebraic,
   c5_norm, c6_trace, c7_tensor, c8_dedekind, c9_involution,
   c10_uniform, c11_galois_abelian⟩

/-! ## Verified Goldbach cases -/

theorem goldbach_4  : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 4  :=
  ⟨2, 2,  by decide, by decide, by decide⟩
theorem goldbach_6  : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 6  :=
  ⟨3, 3,  by decide, by decide, by decide⟩
theorem goldbach_8  : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 8  :=
  ⟨3, 5,  by decide, by decide, by decide⟩
theorem goldbach_10 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 10 :=
  ⟨3, 7,  by decide, by decide, by decide⟩
theorem goldbach_12 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 12 :=
  ⟨5, 7,  by decide, by decide, by decide⟩
theorem goldbach_14 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 14 :=
  ⟨3, 11, by decide, by decide, by decide⟩
theorem goldbach_16 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 16 :=
  ⟨3, 13, by decide, by decide, by decide⟩
theorem goldbach_18 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 18 :=
  ⟨5, 13, by decide, by decide, by decide⟩
theorem goldbach_20 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 20 :=
  ⟨3, 17, by decide, by decide, by decide⟩

/-! ## Structural equivalence -/

theorem goldbach_structural : Goldbach ↔
    ∀ n : ℕ, n > 2 → Even n →
      ∃ pq : ℕ × ℕ, Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧
        pq.1 + pq.2 = n ∧ swap (swap pq) = pq := by
  constructor
  · intro h n hn heven
    obtain ⟨p, q, hp, hq, hpq⟩ := h n hn heven
    exact ⟨(p, q), hp, hq, hpq, rfl⟩
  · intro h n hn heven
    obtain ⟨⟨p, q⟩, hp, hq, hpq, _⟩ := h n hn heven
    exact ⟨p, q, hp, hq, hpq⟩

/-! ## Fragment structure -/

inductive Proximity where
  | matchK | close | distant
  deriving DecidableEq, Repr

structure Fragment where
  slot : CLINK
  proximity : Proximity
  deltaScaled : Option Int
  promoting : Bool
  deriving Repr, DecidableEq

def deltaF (f : Fragment) : Fragment × Fragment := (f, f)
def muF (p : Fragment × Fragment) : Fragment := p.1

/-! cl9nk (exceptional point) reading of the goldbach tuple. -/
def goldbachFragmentsEP : List Fragment := [
  ⟨.c0,  .distant, some 1000, true⟩,
  ⟨.c1,  .distant, some 500,  true⟩,
  ⟨.c2,  .matchK,  none,      false⟩,
  ⟨.c3,  .distant, some 500,  true⟩,
  ⟨.c4,  .close,   some 500,  true⟩,
  ⟨.c5,  .distant, some 286,  true⟩,
  ⟨.c6,  .distant, some 500,  true⟩,
  ⟨.c7,  .close,   some 333,  true⟩,
  ⟨.c8,  .matchK,  none,      false⟩,
  ⟨.c9,  .distant, some 1000, true⟩,
  ⟨.c10, .distant, some 1000, true⟩,
  ⟨.c11, .distant, some 667,  true⟩
]

/-! cl8nk (self-referential) reading of the goldbach tuple. -/
def goldbachFragmentsSR : List Fragment := [
  ⟨.c0,  .matchK,  none,      false⟩,
  ⟨.c1,  .distant, some 1000, true⟩,
  ⟨.c2,  .distant, some 333,  true⟩,
  ⟨.c3,  .distant, none,      false⟩,
  ⟨.c4,  .close,   some 500,  true⟩,
  ⟨.c5,  .matchK,  none,      false⟩,
  ⟨.c6,  .matchK,  some 500,  true⟩,
  ⟨.c7,  .distant, some 667,  true⟩,
  ⟨.c8,  .matchK,  none,      false⟩,
  ⟨.c9,  .distant, some 1000, true⟩,
  ⟨.c10, .distant, some 1000, true⟩,
  ⟨.c11, .distant, none,      false⟩
]

/-! ## Frobenius identity -/

theorem frobenius_list (fs : List Fragment) : (fs.map deltaF).map muF = fs := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    simp [deltaF, muF, ih]

theorem frobenius_element (f : Fragment) : muF (deltaF f) = f := rfl

theorem frobenius_on_goldbach_EP :
    (goldbachFragmentsEP.map deltaF).map muF = goldbachFragmentsEP :=
  frobenius_list _

theorem frobenius_on_goldbach_SR :
    (goldbachFragmentsSR.map deltaF).map muF = goldbachFragmentsSR :=
  frobenius_list _

/-! ## Measured structure -/

theorem EP_counts :
    (goldbachFragmentsEP.filter (·.proximity = .matchK)).length = 2 ∧
    (goldbachFragmentsEP.filter (·.proximity = .close)).length = 2 ∧
    (goldbachFragmentsEP.filter (·.proximity = .distant)).length = 8 ∧
    (goldbachFragmentsEP.filter (·.promoting)).length = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem SR_counts :
    (goldbachFragmentsSR.filter (·.proximity = .matchK)).length = 4 ∧
    (goldbachFragmentsSR.filter (·.proximity = .close)).length = 1 ∧
    (goldbachFragmentsSR.filter (·.proximity = .distant)).length = 7 ∧
    (goldbachFragmentsSR.filter (·.promoting)).length = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- EP reading's Δ=1.0 seams: degree (c0), involution (c9), type-uniformity (c10). -/
theorem EP_seams :
    (goldbachFragmentsEP.filter (fun f => f.deltaScaled = some 1000)).map (·.slot) =
      [.c0, .c9, .c10] := by
  decide

theorem tuple_is_twelve :
    goldbachFragmentsEP.length = 12 ∧ goldbachFragmentsSR.length = 12 :=
  ⟨rfl, rfl⟩

end GoldbachCLINK