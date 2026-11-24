import Mathlib
import Imscribing.Millennium.ZetaSICDualFrame

/-! Source-only square-return collision invariant.
This file proves the algebra and cardinality statements. It does not implement
a compressed collision contractor or claim an emitted source factor. -/
namespace Imscribing.SourceBraidSquareCollision

noncomputable def fibrePairEquiv {X Y : Type*} (f : X → Y) :
    {xy : X × X // f xy.1 = f xy.2} ≃
      (y : Y) × ({x : X // f x = y} × {x : X // f x = y}) where
  toFun xy := ⟨f xy.val.1, (⟨xy.val.1, rfl⟩, ⟨xy.val.2, xy.property.symm⟩)⟩
  invFun yz := ⟨(yz.2.1.val, yz.2.2.val), yz.2.1.property.trans yz.2.2.property.symm⟩
  left_inv := by
    intro xy
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨y, ⟨⟨x, hx⟩, ⟨z, hz⟩⟩⟩
    cases hx
    rfl

theorem collision_count_as_fibres {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) :
    Fintype.card {xy : X × X // f xy.1 = f xy.2} =
      ∑ y : Y, (Fintype.card {x : X // f x = y}) ^ 2 := by
  classical
  have h := Fintype.card_congr (fibrePairEquiv f)
  simpa [Fintype.card_sigma, Fintype.card_prod, pow_two] using h

noncomputable def returnGram {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y) : Matrix Y Y ℤ :=
  Matrix.diagonal (fun y => (Fintype.card {x : X // f x = y} : ℤ))

theorem trace_return_square {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) :
    Matrix.trace (returnGram f * returnGram f) =
      (Fintype.card {xy : X × X // f xy.1 = f xy.2} : ℤ) := by
  classical
  rw [collision_count_as_fibres]
  simp [returnGram, Matrix.diagonal_mul_diagonal, Matrix.trace, pow_two]

def SquarePairs (K : Type*) [Semiring K] :=
  {xy : K × K // xy.1 ^ 2 = xy.2 ^ 2}

def ZeroPairs (K : Type*) [MulZeroClass K] :=
  {uv : K × K // uv.1 * uv.2 = 0}

noncomputable instance squarePairsFintype (K : Type*) [Semiring K] [Fintype K] :
    Fintype (SquarePairs K) := by
  classical
  unfold SquarePairs
  infer_instance

noncomputable instance zeroPairsFintype (K : Type*) [MulZeroClass K] [Fintype K] :
    Fintype (ZeroPairs K) := by
  classical
  unfold ZeroPairs
  infer_instance

noncomputable def zeroPairsEquiv (K : Type*) [Field K] :
    ZeroPairs K ≃ K ⊕ {u : K // u ≠ 0} := by
  classical
  exact {
    toFun := fun uv => if h : uv.val.1 = 0 then Sum.inl uv.val.2
      else Sum.inr ⟨uv.val.1, h⟩
    invFun := fun s => match s with
      | Sum.inl v => ⟨(0, v), by simp⟩
      | Sum.inr u => ⟨(u.val, 0), by simp⟩
    left_inv := by
      rintro ⟨⟨u, v⟩, huv⟩
      by_cases hu : u = 0
      · subst u; simp
      · have hv : v = 0 := (mul_eq_zero.mp huv).resolve_left hu
        subst v; simp [hu]
    right_inv := by
      intro s
      cases s with
      | inl v => simp
      | inr u => simp [u.property]
  }

noncomputable def squareToZero (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    SquarePairs K ≃ ZeroPairs K where
  toFun xy := ⟨(xy.val.1 - xy.val.2, xy.val.1 + xy.val.2), by
    change (xy.val.1 - xy.val.2) * (xy.val.1 + xy.val.2) = 0
    calc
      _ = xy.val.1 ^ 2 - xy.val.2 ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr xy.property⟩
  invFun uv := ⟨((uv.val.1 + uv.val.2) / 2, (uv.val.2 - uv.val.1) / 2), by
    apply sub_eq_zero.mp
    calc
      _ = uv.val.1 * uv.val.2 := by field_simp; ring
      _ = 0 := uv.property⟩
  left_inv := by
    intro xy
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  right_inv := by
    intro uv
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp <;> ring

theorem field_collision_card (K : Type*) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) :
    (Fintype.card (SquarePairs K) : ℤ) = 2 * Fintype.card K - 1 := by
  classical
  have h := Fintype.card_congr ((squareToZero K h2).trans (zeroPairsEquiv K))
  have hn : Fintype.card {u : K // u ≠ 0} = Fintype.card K - 1 := by
    simpa using Fintype.card_subtype_compl (fun u : K => u = 0)
  rw [Fintype.card_sum, hn] at h
  have hp : 0 < Fintype.card K := Fintype.card_pos
  omega

noncomputable def squareCRT {R A B : Type*} [CommRing R]
    [CommRing A] [CommRing B] (φ : R ≃+* A × B) :
    SquarePairs R ≃ SquarePairs A × SquarePairs B where
  toFun xy :=
    (⟨((φ xy.val.1).1, (φ xy.val.2).1), by
      have h := congrArg (fun z => (φ z).1) xy.property
      simpa using h⟩,
     ⟨((φ xy.val.1).2, (φ xy.val.2).2), by
      have h := congrArg (fun z => (φ z).2) xy.property
      simpa using h⟩)
  invFun ab :=
    ⟨(φ.symm (ab.1.val.1, ab.2.val.1), φ.symm (ab.1.val.2, ab.2.val.2)), by
      apply φ.injective
      simp only [map_pow, RingEquiv.apply_symm_apply, Prod.pow_mk]
      exact Prod.ext ab.1.property ab.2.property⟩
  left_inv := by
    intro xy
    apply Subtype.ext
    apply Prod.ext <;> simp
  right_inv := by
    intro ab
    apply Prod.ext <;> apply Subtype.ext <;> simp

theorem semiprime_collision_card (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : Nat.Coprime p q) (hp2 : (2 : ZMod p) ≠ 0)
    (hq2 : (2 : ZMod q) ≠ 0) :
    (Fintype.card (SquarePairs (ZMod (p * q))) : ℤ) =
      4 * (p : ℤ) * q - 2 * ((p : ℤ) + q) + 1 := by
  classical
  have h := Fintype.card_congr (squareCRT (ZMod.chineseRemainder hpq))
  rw [Fintype.card_prod] at h
  have hi : (Fintype.card (SquarePairs (ZMod (p * q))) : ℤ) =
      (Fintype.card (SquarePairs (ZMod p)) : ℤ) *
        (Fintype.card (SquarePairs (ZMod q)) : ℤ) := by exact_mod_cast h
  rw [field_collision_card (ZMod p) hp2, field_collision_card (ZMod q) hq2] at hi
  simp only [ZMod.card] at hi
  exact hi.trans (by ring)

theorem source_path_address (x N : ℚ) (hN : N ≠ 0) :
    (4 * x * 19) / (76 * N) = x / N := by
  field_simp
  <;> ring

theorem parity_pair_expansion {K : Type*} [CommRing K]
    (A B C D x y δ ε η : K) (hε : ε = 0 ∨ ε = 1)
    (hη : η = 0 ∨ η = 1) :
    A * (2*x+ε)^2 + B*(2*x+ε) - C*(2*y+η)^2 - D*(2*y+η) + δ =
      4*A*x^2 + (4*A*ε+2*B)*x - 4*C*y^2 - (4*C*η+2*D)*y +
        (δ+(A+B)*ε-(C+D)*η) := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> ring

theorem recover_sum (p q : ℚ) :
    (4*(p*q)+1-((2*p-1)*(2*q-1)))/2 = p+q := by ring

theorem recover_discriminant (p q : ℚ) :
    (p+q)^2 - 4*(p*q) = (p-q)^2 := by ring

#print axioms semiprime_collision_card
#print axioms trace_return_square
#print axioms parity_pair_expansion
#print axioms recover_sum

end Imscribing.SourceBraidSquareCollision
