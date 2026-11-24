import Imscribing.Millennium.TrineOperatorAlgebra
import Mathlib.NumberTheory.Zsqrtd.Basic

namespace Imscribing.Millennium.FamilyWeylFrobenius

abbrev E3 := Zsqrtd (-3)

/-- s = √(-3) = i√3 and w₂ = 2ω = -1 + √(-3), w₂b = 2ω² = -1 - √(-3) in Zsqrtd (-3). -/
def sRoot : E3 := ⟨0, 1⟩
def w2 : E3 := ⟨-1, 1⟩
def w2b : E3 := ⟨-1, -1⟩

theorem eisenstein_identities :
    sRoot^2 = -3 ∧ w2^3 = 8 ∧ w2^2 + 2 * w2 + 4 = 0 ∧ w2 * w2b = 4 := by
  decide

/-! ## Part 1: D₃ ≅ S₃ Family Symmetry, 1 ⊕ 2 Decomposition, and Schur Degeneracy -/

def R {α : Type*} [Zero α] [One α] : Matrix (Fin 3) (Fin 3) α := fun i j =>
  match i.val, j.val with
  | 1, 0 => 1
  | 2, 1 => 1
  | 0, 2 => 1
  | _, _ => 0

def S {α : Type*} [Zero α] [One α] : Matrix (Fin 3) (Fin 3) α := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 2 => 1
  | 2, 1 => 1
  | _, _ => 0

def P1_3 : Matrix (Fin 3) (Fin 3) ℤ := fun _ _ => 1
def P2_3 : Matrix (Fin 3) (Fin 3) ℤ := fun i j => if i = j then 2 else -1

theorem d3_relations :
    (R : Matrix (Fin 3) (Fin 3) ℤ)^3 = 1 ∧
    (S : Matrix (Fin 3) (Fin 3) ℤ)^2 = 1 ∧
    (S : Matrix (Fin 3) (Fin 3) ℤ) * R * S = R^2 := by
  refine ⟨?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

theorem d3_idempotent_decomposition :
    P1_3 * P1_3 = (3 : ℤ) • P1_3 ∧
    P2_3 * P2_3 = (3 : ℤ) • P2_3 ∧
    P1_3 * P2_3 = 0 ∧
    P1_3 + P2_3 = (3 : ℤ) • 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

private lemma fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ i : Fin 3, P i
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2

/-- Universal Schur decomposition: any 3×3 integer matrix commuting with both R and S
    has equal diagonal and equal off-diagonal entries, forcing a degenerate doublet. -/
theorem d3_invariant_schur_form (Y : Matrix (Fin 3) (Fin 3) ℤ)
    (hR : Y * R = R * Y) (hS : Y * S = S * Y) :
    (3 : ℤ) • Y = (Y 0 0 + 2 * Y 0 1) • P1_3 + (Y 0 0 - Y 0 1) • P2_3 := by
  have eR := fun i j => congrFun (congrFun hR i) j
  have eS := fun i j => congrFun (congrFun hS i) j
  have h11 : Y 1 1 = Y 0 0 := by
    simpa [Matrix.mul_apply, R, Fin.sum_univ_three] using eR 1 0
  have h22 : Y 2 2 = Y 0 0 := by
    have h21 : Y 2 2 = Y 1 1 := by
      simpa [Matrix.mul_apply, R, Fin.sum_univ_three] using eR 2 1
    omega
  have h20 : Y 2 0 = Y 0 1 := by
    simpa [Matrix.mul_apply, R, Fin.sum_univ_three] using (eR 0 0).symm
  have h12 : Y 1 2 = Y 0 1 := by
    simpa [Matrix.mul_apply, R, Fin.sum_univ_three] using eR 1 1
  have h10 : Y 1 0 = Y 0 1 := by
    have h10' : Y 1 0 = Y 2 0 := by
      simpa [Matrix.mul_apply, S, Fin.sum_univ_three] using eS 1 0
    omega
  have h02 : Y 0 2 = Y 0 1 := by
    simpa [Matrix.mul_apply, S, Fin.sum_univ_three] using eS 0 1
  have h21 : Y 2 1 = Y 0 1 := by
    have h21' : Y 2 1 = Y 1 2 := by
      simpa [Matrix.mul_apply, S, Fin.sum_univ_three] using (eS 1 1).symm
    omega
  apply Matrix.ext
  intro i j
  revert i j
  refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;>
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      P1_3, P2_3, h11, h22, h20, h12, h10, h02, h21, ite_true, ite_false]
    try rw [if_neg (by decide)]
    ring

/-! ## Part 2: Cyclic C₃ Algebra, Fourier Matrix U₃, and Exact Spectral Split -/

/-- Scaled Fourier matrix 2√3 · U₃ (entries in E3) and its scaled conjugate transpose. -/
def U3_2 : Matrix (Fin 3) (Fin 3) E3 := fun i j =>
  match i.val, j.val with
  | 0, _ => 2
  | 1, 0 => 2 | 1, 1 => w2  | 1, 2 => w2b
  | 2, 0 => 2 | 2, 1 => w2b | 2, 2 => w2
  | _, _ => 0

def U3_2_conj : Matrix (Fin 3) (Fin 3) E3 := fun i j =>
  match i.val, j.val with
  | 0, _ => 2
  | 1, 0 => 2 | 1, 1 => w2b | 1, 2 => w2
  | 2, 0 => 2 | 2, 1 => w2  | 2, 2 => w2b
  | _, _ => 0

theorem fourier_unitarity_scaled :
    U3_2_conj * U3_2 = (12 : E3) • (1 : Matrix (Fin 3) (Fin 3) E3) := by
  apply Matrix.ext; intro i j; revert i j; decide

theorem fourier_diagonalizes_R :
    U3_2_conj * (R : Matrix (Fin 3) (Fin 3) E3) * U3_2 =
    fun i j => if i = j then match i.val with | 0 => 12 | 1 => 6 * w2b | 2 => 6 * w2 | _ => 0 else 0 := by
  apply Matrix.ext; intro i j; revert i j; decide

/-- Hermitian family operator H(α, β, g) = α I + β(R + R²) + g√(-3)(R - R²)
    with exact eigenvectors v₀, v₊, v₋ and integer eigenvalues α+2β, α-β±3g. -/
def Hfam (α β g : ℤ) : Matrix (Fin 3) (Fin 3) E3 :=
  (α : E3) • 1 + (β : E3) • (R + R^2) + ((g : E3) * sRoot) • (R - R^2)

def v0 : Fin 3 → E3 := fun _ => 2
def vPlus : Fin 3 → E3 := fun i => match i.val with | 0 => 2 | 1 => w2 | _ => w2b
def vMinus : Fin 3 → E3 := fun i => match i.val with | 0 => 2 | 1 => w2b | _ => w2

theorem hfam_exact_spectrum (α β g : ℤ) :
    (Hfam α β g).mulVec v0 = ((α + 2 * β : ℤ) : E3) • v0 ∧
    (Hfam α β g).mulVec vPlus = ((α - β + 3 * g : ℤ) : E3) • vPlus ∧
    (Hfam α β g).mulVec vMinus = ((α - β - 3 * g : ℤ) : E3) • vMinus := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · apply funext
    intro i
    revert i
    refine fin3_cases ?_ ?_ ?_ <;>
    · simp [Hfam, pow_two, Matrix.mulVec, dotProduct, Matrix.mul_apply, R,
        v0, vPlus, vMinus, sRoot, w2, w2b, Fin.sum_univ_three]
      apply Zsqrtd.ext <;> simp <;> ring

theorem branch_exchange_flips_orientation :
    (S : Matrix (Fin 3) (Fin 3) E3) * (sRoot • (R - R^2)) * S = -(sRoot • (R - R^2)) := by
  apply Matrix.ext; intro i j; revert i j; decide

/-! ## Part 3: Universal No-Mixing Theorem for Shared C₃ Symmetry -/

/-- Any 3×3 matrix over any commutative ring α that commutes with R is circulant
    in {1, R, R²}, hence any two such matrices commute (preventing CKM/PMNS mixing). -/
theorem commutes_with_R_implies_circulant {α : Type*} [CommRing α]
    (Y : Matrix (Fin 3) (Fin 3) α) (hR : Y * R = R * Y) :
    Y = Y 0 0 • (1 : Matrix (Fin 3) (Fin 3) α) +
        Y 1 0 • (R : Matrix (Fin 3) (Fin 3) α) +
        Y 2 0 • ((R : Matrix (Fin 3) (Fin 3) α) * R) := by
  have eR := fun i j => congrFun (congrFun hR i) j
  have h01 : Y 0 1 = Y 2 0 := by
    simpa [Matrix.mul_apply, R, Fin.sum_univ_three] using eR 0 0
  have h11 : Y 1 1 = Y 0 0 := by
    simpa [Matrix.mul_apply, R, Fin.sum_univ_three] using eR 1 0
  have h12 : Y 1 2 = Y 2 0 := by
    have h12' : Y 1 2 = Y 0 1 := by
      simpa [Matrix.mul_apply, R, Fin.sum_univ_three] using eR 1 1
    rw [h12', h01]
  have h21 : Y 2 1 = Y 1 0 := by
    simpa [Matrix.mul_apply, R, Fin.sum_univ_three] using eR 2 0
  have h22 : Y 2 2 = Y 0 0 := by
    have h22' : Y 2 2 = Y 1 1 := by
      simpa [Matrix.mul_apply, R, Fin.sum_univ_three] using eR 2 1
    rw [h22', h11]
  have h02 : Y 0 2 = Y 1 0 := by
    have h02' : Y 0 2 = Y 2 1 := by
      simpa [Matrix.mul_apply, R, Fin.sum_univ_three] using eR 0 1
    rw [h02', h21]
  apply Matrix.ext
  intro i j
  revert i j
  refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;>
    simp [Matrix.mul_apply, R, Fin.sum_univ_three, h01, h11, h12, h21, h22, h02]

theorem simultaneous_c3_implies_no_mixing {α : Type*} [CommRing α]
    (Hu Hd : Matrix (Fin 3) (Fin 3) α)
    (hu : Hu * R = R * Hu) (hd : Hd * R = R * Hd) :
    Hu * Hd = Hd * Hu := by
  rw [commutes_with_R_implies_circulant Hu hu, commutes_with_R_implies_circulant Hd hd]
  apply Matrix.ext
  intro i j
  revert i j
  refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;>
    (simp [Matrix.mul_apply, R, Fin.sum_univ_three]; ring)

/-! ## Part 4: Weyl Relation (ZR = ωRZ) and Complete Matrix Algebra M₃ -/

/-- Scaled phase operator Z₂ = 2Z = diag(2, 2ω, 2ω²) and Z₂_sq2 = 2Z² = diag(2, 2ω², 2ω). -/
def Z2 : Matrix (Fin 3) (Fin 3) E3 := fun i j =>
  if i = j then match i.val with | 0 => 2 | 1 => w2 | 2 => w2b | _ => 0 else 0

def Z2_sq2 : Matrix (Fin 3) (Fin 3) E3 := fun i j =>
  if i = j then match i.val with | 0 => 2 | 1 => w2b | 2 => w2 | _ => 0 else 0

theorem weyl_relation_and_noncommutativity :
    (2 : E3) • (Z2 * R) = w2 • (R * Z2) ∧
    Z2 * R - R * Z2 ≠ 0 ∧
    (2 : E3) • Z2_sq2 = Z2 * Z2 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.ext; intro i j; revert i j; decide
  · intro h
    have h10 := congrFun (congrFun h 1) 0
    revert h10; decide
  · apply Matrix.ext; intro i j; revert i j; decide

private def w2NegPow : ℕ → E3
  | 0 => 2
  | 1 => w2b
  | 2 => w2
  | n + 3 => w2NegPow n

/-- Weyl-generated spectral projectors P₁₂(n) = 12 · P_n = 4I + (2ω⁻ⁿ)Z₂ + (2ω⁻²ⁿ)Z₂_sq2. -/
def P12 (n : Fin 3) : Matrix (Fin 3) (Fin 3) E3 :=
  (4 : E3) • 1 + (w2NegPow n.val) • Z2 + (w2NegPow (2 * n.val)) • Z2_sq2

/-- Elementary transition units E₁₂(m, n) = 12 · E_{mn} = R^(m-n mod 3) · P₁₂(n). -/
def E12 (m n : Fin 3) : Matrix (Fin 3) (Fin 3) E3 :=
  (R : Matrix (Fin 3) (Fin 3) E3)^((m.val + 3 - n.val) % 3) * P12 n

theorem weyl_matrix_units_mul (m n p q : Fin 3) :
    E12 m n * E12 p q = (if n = p then (12 : E3) else 0) • E12 m q := by
  revert m n p q
  decide

theorem weyl_spans_M3 (Y : Matrix (Fin 3) (Fin 3) E3) :
    (12 : E3) • Y = ∑ m : Fin 3, ∑ n : Fin 3, (Y m n) • E12 m n := by
  apply Matrix.ext
  intro i j
  revert i j
  refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;>
  · simp [E12, P12, Z2, Z2_sq2, R, pow_zero, pow_one, pow_two, Matrix.mul_apply,
      w2NegPow, w2, w2b, Fin.sum_univ_three]
    apply Zsqrtd.ext <;> simp <;> ring

/-! ## Part 5: Equivariant Frobenius Algebra (μ ∘ δ = I₃) on Family Space -/

private def kron9 (A B : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 9) (Fin 9) ℤ :=
  fun i j => A ⟨i.val / 3, by omega⟩ ⟨j.val / 3, by omega⟩ *
             B ⟨i.val % 3, by omega⟩ ⟨j.val % 3, by omega⟩

def deltaF : Matrix (Fin 9) (Fin 3) ℤ :=
  fun i j => if i.val = j.val * 3 + j.val then 1 else 0

def muF : Matrix (Fin 3) (Fin 9) ℤ :=
  fun i j => if j.val = i.val * 3 + i.val then 1 else 0

theorem frobenius_reconstruct :
    muF * deltaF = (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  apply Matrix.ext; intro i j; revert i j; decide

theorem frobenius_d3_equivariance :
    deltaF * (R : Matrix (Fin 3) (Fin 3) ℤ) = kron9 R R * deltaF ∧
    deltaF * (S : Matrix (Fin 3) (Fin 3) ℤ) = kron9 S S * deltaF ∧
    muF * kron9 R R = (R : Matrix (Fin 3) (Fin 3) ℤ) * muF ∧
    muF * kron9 S S = (S : Matrix (Fin 3) (Fin 3) ℤ) * muF := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Matrix.ext; intro i j; revert i j; decide)

/-! ## Part 6: Exceptional-Point Operator J(λ) on the Doublet -/

def J_ep (lam : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := fun i j =>
  match i.val, j.val with
  | 0, 1 => 1
  | 1, 0 => lam
  | _, _ => 0

theorem exceptional_point_coalescence (lam : ℤ) :
    J_ep 0 ≠ 0 ∧ J_ep 0 * J_ep 0 = 0 ∧ J_ep lam * J_ep lam = lam • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    revert h01; decide
  · apply Matrix.ext; intro i j; revert i j; decide
  · apply Matrix.ext
    intro i j
    rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
    match i, j with
    | 0, 0 => simp [Matrix.mul_apply, J_ep]
    | 0, 1 => simp [Matrix.mul_apply, J_ep]
    | 1, 0 => simp [Matrix.mul_apply, J_ep]
    | 1, 1 => simp [Matrix.mul_apply, J_ep]

end Imscribing.Millennium.FamilyWeylFrobenius