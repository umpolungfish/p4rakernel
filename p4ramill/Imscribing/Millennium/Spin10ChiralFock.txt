import Imscribing.Millennium.TrineOperatorAlgebra
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

namespace Imscribing.Millennium.Spin10ChiralFock

/-! ## Part 1: Five-Mode Fock Space F(V) and Parity-Closure Bijection L ≃ F⁺(V) -/

/-- Bit k ∈ {0,1,2,3,4} of a 5-mode Fock basis state y ∈ Fin 32.
    Modes 0,1,2 span V₃ (evaluator trine); modes 3,4 span V₂ (cl8nk / cl9nk postures). -/
def bitAt (y : Fin 32) (k : ℕ) : ℕ := (y.val / 2^k) % 2

def occCount (y : Fin 32) : ℕ :=
  bitAt y 0 + bitAt y 1 + bitAt y 2 + bitAt y 3 + bitAt y 4

def parity5 (y : Fin 32) : ℕ := occCount y % 2

def v3Count (y : Fin 32) : ℕ := bitAt y 0 + bitAt y 1 + bitAt y 2
def v2Count (y : Fin 32) : ℕ := bitAt y 3 + bitAt y 4

/-- Parity-closed embedding L (Fin 16) → F⁺(V) ⊂ Fin 32 via n₅ = n₁ ⊕ n₂ ⊕ n₃ ⊕ n₄. -/
def lToFockEven (x : Fin 16) : Fin 32 :=
  let n4 := (x.val % 2 + (x.val / 2) % 2 + (x.val / 4) % 2 + (x.val / 8) % 2) % 2
  ⟨(x.val + 16 * n4) % 32, Nat.mod_lt _ (by decide)⟩

/-- Inverse projection F⁺(V) → L (Fin 16) dropping the closure bit. -/
def fockEvenToL (y : Fin 32) : Fin 16 :=
  ⟨y.val % 16, Nat.mod_lt _ (by decide)⟩

theorem fock_even_parity :
    ∀ x : Fin 16, parity5 (lToFockEven x) = 0 := by
  decide

theorem fock_bijection_left :
    ∀ x : Fin 16, fockEvenToL (lToFockEven x) = x := by
  decide

theorem fock_bijection_right :
    ∀ y : Fin 32, parity5 y = 0 → lToFockEven (fockEvenToL y) = y := by
  decide

/-- Dimension count: |F⁺(V)| = 1 + C(5,2) + C(5,4) = 1 + 10 + 5 = 16. -/
theorem fock_even_dimension_decomposition :
    (Finset.univ.filter fun y : Fin 32 => parity5 y = 0).card = 16 ∧
    (Finset.univ.filter fun y : Fin 32 => occCount y = 0).card = 1 ∧
    (Finset.univ.filter fun y : Fin 32 => occCount y = 2).card = 10 ∧
    (Finset.univ.filter fun y : Fin 32 => occCount y = 4).card = 5 := by
  decide

/-! ## Part 2: Ten Majorana Generators and the 10D Clifford Algebra Cl(10) -/

/-- Sparse signed/Gaussian permutation matrix: entry (i, j) is c j iff i = t j. -/
def monomialMatrix (t : Fin 32 → Fin 32) (c : Fin 32 → GaussianInt) :
    Matrix (Fin 32) (Fin 32) GaussianInt :=
  fun i j => if i = t j then c j else 0

theorem monomialMatrix_mul (t₁ t₂ : Fin 32 → Fin 32) (c₁ c₂ : Fin 32 → GaussianInt) :
    monomialMatrix t₁ c₁ * monomialMatrix t₂ c₂ =
    monomialMatrix (t₁ ∘ t₂) (fun j => c₁ (t₂ j) * c₂ j) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, monomialMatrix, Function.comp_apply]
  rw [Finset.sum_eq_single (t₂ j)]
  · by_cases hi : i = t₁ (t₂ j) <;> simp [hi]
  · intro k _ hk
    simp [hk]
  · intro hmem
    exact absurd (Finset.mem_univ (t₂ j)) hmem

/-- Jordan-Wigner prefix parity (-1)^{∑_{j < k} n_j}. -/
def prefixCount (y : Fin 32) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun acc j => acc + bitAt y j) 0

def jwSign (y : Fin 32) (k : ℕ) : ℤ :=
  if prefixCount y k % 2 = 0 then 1 else -1

/-- Basis flip for Majorana generator γ_A (mode k = A / 2). -/
def gammaFlip (A : Fin 10) (y : Fin 32) : Fin 32 :=
  ⟨(y.val ^^^ (1 <<< (A.val / 2))) % 32, Nat.mod_lt _ (by decide)⟩

/-- Coefficient for γ_{2k} = c_k + c_k† and γ_{2k+1} = i(c_k† - c_k). -/
def gammaCoeff (A : Fin 10) (y : Fin 32) : GaussianInt :=
  let k := A.val / 2
  let σ := jwSign y k
  if A.val % 2 = 0 then
    ⟨σ, 0⟩
  else
    let s := if bitAt y k = 0 then σ else -σ
    ⟨0, s⟩

def gammaMatrix (A : Fin 10) : Matrix (Fin 32) (Fin 32) GaussianInt :=
  monomialMatrix (gammaFlip A) (gammaCoeff A)

private lemma clifford_flip_comm :
    ∀ A B : Fin 10, ∀ j : Fin 32, gammaFlip A (gammaFlip B j) = gammaFlip B (gammaFlip A j) := by
  decide

private lemma clifford_flip_self :
    ∀ A : Fin 10, ∀ j : Fin 32, gammaFlip A (gammaFlip A j) = j := by
  decide

private lemma clifford_coeff_diag :
    ∀ A : Fin 10, ∀ j : Fin 32,
      gammaCoeff A (gammaFlip A j) * gammaCoeff A j +
      gammaCoeff A (gammaFlip A j) * gammaCoeff A j = 2 := by
  decide

private lemma clifford_coeff_anticomm :
    ∀ A B : Fin 10, ∀ j : Fin 32, A ≠ B →
      gammaCoeff A (gammaFlip B j) * gammaCoeff B j +
      gammaCoeff B (gammaFlip A j) * gammaCoeff A j = 0 := by
  decide

/-- Exact 10-dimensional Clifford algebra: {γ_A, γ_B} = 2 δ_{AB} I₃₂. -/
theorem clifford_algebra_10d (A B : Fin 10) :
    gammaMatrix A * gammaMatrix B + gammaMatrix B * gammaMatrix A =
    (if A = B then (2 : GaussianInt) else 0) • (1 : Matrix (Fin 32) (Fin 32) GaussianInt) := by
  simp only [gammaMatrix]
  rw [monomialMatrix_mul, monomialMatrix_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    monomialMatrix, Function.comp_apply]
  rw [clifford_flip_comm A B j]
  by_cases hAB : A = B
  · subst hAB
    rw [clifford_flip_self A j]
    by_cases hij : i = j
    · subst hij
      simpa using clifford_coeff_diag A i
    · simp [hij]
  · have hc : gammaCoeff A (gammaFlip B j) * gammaCoeff B j +
              gammaCoeff B (gammaFlip A j) * gammaCoeff A j = 0 :=
      clifford_coeff_anticomm A B j hAB
    by_cases hij : i = gammaFlip B (gammaFlip A j)
    · simp [hij, hAB, hc]
    · simp [hij, hAB]

/-- Fermion-parity chirality operator Γ_* = (-1)^{N̂}. -/
def chiralityCoeff (y : Fin 32) : GaussianInt :=
  if parity5 y = 0 then ⟨1, 0⟩ else ⟨-1, 0⟩

def chiralityMatrix : Matrix (Fin 32) (Fin 32) GaussianInt :=
  monomialMatrix id chiralityCoeff

theorem chirality_sq :
    chiralityMatrix * chiralityMatrix = (1 : Matrix (Fin 32) (Fin 32) GaussianInt) := by
  rw [chiralityMatrix, monomialMatrix_mul]
  apply Matrix.ext
  intro i j
  simp only [monomialMatrix, Function.comp_apply, id_eq, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    have hsq : ∀ x : Fin 32, chiralityCoeff x * chiralityCoeff x = 1 := by decide
    simp [hsq]
  · simp [hij]

private lemma chirality_gamma_flip_sign :
    ∀ A : Fin 10, ∀ j : Fin 32,
      chiralityCoeff (gammaFlip A j) * gammaCoeff A j +
      gammaCoeff A j * chiralityCoeff j = 0 := by
  decide

theorem chirality_anticommutes_gamma (A : Fin 10) :
    chiralityMatrix * gammaMatrix A + gammaMatrix A * chiralityMatrix = 0 := by
  simp only [chiralityMatrix, gammaMatrix]
  rw [monomialMatrix_mul, monomialMatrix_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, Matrix.zero_apply, monomialMatrix, Function.comp_apply, id_eq]
  by_cases hij : i = gammaFlip A j
  · subst hij
    simpa using chirality_gamma_flip_sign A j
  · simp [hij]

/-- Even Clifford products (generators of Spin(10)) preserve the chiral sectors F⁺(V) = S⁺₁₀. -/
theorem chirality_commutes_spin10 (A B : Fin 10) :
    chiralityMatrix * (gammaMatrix A * gammaMatrix B) =
    (gammaMatrix A * gammaMatrix B) * chiralityMatrix := by
  have hA : chiralityMatrix * gammaMatrix A = - (gammaMatrix A * chiralityMatrix) :=
    eq_neg_of_add_eq_zero_left (chirality_anticommutes_gamma A)
  have hB : chiralityMatrix * gammaMatrix B = - (gammaMatrix B * chiralityMatrix) :=
    eq_neg_of_add_eq_zero_left (chirality_anticommutes_gamma B)
  calc
    chiralityMatrix * (gammaMatrix A * gammaMatrix B)
        = (chiralityMatrix * gammaMatrix A) * gammaMatrix B := by rw [mul_assoc]
    _   = (- (gammaMatrix A * chiralityMatrix)) * gammaMatrix B := by rw [hA]
    _   = - (gammaMatrix A * (chiralityMatrix * gammaMatrix B)) := by rw [neg_mul, mul_assoc]
    _   = - (gammaMatrix A * (- (gammaMatrix B * chiralityMatrix))) := by rw [hB]
    _   = (gammaMatrix A * gammaMatrix B) * chiralityMatrix := by rw [mul_neg, neg_neg, mul_assoc]

/-! ## Part 3: 3+2 Hypercharge, 16 = 10 + 5̄ + 1 Branching, and Anomaly Cancellation -/

/-- Scaled hypercharge 6Y on V₃ ⊕ V₂: (-2, -2, -2, 3, 3) corresponding to (-1/3, -1/3, -1/3, 1/2, 1/2). -/
def y6Mode : Fin 5 → ℤ
  | ⟨0, _⟩ => -2
  | ⟨1, _⟩ => -2
  | ⟨2, _⟩ => -2
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 3

/-- Induced scaled hypercharge 6Y(y) = ∑_k n_k(y) · 6Y_k on Fock basis state y. -/
def y6State (y : Fin 32) : ℤ :=
  (bitAt y 0 : ℤ) * y6Mode 0 + (bitAt y 1 : ℤ) * y6Mode 1 +
  (bitAt y 2 : ℤ) * y6Mode 2 + (bitAt y 3 : ℤ) * y6Mode 3 +
  (bitAt y 4 : ℤ) * y6Mode 4

theorem hypercharge_mode_normalization :
    (∑ k : Fin 5, y6Mode k) = 0 ∧ (∑ k : Fin 5, (y6Mode k)^2) = 30 := by
  decide

/-- Exact multiplet counts and hypercharges across the 16 states of F⁺(V):
    uᶜ:(2,0) 3@-4, Q:(1,1) 6@+1, eᶜ:(0,2) 1@+6, dᶜ:(2,2) 3@+2, L:(3,1) 2@-3, νᶜ:(0,0) 1@0. -/
theorem generation_branching_16 :
    let even := Finset.univ.filter fun y : Fin 32 => parity5 y = 0
    (even.filter fun y => v3Count y = 2 ∧ v2Count y = 0 ∧ y6State y = -4).card = 3 ∧
    (even.filter fun y => v3Count y = 1 ∧ v2Count y = 1 ∧ y6State y = 1).card = 6 ∧
    (even.filter fun y => v3Count y = 0 ∧ v2Count y = 2 ∧ y6State y = 6).card = 1 ∧
    (even.filter fun y => v3Count y = 2 ∧ v2Count y = 2 ∧ y6State y = 2).card = 3 ∧
    (even.filter fun y => v3Count y = 3 ∧ v2Count y = 1 ∧ y6State y = -3).card = 2 ∧
    (even.filter fun y => v3Count y = 0 ∧ v2Count y = 0 ∧ y6State y = 0).card = 1 := by
  decide

/-- Exact cancellation of all gauge and gravitational anomalies across the 16 states of F⁺(V):
    1. Gravitational-hypercharge: ∑_{F⁺} 6Y = 0
    2. Cubic hypercharge:         ∑_{F⁺} (6Y)³ = 0
    3. SU(2)_L² × U(1)_Y:         ∑_{F⁺, doublets} 6Y = 0
    4. SU(2)_L Witten global:     8 doublet states = 4 weak doublets (even)
    5. SU(3)_C³:                  2(3-rep) - 1(3̄-rep) - 1(3̄-rep) = 0
    6. SU(3)_C² × U(1)_Y:         ∑_{F⁺, triplets/antitriplets} 6Y = 0 -/
theorem standard_model_anomaly_cancellations :
    let even := Finset.univ.filter fun y : Fin 32 => parity5 y = 0
    let doublets := even.filter fun y => v2Count y = 1
    let colored := even.filter fun y => v3Count y = 1 ∨ v3Count y = 2
    (∑ y ∈ even, y6State y) = 0 ∧
    (∑ y ∈ even, (y6State y)^3) = 0 ∧
    (∑ y ∈ doublets, y6State y) = 0 ∧
    doublets.card = 8 ∧
    ((even.filter fun y => v3Count y = 1).card : ℤ) / 3 -
      ((even.filter fun y => v3Count y = 2).card : ℤ) / 3 = 0 ∧
    (∑ y ∈ colored, y6State y) = 0 := by
  decide

end Imscribing.Millennium.Spin10ChiralFock