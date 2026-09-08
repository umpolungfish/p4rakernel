import Imscribing.ABC_PrimeTransport
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-! # Finite arithmetic discrepancy operators

The diagonal entries retain the signed arithmetic discrepancy. Uniform
upper bounds on all their eigenvalues are equivalent to arithmetic ABC.
No off-diagonal transition or POVM normalization is presumed.
-/
namespace Imscribing.ABC

noncomputable def discrepancyOperator {n : ℕ} (family : Fin n → Triple)
    (ε : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => discrepancy ε (family i))

/-- Explicit real eigenvalue equation, including the nonzero-vector condition. -/
def ArithmeticEigenvalue {n : ℕ} (family : Fin n → Triple) (ε value : ℝ) : Prop :=
  ∃ v : Fin n → ℝ, v ≠ 0 ∧ (discrepancyOperator family ε).mulVec v = value • v

theorem discrepancyOperator_action {n : ℕ} (family : Fin n → Triple)
    (ε : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (discrepancyOperator family ε).mulVec v i = discrepancy ε (family i) * v i := by
  simp [discrepancyOperator, Matrix.mulVec_diagonal]

/-- The spectrum consists exactly of the discrepancies of the sampled triples. -/
theorem arithmeticEigenvalue_iff {n : ℕ} (family : Fin n → Triple) (ε value : ℝ) :
    ArithmeticEigenvalue family ε value ↔ ∃ i, discrepancy ε (family i) = value := by
  classical
  constructor
  · rintro ⟨v, hv, he⟩
    have hex : ∃ i, v i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (funext h)
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, ?_⟩
    have heq := congrFun he i
    rw [discrepancyOperator_action] at heq
    exact mul_right_cancel₀ hi heq
  · rintro ⟨i, hi⟩
    refine ⟨Pi.single i 1, ?_, ?_⟩
    · intro h
      have := congrFun h i
      simp at this
    · funext j
      rw [discrepancyOperator_action]
      by_cases h : j = i
      · subst j
        simp [hi]
      · simp [h]

/-- Every nonempty finite reading has an attained largest eigenvalue.
    The maximizing index may change when the family is enlarged. -/
theorem finite_spectrum_has_maximum {n : ℕ} (hn : 0 < n)
    (family : Fin n → Triple) (ε : ℝ) :
    ∃ top : ℝ, ArithmeticEigenvalue family ε top ∧
      ∀ value, ArithmeticEigenvalue family ε value → value ≤ top := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => discrepancy ε (family i)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨discrepancy ε (family i),
    (arithmeticEigenvalue_iff _ _ _).mpr ⟨i, rfl⟩, ?_⟩
  intro value hv
  obtain ⟨j, rfl⟩ := (arithmeticEigenvalue_iff _ _ _).mp hv
  exact hi j (Finset.mem_univ _)

def UniformSpectralUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, ∀ family : Fin n → Triple,
    ∀ value : ℝ, ArithmeticEigenvalue family ε value → value ≤ C

/-- The constant is chosen before the size, family, and eigenvalue.
    Singleton families establish the reverse implication. -/
theorem uniform_spectral_iff_abc : UniformSpectralUpperBound ↔ Conjecture := by
  constructor
  · intro h
    apply conjecture_iff_uniform_discrepancy.mpr
    intro ε hε
    obtain ⟨C, hC⟩ := h ε hε
    refine ⟨C, fun t => ?_⟩
    apply hC 1 (fun _ => t) (discrepancy ε t)
    exact (arithmeticEigenvalue_iff _ _ _).mpr ⟨0, rfl⟩
  · intro h ε hε
    obtain ⟨C, hC⟩ := conjecture_iff_uniform_discrepancy.mp h ε hε
    refine ⟨C, fun n family value hvalue => ?_⟩
    obtain ⟨i, rfl⟩ := (arithmeticEigenvalue_iff family ε value).mp hvalue
    exact hC (family i)

theorem squarefree_spectrum_nonpositive {n : ℕ} (family : Fin n → Triple)
    (hf : ∀ i, Squarefree (family i).c) (ε : ℝ) (hε : 0 < ε)
    (value : ℝ) (hvalue : ArithmeticEigenvalue family ε value) : value ≤ 0 := by
  obtain ⟨i, rfl⟩ := (arithmeticEigenvalue_iff family ε value).mp hvalue
  exact squarefree_discrepancy_bound ε hε (family i) (hf i)

/-- Retain the arithmetic and spectral formulations together. -/
def spectralClosure (h : UniformSpectralUpperBound) :
    Imscribing.Paraconsistent.DialetheicWitness.Verdict Conjecture :=
  .held (uniform_spectral_iff_abc.mp h) h

theorem spectralClosure_is_B (h : UniformSpectralUpperBound) :
    (spectralClosure h).classify = (true, true) := rfl

end Imscribing.ABC
