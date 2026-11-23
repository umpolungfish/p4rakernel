/-
  Imscribing/YangMills/GappedGaugeSystem.lean

  The gap statement's type depends on the gauge system.

  The Hamiltonian is defined from the gauge data (`H = 1 - S`), the ground
  state is a genuine eigenvector, and the gap is a statement about eigenvalues
  of that matrix on the orthogonal complement of the ground state.
-/
import Mathlib
import Imscribing.YangMills.MassGapInstances

open Matrix

namespace MassGapInstances

/-- A gauge system together with a Hamiltonian built from its data.
`H_def` is the key field: H is not free, it is `1 - S`.
`gap` says every eigenvector orthogonal to the ground state has eigenvalue
real and ≥ Δ (the matrix analogue of `spec(H) ∩ (0, Δ) = ∅`). -/
structure GappedGaugeSystem (κ : Type) (n : ℕ) [DecidableEq κ] where
  Q : LatticeQGS κ (Matrix (Fin n) (Fin n) ℂ)
  H : Matrix (Fin n) (Fin n) ℂ
  H_def : H = 1 - Q.S
  ground : Fin n → ℂ
  ground_ne : ground ≠ 0
  ground_eig : H.mulVec ground = 0
  Δ : ℝ
  Δ_pos : 0 < Δ
  gap : ∀ (v : Fin n → ℂ) (l : ℂ), v ≠ 0 → star ground ⬝ᵥ v = 0 →
      H.mulVec v = l • v → l.im = 0 ∧ Δ ≤ l.re

section TwoLevel

private theorem S_eq : twoLevel.S = !![(1 : ℂ), 0; 0, -1] := by
  unfold twoLevel
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Zmat]

private def Hmat : Matrix (Fin 2) (Fin 2) ℂ := !![(0 : ℂ), 0; 0, 2]

private def groundVec : Fin 2 → ℂ := ![1, 0]

private theorem Hmat_eq : Hmat = 1 - twoLevel.S := by
  rw [S_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hmat] <;> norm_num

/-- The two-level system with H = 1 - Z (eigenvalues 0 and 2), derived from S. -/
noncomputable def twoLevelGapped : GappedGaugeSystem Unit 2 where
  Q := twoLevel
  H := Hmat
  H_def := Hmat_eq
  ground := groundVec
  ground_ne := by
    intro h
    have := congrFun h 0
    simp [groundVec] at this
  ground_eig := by
    ext i
    fin_cases i <;> simp [Hmat, groundVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  Δ := 2
  Δ_pos := by norm_num
  gap := by
    intro v l hv horth h
    have h0 : v 0 = 0 := by
      simpa [dotProduct, Fin.sum_univ_two, groundVec] using horth
    have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    have e : (Hmat.mulVec v) 1 = (l • v) 1 := congrFun h 1
    have lhs : (Hmat.mulVec v) 1 = 2 * v 1 := by
      simp [Hmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have rhs : (l • v) 1 = l * v 1 := by simp
    rw [lhs, rhs] at e
    have hl : l = 2 := mul_right_cancel₀ h1 e.symm
    rw [hl]
    constructor <;> simp

/-- HEADLINE (upgraded). The gap is carried by a gauge system with nonzero
lattice commutator, and H is built from that system's S. -/
theorem two_level_gauge_gap :
    ∃ G : GappedGaugeSystem Unit 2,
      G.Q.A () * G.Q.E () - G.Q.E () * G.Q.A () ≠ 0 :=
  ⟨twoLevelGapped, twoLevel_nontrivial⟩

/-! ### Discrimination: the predicate can fail -/

/-- With H = 0 there is no positive gap (excited eigenvector ![0,1] has eigenvalue 0). -/
theorem zero_hamiltonian_has_no_gap (Δ : ℝ) (hΔ : 0 < Δ) :
    ¬ (∀ (v : Fin 2 → ℂ) (l : ℂ), v ≠ 0 → star groundVec ⬝ᵥ v = 0 →
        (0 : Matrix (Fin 2) (Fin 2) ℂ).mulVec v = l • v → l.im = 0 ∧ Δ ≤ l.re) := by
  intro h
  have hv : (![0, 1] : Fin 2 → ℂ) ≠ 0 := by
    intro h'
    have := congrFun h' 1
    simp at this
  have horth : star groundVec ⬝ᵥ (![0, 1] : Fin 2 → ℂ) = 0 := by
    simp [groundVec, dotProduct, Fin.sum_univ_two]
  have heq : (0 : Matrix (Fin 2) (Fin 2) ℂ).mulVec ![0, 1] = (0 : ℂ) • (![0, 1] : Fin 2 → ℂ) := by
    simp
  have h2 : Δ ≤ (0 : ℂ).re := (h _ 0 hv horth heq).2
  simp only [Complex.zero_re] at h2
  linarith

/-- A classical (commuting) system forces S = 0, so it cannot be a nondegenerate QGS. -/
theorem commuting_forces_S_zero {𝔄 : Type} [Ring 𝔄] [Algebra ℂ 𝔄]
    (Q : LatticeQGS Unit 𝔄)
    (hcomm : Q.A () * Q.E () = Q.E () * Q.A ()) : Q.S = 0 := by
  have h := Q.ccr_lattice () ()
  rw [if_pos rfl, hcomm, sub_self] at h
  have hne : (Complex.I * (Q.ħ : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Q.ħ_pos.ne')
  exact (smul_eq_zero.mp h.symm).resolve_left hne

end TwoLevel

#print axioms two_level_gauge_gap
#print axioms zero_hamiltonian_has_no_gap

end MassGapInstances
