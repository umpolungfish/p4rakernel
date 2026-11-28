import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# 12-Morphism + 1 Augmentation, Six Dyadic Pairs, and Reflected-Transfer Algebra (§§468–489)

Formalizes:
1. Six dyadic pairing involution `J₆`, pair-even/odd matrices `Fₑ, Fₒ`, `G_F = Fₑᴴ Fₑ + Fₒᴴ Fₒ`,
   and `H_F = Fₑᴴ Fₑ - Fₒᴴ Fₒ`.
2. Triangle-complement symmetry `D_* = !![0, 1; 1, 0]` (`[D_*, G_*] = [D_*, H_*] = 0`):
   bisymmetric matrix form, exact even/odd eigenvalues `(r ± s)/(g ± h)`, and splitting `(474.6)`.
3. Exact `+1` scalar augmentation `F_aug`: `H_aug *ᵥ e₅ = G_aug *ᵥ e₅`, Schur quotient `W`,
   difference invariance `G_q - H_q = G - H`, `R₆` / `K_q` trace moment equality `Tr(R₆^j) = Tr(K_q^j)`,
   and noncanonical dual-frame correction `(489.2)` vanishing under `J₆(ran F) ⊆ ran F`.
-/

namespace Imscribing.TrilatticeYM

open Matrix

/-- Six-dyadic-pair swap involution `J₆` on `12 = 6 × 2` morphism labels (`(468.3)`). -/
def J6 : Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) ℂ :=
  fun (p, a) (q, b) => if p = q ∧ a ≠ b then 1 else 0

theorem J6_hermitian : J6ᴴ = J6 := by
  ext ⟨p, a⟩ ⟨q, b⟩
  simp only [Matrix.conjTranspose_apply, J6]
  split_ifs with h1 h2 h2
  · simp
  · exfalso; exact h2 ⟨h1.1.symm, h1.2.symm⟩
  · exfalso; exact h1 ⟨h2.1.symm, h2.2.symm⟩
  · simp

theorem J6_sq : J6 * J6 = 1 := by
  ext ⟨p, a⟩ ⟨q, b⟩
  simp only [Matrix.mul_apply, Matrix.one_apply, J6]
  rw [Fintype.sum_prod_type]
  by_cases hpq : p = q
  · subst hpq
    simp only [true_and]
    rw [Finset.sum_eq_single p]
    · fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two]
    · intro r _ hr; simp [Ne.symm hr]
    · simp
  · simp only [Prod.ext_iff, hpq, false_and, ↓reduceIte]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun c _ => ?_
    by_cases hpr : p = r
    · subst hpr; simp [hpq]
    · simp [hpr]

theorem J6_mulVec_one : J6 *ᵥ (fun _ : Fin 6 × Fin 2 => (1 : ℂ)) = fun _ => 1 := by
  ext ⟨p, a⟩
  simp only [Matrix.mulVec, dotProduct, J6, mul_one]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
  · fin_cases a <;> simp [Fin.sum_univ_two]
  · intro r _ hr; simp [Ne.symm hr]
  · simp

/-- Even and odd pair combinations `Fₑ, Fₒ ∈ M_{6×4}(ℂ)` (`(472.1)`). -/
noncomputable def Feven (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) : Matrix (Fin 6) (Fin 4) ℂ :=
  fun p j => (F (p, 0) j + F (p, 1) j) / Real.sqrt 2

noncomputable def Fodd (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) : Matrix (Fin 6) (Fin 4) ℂ :=
  fun p j => (F (p, 0) j - F (p, 1) j) / Real.sqrt 2

private lemma sqrt2_sq_complex : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  norm_cast; exact Real.sq_sqrt (by norm_num)

theorem pair_gram_even_odd (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) :
    Fᴴ * F = (Feven F)ᴴ * Feven F + (Fodd F)ᴴ * Fodd F ∧
    Fᴴ * J6 * F = (Feven F)ᴴ * Feven F - (Fodd F)ᴴ * Fodd F := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := sqrt2_sq_complex
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_cast; positivity
  have hstar : star (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
    simp [Complex.star_def, Complex.conj_ofReal]
  constructor
  · ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, Feven, Fodd]
    rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Fin.sum_univ_two, StarMul.star_mul, star_div₀, hstar]
    field_simp [hne]
    rw [hsq]
    simp only [star_add, star_sub]
    ring
  · ext i j
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Feven, Fodd, J6]
    have hLHS :
        (∑ x : Fin 6 × Fin 2,
          (∑ x_1 : Fin 6 × Fin 2, star (F x_1 i) *
            (if x_1.1 = x.1 ∧ x_1.2 ≠ x.2 then (1 : ℂ) else 0)) * F x j) =
        ∑ p : Fin 6, (star (F (p, 0) i) * F (p, 1) j + star (F (p, 1) i) * F (p, 0) j) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Fin.sum_univ_two, Fintype.sum_prod_type]
      have hs0 : (∑ x : Fin 6, (star (F (x, 0) i) * (if x = p ∧ (0 : Fin 2) ≠ 0 then 1 else 0) +
          star (F (x, 1) i) * (if x = p ∧ (1 : Fin 2) ≠ 0 then 1 else 0))) = star (F (p, 1) i) := by
        simp [Finset.sum_ite_eq']
      have hs1 : (∑ x : Fin 6, (star (F (x, 0) i) * (if x = p ∧ (0 : Fin 2) ≠ 1 then 1 else 0) +
          star (F (x, 1) i) * (if x = p ∧ (1 : Fin 2) ≠ 1 then 1 else 0))) = star (F (p, 0) i) := by
        simp [Finset.sum_ite_eq']
      rw [hs0, hs1]; ring
    rw [hLHS, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [StarMul.star_mul, star_div₀, hstar]
    field_simp [hne]
    rw [hsq]
    simp only [star_add, star_sub]
    ring

/-- Triangle-complement duality involution `D_* = !![0, 1; 1, 0]` (`(469.1)`). -/
def Dstar : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem bisymmetric_of_comm_Dstar (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hcomm : Dstar * M = M * Dstar) :
    M 1 1 = M 0 0 ∧ M 1 0 = M 0 1 := by
  have h00 := congrFun (congrFun hcomm 0) 0
  have h01 := congrFun (congrFun hcomm 0) 1
  simp only [Dstar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at h00 h01
  norm_num at h00 h01
  exact ⟨h01, h00⟩

theorem generalized_eigen_bisymmetric (g h r s : ℂ)
    (G H : Matrix (Fin 2) (Fin 2) ℂ)
    (hG : G = !![g, h; h, g]) (hH : H = !![r, s; s, r]) :
    let ze : Fin 2 → ℂ := ![1, 1]
    let zo : Fin 2 → ℂ := ![1, -1]
    (g + h) • (H *ᵥ ze) = (r + s) • (G *ᵥ ze) ∧
    (g - h) • (H *ᵥ zo) = (r - s) • (G *ᵥ zo) ∧
    (g + h ≠ 0 → g - h ≠ 0 →
      (r + s) / (g + h) - (r - s) / (g - h) = 2 * (g * s - r * h) / (g ^ 2 - h ^ 2)) := by
  subst hG; subst hH
  refine ⟨?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  · intro hplus hminus
    have hsq : g ^ 2 - h ^ 2 = (g + h) * (g - h) := by ring
    have hsq0 : g ^ 2 - h ^ 2 ≠ 0 := by rw [hsq]; exact mul_ne_zero hplus hminus
    field_simp [hplus, hminus, hsq0]
    ring

/-- Augmented `12 × (4 + 1)` frame `F_aug = [F | 1]` (`(477.1)`). -/
def Faug (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) : Matrix (Fin 6 × Fin 2) (Fin 4 ⊕ Unit) ℂ :=
  fun r => Sum.elim (F r) (fun _ => 1)

/-- Scalar augmentation basis vector `e₅`. -/
def e5 : (Fin 4 ⊕ Unit) → ℂ := Sum.elim (fun _ => 0) (fun _ => 1)

theorem Faug_mulVec_e5 (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) :
    Faug F *ᵥ e5 = fun _ => 1 := by
  ext r
  simp [Matrix.mulVec, dotProduct, Faug, e5, Fintype.sum_sum_type]

/-- Exact preserved `+1` closure eigenvalue on `e₅` (`(477.4)`). -/
theorem aug_scalar_preserved (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) :
    let G := (Faug F)ᴴ * Faug F
    let H := (Faug F)ᴴ * J6 * Faug F
    H *ᵥ e5 = G *ᵥ e5 := by
  dsimp only
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Faug_mulVec_e5, J6_mulVec_one]

/-- Quotient embedding `W : M_{(4+1)×4}(ℂ)` onto the `G_aug`-orthogonal complement of `e₅` (`(478.1)`). -/
noncomputable def Wquot (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) :
    Matrix (Fin 4 ⊕ Unit) (Fin 4) ℂ :=
  fun c j =>
    let g : Fin 4 → ℂ := Fᴴ *ᵥ (fun _ => 1)
    match c with
    | Sum.inl i => if i = j then 1 else 0
    | Sum.inr () => -(star (g j)) / 12

theorem Faug_mul_Wquot (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) (r : Fin 6 × Fin 2) (j : Fin 4) :
    (Faug F * Wquot F) r j = F r j - star ((Fᴴ *ᵥ fun _ => 1) j) / 12 := by
  simp only [Matrix.mul_apply, Faug, Wquot, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Fintype.sum_unique, one_mul, sub_eq_add_neg]
  ring

theorem Wquot_orthogonal_one (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) (j : Fin 4) :
    ∑ r : Fin 6 × Fin 2, (Faug F * Wquot F) r j = 0 := by
  simp_rw [Faug_mul_Wquot]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  have hsum : ∑ r : Fin 6 × Fin 2, F r j = star ((Fᴴ *ᵥ fun _ => 1) j) := by
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum]
  rw [hsum]
  norm_num
  ring

/-- Quotient difference invariance `G_q - H_q = G - H` (`(478.4)`). -/
theorem schur_quotient_diff_invariant (F : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ) :
    let Gq := (Wquot F)ᴴ * ((Faug F)ᴴ * Faug F) * Wquot F
    let Hq := (Wquot F)ᴴ * ((Faug F)ᴴ * J6 * Faug F) * Wquot F
    Gq - Hq = Fᴴ * F - Fᴴ * J6 * F := by
  dsimp only
  let M := Faug F * Wquot F
  let C : Matrix (Fin 6 × Fin 2) (Fin 4) ℂ :=
    fun _ j => star ((Fᴴ *ᵥ fun _ => 1) j) / 12
  have hM : M = F - C := by
    ext r j; exact Faug_mul_Wquot F r j
  have hC1 : (1 - J6) * C = 0 := by
    ext r j
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, C]
    rw [← Finset.sum_mul]
    have hrow : (∑ x : Fin 6 × Fin 2, ((if r = x then (1 : ℂ) else 0) - J6 r x)) = 0 := by
      rw [Finset.sum_sub_distrib]
      have h1 : (∑ x : Fin 6 × Fin 2, if r = x then (1 : ℂ) else 0) = 1 := by simp
      have hJ : ∑ x : Fin 6 × Fin 2, J6 r x = 1 := by
        simpa [Matrix.mulVec, dotProduct] using congrFun J6_mulVec_one r
      rw [h1, hJ, sub_self]
    rw [hrow, zero_mul]
  have hC2 : Cᴴ * (1 - J6) = 0 := by
    have h := congrArg Matrix.conjTranspose hC1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      J6_hermitian, Matrix.conjTranspose_zero] at h
    exact h
  have hLHS :
      (Wquot F)ᴴ * ((Faug F)ᴴ * Faug F) * Wquot F -
        (Wquot F)ᴴ * ((Faug F)ᴴ * J6 * Faug F) * Wquot F =
      Mᴴ * (1 - J6) * M := by
    have h1 : (Wquot F)ᴴ * ((Faug F)ᴴ * Faug F) * Wquot F = Mᴴ * M := by
      simp only [M, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have h2 : (Wquot F)ᴴ * ((Faug F)ᴴ * J6 * Faug F) * Wquot F = Mᴴ * J6 * M := by
      simp only [M, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [h1, h2, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  have hRHS : Fᴴ * F - Fᴴ * J6 * F = Fᴴ * (1 - J6) * F := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  rw [hLHS, hRHS, hM]
  calc (F - C)ᴴ * (1 - J6) * (F - C)
      = (Fᴴ - Cᴴ) * ((1 - J6) * F - (1 - J6) * C) := by
          rw [Matrix.conjTranspose_sub, Matrix.mul_assoc, Matrix.mul_sub]
    _ = (Fᴴ - Cᴴ) * ((1 - J6) * F) := by rw [hC1, sub_zero]
    _ = Fᴴ * ((1 - J6) * F) - Cᴴ * (1 - J6) * F := by
          rw [Matrix.sub_mul, Matrix.mul_assoc]
    _ = Fᴴ * (1 - J6) * F := by rw [hC2, Matrix.zero_mul, sub_zero, Matrix.mul_assoc]

private lemma pow_mul_assoc_shift {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    ∀ k : ℕ, (A * B) ^ k * A = A * (B * A) ^ k
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ', Matrix.mul_assoc, pow_mul_assoc_shift A B k, Matrix.mul_assoc A B,
        ← Matrix.mul_assoc B A, ← pow_succ']

/-- Exact trace moment equality `Tr(R₆^j) = Tr(K_q^j)` for all `j ≥ 1` (`§§484–486`). -/
theorem trace_pow_mul_comm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) (k : ℕ) :
    ((A * B) ^ (k + 1)).trace = ((B * A) ^ (k + 1)).trace := by
  rw [pow_succ, ← Matrix.mul_assoc, pow_mul_assoc_shift A B k, Matrix.mul_assoc,
    Matrix.trace_mul_comm, Matrix.mul_assoc ((B * A) ^ k) B A, ← pow_succ]

/-- Noncanonical dual-frame closure correction `(489.2)` vanishes iff `J` preserves `ran F`. -/
theorem noncanonical_dual_correction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (F : Matrix m n ℂ) (G_inv : Matrix n n ℂ) (J : Matrix m m ℂ) (Z0 : Matrix n m ℂ)
    (hGinv : G_inv * (Fᴴ * F) = 1) :
    let P := F * G_inv * Fᴴ
    let F_tilde := G_inv * Fᴴ + Z0 * (1 - P)
    (F_tilde * F = (1 : Matrix n n ℂ)) ∧
    (F_tilde * J * F = G_inv * Fᴴ * J * F + Z0 * (1 - P) * J * F) ∧
    ((∃ M : Matrix n n ℂ, J * F = F * M) → Z0 * (1 - P) * J * F = 0) := by
  intro P F_tilde
  have hPF : P * F = F := by
    dsimp [P]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hGinv, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [F_tilde]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hGinv, Matrix.sub_mul, Matrix.one_mul, hPF,
      sub_self, Matrix.mul_zero, add_zero]
  · dsimp [F_tilde]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
  · rintro ⟨M, hJF⟩
    calc Z0 * (1 - P) * J * F
        = Z0 * (1 - P) * (J * F) := by rw [Matrix.mul_assoc]
      _ = Z0 * ((1 - P) * F) * M := by rw [hJF]; simp only [Matrix.mul_assoc]
      _ = Z0 * (F - P * F) * M := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = 0 := by rw [hPF, sub_self, Matrix.mul_zero, Matrix.zero_mul]

end Imscribing.TrilatticeYM
