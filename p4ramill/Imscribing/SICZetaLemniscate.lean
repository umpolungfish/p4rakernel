import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import Imscribing.IMASM.BankedWeight
import Imscribing.Millennium.GrammarUniversalDualFrameSICPOVM

/-! Analytic value, explicit tetrahedral dual Gram matrix, banked-weight
enclosing repair, Log-Lemniscate (L₂) void compactification, and higher-dimensional
k-petal rose centroid void theorem. -/
namespace Imscribing.Millennium.ZetaSICDualFrame

def sourceWord : String := "⊢≻⊤⋈∈⊤⊥⊞∋≺⊙⊡⊣"
def strandedWord : String := "⊢∋⊤⋈∈⊤⊥⊞≻≺⊙⊡⊣"

theorem zeta_neg_one : riemannZeta (-1) = (-1 / 12 : ℂ) := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  norm_num [bernoulli_two] at h
  simpa only [neg_div] using h

/-- Gram matrix of four normalized tetrahedral SIC projectors:
unit self-overlap and one-third distinct overlap. -/
noncomputable def tetraGram : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => if i = j then 1 else 1 / 3

/-- The zeta value supplies the uniform correction to the inverse Gram matrix. -/
noncomputable def tetraDualGram : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => (if i = j then 3 / 2 else 0) + 3 * riemannZeta (-1)

theorem tetra_dual_coefficients (i j : Fin 4) :
    tetraDualGram i j = if i = j then 5 / 4 else -1 / 4 := by
  simp only [tetraDualGram, zeta_neg_one]
  split <;> norm_num

theorem tetra_dual_left_inverse : tetraDualGram * tetraGram = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.mul_apply, tetra_dual_coefficients, tetraGram, Fin.sum_univ_four,
      Matrix.one_apply]; simp +decide; norm_num)

theorem tetra_dual_right_inverse : tetraGram * tetraDualGram = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.mul_apply, tetra_dual_coefficients, tetraGram, Fin.sum_univ_four,
      Matrix.one_apply]; simp +decide; norm_num)

/-- Analysis by the SIC Gram matrix followed by dual analysis recovers coordinates. -/
theorem tetra_coordinate_reconstruction (c : Fin 4 → ℂ) :
    tetraDualGram.mulVec (tetraGram.mulVec c) = c := by
  rw [Matrix.mulVec_mulVec, tetra_dual_left_inverse, Matrix.one_mulVec]

/-- In dimension twelve, the diagonal and uniform inverse-Gram coefficients
are (d+1)/d and -1/d², respectively. -/
theorem dimension_twelve_coefficients :
    (13 / 12 : ℂ) = 1 - riemannZeta (-1) ∧
    (-1 / 144 : ℂ) = riemannZeta (-1) / 12 := by
  rw [zeta_neg_one]
  constructor <;> norm_num

noncomputable def uniformMatrix (n : Nat) : Matrix (Fin n) (Fin n) ℂ := fun _ _ => 1

theorem uniform_square (n : Nat) :
    uniformMatrix n * uniformMatrix n = (n : ℂ) • uniformMatrix n := by
  ext i j
  simp [uniformMatrix, Matrix.mul_apply, Matrix.smul_apply]

private theorem uniform_affine_product (n : Nat) (a b c e : ℂ) :
    (a • (1 : Matrix (Fin n) (Fin n) ℂ) + b • uniformMatrix n) *
      (c • (1 : Matrix (Fin n) (Fin n) ℂ) + e • uniformMatrix n) =
    (a * c) • (1 : Matrix (Fin n) (Fin n) ℂ) +
      (a * e + b * c + b * e * (n : ℂ)) • uniformMatrix n := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one, uniform_square]
  module

noncomputable def sicGramGeneral (d : ℕ+) :
    Matrix (Fin ((d : ℕ) ^ 2)) (Fin ((d : ℕ) ^ 2)) ℂ :=
  (((d : ℕ) : ℂ) / (((d : ℕ) : ℂ) + 1)) • 1 +
    (1 / (((d : ℕ) : ℂ) + 1)) • uniformMatrix ((d : ℕ) ^ 2)

noncomputable def sicDualGeneral (d : ℕ+) :
    Matrix (Fin ((d : ℕ) ^ 2)) (Fin ((d : ℕ) ^ 2)) ℂ :=
  (1 - 12 / ((d : ℕ) : ℂ) * riemannZeta (-1)) • 1 +
    (12 / (((d : ℕ) : ℂ) ^ 2) * riemannZeta (-1)) •
      uniformMatrix ((d : ℕ) ^ 2)

/-- The zeta-derived dual inverts the isotropic SIC Gram matrix in every
positive dimension. Its two inverse identities are the rank-one cancellation
using the exact `d^2` all-ones eigenvalue. -/
theorem sic_inverse_general (d : ℕ+) :
    sicDualGeneral d * sicGramGeneral d = 1 ∧
    sicGramGeneral d * sicDualGeneral d = 1 := by
  let D : ℂ := (d : ℕ)
  let n : ℕ := (d : ℕ) ^ 2
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast d.ne_zero
  have hD1 : D + 1 ≠ 0 := by
    have hnat : ((d : ℕ) + 1 : ℕ) ≠ 0 := by omega
    change ((d : ℕ) : ℂ) + 1 ≠ 0
    exact_mod_cast hnat
  have hn : (n : ℂ) = D ^ 2 := by
    simp [n, D, Nat.cast_pow]
  let a : ℂ := 1 - 12 / D * riemannZeta (-1)
  let b : ℂ := 12 / D ^ 2 * riemannZeta (-1)
  let c : ℂ := D / (D + 1)
  let e : ℂ := 1 / (D + 1)
  have ha : a = (D + 1) / D := by
    dsimp [a]
    rw [zeta_neg_one]
    field_simp [hD]
    <;> ring
  have hb : b = -(1 / D ^ 2) := by
    dsimp [b]
    rw [zeta_neg_one]
    ring
  have hdiag : a * c = 1 := by rw [ha]; dsimp [c]; field_simp [hD, hD1]
  have hoff : a * e + b * c + b * e * (n : ℂ) = 0 := by
    rw [ha, hb, hn]
    dsimp [c, e]
    field_simp [hD, hD1]
    <;> ring
  have hleft :
      (a • (1 : Matrix (Fin n) (Fin n) ℂ) + b • uniformMatrix n) *
        (c • (1 : Matrix (Fin n) (Fin n) ℂ) + e • uniformMatrix n) = 1 := by
    rw [uniform_affine_product]
    rw [hdiag, hoff]
    simp
  have hdiag' : c * a = 1 := by simpa [mul_comm] using hdiag
  have hoff' : c * b + e * a + e * b * (n : ℂ) = 0 := by
    calc
      c * b + e * a + e * b * (n : ℂ) = a * e + b * c + b * e * (n : ℂ) := by ring
      _ = 0 := hoff
  have hright :
      (c • (1 : Matrix (Fin n) (Fin n) ℂ) + e • uniformMatrix n) *
        (a • (1 : Matrix (Fin n) (Fin n) ℂ) + b • uniformMatrix n) = 1 := by
    rw [uniform_affine_product]
    rw [hdiag', hoff']
    simp
  constructor
  · simpa [sicDualGeneral, sicGramGeneral, D, n, a, b, c, e] using hleft
  · simpa [sicDualGeneral, sicGramGeneral, D, n, a, b, c, e] using hright

/-- A dimension-four SIC has sixteen projector coordinates. -/
noncomputable def ququartGram : Matrix (Fin 16) (Fin 16) ℂ :=
  (4 / 5 : ℂ) • 1 + (1 / 5 : ℂ) • uniformMatrix 16

/-- The same analytic value, with the dimension-four normalization. -/
noncomputable def ququartDualGram : Matrix (Fin 16) (Fin 16) ℂ :=
  (1 - 3 * riemannZeta (-1)) • 1 +
    ((3 / 4 : ℂ) * riemannZeta (-1)) • uniformMatrix 16

theorem ququart_coefficients :
    (5 / 4 : ℂ) = 1 - 3 * riemannZeta (-1) ∧
    (-1 / 16 : ℂ) = (3 / 4 : ℂ) * riemannZeta (-1) := by
  rw [zeta_neg_one]
  constructor <;> norm_num

theorem ququart_dual_left_inverse : ququartDualGram * ququartGram = 1 := by
  simp only [ququartDualGram, ququartGram, zeta_neg_one, add_mul, mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    uniform_square]
  ext i j
  by_cases h : i = j <;>
    norm_num [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, uniformMatrix, h]

theorem ququart_dual_right_inverse : ququartGram * ququartDualGram = 1 := by
  simp only [ququartDualGram, ququartGram, zeta_neg_one, add_mul, mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    uniform_square]
  ext i j
  by_cases h : i = j <;>
    norm_num [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, uniformMatrix, h]

theorem ququart_coordinate_reconstruction (c : Fin 16 → ℂ) :
    ququartDualGram.mulVec (ququartGram.mulVec c) = c := by
  rw [Matrix.mulVec_mulVec, ququart_dual_left_inverse, Matrix.one_mulVec]

noncomputable def twelveGram : Matrix (Fin 144) (Fin 144) ℂ :=
  (12 / 13 : ℂ) • 1 + (1 / 13 : ℂ) • uniformMatrix 144

noncomputable def twelveDualGram : Matrix (Fin 144) (Fin 144) ℂ :=
  (1 - riemannZeta (-1)) • 1 + (riemannZeta (-1) / 12) • uniformMatrix 144

theorem twelve_dual_left_inverse : twelveDualGram * twelveGram = 1 := by
  simp only [twelveDualGram, twelveGram, zeta_neg_one, add_mul, mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    uniform_square]
  ext i j
  by_cases h : i = j <;>
    norm_num [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, uniformMatrix, h]

theorem twelve_coordinate_reconstruction (c : Fin 144 → ℂ) :
    twelveDualGram.mulVec (twelveGram.mulVec c) = c := by
  rw [Matrix.mulVec_mulVec, twelve_dual_left_inverse, Matrix.one_mulVec]

open Imscribing.IMASM

/-- The exposed weights reported in the supplied banked-count audit, in T,F,t,f order. -/
def exposedWeights : Weights (Fin 4) := ![2, 1, 1, 1]
def exposedCheckpoint : State (Fin 4) := ⟨exposedWeights, []⟩

def emptyWeightState : State (Fin 4) := ⟨fun _ => 0, []⟩
def depositedState : State (Fin 4) :=
  ((((emptyWeightState.touch 0).split.touch 0).touch 1).touch 2).touch 3
def strandedState : State (Fin 4) := depositedState.clear

theorem deposited_register_matches : ∀ i : Fin 4,
    depositedState.reg i = exposedWeights i := by decide
theorem original_fuse_leaves_exposed : depositedState.fuse.frames = [] := rfl
theorem stranded_register_empty : ∀ i : Fin 4, strandedState.reg i = 0 := by decide
theorem stranded_frame_weight :
    strandedState.frames.head?.map (fun f => ∑ i : Fin 4, f i) = some 4 := by decide
theorem final_fuse_recovers_four : (∑ i : Fin 4, strandedState.fuse.reg i) = 4 := by decide
theorem final_fuse_closes : strandedState.fuse.frames = [] := rfl

theorem exposed_total : (∑ i : Fin 4, exposedCheckpoint.reg i) = 5 := by decide
theorem exposed_reversal_loses_all : ∀ i : Fin 4,
    exposedCheckpoint.clear.fuse.reg i = 0 := by decide

/-- Open the holding region before computing in the inner region. Closing the
inner region deposits its result in the outer region before reversal. -/
def enclosingCheckpoint : State (Fin 4) :=
  ((((emptyWeightState.split.split.touch 0).touch 0).touch 1).touch 2).touch 3
def enclosingRepair : State (Fin 4) := enclosingCheckpoint.fuse.clear.fuse

theorem enclosing_repair_restores : ∀ i : Fin 4,
    enclosingRepair.reg i = exposedWeights i := by decide
theorem enclosing_repair_preserves_total : (∑ i : Fin 4, enclosingRepair.reg i) = 5 :=
  by decide
theorem enclosing_repair_closes_frames : enclosingRepair.frames = [] := rfl

/-! ### Log-Lemniscate (L₂) Void Compactification & Semiprime Symmetry -/

/-- Base-2 logarithmic angular map θ(x) = sgn(x) * arctan(log₂(1 + |x|)). -/
noncomputable def lemniscateAngle (x : ℝ) : ℝ :=
  (if x < 0 then -1 else if x > 0 then 1 else 0) *
    Real.arctan (Real.log (1 + |x|) / Real.log 2)

/-- Rational Bernoulli lemniscate embedding Φ : ℝ → ℝ × ℝ. -/
noncomputable def lemniscateEmbed (x : ℝ) : ℝ × ℝ :=
  let θ := lemniscateAngle x
  let denom := 1 + (Real.cos (2 * θ)) ^ 2
  (Real.sin (2 * θ) / denom, (Real.sin (2 * θ) * Real.cos (2 * θ)) / denom)

/-- Central void anchor: 0 maps to (0, 0), matching the ±∞ limit. -/
theorem lemniscate_zero_anchor : lemniscateEmbed 0 = (0, 0) := by
  simp [lemniscateEmbed, lemniscateAngle]

/-- Odd symmetry across the positive and negative loops: Φ(-x) = -Φ(x). -/
theorem lemniscate_odd_symmetry (x : ℝ) :
    lemniscateEmbed (-x) = (-(lemniscateEmbed x).1, -(lemniscateEmbed x).2) := by
  have hθ : lemniscateAngle (-x) = -lemniscateAngle x := by
    unfold lemniscateAngle
    rw [abs_neg]
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · have h1 : ¬(-x < 0) := by linarith
      have h2 : -x > 0 := by linarith
      rw [if_pos hx, if_neg h1, if_pos h2]
      ring
    · simp
    · have h1 : -x < 0 := by linarith
      have h2 : ¬(x < 0) := by linarith
      rw [if_pos h1, if_neg h2, if_pos hx]
      ring
  simp only [lemniscateEmbed, hθ, mul_neg, Real.sin_neg, Real.cos_neg, neg_sq]
  ext <;> dsimp <;> ring

/-- Void Symmetry Criterion (Theorem 1 of L₂):
The dual-loop factor chord midpoint M(p, q) = ½(Φ(p) + Φ(-q)) vanishes
whenever p = q (prime square semiprimes N = p²). -/
theorem factor_chord_void_symmetry (p : ℝ) :
    let P := lemniscateEmbed p
    let Q := lemniscateEmbed (-p)
    ((P.1 + Q.1) / 2, (P.2 + Q.2) / 2) = (0, 0) := by
  dsimp
  rw [lemniscate_odd_symmetry]
  ext <;> dsimp <;> ring

/-- Zeta-regularized void coupling: 12 * ζ(-1) = -1 provides the exact
unit cancellation constant for dimension-d SIC dual-frame inversion. -/
theorem zeta_void_coupling : (12 : ℂ) * riemannZeta (-1) = -1 := by
  rw [zeta_neg_one]
  norm_num

/-! ### Higher-Dimensional k-Petal Rose & Centroid Void Theorem -/

/-- Normalized base-2 logarithmic progress parameter u(x) ∈ [0, 1). -/
noncomputable def roseProgress (x : ℝ) : ℝ :=
  (2 / Real.pi) * Real.arctan (Real.log (1 + |x|) / Real.log 2)

/-- Planar k-petal rose embedding Φ_k(x, j) in ℝ × ℝ for branch j : Fin k. -/
noncomputable def rosePetalEmbed (k : ℕ) (x : ℝ) (j : Fin k) : ℝ × ℝ :=
  let u := roseProgress x
  let r := Real.sin (Real.pi * u)
  let α := (2 * Real.pi * (j : ℝ)) / (k : ℝ) +
    (Real.pi / (k : ℝ)) * (2 * u - 1)
  (r * Real.cos α, r * Real.sin α)

/-- Sum of cosines of k equally spaced angles (2πj/k + δ) vanishes for k ≥ 2. -/
lemma sum_cos_roots_of_unity (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) :
    (∑ j : Fin k, Real.cos ((2 * Real.pi * (j : ℝ)) / (k : ℝ) + δ)) = 0 := by
  have hne : Complex.exp ((2 * Real.pi / (k : ℝ) : ℝ) * Complex.I) ≠ 1 := by
    rw [ne_eq, Complex.exp_eq_one_iff]
    rintro ⟨n, hn⟩
    have him : 2 * Real.pi / (k : ℝ) = (n : ℝ) * (2 * Real.pi) := by
      have := congr_arg Complex.im hn
      simpa using this
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have h1 : (n : ℝ) * (k : ℝ) = 1 := by
      field_simp [hkpos.ne'] at him
      linarith
    have hn_int : (n : ℤ) * (k : ℤ) = 1 := by exact_mod_cast h1
    have hdvd : (k : ℤ) ∣ 1 := ⟨n, by linarith⟩
    have hle : k ≤ 1 := Int.ofNat_le.mp (Int.le_of_dvd zero_lt_one hdvd)
    omega
  have hgeom :
      (∑ j : Fin k, Complex.exp ((((2 * Real.pi * (j : ℝ)) / (k : ℝ) + δ : ℝ)) * Complex.I)) = 0 := by
    have hrewrite : ∀ j : Fin k,
        Complex.exp ((((2 * Real.pi * (j : ℝ)) / (k : ℝ) + δ : ℝ)) * Complex.I) =
          Complex.exp ((δ : ℝ) * Complex.I) *
            (Complex.exp ((2 * Real.pi / (k : ℝ) : ℝ) * Complex.I)) ^ (j : ℕ) := by
      intro j
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hrewrite, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range, geom_sum_eq hne]
    have hpow : (Complex.exp ((2 * Real.pi / (k : ℝ) : ℝ) * Complex.I)) ^ k = 1 := by
      rw [← Complex.exp_nat_mul]
      have hkpos : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have harg : (k : ℂ) * ((2 * Real.pi / (k : ℝ) : ℝ) * Complex.I) =
          2 * (Real.pi : ℂ) * Complex.I := by
        push_cast
        field_simp [hkpos]
      rw [harg, Complex.exp_two_pi_mul_I]
    rw [hpow, sub_self, zero_div, mul_zero]
  have hterm : ∀ j : Fin k,
      Real.cos ((2 * Real.pi * (j : ℝ)) / (k : ℝ) + δ) =
        (Complex.exp ((((2 * Real.pi * (j : ℝ)) / (k : ℝ) + δ : ℝ)) * Complex.I)).re := by
    intro j
    rw [Complex.exp_ofReal_mul_I_re]
  simp_rw [hterm]
  have hre := congr_arg Complex.re hgeom
  simpa using hre

/-- Sum of sines of k equally spaced angles (2πj/k + δ) vanishes for k ≥ 2. -/
lemma sum_sin_roots_of_unity (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) :
    (∑ j : Fin k, Real.sin ((2 * Real.pi * (j : ℝ)) / (k : ℝ) + δ)) = 0 := by
  have hcos := sum_cos_roots_of_unity k hk (δ - Real.pi / 2)
  have hshift : ∀ j : Fin k,
      Real.cos ((2 * Real.pi * (j : ℝ)) / (k : ℝ) + (δ - Real.pi / 2)) =
        Real.sin ((2 * Real.pi * (j : ℝ)) / (k : ℝ) + δ) := by
    intro j
    have hsub : (2 * Real.pi * (j : ℝ)) / (k : ℝ) + (δ - Real.pi / 2) =
        ((2 * Real.pi * (j : ℝ)) / (k : ℝ) + δ) - Real.pi / 2 := by ring
    rw [hsub, Real.cos_sub_pi_div_two]
  simpa [hshift] using hcos

/-- Centroid Void Theorem: For any pure k-th prime power N = p^k (k ≥ 2),
the barycenter G = (1/k) ∑ Φ_k(p, j) collapses identically to the central void (0, 0). -/
theorem k_petal_centroid_void (k : ℕ) (hk : 2 ≤ k) (p : ℝ) :
    ((∑ j : Fin k, (rosePetalEmbed k p j).1) / (k : ℝ),
     (∑ j : Fin k, (rosePetalEmbed k p j).2) / (k : ℝ)) = (0, 0) := by
  dsimp [rosePetalEmbed]
  set r := Real.sin (Real.pi * roseProgress p)
  set δ := (Real.pi / (k : ℝ)) * (2 * roseProgress p - 1)
  have hx : (∑ j : Fin k, r * Real.cos ((2 * Real.pi * (j : ℝ)) / (k : ℝ) + δ)) = 0 := by
    rw [← Finset.mul_sum, sum_cos_roots_of_unity k hk δ, mul_zero]
  have hy : (∑ j : Fin k, r * Real.sin ((2 * Real.pi * (j : ℝ)) / (k : ℝ) + δ)) = 0 := by
    rw [← Finset.mul_sum, sum_sin_roots_of_unity k hk δ, mul_zero]
  simp [hx, hy]

/-- The analytic and dual-coordinate results can be carried together through
the Grammar's existing self-fusion law. -/
theorem analytic_dual_frame_witness :
    riemannZeta (-1) = (-1 / 12 : ℂ) ∧
    tetraDualGram * tetraGram = 1 ∧
    Imscribing.Frobenius.μ_A
      GrammarUniversalDualFrameSICPOVM.theGrammar
      GrammarUniversalDualFrameSICPOVM.theGrammar =
    GrammarUniversalDualFrameSICPOVM.theGrammar :=
  ⟨zeta_neg_one, tetra_dual_left_inverse,
    GrammarUniversalDualFrameSICPOVM.grammar_frobenius_closure⟩

end Imscribing.Millennium.ZetaSICDualFrame