import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import Imscribing.IMASM.BankedWeight
import Imscribing.Millennium.GrammarUniversalDualFrameSICPOVM

/-! Analytic value, explicit tetrahedral dual Gram matrix, and the supplied
analytical_continuation_sic_povm reversal checkpoint. -/
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
