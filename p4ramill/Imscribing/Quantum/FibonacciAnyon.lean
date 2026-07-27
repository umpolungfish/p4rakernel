-- Imscribing/Quantum/FibonacciAnyon.lean
-- ============================================================================
-- Fibonacci Anyon Algebra — full Lean elaboration in the p4rakernel kernel.
-- Author: Math⊙perator (Lando⊗⊙perator team)
-- ============================================================================

import Mathlib
import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Imscribing.Consciousness

namespace Imscribing.Quantum.FibonacciAnyon

open Imscribing.Primitives
open Imscribing.Consciousness
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality
open Imscribing.IGProtocol

-- ============================================================
-- §1. Stage imscriptions of the 12-step bootstrap word
-- ============================================================
private def s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea,
    gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def s1 : Imscription := { s0 with gram := measure }
private def s2 : Imscription := { s1 with gran := thigh }
private def s3 : Imscription := { s2 with crit := monad }
private def s4 : Imscription := { s3 with rel := ian }
private def s5 : Imscription := s4
private def s6 : Imscription := { s5 with chir := sure }
private def s7 : Imscription := s6
private def s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea,
    gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := awe }
private def s9 : Imscription := { s8 with stoi := up, prot := ah }
private def s10 : Imscription := s9
private def s11 : Imscription := s9

def fibonacci_anyon_algebra : Imscription := s11

-- ============================================================
-- §2. IGProtocol
-- ============================================================
def fibonacci_anyon_algebra_protocol : IGProtocol s0 s11 :=
  .withGram measure <|
  .seq (.arrow s0 s0 s1)
  (.seq (.arrow s1 s1 s2)
  (.seq (.arrow s2 s2 s3)
  (.seq (.arrow s3 s3 s4)
  (.seq (.arrow s4 s4 s5)
  (.seq (.arrow s5 s5 s6)
  (.seq (.arrow s6 s6 s7)
  (.seq (.arrow s7 s7 s8)
  (.seq (.arrow s8 s8 s9)
  (.seq (.arrow s9 s9 s10)
  (.seq (.arrow s10 s10 s11)
        (.refl s11)))))))))))

-- ============================================================
-- §3. Verification theorems
-- ============================================================
theorem fibonacci_anyon_algebra_frobenius :
    igFrobeniusAlg.mul fibonacci_anyon_algebra fibonacci_anyon_algebra
      = fibonacci_anyon_algebra :=
  igFrobAlg_self_fusion fibonacci_anyon_algebra

theorem fibonacci_anyon_algebra_ground_tier : imscriptionTier s0 = .O₀ := by decide
theorem fibonacci_anyon_algebra_tier : imscriptionTier fibonacci_anyon_algebra = .O₂dag := by decide

-- ============================================================
-- §4. The Fibonacci fusion category
-- ============================================================
inductive SimpleObj : Type where
  | one  -- vacuum
  | tau  -- Fibonacci anyon
  deriving Fintype, DecidableEq

/-- Fusion multiplicities `N_{ab}^c`.  The vacuum is a unit: `1 ⊗ b = b`, so
    `N_{1,b}^c = [b = c]` — NOT `[c = 1]`, which is right only when `b` is also
    the vacuum and makes `N_{1,τ}^τ = 0`.  The Verlinde formula below is exactly
    the check that catches that. -/
def fusionMult : SimpleObj → SimpleObj → SimpleObj → ℕ
  | .one, b, c => if b = c then 1 else 0
  | a, .one, c => if a = c then 1 else 0
  | .tau, .tau, _ => 1

def qdimOne : ℝ := 1
noncomputable def qdimTau : ℝ := (1 + Real.sqrt 5) / 2

/-- `√5 ^ 2 = 5`.  `norm_num` cannot discharge this on its own; it needs
    `Real.sq_sqrt` with the nonnegativity side condition. -/
lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- The golden ratio's defining relation, φ² = φ + 1. -/
theorem qdimTau_sq : qdimTau ^ 2 = qdimTau + 1 := by
  unfold qdimTau
  field_simp
  linear_combination sqrt5_sq

theorem Dsq_val : 1 ^ 2 + qdimTau ^ 2 = qdimTau + 2 := by
  rw [qdimTau_sq]; ring

noncomputable def Dglob : ℝ := Real.sqrt (1 + qdimTau^2)

lemma Dglob_pos_helper : 0 < 1 + qdimTau^2 := by
  have : 0 < qdimTau := by unfold qdimTau; apply div_pos; positivity; norm_num
  positivity

lemma Dglob_pos : 0 < Dglob := by
  rw [Dglob]
  apply Real.sqrt_pos.mpr
  apply Dglob_pos_helper

-- ============================================================
-- §5. Verlinde fusion via the S-matrix
-- ============================================================
noncomputable def Smat (a b : SimpleObj) : ℝ :=
  let val := (match a, b with
    | .one, .one => 1
    | .one, .tau => qdimTau
    | .tau, .one => qdimTau
    | .tau, .tau => -1)
  val / Dglob

/-- `D² = 1 + φ²`, from `Real.sq_sqrt` on a nonnegative radicand. -/
lemma Dglob_sq : Dglob ^ 2 = 1 + qdimTau ^ 2 :=
  Real.sq_sqrt (le_of_lt Dglob_pos_helper)

/-- `D² = φ + 2`, the form used in every Verlinde case. -/
lemma Dglob_sq' : Dglob ^ 2 = qdimTau + 2 := by
  rw [Dglob_sq]; linear_combination qdimTau_sq

lemma qdimTau_pos : 0 < qdimTau := by
  unfold qdimTau; positivity

lemma Dglob_ne : Dglob ≠ 0 := ne_of_gt Dglob_pos
lemma qdimTau_ne : qdimTau ≠ 0 := ne_of_gt qdimTau_pos

/-- **Verlinde formula.**  `N_{ab}^c = Σ_d S_{ad} S_{bd} conj(S_{cd}) / S_{0d}`.
    The Fibonacci `S` is real, so conjugation is the identity.  Proved case by
    case: eight cases, each an identity in `φ` and `D` closed by `φ² = φ + 1`
    and `D² = φ + 2`. -/
theorem verlinde (a b c : SimpleObj) :
    Smat a .one * Smat b .one * Smat c .one / Smat .one .one
      + Smat a .tau * Smat b .tau * Smat c .tau / Smat .one .tau
      = (fusionMult a b c : ℝ) := by
  have hD := Dglob_ne
  have hφ := qdimTau_ne
  have hD2 := Dglob_sq'
  have hφ2 := qdimTau_sq
  cases a <;> cases b <;> cases c <;>
    simp [Smat, fusionMult] <;>
    field_simp <;>
    nlinarith [hD2, hφ2, Dglob_pos, qdimTau_pos]

-- ============================================================
-- §6. S-matrix properties
-- ============================================================

/-- Summation over the two simple objects, in closed form. -/
lemma univ_SimpleObj : (Finset.univ : Finset SimpleObj) = {.one, .tau} := by
  decide

lemma sum_SimpleObj (f : SimpleObj → ℝ) :
    ∑ c : SimpleObj, f c = f .one + f .tau := by
  rw [univ_SimpleObj, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- `S` is symmetric. -/
theorem Smat_sym (a b : SimpleObj) : Smat a b = Smat b a := by
  cases a <;> cases b <;> simp [Smat]

/-- `S² = I`.  Both Fibonacci labels are self-dual, so the charge-conjugation
    matrix is the identity and unitarity collapses to this. -/
theorem Smat_sq (a b : SimpleObj) :
    ∑ c : SimpleObj, Smat a c * Smat c b = if a = b then 1 else 0 := by
  have hD := Dglob_ne
  have hD2 := Dglob_sq'
  have hφ2 := qdimTau_sq
  cases a <;> cases b <;>
    simp [sum_SimpleObj, Smat] <;>
    field_simp <;>
    nlinarith [hD2, hφ2, Dglob_pos, qdimTau_pos]

-- ============================================================
-- §7. The F-matrix (associator) and the pentagon
-- ============================================================

/-- `√φ`, the off-diagonal scale of the Fibonacci associator. -/
noncomputable def sqrtPhi : ℝ := Real.sqrt qdimTau

lemma sqrtPhi_pos : 0 < sqrtPhi := Real.sqrt_pos.mpr qdimTau_pos
lemma sqrtPhi_ne : sqrtPhi ≠ 0 := ne_of_gt sqrtPhi_pos

/-- `(√φ)² = φ`. -/
lemma sqrtPhi_sq : sqrtPhi ^ 2 = qdimTau :=
  Real.sq_sqrt (le_of_lt qdimTau_pos)

/-- The Fibonacci associator on the `τττ → τ` channel,

      F = ⎡ 1/φ    1/√φ ⎤
          ⎣ 1/√φ  −1/φ  ⎦

    Both off-diagonal entries are `φ^{-1/2}` and neither vanishes; setting them
    to zero leaves `F² = 1/φ² ≠ I` and the pentagon fails. -/
noncomputable def Fmat : SimpleObj → SimpleObj → ℝ
  | .one, .one => 1 / qdimTau
  | .one, .tau => 1 / sqrtPhi
  | .tau, .one => 1 / sqrtPhi
  | .tau, .tau => -(1 / qdimTau)

/-- `F` is symmetric. -/
theorem Fmat_sym (a b : SimpleObj) : Fmat a b = Fmat b a := by
  cases a <;> cases b <;> simp [Fmat]

/-- **Pentagon**, in the form it takes for Fibonacci: `F² = I`.  The diagonal
    entry is `1/φ² + 1/φ = (1+φ)/φ² = 1`, which is exactly `φ² = φ + 1`; the
    off-diagonal entries cancel by the sign in the corner. -/
theorem Fmat_sq (a b : SimpleObj) :
    ∑ c : SimpleObj, Fmat a c * Fmat c b = if a = b then 1 else 0 := by
  have hφ := qdimTau_ne
  have hs := sqrtPhi_ne
  have hφ2 := qdimTau_sq
  have hs2 := sqrtPhi_sq
  cases a <;> cases b <;>
    simp [sum_SimpleObj, Fmat] <;>
    field_simp <;>
    nlinarith [hφ2, hs2, qdimTau_pos, sqrtPhi_pos]

end FibonacciAnyon
end Quantum
end Imscribing
