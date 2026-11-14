-- IGProtocol scaffold: VINIT → ENGAGR → AFWD → AFWD → EVALF → CLINK → IMSCRIB → IFIX → EVALT → IMSCRIB → AREV → AFWD
-- Class: hbar_angular_momentum_protocol
-- Fingerprint: sig=(8,0,3,1)
--   self_ref=False | frobenius_order=0
--   dialetheia_complete=True | period=12
-- Expected tier: O₂dag
-- FSPLIT/FFUSE pairs: []

import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open Matrix

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar Complex
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ENGAGR    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [2] AFWD      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [3] AFWD      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [4] EVALF     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [5] CLINK     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [6] IMSCRIB   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [7] IFIX      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [8] EVALT     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [9] IMSCRIB   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [10] AREV     pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [11] AFWD     rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def hbar_angular_momentum_protocol_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def hbar_angular_momentum_protocol_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def hbar_angular_momentum_protocol_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def hbar_angular_momentum_protocol_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def hbar_angular_momentum_protocol_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def hbar_angular_momentum_protocol_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := up, prot := awe }
private def hbar_angular_momentum_protocol_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := up, prot := awe }
private def hbar_angular_momentum_protocol_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := sure, stoi := up, prot := awe }
private def hbar_angular_momentum_protocol_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := sure, stoi := up, prot := ah }
private def hbar_angular_momentum_protocol_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def hbar_angular_momentum_protocol_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def hbar_angular_momentum_protocol_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def hbar_angular_momentum_protocol_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def hbar_angular_momentum_protocol_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def hbar_angular_momentum_protocol_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def hbar_angular_momentum_protocol_l2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def hbar_angular_momentum_protocol_l3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def hbar_angular_momentum_protocol_l4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def hbar_angular_momentum_protocol_l5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def hbar_angular_momentum_protocol_l6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := sure, stoi := hung, prot := awe }
private def hbar_angular_momentum_protocol_l7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := sure, stoi := hung, prot := ah }
private def hbar_angular_momentum_protocol_l8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def hbar_angular_momentum_protocol_l9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def hbar_angular_momentum_protocol_l10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := sure, stoi := up, prot := ah }
private def hbar_angular_momentum_protocol_l11 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def hbar_angular_momentum_protocol_protocol : IGProtocol hbar_angular_momentum_protocol_initial hbar_angular_momentum_protocol_s11 :=
  IGProtocol.withGram Grammar.measure <|
    (.seq (.arrow hbar_angular_momentum_protocol_l0 hbar_angular_momentum_protocol_initial hbar_angular_momentum_protocol_s0)
      (.seq (.arrow hbar_angular_momentum_protocol_l1 hbar_angular_momentum_protocol_s0 hbar_angular_momentum_protocol_s1)
        (.seq (.arrow hbar_angular_momentum_protocol_l2 hbar_angular_momentum_protocol_s1 hbar_angular_momentum_protocol_s2)
          (.seq (.arrow hbar_angular_momentum_protocol_l3 hbar_angular_momentum_protocol_s2 hbar_angular_momentum_protocol_s3)
            (.seq (.arrow hbar_angular_momentum_protocol_l4 hbar_angular_momentum_protocol_s3 hbar_angular_momentum_protocol_s4)
              (.seq (.arrow hbar_angular_momentum_protocol_l5 hbar_angular_momentum_protocol_s4 hbar_angular_momentum_protocol_s5)
                (.seq (.arrow hbar_angular_momentum_protocol_l6 hbar_angular_momentum_protocol_s5 hbar_angular_momentum_protocol_s6)
                  (.seq (.arrow hbar_angular_momentum_protocol_l7 hbar_angular_momentum_protocol_s6 hbar_angular_momentum_protocol_s7)
                    (.seq (.arrow hbar_angular_momentum_protocol_l8 hbar_angular_momentum_protocol_s7 hbar_angular_momentum_protocol_s8)
                      (.seq (.arrow hbar_angular_momentum_protocol_l9 hbar_angular_momentum_protocol_s8 hbar_angular_momentum_protocol_s9)
                        (.seq (.arrow hbar_angular_momentum_protocol_l10 hbar_angular_momentum_protocol_s9 hbar_angular_momentum_protocol_s10)
                          (.arrow hbar_angular_momentum_protocol_l11 hbar_angular_momentum_protocol_s10 hbar_angular_momentum_protocol_s11))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- kinetics true deposit
noncomputable def hbar_angular_momentum_protocol_true_arm : IGProtocol hbar_angular_momentum_protocol_initial hbar_angular_momentum_protocol_s11 :=
  (hbar_angular_momentum_protocol_protocol).restrictToEVALT

-- chirality false deposit
noncomputable def hbar_angular_momentum_protocol_false_arm : IGProtocol hbar_angular_momentum_protocol_initial hbar_angular_momentum_protocol_s11 :=
  (hbar_angular_momentum_protocol_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def hbar_angular_momentum_protocol_tier_ground : OuroboricityTier := TierFunctor.obj hbar_angular_momentum_protocol_initial
def hbar_angular_momentum_protocol_tier : OuroboricityTier := TierFunctor.obj hbar_angular_momentum_protocol_s11
#eval hbar_angular_momentum_protocol_tier_ground  -- tier of the ground (pre-transformation)
#eval hbar_angular_momentum_protocol_tier  -- the Grammar's tuple-tier verdict

theorem hbar_angular_momentum_protocol_protocol_depth :
    hbar_angular_momentum_protocol_protocol.depth = 12 := by rfl

-- ħ Angular Momentum — exact matrix computation in Lean 4.
-- Spin-1/2 representation with physical ħ.
-- Verified: J² = (3/4)ħ²I, [Jx,Jy] = iħJz, Jz = diag(±ħ/2).

section SpinHalf
variable (ħ : ℝ)

-- Pauli matrices (dimensionless)
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, (-1 : ℂ)]

-- Angular momentum operators: J = (ħ/2) σ — direct matrix entries
noncomputable def Jx (ħ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), (ħ / 2 : ℂ); (ħ / 2 : ℂ), (0 : ℂ)]
noncomputable def Jy (ħ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), (-Complex.I * (ħ / 2 : ℂ)); (Complex.I * (ħ / 2 : ℂ)), (0 : ℂ)]
noncomputable def Jz (ħ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(ħ / 2 : ℂ), (0 : ℂ); (0 : ℂ), (-ħ / 2 : ℂ)]

-- Pauli matrix identities (concrete 2×2 matrix computation)
theorem σx_sq : σx * σx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [σx, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> rfl

theorem σy_sq : σy * σy = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [σy, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> rfl

theorem σz_sq : σz * σz = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> rfl

theorem σx_σy : σx * σy = Complex.I • σz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> rfl

theorem σy_σx : σy * σx = (-Complex.I : ℂ) • σz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply]
  <;> norm_num [Complex.ext_iff, Complex.I]
  <;> rfl

-- J² = Jx² + Jy² + Jz² = (3/4)ħ² I  (entry-wise verification)
theorem J2_half (ħ : ℝ) : Jx ħ * Jx ħ + Jy ħ * Jy ħ + Jz ħ * Jz ħ =
    !![(3 / 4 * (ħ : ℂ) * (ħ : ℂ) : ℂ), (0 : ℂ); (0 : ℂ), (3 / 4 * (ħ : ℂ) * (ħ : ℂ) : ℂ)] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  simp [Jx, Jy, Jz, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Complex.ext_iff, pow_two]
  <;> norm_num at *
  <;> ring_nf at *
  <;> norm_num at *
  <;>
  (try { simp_all [Complex.ext_iff] })
  <;>
  (try { norm_num })
  <;>
  (try { rfl })
  <;>
  (try { linarith })

-- [Jx, Jy] = JxJy − JyJx = iħ Jz  (entry-wise verification)
theorem comm_half (ħ : ℝ) : Jx ħ * Jy ħ - Jy ħ * Jx ħ =
    !![(Complex.I * (ħ : ℂ) * (ħ : ℂ) / 2 : ℂ), (0 : ℂ);
      (0 : ℂ), (-Complex.I * (ħ : ℂ) * (ħ : ℂ) / 2 : ℂ)] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
  simp [Jx, Jy, Jz, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Complex.ext_iff, pow_two]
  <;> norm_num at *
  <;> ring_nf at *
  <;> norm_num at *
  <;>
  (try { simp_all [Complex.ext_iff] })
  <;>
  (try { norm_num })
  <;>
  (try { rfl })
  <;>
  (try { linarith })

-- Jz = diag(ħ/2, -ħ/2), eigenvalues ±ħ/2
theorem Jz_form (ħ : ℝ) : Jz ħ = !![(ħ / 2 : ℂ), 0; 0, (-ħ / 2 : ℂ)] := by rfl

-- J² eigenvalue for spin-1/2: j(j+1)ħ² = (3/4)ħ²
theorem j2_eigenvalue_half : (3 / 4 : ℝ) = (1 / 2 : ℝ) * ((1 / 2 : ℝ) + 1) := by norm_num

end SpinHalf
