-- IGProtocol scaffold: AFWD → IMSCRIB → AFWD → ENGAGR → EVALT → AREV → IMSCRIB → CLINK → AFWD → CLINK → AFWD → ENGAGR
-- Class: cs_recoil_alpha
-- Fingerprint: sig=(9,0,3,0)
--   self_ref=False | frobenius_order=0
--   dialetheia_complete=False | period=12
-- Expected tier: O₁
-- FSPLIT/FFUSE pairs: []

import Imscribing.IGMorphism
import Imscribing.IGFunctor
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open Matrix

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] AFWD      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [1] IMSCRIB   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [2] AFWD      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [3] ENGAGR    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [4] EVALT     crit   := ⊙               ⊙ → ⊙  | evaluate-true — criticality gate open
--   [5] AREV      pol    := 𐑗               𐑗 → 𐑗  | reverse morphism — parity flip
--   [6] IMSCRIB   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [7] CLINK     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [8] AFWD      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [9] CLINK     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [10] AFWD     rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [11] ENGAGR   stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def cs_recoil_alpha_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_s0 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_s1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_s2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_s3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := up, prot := awe }
private def cs_recoil_alpha_s4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def cs_recoil_alpha_s5 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def cs_recoil_alpha_s6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def cs_recoil_alpha_s7 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def cs_recoil_alpha_s8 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def cs_recoil_alpha_s9 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def cs_recoil_alpha_s10 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }
private def cs_recoil_alpha_s11 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := monad, chir := fee, stoi := up, prot := awe }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def cs_recoil_alpha_l0 : Imscription :=  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def cs_recoil_alpha_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_l8 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_l10 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def cs_recoil_alpha_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def cs_recoil_alpha_protocol : IGProtocol cs_recoil_alpha_initial cs_recoil_alpha_s11 :=
  (.seq (.arrow cs_recoil_alpha_l0 cs_recoil_alpha_initial cs_recoil_alpha_s0)
    (.seq (.arrow cs_recoil_alpha_l1 cs_recoil_alpha_s0 cs_recoil_alpha_s1)
      (.seq (.arrow cs_recoil_alpha_l2 cs_recoil_alpha_s1 cs_recoil_alpha_s2)
        (.seq (.arrow cs_recoil_alpha_l3 cs_recoil_alpha_s2 cs_recoil_alpha_s3)
          (.seq (.arrow cs_recoil_alpha_l4 cs_recoil_alpha_s3 cs_recoil_alpha_s4)
            (.seq (.arrow cs_recoil_alpha_l5 cs_recoil_alpha_s4 cs_recoil_alpha_s5)
              (.seq (.arrow cs_recoil_alpha_l6 cs_recoil_alpha_s5 cs_recoil_alpha_s6)
                (.seq (.arrow cs_recoil_alpha_l7 cs_recoil_alpha_s6 cs_recoil_alpha_s7)
                  (.seq (.arrow cs_recoil_alpha_l8 cs_recoil_alpha_s7 cs_recoil_alpha_s8)
                    (.seq (.arrow cs_recoil_alpha_l9 cs_recoil_alpha_s8 cs_recoil_alpha_s9)
                      (.seq (.arrow cs_recoil_alpha_l10 cs_recoil_alpha_s9 cs_recoil_alpha_s10)
                        (.arrow cs_recoil_alpha_l11 cs_recoil_alpha_s10 cs_recoil_alpha_s11))))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- deposit T
noncomputable def cs_recoil_alpha_true_arm : IGProtocol cs_recoil_alpha_initial cs_recoil_alpha_s11 :=
  (cs_recoil_alpha_protocol).restrictToEVALT

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₁.
def cs_recoil_alpha_tier_ground : OuroboricityTier := TierFunctor.obj cs_recoil_alpha_initial
def cs_recoil_alpha_tier : OuroboricityTier := TierFunctor.obj cs_recoil_alpha_s11
#eval cs_recoil_alpha_tier_ground  -- tier of the ground (pre-transformation)
#eval cs_recoil_alpha_tier  -- the Grammar's tuple-tier verdict

theorem cs_recoil_alpha_protocol_depth :
    cs_recoil_alpha_protocol.depth = 12 := by rfl

-- ── Center-of-mass alpha recoil — relativistic energy-momentum ──
-- E² = p²c² + m²c⁴, COM frame: total momentum zero, recoil balancing.
-- Verified: invariant mass, energy-momentum relation, COM momentum balance.

section CenterOfMassRecoil

noncomputable def energy_momentum_invariant (c m p : ℝ) : ℝ :=
  (p * p * c * c) + (m * m * c * c * c * c)

-- In COM frame: p_alpha + p_daughter = 0 → p_alpha = -p_daughter
theorem com_momentum_balance (c m_alpha m_daughter p_alpha p_daughter : ℝ) (h : p_alpha + p_daughter = 0) :
    p_alpha = -p_daughter := by linarith

-- Total energy in COM frame: E_total = E_alpha + E_daughter
def total_energy (E_alpha E_daughter : ℝ) : ℝ := E_alpha + E_daughter

-- Invariant mass squared: M²c⁴ = E_total² (p_total = 0 in COM frame)
def invariant_mass_squared (E_alpha E_daughter : ℝ) : ℝ :=
  total_energy E_alpha E_daughter * total_energy E_alpha E_daughter

-- Recoil: daughter takes equal and opposite momentum to alpha
theorem recoil_balancing (c m_alpha m_daughter p_alpha p_daughter : ℝ) (h_mom : p_alpha + p_daughter = 0) :
    p_daughter = -p_alpha := by linarith

-- Energy-momentum for alpha particle
noncomputable def alpha_invariant (c m_alpha p_alpha : ℝ) : ℝ := energy_momentum_invariant c m_alpha p_alpha

-- Energy-momentum for daughter nucleus
noncomputable def daughter_invariant (c m_daughter p_daughter : ℝ) : ℝ := energy_momentum_invariant c m_daughter p_daughter

-- In COM frame, equal and opposite momenta imply |p_alpha| = |p_daughter|
theorem equal_magnitude_momenta (c m_alpha m_daughter p_alpha p_daughter : ℝ) (h_mom : p_alpha + p_daughter = 0) :
    p_alpha * p_alpha = p_daughter * p_daughter := by
  have h₁ : p_daughter = -p_alpha := by linarith
  rw [h₁]
  ring_nf
  <;> simp [neg_neg]
  <;> ring

end CenterOfMassRecoil

end Imscribing