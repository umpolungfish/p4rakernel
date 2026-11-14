-- IGProtocol scaffold: AFWD → ENGAGR → AFWD → FSPLIT → EVALF → ENGAGR → CLINK → FFUSE → AFWD → IFIX → AFWD → AFWD
-- Class: rb_recoil_alpha
-- Fingerprint: sig=(6,2,3,1)
--   self_ref=True | frobenius_order=1
--   dialetheia_complete=False | period=12
-- Expected tier: O₀
-- FSPLIT/FFUSE pairs: [(3, 7)]

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
--   [1] ENGAGR    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [2] AFWD      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [3] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [4] EVALF     chir   := 𐑖               𐑖 → 𐑖  | evaluate-false — chirality check
--   [5] ENGAGR    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [6] CLINK     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [7] FFUSE     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode
--   [8] AFWD      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [9] IFIX      prot   := 𐑭               𐑭 → 𐑭  | irreversible fixation — winding number
--   [10] AFWD     rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [11] AFWD     rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow

-- ── Back-propagation edges (self-referential loop) ──────────────────────
--   IMSCRIB positions: []
--   IFIX    positions: [9]
--   Back-prop: IMSCRIB→IFIX (LinFix) — igProtoCopy_isDagger axiom applies
--   Weighted: CLINK→IMSCRIB — feeds next winding via .seq after .prod

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def rb_recoil_alpha_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rb_recoil_alpha_s0 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rb_recoil_alpha_s1 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def rb_recoil_alpha_s2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def rb_recoil_alpha_s3 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def rb_recoil_alpha_s4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := sure, stoi := up, prot := awe }
private def rb_recoil_alpha_s5 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := sure, stoi := up, prot := awe }
private def rb_recoil_alpha_s6 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := sure, stoi := up, prot := awe }
private def rb_recoil_alpha_s7 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def rb_recoil_alpha_s8 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def rb_recoil_alpha_s9 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := sure, stoi := hung, prot := ah }
private def rb_recoil_alpha_s10 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := sure, stoi := hung, prot := ah }
private def rb_recoil_alpha_s11 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := sure, stoi := hung, prot := ah }-- ── Label Imscriptions (per-node delta) ─────────────────────
private def rb_recoil_alpha_l0 : Imscription :=  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rb_recoil_alpha_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def rb_recoil_alpha_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rb_recoil_alpha_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rb_recoil_alpha_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def rb_recoil_alpha_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def rb_recoil_alpha_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rb_recoil_alpha_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rb_recoil_alpha_l8 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rb_recoil_alpha_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def rb_recoil_alpha_l10 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rb_recoil_alpha_l11 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def rb_recoil_alpha_protocol : IGProtocol rb_recoil_alpha_initial rb_recoil_alpha_s11 :=
  .withGram Grammar.measure <|
  (.seq (.arrow rb_recoil_alpha_l0 rb_recoil_alpha_initial rb_recoil_alpha_s0) (.seq (.arrow rb_recoil_alpha_l1 rb_recoil_alpha_s0 rb_recoil_alpha_s1) (.seq (.arrow rb_recoil_alpha_l2 rb_recoil_alpha_s1 rb_recoil_alpha_s2) (.seq (.arrow rb_recoil_alpha_l3 rb_recoil_alpha_s2 rb_recoil_alpha_s3) (.seq (.prod (.refl rb_recoil_alpha_s3) (.seq (.arrow rb_recoil_alpha_l4 rb_recoil_alpha_s3 rb_recoil_alpha_s4) (.seq (.arrow rb_recoil_alpha_l5 rb_recoil_alpha_s4 rb_recoil_alpha_s5) (.arrow rb_recoil_alpha_l6 rb_recoil_alpha_s5 rb_recoil_alpha_s6)))) (.seq (.arrow rb_recoil_alpha_l7 (tensorProduct rb_recoil_alpha_s3 rb_recoil_alpha_s6) rb_recoil_alpha_s7) (.seq (.arrow rb_recoil_alpha_l8 rb_recoil_alpha_s7 rb_recoil_alpha_s8) (.seq (.arrow rb_recoil_alpha_l9 rb_recoil_alpha_s8 rb_recoil_alpha_s9) (.seq (.arrow rb_recoil_alpha_l10 rb_recoil_alpha_s9 rb_recoil_alpha_s10) (.arrow rb_recoil_alpha_l11 rb_recoil_alpha_s10 rb_recoil_alpha_s11))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- deposit F
noncomputable def rb_recoil_alpha_false_arm : IGProtocol rb_recoil_alpha_initial rb_recoil_alpha_s11 :=
  (rb_recoil_alpha_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₀.
def rb_recoil_alpha_tier_ground : OuroboricityTier := TierFunctor.obj rb_recoil_alpha_initial
def rb_recoil_alpha_tier : OuroboricityTier := TierFunctor.obj rb_recoil_alpha_s11
#eval rb_recoil_alpha_tier_ground  -- tier of the ground (pre-transformation)
#eval rb_recoil_alpha_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem rb_recoil_alpha_frobenius :
    igFrobeniusAlg.mul rb_recoil_alpha_initial rb_recoil_alpha_initial = rb_recoil_alpha_initial :=
  igFrobAlg_self_fusion rb_recoil_alpha_initial

theorem rb_recoil_alpha_protocol_depth :
    rb_recoil_alpha_protocol.depth = 12 := by rfl

-- The existing dagger theorem requires its O_inf hypothesis.
theorem rb_recoil_alpha_self_ref (h : imscriptionTier rb_recoil_alpha_initial = .O_inf) :
    (igProtoDelta rb_recoil_alpha_initial h).isDagger = true :=
  igProtoCopy_isDagger rb_recoil_alpha_initial h

-- igProtoCopy_isDagger licenses IMSCRIB→IFIX burn
-- CLINK→IMSCRIB weighted edge: .seq continuation

-- ── Alpha decay recoil — conservation of momentum ──
-- p_alpha = -p_daughter, K_alpha/K_daughter = m_d/m_alpha
-- Verified: total momentum zero, kinetic energy sharing by inverse mass ratio.

section AlphaRecoil

noncomputable def kinetic_energy (m p : ℝ) : ℝ := p * p / (2 * m)

-- Conservation of momentum: p_alpha + p_daughter = 0 → p_alpha = -p_daughter
theorem momentum_conservation (p_alpha p_daughter : ℝ) (h : p_alpha + p_daughter = 0) : p_alpha = -p_daughter := by
  linarith

-- Energy sharing ratio: K_alpha / K_daughter = m_daughter / m_alpha
theorem energy_sharing_ratio (m_alpha m_daughter p_alpha p_daughter : ℝ) (h_mom : p_alpha + p_daughter = 0) (h_pnz : p_alpha ≠ 0) (h_pos : 0 < m_alpha) (h_pos2 : 0 < m_daughter) :
    kinetic_energy m_alpha p_alpha / kinetic_energy m_daughter p_daughter = m_daughter / m_alpha := by
  have h₁ : p_daughter = -p_alpha := by linarith
  have h₂ : kinetic_energy m_alpha p_alpha = p_alpha * p_alpha / (2 * m_alpha) := rfl
  have h₃ : kinetic_energy m_daughter p_daughter = p_daughter * p_daughter / (2 * m_daughter) := rfl
  rw [h₂, h₃]
  rw [h₁]
  have h₄ : p_alpha * p_alpha ≠ 0 := by
    apply mul_ne_zero
    · exact h_pnz
    · exact h_pnz
  field_simp [h_pos, h_pos2, h₄]
  <;> ring_nf
  <;> field_simp [h_pos, h_pos2, h₄]
  <;> ring_nf
  <;> norm_num

noncomputable def total_kinetic_energy (m_alpha m_daughter p_alpha p_daughter : ℝ) : ℝ :=
  kinetic_energy m_alpha p_alpha + kinetic_energy m_daughter p_daughter

-- Daughter recoil energy equals alpha energy scaled by mass ratio
theorem daughter_recoil_energy (m_alpha m_daughter p_alpha p_daughter : ℝ) (h_mom : p_alpha + p_daughter = 0) (h_pnz : p_alpha ≠ 0) (h_pos : 0 < m_alpha) (h_pos2 : 0 < m_daughter) :
    kinetic_energy m_daughter p_daughter = kinetic_energy m_alpha p_alpha * (m_alpha / m_daughter) := by
  have h₁ : p_daughter = -p_alpha := by linarith
  have h₂ : kinetic_energy m_alpha p_alpha = p_alpha * p_alpha / (2 * m_alpha) := rfl
  have h₃ : kinetic_energy m_daughter p_daughter = p_daughter * p_daughter / (2 * m_daughter) := rfl
  rw [h₂, h₃]
  rw [h₁]
  have h₄ : p_alpha * p_alpha ≠ 0 := by
    apply mul_ne_zero
    · exact h_pnz
    · exact h_pnz
  field_simp [h_pos, h_pos2, h₄]
  <;> ring_nf
  <;> field_simp [h_pos, h_pos2, h₄]
  <;> ring_nf
  <;> norm_num

end AlphaRecoil

end Imscribing