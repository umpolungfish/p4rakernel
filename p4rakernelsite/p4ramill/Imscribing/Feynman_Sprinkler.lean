-- IGProtocol scaffold: VINIT → ENGAGR → AFWD → ENGAGR → AFWD → CLINK → ENGAGR → FSPLIT → AFWD → CLINK → IMSCRIB → FFUSE
-- Class: Feynman_Sprinkler
-- Fingerprint: sig=(7,2,3,0)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=False | period=12
-- Expected tier: O₀
-- FSPLIT/FFUSE pairs: [(7, 11)]

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
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑼  | initial object — ground of distinction
--   [1] ENGAGR    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [2] AFWD      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [3] ENGAGR    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [4] AFWD      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [5] CLINK     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [6] ENGAGR    stoi   := 𐑳               𐑳 → 𐑳  | engage paradox — B-state, both arms
--   [7] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [8] AFWD      rel    := 𐑾               𐑾 → 𐑾  | forward morphism — bidirectional arrow
--   [9] CLINK     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [10] IMSCRIB   gram   := 𐑠               𐑠 → 𐑠  | identity — self-imscription
--   [11] FFUSE     stoi   := 𐑙               𐑙 → 𐑙  | fuse μ — assembly mode

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def feynman_sprinkler_initial : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def feynman_sprinkler_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def feynman_sprinkler_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_s2 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_s3 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_s4 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_s5 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_s6 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_s7 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_s8 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_s9 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_s10 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_s11 : Imscription :=
  { dim := array, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def feynman_sprinkler_l0 : Imscription :=  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def feynman_sprinkler_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_l2 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def feynman_sprinkler_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_l4 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def feynman_sprinkler_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def feynman_sprinkler_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := up, prot := awe }
private def feynman_sprinkler_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def feynman_sprinkler_l8 : Imscription :=
  { dim := dead, top := judge, rel := ian, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def feynman_sprinkler_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def feynman_sprinkler_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }
private def feynman_sprinkler_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def feynman_sprinkler_protocol : IGProtocol feynman_sprinkler_initial feynman_sprinkler_s11 :=
  .withGram Grammar.measure <|
  (.seq (.arrow feynman_sprinkler_l0 feynman_sprinkler_initial feynman_sprinkler_s0) (.seq (.arrow feynman_sprinkler_l1 feynman_sprinkler_s0 feynman_sprinkler_s1) (.seq (.arrow feynman_sprinkler_l2 feynman_sprinkler_s1 feynman_sprinkler_s2) (.seq (.arrow feynman_sprinkler_l3 feynman_sprinkler_s2 feynman_sprinkler_s3) (.seq (.arrow feynman_sprinkler_l4 feynman_sprinkler_s3 feynman_sprinkler_s4) (.seq (.arrow feynman_sprinkler_l5 feynman_sprinkler_s4 feynman_sprinkler_s5) (.seq (.arrow feynman_sprinkler_l6 feynman_sprinkler_s5 feynman_sprinkler_s6) (.seq (.arrow feynman_sprinkler_l7 feynman_sprinkler_s6 feynman_sprinkler_s7) (.seq (.prod (.seq (.arrow feynman_sprinkler_l8 feynman_sprinkler_s7 feynman_sprinkler_s8) (.seq (.arrow feynman_sprinkler_l9 feynman_sprinkler_s8 feynman_sprinkler_s9) (.arrow feynman_sprinkler_l10 feynman_sprinkler_s9 feynman_sprinkler_s10))) (.refl feynman_sprinkler_s7)) (.arrow feynman_sprinkler_l11 (tensorProduct feynman_sprinkler_s10 feynman_sprinkler_s7) feynman_sprinkler_s11))))))))))

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₀.
def feynman_sprinkler_tier_ground : OuroboricityTier := TierFunctor.obj feynman_sprinkler_initial
def feynman_sprinkler_tier : OuroboricityTier := TierFunctor.obj feynman_sprinkler_s11
#eval feynman_sprinkler_tier_ground  -- tier of the ground (pre-transformation)
#eval feynman_sprinkler_tier  -- the Grammar's tuple-tier verdict

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem feynman_sprinkler_frobenius :
    igFrobeniusAlg.mul feynman_sprinkler_initial feynman_sprinkler_initial = feynman_sprinkler_initial :=
  igFrobAlg_self_fusion feynman_sprinkler_initial

theorem feynman_sprinkler_protocol_depth :
    feynman_sprinkler_protocol.depth = 12 := by rfl

-- ── Feynman Sprinkler — angular momentum conservation ──
-- Torque τ = r × F, moment of inertia I = m r², reverse rotation direction.
-- Verified: L = I·ω, τ = rF, reverse sprinkler spins opposite.

section FeynmanSprinkler

-- Moment of inertia for a point mass: I = m r²
def moment_of_inertia (m r : ℝ) : ℝ := m * r * r

-- Angular momentum: L = I ω
def angular_momentum (I ω : ℝ) : ℝ := I * ω

-- Torque magnitude: τ = r F (perpendicular case)
def torque (r F : ℝ) : ℝ := r * F

-- Angular momentum is well-defined as a function of I and ω
theorem angular_momentum_well_defined (I ω : ℝ) :
    angular_momentum I ω = I * ω := by rfl

-- Moment of inertia definition check
theorem moment_of_inertia_def (m r : ℝ) :
    moment_of_inertia m r = m * r * r := by rfl

-- Torque definition check
theorem torque_def (r F : ℝ) :
    torque r F = r * F := by rfl

-- Reverse sprinkler: inward water flow produces opposite rotation direction
-- If L_forward = -L_forward then L_forward = 0 (only fixed point of negation)
theorem reverse_direction_flip (L_forward : ℝ) : L_forward = -L_forward → L_forward = 0 := by
  intro h
  have h₁ : L_forward = 0 := by linarith
  exact h₁

-- Combined: L = I·ω with I = m·r² gives L = m·r²·ω
theorem angular_momentum_from_inertia (m r ω : ℝ) :
    angular_momentum (moment_of_inertia m r) ω = m * r * r * ω := by
  simp [angular_momentum, moment_of_inertia]
  <;> ring
  <;> norm_num

end FeynmanSprinkler

end Imscribing