-- IGProtocol scaffold: VINIT → CLINK → CLINK → CLINK → CLINK → FSPLIT → EVALT → EVALF → CLINK → CLINK → CLINK → FFUSE → CLINK → IFIX → TANCH → IMSCRIB
-- Class: Refute diagonal equality a = b on F-arm via hne condition
-- Fingerprint: sig=(11,2,2,1)
--   self_ref=False | frobenius_order=1
--   dialetheia_complete=False | period=16
-- Expected tier: O₂dag
-- FSPLIT/FFUSE pairs: [(5, 11)]

import Imscribing.IGMorphism
import Imscribing.IGFunctor

namespace Imscribing
open Primitives Frobenius IGProtocol
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection Stoichiometry Chirality

-- ── Token → IG field mapping ──────────────────────────────────────────────
--   [0] VINIT     dim    := 𐑼               𐑼 → 𐑱  | initial object — ground of distinction
--   [1] CLINK     fid    := 𐑱               𐑼 → 𐑱  | composition — regime coherence
--   [2] CLINK     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [3] CLINK     fid    := 𐑱               𐑱 → 𐑱  | composition — regime coherence
--   [4] CLINK     fid    := 𐑱               𐑱 → 𐑚  | composition — regime coherence
--   [5] FSPLIT    gran   := 𐑚               𐑚 → 𐑚  | split δ — range decomposition
--   [6] EVALT     crit   := ⊙               𐑚 → 𐑙  | evaluate-true — criticality gate open
--   [7] EVALF     chir   := 𐑖               𐑚 → 𐑙  | evaluate-false — chirality check
--   [8] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [9] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [10] CLINK     fid    := 𐑱               𐑚 → 𐑙  | composition — regime coherence
--   [11] FFUSE     stoi   := 𐑙               𐑙 → 𐑱  | fuse μ — assembly mode
--   [12] CLINK     fid    := 𐑱               𐑙 → 𐑭  | composition — regime coherence
--   [13] IFIX      prot   := 𐑭               𐑱 → 𐑡  | irreversible fixation — winding number
--   [14] TANCH     top    := 𐑡               𐑭 → 𐑠  | terminal object — connectivity boundary
--   [15] IMSCRIB   gram   := 𐑠               𐑡 → 𐑼  | identity — self-imscription

-- ── Stage Imscriptions (per-node cumulative) ────────────────
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s4 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s5 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s6 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s7 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s8 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s9 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s10 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s11 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s12 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s13 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s14 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_s15 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def refute_diagonal_equality_a_b_on_f_arm_8d71e2_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def refute_diagonal_equality_a_b_on_f_arm_8d71e2_protocol : IGProtocol refute_diagonal_equality_a_b_on_f_arm_8d71e2_s0 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s15 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct refute_diagonal_equality_a_b_on_f_arm_8d71e2_s11 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s11 = refute_diagonal_equality_a_b_on_f_arm_8d71e2_s11 (idempotent)
  (.seq (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l0 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s0 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s1) (.seq (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l1 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s1 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s2) (.seq (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l2 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s2 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s3) (.seq (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l3 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s3 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s4) (.seq (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l4 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s4 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s5) (.seq (.prod (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l5 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s5 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s11) (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l5 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s5 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s11)) (.seq (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l11 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s11 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s11) (.seq (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l11 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s11 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s12) (.seq (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l12 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s12 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s13) (.seq (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l13 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s13 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s14) (.arrow refute_diagonal_equality_a_b_on_f_arm_8d71e2_l14 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s14 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s15)))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def refute_diagonal_equality_a_b_on_f_arm_8d71e2_true_arm : IGProtocol refute_diagonal_equality_a_b_on_f_arm_8d71e2_s0 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s15 :=
  (refute_diagonal_equality_a_b_on_f_arm_8d71e2_protocol).restrictToEVALT

-- false arm
noncomputable def refute_diagonal_equality_a_b_on_f_arm_8d71e2_false_arm : IGProtocol refute_diagonal_equality_a_b_on_f_arm_8d71e2_s0 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s15 :=
  (refute_diagonal_equality_a_b_on_f_arm_8d71e2_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def refute_diagonal_equality_a_b_on_f_arm_8d71e2_tier_ground : OuroboricityTier := TierFunctor.obj refute_diagonal_equality_a_b_on_f_arm_8d71e2_s0
def refute_diagonal_equality_a_b_on_f_arm_8d71e2_tier : OuroboricityTier := TierFunctor.obj refute_diagonal_equality_a_b_on_f_arm_8d71e2_s15
#eval refute_diagonal_equality_a_b_on_f_arm_8d71e2_tier_ground  -- tier of the ground (pre-transformation)
#eval refute_diagonal_equality_a_b_on_f_arm_8d71e2_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem refute_diagonal_equality_a_b_on_f_arm_8d71e2_frobenius :
    igFrobeniusAlg.mul refute_diagonal_equality_a_b_on_f_arm_8d71e2_s0 refute_diagonal_equality_a_b_on_f_arm_8d71e2_s0 = refute_diagonal_equality_a_b_on_f_arm_8d71e2_s0 :=
  igFrobAlg_self_fusion refute_diagonal_equality_a_b_on_f_arm_8d71e2_s0
