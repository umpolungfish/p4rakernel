-- IGProtocol scaffold: VINIT → CLINK → CLINK → CLINK → CLINK → FSPLIT → EVALT → EVALF → CLINK → CLINK → CLINK → FFUSE → CLINK → IFIX → TANCH → IMSCRIB
-- Class: Rejoin T-arm and F-arm into single counting bound verdict
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
private def rejoin_t_arm_and_f_arm_into_single_61b456_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s4 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s5 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s6 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s7 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s8 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s9 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s10 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s11 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s12 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s13 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s14 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def rejoin_t_arm_and_f_arm_into_single_61b456_s15 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def rejoin_t_arm_and_f_arm_into_single_61b456_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def rejoin_t_arm_and_f_arm_into_single_61b456_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def rejoin_t_arm_and_f_arm_into_single_61b456_protocol : IGProtocol rejoin_t_arm_and_f_arm_into_single_61b456_s0 rejoin_t_arm_and_f_arm_into_single_61b456_s15 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct rejoin_t_arm_and_f_arm_into_single_61b456_s11 rejoin_t_arm_and_f_arm_into_single_61b456_s11 = rejoin_t_arm_and_f_arm_into_single_61b456_s11 (idempotent)
  (.seq (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l0 rejoin_t_arm_and_f_arm_into_single_61b456_s0 rejoin_t_arm_and_f_arm_into_single_61b456_s1) (.seq (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l1 rejoin_t_arm_and_f_arm_into_single_61b456_s1 rejoin_t_arm_and_f_arm_into_single_61b456_s2) (.seq (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l2 rejoin_t_arm_and_f_arm_into_single_61b456_s2 rejoin_t_arm_and_f_arm_into_single_61b456_s3) (.seq (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l3 rejoin_t_arm_and_f_arm_into_single_61b456_s3 rejoin_t_arm_and_f_arm_into_single_61b456_s4) (.seq (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l4 rejoin_t_arm_and_f_arm_into_single_61b456_s4 rejoin_t_arm_and_f_arm_into_single_61b456_s5) (.seq (.prod (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l5 rejoin_t_arm_and_f_arm_into_single_61b456_s5 rejoin_t_arm_and_f_arm_into_single_61b456_s11) (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l5 rejoin_t_arm_and_f_arm_into_single_61b456_s5 rejoin_t_arm_and_f_arm_into_single_61b456_s11)) (.seq (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l11 rejoin_t_arm_and_f_arm_into_single_61b456_s11 rejoin_t_arm_and_f_arm_into_single_61b456_s11) (.seq (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l11 rejoin_t_arm_and_f_arm_into_single_61b456_s11 rejoin_t_arm_and_f_arm_into_single_61b456_s12) (.seq (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l12 rejoin_t_arm_and_f_arm_into_single_61b456_s12 rejoin_t_arm_and_f_arm_into_single_61b456_s13) (.seq (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l13 rejoin_t_arm_and_f_arm_into_single_61b456_s13 rejoin_t_arm_and_f_arm_into_single_61b456_s14) (.arrow rejoin_t_arm_and_f_arm_into_single_61b456_l14 rejoin_t_arm_and_f_arm_into_single_61b456_s14 rejoin_t_arm_and_f_arm_into_single_61b456_s15)))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def rejoin_t_arm_and_f_arm_into_single_61b456_true_arm : IGProtocol rejoin_t_arm_and_f_arm_into_single_61b456_s0 rejoin_t_arm_and_f_arm_into_single_61b456_s15 :=
  (rejoin_t_arm_and_f_arm_into_single_61b456_protocol).restrictToEVALT

-- false arm
noncomputable def rejoin_t_arm_and_f_arm_into_single_61b456_false_arm : IGProtocol rejoin_t_arm_and_f_arm_into_single_61b456_s0 rejoin_t_arm_and_f_arm_into_single_61b456_s15 :=
  (rejoin_t_arm_and_f_arm_into_single_61b456_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def rejoin_t_arm_and_f_arm_into_single_61b456_tier_ground : OuroboricityTier := TierFunctor.obj rejoin_t_arm_and_f_arm_into_single_61b456_s0
def rejoin_t_arm_and_f_arm_into_single_61b456_tier : OuroboricityTier := TierFunctor.obj rejoin_t_arm_and_f_arm_into_single_61b456_s15
#eval rejoin_t_arm_and_f_arm_into_single_61b456_tier_ground  -- tier of the ground (pre-transformation)
#eval rejoin_t_arm_and_f_arm_into_single_61b456_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem rejoin_t_arm_and_f_arm_into_single_61b456_frobenius :
    igFrobeniusAlg.mul rejoin_t_arm_and_f_arm_into_single_61b456_s0 rejoin_t_arm_and_f_arm_into_single_61b456_s0 = rejoin_t_arm_and_f_arm_into_single_61b456_s0 :=
  igFrobAlg_self_fusion rejoin_t_arm_and_f_arm_into_single_61b456_s0
