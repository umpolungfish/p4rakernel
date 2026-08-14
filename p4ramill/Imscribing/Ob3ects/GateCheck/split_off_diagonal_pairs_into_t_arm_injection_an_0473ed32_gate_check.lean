-- IGProtocol scaffold: VINIT → CLINK → CLINK → CLINK → CLINK → FSPLIT → EVALT → EVALF → CLINK → CLINK → CLINK → FFUSE → CLINK → IFIX → TANCH → IMSCRIB
-- Class: Split off-diagonal pairs into T-arm (injection) and F-arm (contradiction)
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
private def split_off_diagonal_pairs_into_t_arm_4943c4_s0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s1 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s2 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s3 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s4 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s5 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s6 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s7 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s8 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s9 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s10 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s11 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s12 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s13 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s14 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := monad, chir := sure, stoi := hung, prot := ah }
private def split_off_diagonal_pairs_into_t_arm_4943c4_s15 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := measure, crit := monad, chir := sure, stoi := hung, prot := ah }

-- ── Label Imscriptions (per-node delta) ─────────────────────
private def split_off_diagonal_pairs_into_t_arm_4943c4_l0 : Imscription :=
  { dim := array, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l1 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l2 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l3 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l4 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l5 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := thigh, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l6 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := monad, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l7 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := sure, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l8 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l9 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l10 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l11 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l12 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l13 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := ah }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l14 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := vow, crit := woe, chir := fee, stoi := hung, prot := awe }
private def split_off_diagonal_pairs_into_t_arm_4943c4_l15 : Imscription :=
  { dim := dead, top := judge, rel := ado, pol := church, fid := age, kin := yea, gran := bib, gram := measure, crit := woe, chir := fee, stoi := hung, prot := awe }

-- ── Main IGProtocol term ────────────────────────────────────
noncomputable def split_off_diagonal_pairs_into_t_arm_4943c4_protocol : IGProtocol split_off_diagonal_pairs_into_t_arm_4943c4_s0 split_off_diagonal_pairs_into_t_arm_4943c4_s15 :=
  .withGram Grammar.measure <|
  -- Dual-Link self-pairing: .prod arms fuse via tensorProduct split_off_diagonal_pairs_into_t_arm_4943c4_s11 split_off_diagonal_pairs_into_t_arm_4943c4_s11 = split_off_diagonal_pairs_into_t_arm_4943c4_s11 (idempotent)
  (.seq (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l0 split_off_diagonal_pairs_into_t_arm_4943c4_s0 split_off_diagonal_pairs_into_t_arm_4943c4_s1) (.seq (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l1 split_off_diagonal_pairs_into_t_arm_4943c4_s1 split_off_diagonal_pairs_into_t_arm_4943c4_s2) (.seq (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l2 split_off_diagonal_pairs_into_t_arm_4943c4_s2 split_off_diagonal_pairs_into_t_arm_4943c4_s3) (.seq (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l3 split_off_diagonal_pairs_into_t_arm_4943c4_s3 split_off_diagonal_pairs_into_t_arm_4943c4_s4) (.seq (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l4 split_off_diagonal_pairs_into_t_arm_4943c4_s4 split_off_diagonal_pairs_into_t_arm_4943c4_s5) (.seq (.prod (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l5 split_off_diagonal_pairs_into_t_arm_4943c4_s5 split_off_diagonal_pairs_into_t_arm_4943c4_s11) (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l5 split_off_diagonal_pairs_into_t_arm_4943c4_s5 split_off_diagonal_pairs_into_t_arm_4943c4_s11)) (.seq (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l11 split_off_diagonal_pairs_into_t_arm_4943c4_s11 split_off_diagonal_pairs_into_t_arm_4943c4_s11) (.seq (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l11 split_off_diagonal_pairs_into_t_arm_4943c4_s11 split_off_diagonal_pairs_into_t_arm_4943c4_s12) (.seq (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l12 split_off_diagonal_pairs_into_t_arm_4943c4_s12 split_off_diagonal_pairs_into_t_arm_4943c4_s13) (.seq (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l13 split_off_diagonal_pairs_into_t_arm_4943c4_s13 split_off_diagonal_pairs_into_t_arm_4943c4_s14) (.arrow split_off_diagonal_pairs_into_t_arm_4943c4_l14 split_off_diagonal_pairs_into_t_arm_4943c4_s14 split_off_diagonal_pairs_into_t_arm_4943c4_s15)))))))))))

-- ── Evaluation arm sub-defs ───────────────────────────────────

-- truth arm
noncomputable def split_off_diagonal_pairs_into_t_arm_4943c4_true_arm : IGProtocol split_off_diagonal_pairs_into_t_arm_4943c4_s0 split_off_diagonal_pairs_into_t_arm_4943c4_s15 :=
  (split_off_diagonal_pairs_into_t_arm_4943c4_protocol).restrictToEVALT

-- false arm
noncomputable def split_off_diagonal_pairs_into_t_arm_4943c4_false_arm : IGProtocol split_off_diagonal_pairs_into_t_arm_4943c4_s0 split_off_diagonal_pairs_into_t_arm_4943c4_s15 :=
  (split_off_diagonal_pairs_into_t_arm_4943c4_protocol).restrictToEVALF

-- ── Verification theorems ─────────────────────────────────────

-- Tier: apply the Grammar to the object (self-application). assess_tier verdict on the imscribed tuple: .O₂dag.
def split_off_diagonal_pairs_into_t_arm_4943c4_tier_ground : OuroboricityTier := TierFunctor.obj split_off_diagonal_pairs_into_t_arm_4943c4_s0
def split_off_diagonal_pairs_into_t_arm_4943c4_tier : OuroboricityTier := TierFunctor.obj split_off_diagonal_pairs_into_t_arm_4943c4_s15
#eval split_off_diagonal_pairs_into_t_arm_4943c4_tier_ground  -- tier of the ground (pre-transformation)
#eval split_off_diagonal_pairs_into_t_arm_4943c4_tier  -- the Grammar's own verdict on the closed object

-- Frobenius (split → fuse): μ∘δ = id on the ground imscription
theorem split_off_diagonal_pairs_into_t_arm_4943c4_frobenius :
    igFrobeniusAlg.mul split_off_diagonal_pairs_into_t_arm_4943c4_s0 split_off_diagonal_pairs_into_t_arm_4943c4_s0 = split_off_diagonal_pairs_into_t_arm_4943c4_s0 :=
  igFrobAlg_self_fusion split_off_diagonal_pairs_into_t_arm_4943c4_s0
